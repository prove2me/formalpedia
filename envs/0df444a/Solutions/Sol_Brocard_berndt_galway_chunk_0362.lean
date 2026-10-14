-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0362
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:25:32.377978+00:00
-- url     : https://prove2.me/submissions/4f63ca2f-499e-4b33-8455-990517895db8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 64928060 ≤ n < 65107916 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 64929310 1250 64928060 64928063
    0xf0a0902030f06070305151504031101171003020f040507020a1101030f110403120f080a0f0e0a0b09190c05100504080f030415080403080420100905040507020601080d050f16 76
    0xd4840d410880c190b5494020310a800b030040b5035040c099907145146044602403804010b100c008a804bc000c03050703000300b081a58420325020810b01d03504d002401c07418007a1032440220302500010702249054a03040c003441c4d02c2a5480e90080807001c040740c030350040903c0041788075810315940700c8120b9071581e850300494021209000700140e40c0d900c0d515028205102e551448001c0108226203017030074545c001c00244d00301200e0030740401d0b0044c503050160002c14206904000030320508022104015540c3c20f20740c4a01c00c460b040d5007030300742c2550540c0c0d407107080fa0704003d1019054500c240414034141c1e9206134000002d00e8298201500c420700b10b458503000500d00100c1d03510100d010400b0490300100034503140c1140c0742403d0b803410a80d902030648040600b0045c20004030707096400d4614031102c910300610b0b2000707180e40405e6503101c401805080050242c02e00a600304000034420900004540e070480c1c118100520380000f060000719401c1e0010000e0a14100e030400c00413400740b00200f400103185 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 64930560 1250 64929310 64929317
    0x30513030f020a05010804030801060302030a02120906150a21080d180c1d1302030114011e090e0a02101704030503180a0c05010e060706090507080607080f0a0902030f0607 75
    0x440c1076004201520401c0c0e840141044010710400001a078401c0409046602038100035850b51074603038802001e4024280501c240b40c602404100c0184d0000583c03602038844017070000320520b030700f606211904450b802904000c011840c0c0c00040c12035211a1049074501803900c0d00d00f004040d001c403006907442d010a20442a10440c844024400c00110364801007001c2c04c00e5458a454041c11000301e00c7c03004001c1080860000004001e644080d0000303a480410302d10262303401e41e114603a00c00000202880d00140d1b400d10080420030106511840310350402110042100340515402c008800f00c1845546003041403114546400c1d0b05005145070156200c0e4990307545134506840e2508015144201501d41580150480404030b40110042c2b230940d8000e1031b040142450003070100d000b07440f580d00010600c0d0714107d21142440300c082465000d6030080c00541e04a0b45841004485250b4152a03e049541d41003011518035503880d800708050a01c0a0142c540001d01a4041812b0071070407203406022 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 64931810 1250 64930560 64930583
    0x71d1203091c0c0302010c02130e010203091905060a020903070e01031208070315061d0306011410050406090b0904090605180706020706050f0318100902030c01050306030c040903051303 81
    0x540c90511075510105075007945040020340c907a00d0f03543c896161444080d06212100002c0380a5485508510040c1d00c00d80034103100d00360000003480d000391305c1103a03c0400b501590b0840048000801804e40300316412000412003611198a160003c0d800f549a542d81882100c90000381c0d42008490f01d8020b5004452940d95400447d034080c10041e401451481010300c1c10300303000b2000e04c0f40740720101659040e160442600c020154904080f00342200303c00d505100b12400020030301c02441c0c07843c16041050f59202020201070205441c9400b4600035080030442c00c8805008e00b41e0000090f03c0059801000841c0b10089901c902e01195005e07600b81f240c401030a00b00c0030980004020300d40040c0a14030041104914240d8014814003070314800d10580750000022502808035444e000d2141c6c641201130f12840e200c2465010000c3c8411103040303000780180d506c460381d40c0d801881682e03c01c0c1000780291070f16800041c200402002c40d8501201484424481c0004154000c01c040c40030b14030074102c6042 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 64933060 1250 64931810 64931827
    0xd020909090102070c0b03010b0a08220516090507020715020a0605040305031501020c0105070206030402030f0d090609050f0a0b070f081903140c0a110c060a03050106080603070806071d1203 83
    0x45c490f50340041c400520304200400c40c021009007110b04607851407400003029200c10b912001d045840040d42c030f452800307208450090020109005c40c14000c0040750f981c2803641c039443e0b00c05607030b8101c0306440980c000305401c12030203889054103210402c4a2042c2c80d2030000c5a541d80040310425202a40000d0002c41045555600581d40c00940750090000345609a1752500003400ea1082860007800b80001001107811510200038404031718585030142e03109501002401403d41250740304200003e40e815000013802d04109038030007000b05018004c5080300e0300389655030515074081001100c2507006130003800081800030000d8001d10388034480d014402000c50340d005003980d007100b42422840391f851052059180084080f030b06200201d041410707417402c0d029001801d042d0300c5072440d0780107500010300c2041d03154154000d07130683d00b1607114410700351514800e0669031000c07401340000c030790300180210715100d009240381030040444003403095101503810041180c0800e82740c800304060b840840d0032071 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 64934310 1250 64933060 64933073
    0x4060509010e04050603060105040209060708040905040302071403030d0207110d0c0801060f140f0a090e011508030309070b1605010219030c050f0d0b040905010216170705060c0d02090909010207 85
    0xb144000c1c00c503811302c142e05104000a40314401845454401d55001402c078400da02c2d42c6003902c2003180c01540c540d0b01da580e0381c40d420f0007800c0708440443c0180205500820a403845141014030440e024000318200511000440020740c4800c4c02070b20740b840d603a00646041e0342e40e59003448000c5e00c9015072112442c40c1025050a4030055085850001300c441014012480102507100c81c2c81001c8407015000d000fa1b07008502603c400d134203c84402410712000320410b0005401c08840000c60102a00d4486d585016160f10380c00161440c140f00d4001100801003118581c1c003900c401d400304c201c1e032100d07108165580d41c01c83e440840a07138074454001ca0740e103d0300743e014800c5822030103e504005240040c00c4480700d840d4442e9042c0031500541d18890a074503601c40d94007010160382d00c41c0085580d40030f81002d0040c1c64500c200b040302c3c007000c400065001080a481a50302c20b80d07215004002945400745800d172240c2140705883c002540c240321400e07082c0d40707840301035003d0018140010b90701c0301c1c03030704015 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 64935560 1250 64934310 64934327
    0xf030f070905011505030402061308150906070c0201020312091617070501030c050708030a110f030f0a0b030a030e060c03040308041802090a031529040f0b0a0e07140406050901 77
    0xe048050003407082000303030317040300031641e000ea8101c441c80d5031400390026511450000341c00203455446002032401e80700c0c40140919001d10720040440300c00796201c0c002141e1640031240002d005030428400c0b54280c208179101c1540002c0343c00281c5483d00e010559103400c241c0c4c15885441050a804282c0c6070a07c000c1c440071021302400c2c1707010f0142c0900450040e0040c0308002009100c101c0000c000746c0ca41440b64014254460030b00d10290307031032054408991b000c1d0410388400002000c81c00101c0d04040350340c401c0050044025024254004c5103403416200c00c03a44170b401c1508110104460b220b010001d000500c081d500c500603043d1140d00b41407540c418802c04020043d4482c3c130410901c4600d070341e00184041125800f400d010410b0b0840c0a060019002a1801d00d0007082c104071a80701660502d003d420110009880030005c05108003650008d0b150101a0113400107221141448121602c0600ca0341c0031407141418400c0300c912071401115640198058070008101013a205032560f0b000020 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 64936810 1250 64935560 64935569
    0xc0309021305010b120a060902030112060b0a3503070c06090806040507030816061103011802070c0e07140304030801030b09160b0a030b03100b15070b0c0304020f030f07090501 77
    0x4010644c14803400940c14031075201c280c1e000800c03100c00503007465015003081010f81950803055440756958020380903062070001007100c04905081c03800f203040c148000c03010200c5e84000d108180c0080b005e9032200701c0314891041e02685075440c1c2203100844000f00000d00c1003511401c1c11072034543c80c112004210100d00d401c0310209400180600021490005046040d41c2d080303400d40c1e950350054081d8040f451a028030052a09003403185c02e12690740030030041d5048070f03d81030141405800b0b540100d0100c0c070915800900e40003c00405001d40c000c0700082e01d604c00513a040240400c0c440b111503800c990030459040340056125401402040140c02a5039004414440107008424040154958600c2da50160060200000c1440b14032503110b03030011200c0203c0501901c0143c25112103041c003070240003455074003840884901c2600031309400708130f0b6005604514440103075210302a0741c8103103500260043c0d81c13040181c61046801d1b601440501840782d100d00003000542d15002900c019140705a10 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 64938060 1250 64936810 64936849
    0xf06130b0925020a0506040305030a06050d1410020a051206040b0a03051006050d33060608090111040303020613031211070605071d060c0115060906020c04050c09010c050f010c030902 80
    0x104000020000521281c00a80c0750901a0300d0340d03032f22640000245541e500295001c00703c020070005003c03040e0300701450b00441c0c40c00c0e1303845400d0a1111800764030507288000001a0100905110080c5c80d404845e00504003c0c8003007076209584000684003c2c0e9504140c405802c0100e01091140d030510801e030003030100382c03a081601c00c015144c0e85003146c00e0382400c03601e40400707990403c0c101c1c0824080580c4200c0b07000003046032640b2031030000c04c2c3c000100e03011450742d80390441004030405042e0076641141d5056000b081c00341d4030000300d4104101e141008405101040c1e5040181c100d40e4083c10031440c000301c00c0c0540344c0611b03045c0201910005840b20051020490107002c031400b80d01c2142000400560f01d1f990b07240303010500a03004148581800b003581c107180002145095020000a00302c91300c650840c0c0c41c4a94130b07820002114015144031411960030000b45c65254081c0f503010f0300d4240202c06880c43d46d0f206403211400c0d81c403c3c244840000ba55460342d84110b240c81400d1000e08200e622 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 64939310 1250 64938060 64938073
    0x9070f05030c010e0d030306080d050c0c0306040b07180906030803060108060a0b0307050f0f0703090e090102040e06040c020a0f06270503040b131203080406140f06130b092502 77
    0xc0060068a10448114000d410881700d003802e01d4081d40004000380000001c40e40c107414070400007001c43d002144020021b01420442000c9450000340b805d000d19080604154942c454150070b44841100100c0320360842e0490b00001451540d500c2480000c40c021070352550f907440c00c3c600051044100806442c07040f03031241024001c001e100002d50342c0c840d40741d041c00c664480ca006800c107294010b9008280ca420000690f8008165104000c0c408030343c0d00740d003214041d03220308140500303038051402070390242483c10000484900e0b064000c0500600d103801598203500f11070710307600600502c3c5e91003030303074865140e030001c8c0c026440608409009210444100c000e018991303a9181d02e03445103110300030724400c002c13808004903011a0079410040008009204d071500c102d2a000d00a020100c1e400c2d81e4a1b40ba040e40d1103130007890500442d02c107109a0f9807080b042d5071500c08000149405250641e513003540c1d00200c14190300c62584050142c0c441140c002918040585202005001190301c3c0c0210340008 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 64940560 1250 64939310 64939333
    0x3020f06090a140f07090b04020409020706020c010b0916030506120a1101090605040b0304080702010e0a03060e06060628020f1005090709111c140a0b0102061501091a09040509070f0503 81
    0x4151720050f2100d0b214042a2041c400f400180640519000b00e114a07200003000d604000f1594024100100008000d0140301e03e00c1007003001d003600881c1d1243d0410400c0d58038000c60392095110f180d00c50780007448135040681030004545030840720b940442e164070461080a400c0d680100d070100c02014203151141c90315042c40d0041500d070101501c01002d0b00404507280302160302800701012601c4c8040c1c4480900b561300d00b04035001d0920b4210009880c0601c2c07000c541c1d81d003009401c445a03a091036202910025000b5041014910013000e200c00f1802021511800359400b0f200400490040910100301400c0503581d8600b0308920740d010301c08841c81c116a08210aa0340010307a141030100d407181c42c084c001d00c0781c81c6101034085043c00104420210003086520786017580705c2481e8103801c0e0b00729903844e560f032140540d00c01c0910800502065a8ae102085560464899240318410403200c40d8102030f165030100382907071000e0300d15980580103500e0a0280100807150007008107021001802c031030008 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 64941810 1250 64940560 64940563
    0x9030c17160b0a020706020a02100507081015030b03010203010909051504031e09080304060f031406011b0602040e04030c050f01060b030a0b040b1305061302030c1603020f06090a140f 80
    0x1e507038010040c80340600080d40104460b070660301c0140e048901590390f0301407050000e441c2c1d04070001d0b410104e131030701000c108494400c1c84124820700d80a8003101056080501c0c640d45c00702c11003604010152078624910541d2001c0c00654000c100c41c110110381d14441c0c0c80d0540c14805103d012120601c44041040b0200c0d07070200c0003100402c0309001c801450a0070040403030380c180450300058420301c0002000103040e64440d4903034115441a980c1002110411500408001c1c815207403c1d002606501d800101c850b609060060b00d54420800146020344e280ca115103603507012034081d000b180b0030281200c1480750912180304d00c1e4a003003000304622420890702e000c56001c06803d9201d01541d03016205040d480e2980721546c0020000c02601c0c50001e08160304000d490100c911a0098a1212516609558900907a0f000c1c09036951000d040113098200c03c3c6084101c0705003681140304040040d10706d8581070007081c1c06105440081c090610050030709035420b101a803001c3c801940700e02c05203030307640701c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 64943060 1250 64941810 64941847
    0x5120a0507020307170306090c070201090504051503100608010b09010815060607051c0f05070c12050313150e22050c0c0102180901080a030503150109030609030c17 72
    0x990110000d541d8403415800c918500480c000101181218880000311100140c082c52290308207c4403480c050b40c4005005840d4041d200001b0301007048110140a0340c03410360409036101d408003414000707184018000910748142c0424003003016680304401d2152040a0160040c0b82c0e0b01540c21080c01d52500c4c04031580c840d20440c04040700030900d03001c540c0d103650b040200c51005402904494000ca034090450f24294500044680414901098540b09074054002c4d213007203035040340740803100ea4644900b2945201101d0300440d40c90008114003d008144405900c003c1c0c0401010344150310083c8d14040d01c03002c482c8182d00d00c142c40b80720749a4400445804c0c0441381104111021641c0e448030001d064107405108410704840d400030031b011048050605100c04802c2c0b04803405250369980389003040e1142e40b00b200190001e00100001940041003041060182e1010b15003482d407070390b481d202c0c030b4201c035107181d0200d002890098040090001010039051a1040700c050285080e000c04090a100c00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 64944310 1250 64943060 64943071
    0xf0509060604031e05030d0f05090606152709070206010603060b03060d0305071a07050a020721120c12090306050a0c080a0b01020f12030103140106060909020702061303050d030c0512 80
    0x98200d071300c80200181030040ea6901003002105000f4403081e484035201a00f400c54540740d9500c29080050828070b06201301c00d61080c43c0d0340605160800d030007042d1510014159042100140e4000a106662540c80c801807103a462a03000c3c1003994104a4002c0c1a00c40c00c0d48a010141c2050050040307541d101104641044d0b07050410f159164058a401901f81d44000c0314030b020701843c18100800c0c2c6400400030000e4901950036107400750303200c1d81b20b0071000528405403151558101440000100c4004070300c140e03004103061020402641c4c0d0754682c42c121103141c40c600007038941d0a0801c1000042d001c0c817070b00b10b08101014070414245010041880c1c400400356858180c032030101103480d034000e000803007400c11128142c500001c0e01e041c11901680c8207100c02c072a849a40d98140030399110600c101d02c1911131941d80c8069040c40c15502401a4200010590b4003440800166a100c2c081010500003140318201804040a441401030b0490301c030700701030310300f0b100e0204066410341440802950b03104 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 64945560 1250 64944310 64944353
    0xf0602010e1b19060e0301110c07030206070201090e0702030a14030906040816020d05030c0c030d02120a11010903020106080c062a120c03030a1802130506010e0a0f050906060403 78
    0x2003480000080c001c2c284250000c1c001408090046046a403110685d59450310544c001e012803011600d07511400e22655000114036000b000301403005160801c010802c060051400c522126102d400e5030a00c2d80040d07480740003603030000919540700c90f000300740000c0070300d0a22a414110328042150a840e283d00400091444d4400103500700781a80b440c41c11210290094120381e41d10300c582c54031a82e01d07480546c8040e02486054003011035440c0000d420361012003560f000c0e01070b400000448800d02d8000b411908284100810801ba1a400920038130f01d08500a82c008100d1500d4074980c039080841025025006034010082c041088844015110740300365100300400c03503514071202c00b60508040c0c01c82154801c2d80040c7c0081c102400101850107408a0081000203203610214543e4405d00010b0080d042802059664010f81030356010710b03170110041c10140201a003100c00070301c000b00e0b0390b00000e5200c10800400d00007400d084800c150302c04026503500e840c190564450b0140a42c01d00300e03c00c81d0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 64946810 1250 64945560 64945603
    0x9030613022e18080709090b090613030c060b120a0b010801110a0c080c1203010906121a0402010903050d0203070605090d140f04050406030c0801180305030612031e040f0602010e 78
    0x5800c00d64250f0801001140240c41844c0c0d2180358920240030703a51b4082d2980005540446d074035000204030540100c0d8050040c0040c40f0080c1e505440103d54842c0c00d544c09991551101c0a41d01d4962120040c01000301c0a4241d104480c506030b01c0b90101078001210720781c035084844078880704040840300d5590840c10804201d428900c0c000e100c901c036404608003140100354555680c0700340800550f0607204034040c03d01c01d19803201011007649520001c0903040740c0f0680c61042d007080d00144000d42250041c0340c0401c0d400d8698440a06d8101380c081840700607800025a48103000883c0300d056042111640541514003803940c009010000503008031041801c00030f01c0100c211071501c1114018076000d00148201c1380d803410048507042c06803050311059400c100312007005044e20081842c03200d905854060440d110501071000151003035071520305902c01007100300190380358000181c156075244d2010a540340d04000c41150385008942c0050250381c104507003141d04181c007140300d02609181e04840b43d00c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 64948060 1250 64946810 64946837
    0x7020a0203061305160b1308010b1012021911010b09040c03031416060615020102090a03080306010e0603040f0201031b0f0e01050405130c08060607020a090507030209030613022e 78
    0x180140c0d0009810410045c40000070010000341c00340100f240d40c0a01011b005690300c84140c00e1310146002d25034400c100034259641c460150105400d10111140c3c01414100c060388880084c14203100b00b031002c502002c0d142e50010109004d035001c815401d960179101828603684000c529440350000600348a400110100c9407803038403050314429041150141c100ea0001e0404000500550040000c5e0b20320328a060415135005008680700c1d84009883d4034002403031901c41c00300607000500380c80d0402a103010b40d10202e1361903201a600450280103030001e600300a1001408441010740f201c03042120758816584030350b8003c8560b0300140710905201400340d28420040350b692040f074001e41d5001601d03041d2980507020031ba02c880a070030003030348400d0443d4850354108400742c021150001d502c03040d01e0409104000d8141c1003a40c000e095400d0240c00c110f080c000003814440c0440b1110a44000d80300100154039003a848040c1c44500c03800c2c2d82c3c100002d195502900488210b41c50030038821650f41e03844 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 64949310 1250 64948060 64948063
    0x5060d1107050a0803071713060b03010b030115150323040c0b03070302030a060906050a0b0903120304150609020307050409180203010e01020a030b032413020a0b0a020607020a0203061305 82
    0xc1c0740540c00829244502ca02d0300c0c102440d5002034461000058000900c0403130300035001011405a12200d0403002e0226031550f07000d000e4480c5c441942c0d015500c0709001902500c09029010701c1d00b003540c21100c091030400b040c40940c40b42c3c21814a04060800192100f0a09046000000d508400f1403060241d07071203061046000801e07511913254503030000200540568182c0c099405011030b01000e009070341e41c914400013619114003030181c0c0310f00502010000c500c0508020040c8940281c203640000d614202040b92a40007202d01fa1001200003400e5004040b5920449000d4400300c18118194102020001c1c818019409070030710140c0e849040b084400c1c100b54000002c01d900500900c0414800181c0c9800703900141c9a000203c2e00b4030648a00c5031030049030000080d000c1c004840c0002c2a003036403640d0642e4000c1c03c0300300c81050511301c840c00368540075000d001a0001140c441d64800d083d00d0000d00c0c00d5802050b180854100b0558500141e40c08150250029071903a05091100400d04046 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 64950560 1250 64949310 64949317
    0xf1a060301181103011511060103110d0c05120a050d051608181003060611060c0a030c1b03030203040b0c1908070e0306040b09060702161e0e04061d010605060d11 71
    0x1603c42003011000140050350080d40025000c2c4582c0c071070844030b07440d0800c1c640c2d0307141c00e000040850241884084c40c5040c4029005001c80c000d590000003150343e840032620903a1041c11010027500102001d04c20b00504100e44050f203e510710308641b07018130060301788000d101d2107980104a80e01c0014001500c52200600c0d40c02060024140e004807080300c4000f07002044144a400042424200d61922042d404183c071031090300034504540c50710003690800c40c010308040404000f032016612a807015404005c0040102920075207005940b030520742491200b4450040c644071500c00c081000e500010600d09000720b52a0540c10a0825910303001000ea6486203400041900b5120781e0003003005202135a101d00b8014901c0d2010b48000783c568000c120317180c0c8841344910000034103d900411034122002e86003c0717441c82000c0381c250041c4e103a00e1441e030500e40c1074405555040e1aa80241c110040001c0ca1107d10344141c1c0c02041030529120125410703028966060843c03540d21006982e060001c3c0044 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 64951810 1250 64950560 64950581
    0x303060503150105090109020c060c07030311030103050d2a0609020102071e1403010c08011202010e09040b090105010902271302030c0c0c0319080c0106180f1a06030118 74
    0x2980c00840b8201c840c0e011014003440b80c1c41c401d580351000015641014822034000c0c1d6115070150150b81d4540f00500525403043c02e0450402d6503070145034600724120340207140694401d070040c0640005020000301112103481c180194520b80c5001c0401540f81803621200e081d134040c01c0402c40340b0b400d0005038289a185e901429400c1034491401020303070014062681658401c0c1025040502c41c002498200c402c2c41c1e0402d00400d07800710051004c400c442400f9114944145410070b050782110021480402040e03808551807885042401050304013030150764007504203070a0850038200d03080306203225004450040c0c1036420101c9604545d81e00e48410364007004100c02c0040d0750300d042c080c0d1814082d6015000e410301900644c4030380315040c540490b0480c0b44030501c00109114050355158041d5a0307111040030140e0350342e9201d00040000061504400500301041c0000701c0b10785101c0084196020150792000000e4003281003480356441c841502d040d00d1600d40c0c2205004540b0019000500c0080b50 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 64953060 1250 64951810 64951813
    0x30a060509240c0409051504330b1c110d0204051e060f0912030408060103020907030b0a05091305010c03060810060e010e090a0503030103060c2006040b15040608030d1b1b0303060503 80
    0x101c0020011403c9270311325424120154828400c101c0030412032041c07080c1c06141c1104c00c0400400d504441c030b412410251441c061000142170400b940505115808100d0400903540c01040401c118a401703005103032485002c0144040d08500306000a410344128a03660707484100108a524103a1250144e46003040324a6080b295102e0b11151180e6507000240700480c4101362110004494038428020400150405002a4812230410081015565000b40040d51018896070043c005c10424001c000500b4400d883c001429803c29044e0ba00b032000340c00541802e1800c00c1d00402a88140c0e0040c00d0441d81d100754a0381d010b495841e046402c003410024041c085110210002c41840308903403045104c0162910f4550202880841c81307034a03440944c2b541c040e142c0040c80044c2c04a1741c0d0702c074200d51003c4851240318450a039480014119100c54000010551000c50250b803c00d60074840c21101d10356a54070750403403039224a80144440d0b14084071041d8020300d107203540e00305400398101202a160090 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 64954310 1250 64953060 64953071
    0xa090f03060e06010b0c0a0602070602070b0a0c02070512100507090e040b0a06050a08060f040201030b03030406050403060e0c210a20150a050a0c02030a060509240c0409051504 77
    0x50500c003a107082e442c520441c3c061100002403030000a42120081922003010b01080421500c80c40025040003a0940c2c0260b001c202c2c10000410401c00244210050f8000040200c003000c0300a1030048180c00803401848101c0400b484c140000a0014007007981d00c0d004609075031121421a01840307194010a002107841c41480200300301c200c513041c030800c0c0103d010480142d4610400015250301d208916458000c0300125001001c0800999030050060501281241c100303800f00b803560340254000000554007040034001c0054030300031641c0840c50f080c0140182c0016000140c20b823040c0205039402030b201c0e0380604002c10702c14450020391542080448141003400d031287e0480040d6000c45500c40e04260b00600c4c030840c84481510b40c10707110703580c0d40c50070500841d10a54180444090699261150000d02030000cac0395405042d00c2024084003a00040c4200402101c009803807402d80310001000c02d040190500000041d2411102661b038040340a4450061031951a1031080c000c84c2c1160401 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 64955560 1250 64954310 64954313
    0x2d030d0903050f070b19030905120d0506041413050f0703061407080421090b04090603031d060702090408091002070609090203011520071202040b0f090c0a090f03 71
    0x3003110085901640644031559108101070380c5950b224095580c1c6442c00384034065866691510f07240f1100614103000074400c060351104c5140030303040c6590840224002035800c040e24441d000716138201c44152014007445240c9502c5030f0104d070000b014000030031650a0240280f060030400201454103010035074281c15140d00784600940500c4904800000c24800070507180e511440b0600d200e90b402054000d007014022104d1b401c00c5603032012103002c2045050000c500780b49158024001404c009500142c503601d507140250004040a00040d000002e04400400315165002110011581142c4000117030f03881b0f24007290b481c0101d40ca015041014441c0c04030100e9000514a0280d0f00d90740ca407002543c0da0359044d0008d07440b00740540d07080f031600000301ca942c0a0180e0b08051240142050210302c45500191907880c0c40900d0340400c3d4584101c0c6c040c603083d030a0521607180e250606030788030603064442d0804186200b10250085205040c00580304d01814410000c11020702003c074450441d060340c9 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 64956810 1250 64955560 64955567
    0x7020a0e09070504110c1e0a08040e090c030a050304050f01030603080c06090f07120b04030c122111072004060605090a08010e0706050a1407030f02060108010203062d030d 75
    0x80f4003030315000314600b00e03221a050100300291011041800010154a240b06119030066001d4041704620392040310346440c00101401301030400340c050b001c610708003071805e1402d40b480c0c0001d40030f10b40c2c0030383c12400007940403810104c200e6013900d005030360002e40083c130301c80100c00030107840c0c1c00030f00000c2c2c01107420000d650010541d5400340c0d0345003085550b082e1950710900d07100c086510541b900310800c1c0001c0d4002035040006d03690700a0003402d00707224855181e20b4080c0c08000e4104000c0003c0c0b804080c0714100e5003603044200009550440811850f22804400078480c85100c0c0042e01d030703001c00c1c199655084002030003400030000c041c005001d0380f5507891000e0525044140c18504c1181a068046840c030414810901c012417800000d0400c5490040242c409500034200701082111b4600706000101440c0002c00380280b10781e984010000c04424001d080410603000700390076034010001d2280caa038562032220394408a0b02110b001e1000024030708403442e440060301c0340e01805030b180e150004680 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 64958060 1250 64956810 64956823
    0x30403020a0b1903050112060b041d0609150c040b0702040e011e0f0207050705150c06010f05010206090706090b09040207060c0c0b0c04060f0f030b130204080705030f0309040207020a0e09 82
    0x980107040c4140680c0c0143c160141d8109025200c0d4000d903400c45040818a25040a0140780b03000c2e000260740d0492419a54280d804c907011104954450401d11600704000c01c1001e100040701201cad1803141c10700c203280c171510f4030842c894107603689404900482950348030380c003440c4030442c80340c020800711080c622451035161806018480fa80d180070f0103041000014000c4400243d80134001d8a40a400e19040000d49110711340c1400b0085010b000682e11300800f081140e01802c83c42c1d03176030484d203846c00000a2902c03200400360125504803c9041145ca80c00c0300510042d82c81c01d00d00a0b80300c0e44501d01050090260505c058080c40c00d01c5012071025400c0560780711500c2c01101542c0c0d02d83e85821007a400c0b80308520441c1c0008283e83c0201c1003162050311003900b180054174001c540031409800103010003010b10128445950300040421000d90200181002810290090724410142000b25a01c4e401004069030086400184450842d600c038407500001d455100501c21250a050100c01d80e07030f00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 64959310 1250 64958060 64958077
    0x2010f1808010c1202070203071e03050f0616170601050c0a05030f070302070e0405060403050702040b0409051c030b0603040609060e0f01020703030b0114030a0903020c060a020c030c0a05090c03060102030403020a0b 94
    0x42040c4c140c1141d031004c6008a440281c1c010f401410114901075110f0041752689003d0003618003000b101000103201031040141e6150401c0091000c0c0c02c280304d008100d0300510344070b00144a1122026080408107c140d16804002400c240ba1107851014080b82405640c000090a501000130a0f120b408003803c0586860381c001c8d42260001a11200203076020032055401030070391f900200c00280024400d00c000d0010502c09000450011036460104013640c0c4204011a0a40c10503901d140c04200780b2540c08129801c40d15050003000707000341c007090b01440007501c06425030340c541401109002c0e19030400000148140200e03000090400e13a024000d412036030702240001d00f003801a205c10342c46080c441e807a002400356002e28544400c9942030090009800071000d50042001c0c6404503956080903010803074440c1c02030300032102d03040100350501308010300c4d5501c80c803c1c40209115548618a2940e481520040e401356070742c80300c3e40142d01d180510703403000754007000c40710012030f0040030140603133a0309 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 64960560 1250 64959310 64959317
    0x90a0213030c0f0506040803040e04020607060c0806010e060306011d04021603050408060705042409030602160b01120803060120070b180904080a0e01090f03060c080703020703080402010f1808010c 86
    0x16503c0e03808005252081d4441c280b0954409d01c000c1c8140ea8080c034000303400a1000345014600803643d9904c10a80d61703c4000100800d112804100955812aa030300d50601e000300c0e04540b071880c080d80060036a285a00028614140c030300d00c0c60582d52540d504481440e642c2d03e48064101c4030074030f0001c0056100d4058056680521004540e064dc0039800307031025144050078024030525407650400204120310440d03410440605000008185c4038401020541d02c103081c1d4494010f282e0074060324500c01a80200e082c003000005130300201b0540340540390050803d107010001c2c0d51070070360139800e042c882608412490003200070025010024800901268050080d00a05405034004100c40044210b802030402d01c005c1010540107071007001c250000c8001410901c010036140c451900c0c090020b07800403a14260b48454400000d5006040103034004400d140644c5041c03402d40d1f004100c3e12000d40024184041145c2d410b50143c042c09041c1a000c03400c81200c18015520310f0794601038801c40106d45c010 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 64961810 1250 64960560 64960589
    0x105300f0601141206090601021f1b021603111f0305180d0e09070203130902210c0409020a1116230a0b03090a051203041b0311090a0213030c 62
    0xe410103000d440c01a415211040c1440d981c2c5e40c1806803048000b0915411802010740f00d007211007101c08607005565a69900041ea24030041d81200703011851ba00c03603415580850340c0c0106030008920007100341e039800704140d5104007050000c698455071382c1c02c0718031011310040320840b1000d0303043d1f01440c4107005942d289502548002c1d800e90701d48680c400c0480c0040c1d14405103002c281040640707107410100a104880c03401d119264a00301582c81d81c1c0043c80020380000e410199450a18061078410200c41031580c1e02d410003040c1c0401034070a5106000c502030300030070300d4510b40340a29003280100748030809071400f00c1003850b560b0305154014080d10441c1c1a0034801043c0f2801d2a50100b403210002400c1d41c4c80581c00d20000e030301c0300c0d0002454021070740310303648486c0d0029030148250560009101c090310344a04062400d2111715070700c03889043d803907480f8034001c00c0400c0405034002d0b45c003601583c3c060440c1d101d000255019200d880d0310034500482c00e0b0030010402560400d214215841c0f503031a03144d0b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 64963060 1250 64961810 64961837
    0x801020d0f0501050d1103071208070c080d2102190e12010501060512040f08070f0605060102120715110c03070c050f0609100c02040c120c020a020105300f0601 70
    0x407200700b03004a41e00716800034040000502c84032508a481e52008084418190342c489e0303034030a0a50068022a00303500081811010400200360b500042d12504c0d014040d4030720881001080304484051258008128910511012132594102e401141c08000500421102030402a0881d192282290f004002c03411005404840c10300c01c1a042e40d460380c1e1042e24008000150403844100544240c45042c0b681c4020f10019100d403004081844c415455a10b014185007081c908403a030041c506030564004502c6c4e80030400c04042101c00c22980714000c9402011903110080042074012140500d580000840d06881903002001e00340e40b40c80362013102031701500c3d9400c0c00019112210440e40000060202a0309840c241428654454051900c1c0b00030304550740000b010354072000c491201042070684a42041401400745c061005d84500041000850030b900080030761198151165000e0480849040c8600d405855108902c20500c2404d50508014080e2000d68009036226404203180090720744 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 64964310 1250 64963060 64963091
    0x50603160303120f0209060d05040c06020a05070b0c0c0910050f0d0803151c0303020703090501050c0a110a08070b0c150f04120509030f0c0a0504200c0106030c0801020d 74
    0x4141ca5141c0d4070021a103015070090b0019124040070340c403480b502407140d0481500c4a00240081004040d4007040d5401d043c142180c51844680040045410403d00a000b295000401e6811255110710840d990321040e0f240f00e080c1132a02d05801c0d80a0844018441109075121f48042612000c903030302151301c0c0c0c0f1a01009001d110745200100381860502c0007640f01120301d0014045010041c2610542d01a00304d20141500a0380504074086640815402d080c558084210b9000d04400c0c205607113007100002e035243d921209900002d03e044a0840f51700c6103030716803805580051500c80c00310399030151910316684698200c48a685401e1181c0c24140d0402940f2080803400b6484122011885481b143c60b044a0140841c131420280001002100096241000341410012184010f0500d0030b00290401030310100960000d8420703810950342d90644049480101152803001c920107946540c011040d41c0585496807005e8800e00c4260302c00521024103400410041e8160401000144409440003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 64965560 1250 64964310 64964353
    0x2010b010c060e0a02062110050f0906010e03030d09050d0207060c030e03070509041209060203031501110708011b02010533041b02030a08060f1c0f050709050603 71
    0x150005036075900020100304a5030086074050300d007105031020b0014680100e00c40c2d80c4840c40d103450242030b040a011403003001c5221a500310400b240725100c514035181c0061107a000d0810312510908240303000c90003030380c0a010140d112400c044c05403a03e0702c0c514441540100341d020015120f50154181c0021103034030201d8032000b81c40154075140c82649131900c04541c00e4064042c0560507106450011809036104082640710350301c184030501d43e440840c0380007490a05c05071320801c1594024003d1014070000c409041d5915082840c1c0400c6218000c3c44030f5141950591207210030b0352801800c20003e00341240d0f183c4111200d03030020b0107140c4a02100c002c0328200e94034680c40d1841500c1c204840c990100712416602d9100a002007024064818100e03015101900a2409a84000303009040390750051880c9600110448040c00c50322203140201d036060410303989000203610900600d504000c10040c2c03120102c0c2d000740841c2d5945031103900007401089c0079983d1070b200c0d108075884c1c184d844450200701e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 64966810 1250 64965560 64965581
    0x70c0f03020604120519150c08010f050d0321021e0901050717070515070e01030603050d030507020a05030a0e0a150e04051e0a050403180e0c091809060a05070201 71
    0x152840c1ca49003600440c05015248000c40d003a000b04880700c406d0300c170130400072034886d40076801c03030085900301c40e507202e08031b6141c0f090302400c0c043c110300100314142000900604540003a03a2046880700e440c981255218107904240000020005820340150440d0303025000400c0140d845000300c0c0150661161a4003c0c01c04250005004029400000d071079840c1052504400f110100d041c02d84681c0d074a030a000315810038072400e00f001c200b0041030340d505c035550812100081c00c0070030130725066445e040d03214885681011705154072240403401942c400c0000c0c40000e6000030030f503a1220140e250045c21104c8114020b44101c000c80307800300e8103141c844c0409003e4442ca07100c00b40c031241e00e0340c18007000d454000c081c400e0680e00f02d40c400c040c4a5070340107071912400c0465030020f51464688cc01814008500da082031031700780d001070144140d01540360100d4026075003070329107500c3d0910780c0005501e46020000c5001c0500c22502403025241c00000d2081c0607403001e480501040ea1900e00490032540e04101 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 64968060 1250 64966810 64966819
    0x50705030327011407060c14070c050409030905061803060a14040b04080c010609020301180c0206040318050a03050102031501020c01170c040812130614040302040b0a05090903070c0f0302 82
    0x40000c00d0441298440300b4841814a5001443c2e401c8120a440d04034400075070b04144c4406c00c404802e544229203e281c2204800340d50301f040116250015103003882e024a6000f55a5450217506050251507210020000104000c0d0384038007458407111002030440c0464020310401001c00d86840050284807025501c181c9243e0050b502e6440c0e0341c0381d030100a0801d07220404208218004400b080c0100000b92108000144c3d50703514104030040310001540d0100d24081c54030804d9a00309901003602500507415140544000c0b02e907070650500d1076260740c45141d0060165100104001064010710f11560106204c1c50054180100698a5105851074140002c2d07070050b2024502d6000c6c05125003201903560024180750301d94035250301d0802c189030403000207030001c108644c4041c541103240014113490b28140c030003c00c5a80c0400860b00543c08002c2c851525511080d5071500c03032420600040030000c1000f01d5a0801150706038890b402a9400d030340000040801182c1c00a040b82404100c035070103403 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 64969310 1250 64968060 64968097
    0x5191103010b1801030902030f0d090b0405010503040b07030b03031204020f01080c0d02070311010c03060f0614040605030702250612090b0408031305070e0a06090b01021e0102040902070f0507050303 87
    0x9120042c0c1071030034041c070f41c103056988402c54056201040602c0c280003482008040c4030044030806004030046a02160940004000500c03950360300200f5250855407002900c001600d42c0da006038050509540c1068152101203071003520304003288113450044d80281c0d42c1e9400800154011a102801218241c1c01450300700254201040e031680100a11030003460b0118040d00131003100b0b400e5038404c07903030240000e46501042c03041440c02c442c103500400f818140b102d8031384642d01c080d00d0b0300e008034800c1c1d90034030201100149016000707206022003d600718401a00400301e0036004d001341a07030303805440005010310342d4040d030382d40141c480c0307421464100703180c80c1e4103542da5540c1c880d032a03000500711050000076080d03010014200b0060b200c06044510f10300c211600d40000b04004860403684030804050500420700a1640c0103e41740e4080c1155101185000d440d616030f0a01a00c19a40000c3c13055200040070824005903209200c1928418019186801d80c1d4104041c0e4a010b00c100c50300b054a15803 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 64970560 1250 64969310 64969327
    0xf04020a0510030b0406080601031208090c011b0f0c090f020c030319060e010801020903060a09020904020d0201031104090905190c0b0705011508030904050106031e0f02040905191103010b 82
    0x402c449110040c00385000b04501c20f00402060507202103038031040e2594000001030013000000300c034825040c5054507060000b882c00310002c9a035002103403c21030511140010302c0d4018807a1140440540760840d0b01c00002080e249860407c078101841140c1a091410548100490690080303600c0030012000544c11621040680421701c1d43d4508410f2990390f560100040402d505010726000b0903c07400010f032075441c6102418146940204900c281500d0822920010b9071050181500541c066a41032010f03442c0e44010b0b40102001c070005210179001042c0021228019001801302c4c500c18429a00c2e00000c001c4020141500401c000300104110042801076104d114054a1714501420001c9140001d42140c4c000c1020309070031450380b40d00001204c0000d418180529030043c45145000c014030085a081c004011540015191f50305842d030901042000b041c3e0182c0b40a05881c01082045040502c10a14002ca1644901c0b00881c00d00c0000306840d98503c0030349048410b0826a1881c20002 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 64971810 1250 64970560 64970569
    0x3110c0d1407090603080309150f070302090d0203010204080708070803120708090304030602040f030201110d0906050a0c020909030304050f06010b0403031115040c0503100b1516051002120f04020a05 87
    0x4a41000800340328102c0c000074144101d01540000314052446207540742441d0340380b1402c00405c240071384d4000741c00342d0600c5545546800c00c5580480c0f03d107001a142c969800024800e0b150f03040c0041e41c15800410080799851021a41404a40e0542d0840319429511400d40b91207010318014021798103010030008030120700800885511408280a60386440e8484e503500307080760455007104046000ba0721003030085503081308a141c9606656001000d02c00c0c020f0600411142d181e0041d401002804180354007007c1c01040040340d0543c0c000c0c002d01b0390789820361401d0740c2c0f03400495068449100e0b0024020300c189010070018182e03803500300ca0a01d40784c01c5460a0700c100942c0d5041076050320546208403149004542e580e4003d5100e0141c2034001403a0000701441e1029042c11118014503005815034940c1c4d500300000106000c80596603291001c94a05e19404168810040c041d80100c004d03004101c0ca40c0e50041c00c1400a4074003422250b00e41d54040c000301034084800a400510f01c172000d1015142 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 64973060 1250 64971810 64971833
    0x4090605090412110a0804030c06030b1914130e06041101081005010804020a0e090607090b090a140301021c0b01090905090a030305090106120c03170304020112020702060f0304080703110c0d 83
    0x1802c0714083c0711701d6603440c00f0303641c807545c001d88a5502c20403052040542c140904c1810560072206010025400c0c01340040014a5102d104180c0c10780000c00c4000e521a50600b070f502c0b001c0e40380100300b50380070000d40360340b50032040310100c680e061400090749142d801085402d02660210804904c1d403410a8019910803001810580e84425058070024440740402003031031041528002901e901d080c800000f1f0f095110b241c000e00000c18040c4001c205a450f44850042100c003000c500c5414401c160020900911481e04200e0030200069000c10a45550760020b011840c2d00383c0c2d40e50b8032165602003c104a503015502c0a4003608000820408603110303070401500021114000500f4030307507801c2800b40080012200b10f500800200302017091045500302e400c0c0055003a003a0910b103180541c002410000d860108241e50313640451040159156007003500c41100081b01e500c2d03500d00386401e0206450304800c4c801c800140c0103030401042183e01140c0240e454001a204210b0200c055840c1c15a66030b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 64974310 1250 64973060 64973087
    0xc030203060f060c0a080c120712020c01031a060d090501060803070b01090902060f0901090e010609081002030106091e0e0f1501020706050d0c18030f170702030705040218120304090605090412 84
    0x110305500d038251401440000c0c0082486108642b042c1d541152003e81429480035403d41411721b0b1600410f00d460b891203900c900c14008a030704680d107102d010985d400170050f0b29806409903180c61400f05200700000014101c10b4003403003d080e501da0380c030019602a07a1444400a410040c24449480b80c0070648000d0f00fa0070605042032081251103084030310050601b40d001c0700002c0c1c10200d04101c1030390140014a0159094101035143d58100400500003c80350301c100740380e00b80410300d164101459816820040c2c610b400c0919220708000e1001e0441410a0321300103880c1d0440380d0035080302d41c000200c481c121041e5841c2c0c02e05010580183e00020000050100c050040d101c14039044e4894406140d0061442204070240001141c1899030280001602070380c4002c00400004000da540040c840c000ca400c11140540c1d00c4c3e40e0f03081d02540442120500b260814440480018a032001101a10035519000801c1042d15515030800040c0714048d02c018240180c0c0112400401d803250544103c40c0c0c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 64975560 1250 64974310 64974313
    0xe0c0d0311060403270f1205100509100b0102030a0212030a020d0e01020d06080a030c060507090504020d09110102030403170304050703150c170402030d031a040c030203060f060c0a080c 81
    0x980c1540c605001d4103d408400045981c0314408401c4c00300c215002c2c4a081e841c94802d02c4a08084540400f20f0b000c2c00b568041450400c50402000410800840704c1c02d202d00c0305008a0902d0307480d85680f112201440b00e112418003408a00c00d5100100307582d61005198000d01200070f104035071180940c009800024129020030005909118a0240c910141c090320001640c4024800f692000c45013160880304080e0080d1704a0004a40d02c81038103c05207411901c00141d584401c038040d1510842c2e94041d075089400031400120300d40c010351150030321600403403268450b0138080b801240c40780b0641c04018503080c9400310b07020743c0100040255174402d02c550704548000d5243e440b0750303c05040351420684041e403500040410558010001b02070001c4151860196090030b500003a1100980c2c101d040400d80c0d2010359080c58042c040901c5c1021801078020000c0d040b4075000100070390702c1111010b0080348100c240c0c030700c503007010001c0707406442001c000f4100317030111503898409a40c0002c40385140d9 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 64976810 1250 64975560 64975577
    0x613050111070318120506072105011203030e160b0d0f02040b040f0504091101080601020721030201050603030f1605030d0f0f05060f0a140613061701090e0c0d03 71
    0x6040004000b04030140c029200c00b00a060002c6000b08042225004414000742c860351150000d0000a2031b039400c001e80307040920910b2410600c1d00e0080c1080205051100c0c00c250000920380304021a01003124002d42e000d0120110700400c480c0d548104006615010b00d120302c041250102840203824800f01a000c0881c01041c0c000740784060303803c550032101c00508009002c000d80c0348030748007000003844144d6090210602d9a00c50b0020110070810213030500c41c800d40092110b03842070001201800800311100c40d20741004011044003550340c40110301541c41c00001c24518a40001540c4114210304042c1d850441300c0110700341d1a00190300300b00c4861200f44000b402c3d80425028181001850704000110f900c0c1c00f1207003001f03948002d001a07010b40804d0080604070344500e16207400f0b07075120f0344200f0310103c1210302084c0039214812503101a81e0401d9400304010f80e121201d087c010485070280070f426600c3d400345a04980c00034810080342e0340310909080140c14032065410840c1d001f402c0c032012 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 64978060 1250 64976810 64976831
    0x801141e190f06050c0d11060601080a021603020c011101050c031303021905150a0c120b0a0308130501080708010e01060e0f031005040506010b09030303010b030a0e1006050a051206130501 82
    0x107129042e0f802c510007150020801d42c003000c2c8200b107a600420601c2c540443d09a8042d20700380d8403014050315036070411440d4000620b600c041501240c4e08100f007801001400781090a000b504c0f00421940c950020381500e0f03000407a0714050150350700840301c40d00150300e07540350ba200c03058107a09050821020b5026410980032500b01241c148140a8040d5014111207449000c40700ca4080001300389620380c2d403800300c03120b2030146e211035180b46018410707000154040040001881315052588001c010b15400a800c0c00c0124001c52101d0880d102a00c1e80015a1141c0c0c0003600c5640c42400740c400ca8182c5c140042181a104140344c07400716801500c01c2c00081342102c013190429903004d00041c003c9441d2018802080820000d59005020010705e003800c2c03940316030019440c1d00c0113209031800050040046480c00380c0c5980003044050f40302045803005e001c0d40a2200c0035004a01c1641c2c8110007901c000a6203080c014010005201920040c0505a803401c2051048814100c4181c80319940d4588650 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 64979310 1250 64978060 64978079
    0xa090f060e010f05010816082e03081801050405010f030504060b10051306020607020d0c08120405070303091401050712020a170405041514010f050c0601060801141e19 73
    0x20b01a0140d5126000702c2c1d400c000026000c10006403144005070728849550040c40c0c0d02840d203903040070041c03a01590403100b10969079400f400c0003541c0f000300160300400204001544000340940c0380320041c0402403c00d01c000540d824000e502c603150104007210f82e81800c0a01c40d60003036900500c5030000090403540080851170601014030741c1404500300044010106083c802c00400034031072840242450724241c50700030345984089040d5018841902d64050400403101d050703420347c14030060304400740e2806081030b9648481910090300814000350010801c442d075190f52200710310703040c0c441904d09000b641d03c003546000c150a6420460041c0c80309000045c21040d0b40300003065950703960907281d40c108030401c800c603058241c104186840c0706030100541811900001c41581090030101003207500002c0a42c0e444c80b40014506041c0541800815030a8115a410381a6070401c810a10000211801e00c9036030340c0c9140365004040000c210400b4580b400181030741c403444404241003140e0740e83e2214007 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 64980560 1250 64979310 64979339
    0xa0b12041a13030e03060603030d022a0d0f03021e0307050d09061505030a0b0c0c03040306020409050a0b04021206150d02071a090313050d08040b07060b040e07050a090f06 75
    0xb0b41c60450351050580505a02c241321034141d0800310090201d40c10b2100002e0fa8900c1040113100300c10341c02140c2300c5001c0040c8107500c60240d4000e06900007104403014215100c42c0518824800f1541c2e0300404650684a0300c02c0d10301040680d0160b804c0c03900058803040340790b00000c10036020031108200300c3c0c5040c0f0a41c0100342206103d40c001044c03d5504900f102e8141240790411070095018a41001c0400d40d03180b0100d030004a144015503a03034030350407a210308611450300007600c12800000c0c0007982d00f0413a4801440b0b400400d10802c258400601080b0a070b02c210740b442c1c448000000c003c9002460000c40c1440310910322903182e85008868038040703003681c024a9056660041c3c074100b107054181c949064681c4080124007031441c140c012440d88242800f00e00a482c09006840034840420102400301c40140c507000030cc00b9221092854040302801000c1c40080c001d9040803540607600e000010180140caa005081b50309160a050010004005245581c41c100752a1400018101040c5404 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 64981810 1250 64980560 64980571
    0xf020d141903060503120f090f15030f0907092d1d01060510020606060412080d290f01020304030201050d060306090506010815010e07080601020a0602030a020a0e0a0b12041a 76
    0x10606520380300815003400680c0170300741d143c44010002c1c0b58450b4051400c40d50803050441c3c1100452004202040c891a490804410544ac0000a2203150002020013511403101401107400702501c85a00005854048421a45440c01e034007000310703d105001e181c000c8000000000256100454045c0a280694803580141030f0359034038014400e500f09081440c09401315400100110300304200424104d1080b440360004204165980300704100b540b070121448103c40c07480c10300034181401c141c0e080041d5020341c1e441400c81e9010389a0030b80d003000d801c04d40c0402c805802450915145800640d60380d44180d04100c0a42e0b50b0398400b00000d102e6200f01c440c0c075402103009140942c14404054a042c402d40c00c000d019402d000c1c01000358410306024960b10400c0ba00c0c1c8840f480d2241e100503480c0100f9400010809130000c410880001100d40c007030002c19401b40c2d070f0f8014a2a1382d1081c040010003600951040d200d0070418139200020105110750803500ca007840c1d00180c2051140c010700ba8005072030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 64983060 1250 64981810 64981817
    0x60106030b030105010b0a05040b0a0c050313060e09090d030e120d0207170403080723070905150109080709050c0f0a0801050111030909040321060b0c0d0f020d1419 72
    0x1256950380c02e0074482e040c09008858052458020b8100003e8030780d01070762252407070130340000401e0709411748240d60620300c640e409002c072921800d100a400e80b40002078050880011000f000f102d03038914000c44024000c0f0b04110240c00000c946031401c0300a0b03c03107003039120384922400a810350001c4940000740000c3c82c1c1410300503202d9103145880303d040d000d20b520910001c402030109001040c80c210480701d075903030711040340c4581441440c55481000c00b0080c110250780540c2c08009404a110740010340701d40d441d034416070711504101005642c0641c00340503404169100240610203180d5950105401007800300c0b05500300743e05044135242c1a403017aa09000010311200040043c1c1d60005100144110300e50091401c0194900c04507160040041c000380400c0303e11080007032200000d4030000500c00740c034a1306200440c0c40b22a01d00203a480381208089906c1861502d01d103052140034584030742c0c162030740900003500308050f0840c0c250903144030302d158283d4100031a0784080c4e170300040ca010180c0b0a44 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 64984310 1250 64983060 64983071
    0x10b06070510060e09100b01030b19060e010201090c091505090717010504020a1b03091a03010e090105060306160302041502011b09060e040e100e060f1003110105071406010603 77
    0x2d42d059542a612100140c0070050034000000e1010501c0d40300030282010025540d000000128060705030f41c0040c3e9040304c20010300c40030300031800e8221000d49071243c40e084820410400128200c1d0034010002d0f1101d81201c20a0010000c0e9421441d10030003629940502c1d10344070400030f101c09005551100100350340038100c81211000b00790140c0101400ca508506001d070201d03024100000e801059142c40480300c040c1d10816018000001c0603000f4464078906880d01400b5480450b8800c1c01091800c1604a00242401303005000311481480064042d103000d0b101c2081c584000b80d614100c010516409000216004040b405c40b2906c42000384c2c0040740d042c1c00d0305548100307881041c140f0390400001200a101c0590803099104102da003e6500098034941c1c1c260b8241045440850307564043d040485610300c00200107001070141c1c014543c20080d6807034401d02c0980790311061100519010002c91400d20381d6016901604005029203000c10a05e00d4075520582011403d0304407001096a51 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 64985560 1250 64984310 64984333
    0x6020705030c03121b04060302090a03060606020a05011401030203070e0a0207120306170d05030c0903030c0d0f090e01080606130b090906100e090604020609030709060b04150f170702010b060705 85
    0x3070220b240c0000c540c05d03c04020f0380c8000ba00003554400e9014075028160006031035403d50310742d450540015500102c082000b192a00002908d070150010b0580b0750750300342070b00650207040f104a950304a0342d00600074103200b4544403116030882e1300142a411820303428000c1501003516120b0300c00070361000e0382e030010b00b02d400c103000c0540c46c207220304040240c1d50150282c000340300d40100840c3d0b000005031404a403500c8020300000d145118412440b602400b40c003c401090f150810505408076849880301100d6684444100503c1102482a048980e00c18408644282400d41a0b002d810400f401c0120b142030b0781202085100200341c030001c110350300c030004225050814400c0800070f001d200c42d01d4070703060070141c3c80c0907035030030000d070010340704038000280d120865030104040c0f401454900d40c2444066a201105880703a0468803032860445008440069140d00c40d500b40c115600b41901c580703070078030000d05078110b0400008226400759940c0718945122a0344800203002e21601c182d009201e1000d44 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 64986810 1250 64985560 64985587
    0xf040501080a09020a0611030c070902040510300902030303042001050a3c03050403020c0a030f140c040f0e0d081b03040302100c0c03090b040b09090406020705030c03 73
    0xd02c0b9007407407881c0c00c04a10044e07543c12400c02c2141d07605d16013406d88011042d003550851258261880d0948100a4005010401c58001d0011240102d83c07001d80001005401d54415008012030310f001c0c43e0032640c4514102450100c401e0f035030b40e824000500c0c4050740c1e000c1703895680141d6054441c4241003030b00050035a0a0008241890020710b0460b041640030313070000d080c5c000800752082c0705107003a00c4003100f443e107201010a942e0031000010411410700080140092505030340503801800f641e04500c090b800c020032030804896000d98000d00c0240b05031034001c0490310000041d40c05005050039001e01b941d45002e82042150607290004156209444080c42c1640c2d80b103070700c024021704100700820340c01c004602004142c0e0b10340c90950b0700d0b9a40c3c5002c030306001c04000d501c02c00c02c1c07410b900b12161550180e40760509921035100c002205840754040c601d40d008900c24220300700c1c410004524141401105a60080c0c416180541848900da40340ba003190002010041c0943c008035114411402 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 64988060 1250 64986810 64986827
    0x6030e10020405030703081c0c080f0f07120209010e03011505180417070c030218060316050f040f02073c021f0c020a0e0907080303060618010c080f040501 68
    0x141032000314905840c2c2000b090b2525003a01c00500201e4000c51000c031800308504c01c942c5101800301c03003008522520301c40541b420030241d40340a010f030b0000c800100400081c1551700e01400458807030442058001d41c07110301940c0051849410030800200c15612a2400d01880e0a00503030580c0c0440c00c2d500704014071040304141c040100c40c5050f03003030a203c0072030300718004241c000f684480d00d207503250a02d0070716900320035155000a42051a2010055441d00c07144d07850b6000c0c10003141aa08141003034100344400810340d005080e0311404d119503c42e03103483d00f03078404010151076000260a180c0c803a11010410503c1038501d500444054015642c001020a1503208240707848001450074280394011903180d00221607200e004440c0c101c00000840c0c041d62868405543c014071030141141c9070003042e541a03809890081c0f03940f00e40f403400318000d0804015280300e008041d0100e420010804c9241c0340c01580f030b1442d181440364040f03100010400400040404c520982c500542e500d1421000600100 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 64989310 1250 64988060 64988083
    0xe010c1407080405061b0307030201050414030309060c0c07090f020415050408030403150f020a0c030206150121020408030408150109270201020f0d090503060c03010807030303020c0109020a06030e 86
    0x41040010744001680304060310152041503034200d448441440c41203410240e803243c460064880400c800c010541d054100341c2c0318030b20500c0e5420f4649003004001d940c0b80010f50f1000d0291308000002038118103408043c01661761108215228580d8805c19401141c2c80c840c1484800c0d5000141404688401490b01e944008a0300c1d100d883d181c60310359919168000c3e8040103001c8169405003110540b140d0b04520002594072204542c0d4000a52000e041e080454204030054090000060b00020f5042141c40307000406843d04005920851001410109005200c0750082e80c01d102c0030a1440c0100701a001902e002c0000304140350416180c8007081c50160f10425070b00d0700b84242d0a91640040120b90b002d82c800c00d501c00a0f410880c40141d083c40c0110700062030700d20446149102c50fa44c401c202c00d0840d1026410340340152030f444003401441c8000d0040100b5036114000c01c00010f44640d00514441000c1c03c0001560071884c0c0c0010300c12462039003c00d00003a1107101d4a0198030041c480d07903032901e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 64990560 1250 64989310 64989347
    0x210603030a020601060309050c1e0a0b0309070306181202070602060906010f0b090f060310030c0e0705030612070b03010902031e01060f0c0510060f15020303072a02040e010c 76
    0x401d40c600003941c0300c40500682c0304040e00e0720700b41d004000e0b00b00000740040000420300c2203031103c1603848030801d02507504118802c00e00d1040000e401c154102c2200c0c003403c503020141400c9415038403004098002441608904400280d10801081090032061810880ca6000e00340036450729100a10b00341d005040301809810402c0100039080c604410070045401240703410351240e49000c0080c58107825100c0149e0085c02c004200148429420790b264180e078420342c05480d1710b903103a040c0c0035a00c0c0c10446208010078001c01c08921246008044100302405081c2102c0c0019202d1780c1c0d46140e60001c0c1d21041c06190044184800000d10b5008540c8030507454901c860290b2403c01d00034038081c0c21504000c02d106600c2c14140c1400b1060050740d41441c0240410f1022030f60314800c01d40e0104092081440c9001070078009040d0358404021a4050492992144d284076005007184140d02040845085001030b000316800c0141c0780c0e401590f41c504940b5000107841130341e420015113108422800300000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 64991810 1250 64990560 64990567
    0xa0503041506240203130b04051203090a120f060e01020d0507030c02060103080d110418061d061306050d050c0f03120f0c1204080105010302011b080702130f0221060303 74
    0x800303450700c200300c00039000030740915442d6a1044060703045106e8291079006211044030301203000c1991130b008004035501a51100c00750544c01c84526100c0c0240b0741007503840345c003020080012140307040e0400041030040c5a586000030300e0303a8402045600c508100e207085d0750003241c01d2101c42284d2148940c06139503410240b100c2111140025120b9505000c0182140800b0443d0300002c0020780c032117251a81d5000001e640c468445204081045005003090081828251b0104400c490684d0400410007606580781d4281c03a08010401d1462282c840e104410b50794110000d0341c1d944095200a0090183c7d014107008003480040c0400d42d600815414041e6011700745a200002880080f181c402c1000100381c2c1d20303000154901800c124060b4254000c0b180c01240c0460364030700643c01241228404d89401c0b0b40844005000703403040620b418041c0900c032041c04898054200907050b95040e251040000501800319040752040340c211080800c101c1407000100e061a80d9040142500848210000c41c01c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 64993060 1250 64991810 64991819
    0x160f140c151e0c180d051c0c021e0603190902150304060f0501150503090a0507060f110a08070204090501060f090c0305010b09030a02100207090c030b1e151606020a0503041506 77
    0x1551202c04e12140185402440082841414050440c000c071221048000700c4e2140400102010105101644039071000390054000030322200c07501c02c250340080d100c0c0341590750790b0400501200c103081c01481c1c1d041d02c87d4603d000503a240c5400145450b440c405064590400d0309180007101c808000120035949010014031041003140344000c0c0c1980e080c0781856036652001c00550a01a401c400209644502000854095000001e03500c8800306560303044188a00400520380d1003030b0a00d07014010700b034100010301c00350510342c01254001e401340c00046003140c0ea13407282c880070307050b10741c4071203515580d501c0000601641405240d00400a00c0b840c642000009400244c6406d00340c0402407054207007080e040b2407a4004c0c411300008241c5400100140c20034400301602614145603c1c512840c84130211502e10842d0007103404600c203000e44900c1c0c5221402c038811840340d00c201d1400c2140306095501d500007410600060894171400d0343c403140ca1707003098600300d03601c111129003c01016081110920 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 64994310 1250 64993060 64993087
    0x20a02060d0207050a0203030c0a03021603080409050a0b130b03010b03010603110f15030718050909060403050a051614010b1507020405060117040b160f140c151e0c 72
    0x1042241040d41c0103a490b482442c1c0580f41022001000350140400320f0a400450301c0410411302140c000c1d02038442c6034074290503681307411809000c0240f05030340901040c0302d0610554003485d80b00b00f86080029904100c40005007001203490000d40c4020303150b501104c2181001c1c0500540020250001c4c80507030b04654803048202128410240a100d2103400e402d2280d0300c841440a8807244088000d90760f00341550020b1858103401485000520b01c0c110005840c2032909203a0700c505c5c45c00c0081c0c8040d449617070381111240d100d04000010040300340460f0000201c80c1c00d250302468410309103084603d240318100b5003910314001000c0e03c91540c0c0c05682e03098000c41e00c203c60826604590001d0141ea610ac0141c07001c010039042001c006401d40304000030040003160046c000c0c0307600102c041c8111400340e0200d81c1444002c060b840098900d802c40c518041e1050064510840003030280c0781c044100d00f55841504d0811203a01003940b18030480419040034440095400c20040d2031242d15140c000441300 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 64995560 1250 64994310 64994317
    0x9060f0c06150b03040804091a01050304020d020a050a08060108010507090302061209010f0906090c0503160302041a0909061602070b040e1e010609091b0c1e0501050c0403030e01020a0206 82
    0x203801c507a22244165415a0242007050140200c0941542c07242018100b4200d07580043c00345841b00c501c0d0038420040175400c5a03c08204407016034502c1c1c5540d5642d4284071043d03850305000c0b41c218030741d40c3e0040f48075964041d002e809000340c00005c2a0030f600d00b501c01e50a484c800391051090202080d818009a103d042c2111078030501301541c0c001c00d8581003442801031000d5035605071820300e40f40a0700100f0940c2c1c0c2100341c00a006011802090b601e4504050b00d903086148800f040c10601c0034200300500b000c2c2c0200100032150150100100c140d4004501c1400045a904030b030b541048017002030103030040c100418645040d100400b006401c040b000003951046018001e0921203480020f40c1301d401c54221200c00d822041d40c85103032544d4507180584229030034041c00c4170007820030f000011203182c01109600306080d26540c8006243e015141c581d442c00098004500105100c0740301e101045090003402c2c003411034113000760358891550500500c40d09181040b0390440d0001010760016982e40c1c000d8 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 64996810 1250 64995560 64995563
    0x3090e07050f0703090905040f0605070e010e0f01030e0a0506040c1509181b080703060b0c0c1c0606030b01050f0102060702060f060d0b090109020103110c0d12020c0f0a0309060f0c 79
    0x55840a807810150390083e010ba001912147c1813004000410003903d244e0300c00c0781d00c035070000e0106440707988054800403020400e050001d9152090020189440d4500426440d4103040018000c08500c021030708203103110034181d81950126042c40100007056040c0c0004000194200c1110b405046000b0001c1c115441210040401c4683c103400c02c4819500030007494031514000c040f89450200040d11240781169060040307803902d2000070744100d14000b00c49801441d03801a0001c80c0001d01040250090480300c400c1000028600800250081c8520300103903000700014482503150908001e036800140c0522030440d000541031255943d000a801c94000c03c1d2818882a15503070400855071200702c03500c0190030b040098041c040d40310019404080c005000b03990501c0851100400c00300680b0548840098941c0096042c1a010b4880c0c2c3d4044110284110003514011541c140a498000300d0040500386410a100700000c05400110b5080180403178100840d010604140151004003000700 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 64998060 1250 64996810 64996837
    0x40b1e130c080312010303030c090b190302040506030c030103050c060a1b0201020c0d0b060f010908101104050901091d070f0e040f0803010e01150507020901140a05041803090e0705 79
    0x91010004807841d5180908141c2c02100c0e01c42c0150140030014560031b20055000c40e1401703103e41e005601c1071036210150382c034501c0441c1c40c104e5806511981810018905001c00d5400d10021170150b41d6940154000e144a4181e5034a17941036041c014100200500380b28868a820400c0e411502e0f00320614109503c10385060443c0000ba45c001030f0708140488501d43d070b01c00340002000701081503c1036048d0103404241d85001811220000540304a1214011080c2990005c0103084107403116821142903182c14007041400e0590706c2d0701040e00d0840a8110307161940d01e5203503140d510881c1092000c03103c1a45002080130901e40f800b00c01d003070030303c07401032110000c01000010180101c80c1e08104000368805101c0e5629a940c071540000d00300203000d011030300070302d62a455840034860f0098a4949030024158a456403030b02418444c4607580e43e114a401524045000805a40b24071a401c03c0a14801d000b070b001150f0351400902c9200b05421404615a141301409103070356101c0151440c2d100c9046 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 64999310 1250 64998060 64998091
    0x201080c0a02010609020c0703050601050d02090f0c190522150c03020c090a0605010216030308131b0305100b0a03050a0b06010c0506100f0b0307020d0315080303040b040b1e 76
    0x30710490140c100c540021151600008800101d040c000610004503405003040d2907459880d07d0030440c529044401c06940400c91724049031072600408d042541003444948500e151581980190a85445011001c40072840118018102070140386c200000c03008014580c114490429005c820740c03403081641401046041c881c1d40082500802851a0388840204400e2051500001c141c1c044c0000d07003d143d006000c0d5201c2c5440302c3d155081c80905495064848440310b07600c640e461003405002c0754003540c24840c0c0c2000c40105400002100e0b000d54000c501800c0044035407002074003506d41c0c0440c802d000b9a1620300c10404214042509400d1039800220f030112034903000012a42d114401c40044d007180990414080d00e4010038a80300100d510318900004d025503180700c804450700048030b0071b00168110002000c94540700b80e1005c108030503c200c400a040d51079441851450f002164211003102084041c802408944400203a1010f401801c60485210f0304200c0d0820300405024503039103c1092 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 65000560 1250 64999310 64999327
    0x3120c050a030e010306260f031303121209110406080a020f06030703020913050403030b04050f1302060c0d030603050705030106030f060b1807021f0b10050715020a0c0302010e07030201080c 83
    0x94002500030840140c0049147d144044110f5400b100e40e0301a46d040e220307842420184403804803e030ba0b04040140c0725056502e1850b10788200d0f295400c1440000c01503da80071091070340791032084c017034041e01401044541907801014072040b900550090701e26984110304050040c0c0d90f10b10810003c0c0c03c00d41301543c0b00d407203a4034290f02070301500040540c02a808403844100107600c1e44460b1245000756002d000003900242804211013056902c2d125030140000007030703104180040e1010f0010b01c09000300707103000d16642c20345042803554440e440000303854a0302041030120401420000c0d00d002c8000300949407466444485c2281d46140081c2440c3d1030b049401c0300d50340c902444812074900c69104469603e884000251564012441c10380c29540d441c0c12742004442601c200902808050003035083d62100301815105500500d00884116105a500200c0020580090300c10090151a02100f40f807452502038251141d081cac00c4407a0380c1c8001402c10240c0e030f001c0d001a82040700d480304256a030300307032 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 65001810 1250 65000560 65000567
    0x30c060a210204120c0f23030a0203101d010203151002010b04051e100501020606040b0406081213061103090f0f151b03041d071110050103120c050a030e01 68
    0x10601d00308114804580042c041c9810502210424031503094010b0b0b0ba40c80d40384400c007420b600e008407088004209a41c00a00d1000d81c903100a4a200508482014515500082c6010450714509590503213030300c4040c8075030440004000036100050002d50842c81c22050700c3d981454018222071081105900c2040704900070361142c00d091342c2c0a4000d2101c0d290403060344c0c403103000c0d03040707003210000000c4002014150360b050f48804ac0d4405901800d416111442004003a206440c449a809555924000381095080201941241e1507010300c03616080c82e81150b481d05409644200140701280e400721540490120445607507800c200c8141c2e540101d83c3c008110401035118486421450176184520030f600d9140c05020b010068110401820840e04c2285880740698486d5440d00320083c904010b014500c5141d00e035004490b4684101d50901014825103010034040300320202c0c907030b0b0f40010710038000348550706038400401e82000d0721001910b541e202d5588100107806010000b804100503a181e22 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 65003060 1250 65001810 65001857
    0x30f091e1a040b070f030903080601050919090902010f0c030207030201050d14240f01090905041103060a0c03050f1611010e0708010209040608010603150209010c12020a05010605030c060a 82
    0x70401c0000c0e00320300d003d140500d111074090f11250301044110354aa0502840390060703a24003a0315035560740040d162800150b445030844001c141e03201d42032001da101034101c203209890050100d21004980c0305054000901041b10034584a01004002d4414902003500007410404032035080ca002580c0e142c680100d20018040c1e110b04802c428000428064602c841480388525424001c494210b0310f59a44100140b003800c1107105804a41650410022100710350702c4250b12a0168095009032015100042d081010440d16000b040e965856515003040d490303c0307a140e0129040200c4107880c00c080b458090a440c64101000400a400c03100c210540406c0d000101300740564011a00d006e138540c0a000d010750080821680201e1900d40c00090544050041c0b40840e50813132502040990b0084440c0c000c2e500c40742030941448001518040040c020400c4000c1000495000e080844128a00301d820b40c0c0d0740d03610484c400d601c8100550a1a9200c000315034001200381000c82c80704081e640800060034 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 65004310 1250 65003060 65003093
    0x23150619031b0b0319020304050a1209030b09060106120504020102160f030506090606010903030c0503090a06030209091b0327100203040c0b0307020309060c0307150606030f091e 78
    0x600d16030000c10088501d080d4800c500b80445010b62003521100c040340d1502044404a0040d070340150160f8031410158019500140aa000c0d216451010740303d0f03000c0c45610b411010002120654104184008504100d400c210414050f107015454107400800000041d0071110300580d51b000420216030007000184a40a240003034940815950b0075042042c25141c4025680c81c011200000d6072624080344d0148507a00c143c41d034424a505588044a070011b020b9801c4a42d480100402c00c031a41d14692580c00074141d0343d40141e680c002032402c0c4100014080c202e02500044264a0000c3d030341040c0075694804011100c02c1d007880d0b00d41440c021180301d5400000c00500902c0b00c2c08a60800720780055201c0c81c0200c1c285c800490343d4841071401d6100840e014070058006002503406480d10f0300051070b0408010040341d0400b070141d114a52692500c01010710300a9a4540400021380c040c0100c281d0101e404404102480c4c041d01c440c041c1030b000c0c07428030032400580c0080c0c0e400c20031500000041d0381d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 65005560 1250 65004310 65004349
    0x8030a0b0d031d010206090d20011506030b0405060306060108190204030506070806030a050a0204150e0a150902040501080a09020102120a0201020717041211150a0c231506 75
    0x91403a0030b014105503000c2c0f149034264000310100c1c00007540001041d0b40189074003402030002c10100c480440d40d5070185d121081d0708091103640e40e80d66420034001c451030304c540d00c0700d030b2140c01e460014040d00700c96489407414000c508000800000381c4c1c000c660701c0c0d070207402030801c00c1260b0f070346440c60f502c03c4c06911001702c040c0d031001c10003100f8000009166403040c7d285d074588205544400c003c142d40c0c2c6030302d140c0007489035001c0740c0c0940042c1000d42100c0c0e080c5900e5030340d100250f0780300c034040c2030303e030701d08030341d1a0340c0c044d511040c1d01550000b02c1d10702c500400760110214070706410080020320f0b01c50000c004290f072507120304840c01164400c0000303080507406285070540b18403810b10024041e510408003034072060b0441083c0c00a6555070811102150070648925a04c071400c0c1d0748012502d4407940f00d05034003451100360504c40030a004000c0c02c0b11507480e982c8803400421440d2040009040b0022225200d115880440c840c1d00c0000e0110001c610000248509070f80d5500018042c000840d04040030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 65006810 1250 65005560 65005579
    0x150111030c010c030203011a040e1b0d0614040c0e0a030201031d070617010807150f02010905060901140109060f030201051e040b1209010e0d0c11060406080718030c0308030a0b 77
    0x3c3c1d60381980554180c0d0300c01b200100b040c540561000c5400d01542c080c1d400d402c1c12940c0031980d00d1100311000b04003001182c0d4010b0402c41246d841004031501a0300038030b140040e40e618403140d450144031b81e41e404051810024030b600034000c040303101c1178958003009060642d212410120301c161404403121200310700c8104c40d5510b494560080100c1d00c0e8083ca08100f40d206400810080c002048074400c0c0d9460407910610030480f1041181c2515a010505040d5540c0700c51010201d4800e0001502c0ba014142c00401c3c280a103a0108021581c16407100d008a882c0c5042070084c40d455442c100201c0c0e80903e015030711210543ca406001b400002c2c0c000d805501c0000380090a8001840505032020160b00c80810665135844028260340304040d044400d034002440d1700000034096040000c400d4010140c40003c00d0700d150114600e42d2054121001050b0703d4010428bd036a40110410034142e103120711001518559070741c51042c42c0041c04010801100480052410500b907170000854003002000c242a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 65008060 1250 65006810 65006831
    0x20705030313021e0112050c13060315050904020a0b0f040b030406060510020a330509070306060602190803060103020903030d05071b020612040f02031509060f150111030c01 76
    0x8490600708a0040d0002408500c48008021300ca02007880182c4510907100750b0940c03404020a130041c224040000c0900c803036008801d00c11010400341c100b176100010001481c1d03a003924031031441c0d4040c9205d03510030000c0000503207454501d03070200e50307103a0690380d1a10044100e120490089400003040703010040b0400003445503540205040326010b441031900100d01c56012a1202c00b401000b81408041041c1801440700c50f003202c0b000c408003200c0d00341d00700500300d1240041e034030113803400f1110fa80004000c5c000d03c41c0300e21442d401001c0d00d00090034440d240e0001600c8a58254101400540000c070001e00356900a4045550146008059980c0d07254001407080050a041c0d6a80000802901c04014000c03e940c0240413610b400410700ca0500d9041000c03000d545000401c02c44240e2a5040a00010b80b010800c4005260016059292502d44a010710345032640c006c14456406e03449606020000ea1003100640d14a8000c2ca40f6181c484403800d0301760302d18444e48003444810740c6404035550 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 65009310 1250 65008060 65008081
    0x140f03010e0616080703022805040b070b01080d0e09070518100c1203200c15040b1b0703050a11070f0803040f090b01020312070306150504080c090411130207050303 72
    0x10b503114804e464150303540c1c5030308800b2405c9014242c00000c40308415072000c20241c9144010800c000b81900c3c2c2245416150011400c16030484001100c003950240014880841d083c04181302c80555860003c0669a2000000300d6a8002030b082d14144007000800c440350282045400c054124050081c031051050410000d120583d0342c0002e42d5440c2c020716110b03158520a0048030641c11084885402c06000c0c0f007501c2c0d4150b40414118616485056020040036001e052550720031802044a0101071a240f64440032898043c00304a8521400b04a0000043c1e003042c16503244154518014119050a410440c40c0021a41000800000d440000554031070000700510590f000943c103c011141d0b1030a1180a58902e001c455015030014400c800059401c88015a4040c0d1300f440c0c0490000d5482004015250129100d84000f980000f000d11401c40200b082400d040400da40324111840e0075207400d240c0021aa600c14440d181035410644d20720f030b054042e2066140c00c54107403aa00c2c2880b00128 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 65010560 1250 65009310 65009341
    0x20403030c0203010b0102070b0316020c040c030b1906090306050c0714161a040303080601200703120806030a0303020913150e070f050a0507081603020610080106140f03010e06 77
    0x200e01c44d41c02c18514880ea5440846c00008a420302c24195084d0340300d42c1d803045c0e211000e0105104c210b10610203000301c2c95542c1e0181ca5504080d0391000100141d40380107211802e14010120b07180c1c0d00444004214460b48105407408807900254002103949580c0341840c000c0c86880c1d405003c94518442d00700c0504000309014496003410b295a0146640e00d5889102410403040c1e50349040c1800c0c03000300003103400f0340700080d401a0145840f1041c01007802060010321348421015107160b011400600402c040711010308000c13180384c00c003c0101d1600c080002d690300000c1350f006040640105d89920316403215000c200112401041c14841d4004000e402d4140b11000c0c407501c949180d03060041a5540e0141503907030317011805640d031546444c1000c1c0d429200b80c0c0c4620342c11540c2842c10002c0e074bc0e440c1084d0700c10400e00382c825800380c501410854229401048550040c81171079241207010455044690f0446801e1442a15800050315914000a0040c900c5100420190081c801000300321340015014 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 65011810 1250 65010560 65010563
    0x30305090f0f0307020402070c081c03060b0313030e0609060c061603020306100e010c020d0b0f0705041d04140a08031602061b07020d0c0902070c090209090402060c010b04020403030c 80
    0x86076503003000501c549568120340d04901885410400c00d1102506240e00213108203801881065901542c030130b00d10707140a4a940042c41c04514001c040c0300c036554103000b0034008008410300a411418210f24114420103043d0004083c0240c25050320040d0321604180c4040850003402d0940391081041c0054503a0400c840b000000741d4002d450000b654006c1c42901c4c0100c80c0a0180301c2c0400c2201801d80b464241d8132030301e50501560700e01d240b00691321003508000442c0324100122950030a11540480500e002d40310b241448410f20091104130300d140d003281456000c2d12a500d00c1903c035820524a01c1c080c000c82c4503814000c500c01d140500c2608001140550310031222207035881440c40040703895803415200303a090a40da140408050a01c2c01c409800100d000070501007801401e541d0f4660707080101d44c0240031080e000f02c3e41001313214001483c0d10081001c03075003e5140c07040c3c81c40050071900c0001c00c02441810b01103502540070000b5408402d50f100007500840d07646499080c040d00c4094407480 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 65013060 1250 65011810 65011813
    0x30f0506150114031f08060c0a080f04030801150215040f211e0917010209010906050f0a08040302011b0e010e0406030b0f040804030c0b030a0506040209090601030f0902041503061409031608040305060403030509 92
    0x100ea12f1600c10a1501d2059030503076903801d9540d00b04214590006540400742046114122081c4140b80c0301d20314960141c0d02c01d00c04020445101e14100111030f0103040a01c500b8a10018aa5502500b1480a9210380e82c003500b0b06c007480507005810340e880700007a0444440750000300d20448404805500070002a90242ca07080c3e41d01d40d0b6a50b0031281881440510603c09000b800205000c9015603413a9821038070078000071403100c0d50004150794280c6140b8040b00096112520f80b190b5517001505c101e0000d50a903000d205030f80c10354441d02081030000e01605a195000780014003403059105c10b56000c3c40d480740546050a0b81d40454000a400941d1000c0303849251070040f907030f40d1409100b220003015004d80140a15a540300c0194010400c40c40020b070f44e0740d03d40c3d41c05001682c072881045000c0780b84400301c1d0078090031400c1c280112101c3d110302d00b40340b0b46d40c0c1052250512002041e01d221490415a4003860b98980c5040c0110b8040d45d03000501601c95601403000701038250308142d100e050103d0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 65014310 1250 65013060 65013077
    0x309010203070908030a0c061808130e010603090803040b07110d020102120601090e04060b190906090e0d080411010207171c03050105060405010e0604030f0506150114031f08060c0a 79
    0x3065842c1e00c02c82c81c040020500c7c00080a00080054101d695000d00035002124a1200c5031210182d175406200240a045a402818044c914410359228090641e510f07040014018566540d80036210140002c0d114110003c0000d0380e140c4100720f076805a1304100706403000c3c0032a010b00a8080d401c03054402078442c1051000400d654400e408010895400803c03204454843d13441b9038000341601400d032608201440300020943c0d072039142c000014510604000b980c0ca181c440308a04030f440c2c01c4500056034100d840e00708901d07030780100599003103500000c1c90112901d400005030b05d050b003258840000c402c00c911030445604000b281903d091345a180000c0003000d410f40c0200c1c00c4078824040c00342c0c0904103200501003544034040414250030301510991030f260303d9888d101e03d00e61741d0703910454050f8404001c025007900b064800100c024002c3c00c1800c445100103a445c1b07500c2c000100500b01d00041071030301f6550700e0760303000565005115000c1601c00c9810311107000b5001d64403201121010030000c1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 65015560 1250 65014310 65014319
    0xc1606110d0804032f0d0917070e0702010902090a0c020f0d080705090d050f1e030909070e01030b0907050901090605090607170d0c0302070c0b07050a020405060103090803090102030709 81
    0x8101d0a100328034036501c180640d03440e81c1c0e06030f070313816a00494185842d0b1070380c10034060803001d6038a900314204128018640040b51000c001c0c540a070b02c0d000120b1782000d60741c81c40c40d44003000489409035868404401e07019602d0010032030060214600c0a503224031113605000c06002903030b00410310402c503942529044150420f42aa840380b4070381e03038600010302d0000064400c502c10400341c01411401040c040e4038013410b803100c9107824040f04401d8000e8000801e0700c0c42159049800c61594103c85000d58100b00d0742e1000142c00310310080000060002102c2030050984c404d5000c014110030040c00303140141442d030402072036500580502804214100c40114100d4060400d8826091000300014504110381d55075200c3c0303074400c10904140041c01d20504488000d20b014201a610840d54016219a41400c241c2e00056103544210300e280d00420120303002c03480c00304a141d42e60b501554080382a44804004078002c00c00320700003030482d102c080b0522540b14010f40040d070041d0148d548000c82030341c44 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 65016810 1250 65015560 65015563
    0x8030402130b010903020907090302040f0527030301030b040309091a0f03010605030a122606150901020606090411041e0f1e1a0603090d0314010b0405060904020c160611 74
    0x20b074101c0e03030220303100210410040c0741a80d001940207982d0318207404107175969404502500c0c8140b4900307050315110070810101007903860f88001840480d4520303041e50000000d2907600d0b0310041c00080c03c025800f500090a140c0241800c0008190a01c03003040003007031030a200c0d007001e8400ba99080c4100340c40c50b55090385140501070081502d00050241c06d04000e00e03a10490136410340054042032007802980c603010310000d518850202e40700c14a9245180c5440401c001007980c0c000d00050b8442c40900007954030383d90014100da40004180d07100c030740a13103a50621208601c01041c2c5154082d08000d01694800b00782c0201c0c01820100701c0301440542000c0c901d070300960304580410505601114450000c01003143c004030340780b6075001e12000c00184110085003090b441140e4104041e03100d035468a56090340340c440c4030248000c50005400039414101b6000041c0f00700e2080510950f00821403080d259280d070304944040a0140c00c0f1a030002d01902c0240000c00144114004070350f00e402508140c000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 65018060 1250 65016810 65016821
    0x4080102070302010506190b0c0c030708070e0105090408030a020c1e0106050406080d0f0f09080106060806030d08010807060e0303130e06120106030503030703050703091202011b0e0d1416030803040213 88
    0x2880301f9031400322400d04501e03072103903080501706030703024400c0d0188034030251024004000035003e0310380544076550418001c109203185c1a80454001d640003010040030071040c40035250417800043c800740c1da4150300201a450010445404644100d00b0304029001106c154494003c42d8020703281406102e50300c002d2181ca035808400078002007040307207990b241524810f100c51306038481c99040c00082e0719102d0302c00c0760844907503400030303808148502c0038420b0b00d03c1c003000b102034480117505d0148400d6051202441e02c407001c501c120001d0014080140d00d8680d0148107946966120800c168401555043c00303003c892800d03904640508040d207901c1c4000e007030600850b4240e90301312004628503102c4c01e004071b009000041c409001c055607120007800040d085070219080080ca41d00100300080c400707840b0703100c008005460b44180040c03408804601c0d01c40a52a544647d0048007544812641241c050300300302c5d00348000f1401d40c1a800000c010450302801071401a4000e441c1e4014151404084400700c07038 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 65019310 1250 65018060 65018089
    0x1060f06030b03100c120501181107050706110106081b120604080901120e010c0c0c1409010e0c160609050d0e010503040f060209030109080405100804030c0b0a02040b04080102070302010506 83
    0x20401c000d000513404064111880882c014500b48040754040c3c0d1503041101e0082e040008035800212134000c41070142e004000140801e5000985130000c1503031402d0b5940c0442c42050f042c805030b8030030000003c10030b47c8208001d003105070603199100540180c50041030f03080d11109120380808464032280c52000641d040c0714640c071004641c90243c6420041d07131410040c0490b038242e030751506000100b00e03801303001c0c59080942135110840003182518101d0a00c44864006201042107140014240e589280348541118180341400129803180b044039001c900c140354200e10409070308a503c01c100480d540c0520712649c0184195001c585022904a511041450b503481c00100c0c10720200e4081000c0e030400c034011a10800e00107152050300c02c0400d007903c2c800c0005a0300014042020484c82c00c102d003a0b05604da00928011007546880d0780c010b402c070800e2030780207084054007000203120104907504440160487c40780d02d94a859032003164038080d500001c4128010350801010410504080240170040c1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 65020560 1250 65019310 65019313
    0x903030a050604060906181407020309220c020609060a0209090711010b040606030207020f0402071e0c1206050a150302010e01030207052406030d08070c1e0c0801060f06030b03 77
    0x64540400d06009072102400c0b055003c4d5468400081600b4148543d60041c2001403031003903010b0308030311900200c580503603038010003412034810003201c9036000c0211203400000300c44900f0f0b059409540c8081a0001d04e00f08003c041c80c01e14601c02c1c80d0340000e4264403449030001210a190396007240035041c0d0007002003d9030000000d0b004951400c3c01001c4104414103ca400050100010340015042c1c40c0d555105101007580003c40c0d07419401e01d51400d0402c1c5805440a41c9400050380d03c0e42841401c9000d05c1d56010208080a0100000c60302040f004040a0000d00800310560500000900e41582d02c410290300c0c0c00000000000c041440b0811241c058445103840c04c900c20054020390f100140848940c0a04014401007148505c0c40400001e01d024000100340707000700505250500040c80b14080c48109420050a2036001481c5585c840d4480a0956450f5000302101901001c004000b80030300705020020444940550241088821501a1581c0d00d0744e100d0055044411129455405 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 65021810 1250 65020560 65020567
    0x809041503151d0f0a020d0503120f0615160b06031501090203190b0109050103020a050405060c070303030b011b061d0a03080a1109030a17090a03050309010201110408030a0807030f140103050607080903 88
    0x25190041e001f940d0030340120107903031400790307681180e42c19510220b4210120030400c4080c4412801d2a88828030580405040d01d80b0b41002a001c05001c603900c001c004005407840742c00110b8a41b8244503950b4142c0c60b0940509042d61204100c0003e9041203649001d03000c011703c14401030140da8000d0001f41401a118451018100300c0110b000e0b5002c0019502801010400011035482d00401802c41d181c0c244041c0542074203516004056800c2109070b58104402c6061702010078010381c041d04150360703001c2800a08000c6e0020b031040705091850050115020700291401856000703a800f51148540e000c040100035600712111035103011b500e44154040c1d00c1b60fa1042d0012b8480b603103407031218070101d507003604040016000400c40c2c541600304441c29040440d400c1031550f0240203500c0e05022401186040500302032005036a402940015030401080c20041454035009070b03c9220241656002400340494450754400446070a20080b9964800c440018007441d2041404a00540c941d034042d515 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 65023060 1250 65021810 65021813
    0xf06040b0901030b0102070f0b030a0509010606050d0b0114210c030712050414120a08130f0f0f060204080c0a05060307091205070e04060b120a0809041503151d0f0a 72
    0x1d0240130900c2e41507102e801800300d102c0c020880c04900905010000541e00e2901c10408404d40b100034111036100e03811710314244143c0d90802c0503180b0105012500195036058540100d401580101a510500f94002018541507400c42d40088480c0c0010016261a49410b9aa82030074401245c420703000a01420521600318142d8000d01c0d0080c0c0580810281200c0c500713003031400c21003144000055210000742203000942c00c0544035070300642c0c80c4012a50407255884900442c0c400d490028040150420301d0030400091684007210950044800c54503035490700d11241d5103808400d0650700c01e10712000001640e1034508201c3e44240c800d69100300f50585844110390b150810240708032000d004044000c510398007400c4150b882940182004a0014034050078488000a01c003007044082d002003c40344081448501143c0141100340d400140c4020008101d10351a4003030781004056000030f0500b0718100b010394020b044030a83c6902c0c07080103000c41c0320465644405180c1c0010b02900541c2a460 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 65024310 1250 65023060 65023067
    0x2009010f09062102040803042d0f090507020f0106030305131406071101050c06070905150304021e0f04020d0c0305060612130206090d030801030320031b1203090703020f06040b0901 79
    0x409543c00400903041c41c0d241c3c0c00b06402d640143d00036501c000082104500000f0110301243c06a4074480707003006400c1e0402c1b007004da040645009081c0d500e034841000c586005e2080082ca03840a603400b0080200325100e140091484e407000d41d10341000c410200022130300e80c14826500300c0001c0010821440d203656550707003900324035000c10400d047c031a043c080c65010b500d05006482c40b420803903440195160401d4100301365884400b0b40602c035581c0500c20840141c03a244034242140610224405100340d030500083c2d407041c3c00c112520b400078008140d14030650300642007981d9601064800340890b85d11582449814050a03c8035580180540041441907003101a03403c0720b10700242c01c0e1803030200c441001ca821841d01c500103c0000c9c01c0da500401c1807650100100280e48080401006c0280c1034a509590300d02404012010405002c0020240400b04000e80100c00140384200354483c80c10b062030507258000c40c17009034042c50008804510900d800011034051320407015142e41052640360046 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 65025560 1250 65024310 65024357
    0x1150503041101110d0801050a090e1509010b030307050a060b0607020a0b220b070b06090c09040b060915040609050301020406050403030305041505092404030f0804062009010f0906 79
    0x2605200c00700034043d82c0300707000707002c00d15000c0d045491b12401545030005110064500c1da00a5001d10301d440c41112141d2000715585181c0c0d820741c4002005612035070369890040529483c899418800024544200710b40072800d6403020b4001c84081001c1c090080900420744103000000398084030b05070080c04030052007070150107980e001401c00440454684002144154960032600240c40040380380b804200400d02501d51004c4240d46c2041d85081001e000320080c09030f0328146200f1a03c841801e02e00303444e00001d507189120010500c84c00a584500e4110495116000c1c50000681d414800b2a050405008031b07012914030b980e0f294600b6281d07840c00c40081601900442c2d61148038516880020135600465000340b491102420880e010a02031a82410b203000385c1a41503401035081001013504050b1480914901d07041244166803649049002407140311424500442034281d0403640d041c1c2000a0042c8244c2030b00c80010401e01180242c07403080e4648552000584c184800c0d54489600350543c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 65026810 1250 65025560 65025593
    0x5010f03020d020307090e0a0b1e060903010f020405011b0521070c0e07031401030206030103062d0c0806011d040e010207021210060f0806070302030705121005010201050115050304 79
    0x1414110741c90707520003d0b684103031110030004035040000d00281906181c42d940028000d5010051030018501280401c0d5148600c100c00e101d0342c6c00c0d8401151602411500100f00c01402001000c0080188000070740142c058140050000300822449045c4038800c01c9011350400020482e48400d011011250709800a280c40100d000344140c0c00011080e401b02006400780070346d02c0b0f00514040c20001c0c21107010308000e01c0070702c0d8044010005a100c10b001c403815039030090008603c40d207100001c02c0000840c2c0b241302d800000c0c80e45030380129074460f501c003a034980031380ea50b0441507031101001101e01045416070500c641d0459001205d56107055886a0000300c1103031300145c2810b0b669000140d10100204a220554100321418002d1030440d11400d005044800308003e44c0d10b040c8001c0c00da5400000742008181640000403030303280d0b4003500c19250341c030031080000c0210b0f2504541d649048141446440d000d5801c0000209411145003c00446880d56a40d0f041c150354882d01c1e14510386c0201d811 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 65028060 1250 65026810 65026817
    0x301140402130b0a0804110d0c03110d0b0405070302010e04090203030a0c0c0f080105090118050706050d0207020402030103080a03050f090c061b0f0a0c0602070501080c0904060503070621090c05010f 87
    0x50071902c40d4041d1400003000e417525011464039003080d0703008420a805d80b61107060203000b8071740002c0e446000c88041e030740c20201491402071054081007117465030f014054039080898040008020002442d40d06803031003a6500301c04a12043d003400155000000000d60580060002c4880b0b10310070317000c0d982282c1c0100d940306491540c80802e101504503c2d0044c120503511541000a011000d028007584020500c9290007001e1a40d00c646480742402c0c0124000c1090000303210b80d001285405595081c0e40050045540b56521316214000340c4c0500180c801103818280002d10050400489610908208000e001500070040c1001425440340e1800d070415145444a90846001041410028890000140032044442c00c000c01200031503441842103510507138090059980c840d07140e07070f08000003008107900c80e004200014080c00c1b0070740100d0f401d0305c12132a00154907580244003518000e0710a2101206012010120042d038070102c0004e040401101c000300942c1d4811140c1c46d46c40441843c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 65029310 1250 65028060 65028097
    0x1060501210c0e1002070504051509040803090f0706080403032904020903100e01061e06021209180406060911070b01030212030d0c0e010f03140402280b04080d02030301140402 77
    0x240001e08080003904c4100040c0c1c0540000c1c4040d040c140b2406800c1909014070070f040801030400902070301c5000b403009050510210103d43d000d0020089045082103080c1515859034403044000c014181c1181c050340000d041200700c440f0f5511100c040e00c44140c2e010a0350300d55a512a0904c4003950166240075013511482c4421200c0b014144940d100400c115000400c055252400c3c05034604940c0200c440c01c007050710404c1040d6600000c4008940300c1d02228551a0701000001807002c01010f02410f00060a22041100b0404194842000d650b81000304101003001440f10321500e001741440109440b04110041c07015103895081402908250030880e071030100c00c020729505840380c4840440c00300c1c00c0d03006100269a0881c0d00d040000b40789140c100941401080b04403a05c140c0513101078019150194015104643c00c0940c0720000c10030b64a4241040e501c0c10344514640c40b52107070b1807a5001c0d032800000d4107440402140e0494601e0601c5a00d4400188104002584070b240d040f484000e050 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 65030560 1250 65029310 65029337
    0x913110d06030609030201060e070504050d0f0209040c05120a020114030c070206040306050604050c030603060711100e0604052103041716060b0306071b0f15020304050f01060501210c 80
    0x60040707902842c40780c40042200350381881c003c0d081d589070303802a07440420000b041002c0702d0b03800800e071012250111066000e00b0003c0c00c1c1907401900e07019029421000c00070400003030083c01c8180000b180c0c8107503421598800360590054441b4591100203002132401c6102408000014000d140c0008550030101e140100903800180c0c60b60140e0301c101e410341c0d100c5040085070f24241c440d8950100581003031628500e08140083c0d120400104200d00340402220301c800385042c00c109000b01050032410403c913042007141c40c0359403814100e804881600c1a024000716154152a40c61146100704015600f1501d450340d5980500030030b83d4001107042410b01003080303000141007000d10058010301c000100c04440034145070501d00020004d10034010301c180504408540030020088580d00a40154081b501e03901d01100685ca0b41803401c50110300100030300080c0040800c01c01950828a0000c00c211035807040155000e0074221855000c13800703119640403488802d504001803040c2c0341d20340b031404403045 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 65031810 1250 65030560 65030587
    0x21b010903020f060f060f0d11040c030905061b0901200604030c0201110d05030604090c030b1806011502030316120c03150801020306060304081b030301030302011b05091311 76
    0x10300c0e10540043e4012009800b4036001445001c1e0071440c00d0000307480d54a08440030803030602286000e01d02641e00c00010780107000c096440180300c4032008009200c02d41904030020041c020900e002e803130038000c081c0450403c480340c00d003e50768444510031490420308208015a900101c4400c45020f0301018072402d00300540502c002071241d482a1900840c4402c1c03400010700d42d014076100041c0c2944009000300105800c6805d9175448502114041500700452614a4440009620041c951580b0109104190218824884142c00400c4c102d40d491f82c0e03510456402c80f56581d02480c01750b00b04001013110f03070354490310021002d551401c014100a801e010310000711101d40203290f000940c1c8000c40c055000800e09041e004011020086d41182001e50015555100240005240810005000b5044222003000554180d02c420687e520303980e503030502074042c00c20710400f0b0303040c1c0226141c1e8070900c07401b550685040e1203015103001c003000c0c0005a80380007407c94244a560300c103014009502c40402 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 65033060 1250 65031810 65031821
    0xd021516030926060f06040204030507093602241303020109050a03030210020306030f0303011d0f0f0a0f02090d030203091201020702010c06050406020706090809090127021b01 77
    0x11990b00d503240145090110079007007840e82a84072081e03401c81000d15071074000040d400e401001d00416a8150789500d00007400a11540e41b00074128010701c240001c02031059071140540e60040c10020302121091440c181204402151074034020f41c6150100c030240c185040300401e104009060115001c0050300f2506140c2c100c1000c0c0802d40d5445a014011544d000000000410060382c002001340d08503030300070b91100260100710b08031070360100020b4400d60741000f1600101080c0801c0d641e072961560328549003e034020102003007165040000c04c0d1784107161658988a2a041210712840c3e45a4100340806881c1d00c48949460716000e00c1043e2080d5034001d603000805100c6d4009560b20842c1c8000d010480c428403180c12074030b0348144402c201507604062001401030703010300d00151603520351074000028014040040d1181e480c0c92040803c0065030703001040600400c0700d95a2a680c4d0302d020f50650a84078404004800c040c01c41e0566409003641c010b0000081c05041808180303c9441c2d03d07608558 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 65034310 1250 65033060 65033063
    0x804060b0913020f01030606020c0409080909190e0a080d020304030e0a06020706031d1f090605040605061c200102070b0d061502010902010903030f0e130e0d020604020d021516 77
    0x910042d50b10741140b51030101026100c9003802d05110039441e00d02c0203500d90000d414464055600d518420042004000454604480050099825041140340c0040956402d603006040c586091200103408400003226503c4a41c03288119140c0014030000c50041d40001d44120309100d001c1600301c0442e99442c025401801d55a80100750085c540340006040d54083c0108859190801c0c0da00c1240c032202103404d03a001c0d01414070b04490507808510b000700a00300510050241450b080078401044201d8000d80e0090703108a4000301c1c00130034034902c8544440030ac10020101401070203072030400c50b10201c044150034414010345890940e54002c180d4aa80803072206800c4650301c00052064409043c822003407000c461008006c3d40300a6030001c2c110709950b000140a01954405c015a40c3d80b24410120821601405240c4a50f0100039020082c10148a00540b00c0c090119420540c3d4400500644282c1e00200040000700160b000e022102c849035411010041c420003100c0e582c00b85000c410a0000e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 65035560 1250 65034310 65034331
    0x6020a02010b04150303050f04090c0e0103111201031b0e0a050901060602070803090112020408010c0c0201020c1009030f031407030804020907080105010c060e0f10140c090607030804060b09 83
    0x1610558002400c44191091540c07040b4585205205058103040003141903950606110382e0b01c01c00e079540751526015541c0541c40007030824460581d42648824050300010003a00d0500010b8000c1d01c1d0788c0d0f0b01c0e000350903000c449141d000004201180c1c0b5110321202c450f10f451501e490164443c1c02c1c40c84220000c441a0b0b506c1d51721030050000c8000240300307880082c0b449202400b8502d0401020350703242d2181503080350401100745007000f20402d031981110021312074540200880503907441e0160541c4559001039015014030000c0c812a0b0a1580c0d0100c1401d0b15030341c03005040c07402c1d0307550b8241c08138074250203400304401d42c0402e82100130303801c008100f0305000740c8408045140c02d104001d8cc2c0075008000030104002d40d0300400240c0d0f044118003907040e900c1035000c0fa001b1030206019241074001d0324a01e00611611a02c00c4440f8220740c402c10035100a0750701051075a466950094040c8900d003101c0350400d5040241201003071040d800e950f0041e01c00c0d1408035060f031000001801c0b1031010348060038403 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 65036810 1250 65035560 65035567
    0x30d0603020a090605030604030e040f0513020306070503010b040612090515090601090c080c0313021f080105061306050a02120304080306040b0111071203020f0f07080709060f03080d0b0a030602 85
    0x20762030654440c0d8000c3c5080002445128205408a529998060801003d10030501c882101703036030ba140c0180c1c1d020190000200203d03d013010003040000700c00c00050b8040c1c002c0c000440c02d00e85c4124210790588072a842154901441c00030103e03a02d02d40c03500500009075807503000c0400280203000309001e400c005201c0076100d0421440985c01d008042c5d2016000310701d401507440d100d0340c119421720360124a446580d520b95454980c9020001c0c0c4840303009621415204040f203441c010810701c46481d2003141d42c0c82c0e071141e0701c410601031035104d1448103d11502c1e100404000302441417004000c8004244196110004800000340081d00155012178441c900442040b100342010300c1038640f04800ad10f0310303401c3c0a41003100c01c3e0b02e4001d07901524919404907200304c420301d8020000000707030302c1d071b9002291075241c0c142064bd902c07a00c01d07018014039030150120004865049001c1c2c2c0d016580303c060140b82c02803079039407143e00e2903200082d407219072030b21564040c42e00d80c2c416201000860040201503074 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 65038060 1250 65036810 65036813
    0x3090503190f0503010806070e0f040f02030901150e13031e0507061107030806091506031014030607050a03020901030b031f05100e181c0215010f0303020c01080402060903030d0603 79
    0xb10290006010042007800c1c0700401a0500006203560841a50b00302104660100804101c400f05002c02ea00d42207410316054000d1042070703500441c0700b2050140200b26143c070100c03009403c404c00d48a0115071b0700251001c260f144508001c840311040c030030b0429450083c0881c2c4644a0140032408102c0490400302d126014840103016085840800080c100e140000a030b0b000b422415020741200c0c06280c203000020004008624240d031120b500405050701c91074030704030125240080303004a102d2200054a011414200001c4250103040b80342c4940307040c513981c44401c400070b40110b4000c5041648a06031002c2e00d4a0a0110000c03807650961482d07990301c80b8900e4002500d802030b0090803103011041003041038414410305c0759001007109502503003004012140b50324141d102d400c280e00646520130000b11407900007031494014420640124010f13a41c400000c1643e200301c0c480034015821400740d101c001e6120781c512030f03031040c40102420b0a01812070046407568121600d43d08619a40300c10910 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 65039310 1250 65038060 65038067
    0xd0c0501140306011209051612170406050d0213120303020c0c03030310030201030506030a020a080a0c0605120601031d01050903040f0f060e2103030406021903090c05100309050319 79
    0x142921036841d80a203181018000200315499000c03500c3d580c1e941e00c2821400b004424815002d040428190b1032150940f11640354100ca00310b00001caa280806140c1c08000104d50010b950494215032034017400d1070720864441010b51b000e44e40021a20525003004681c40c001c0305400000f5501950300140c407141c40060302c0d4a4030b8590f0005510980c020300030007036071956400000040c2c81d42860045203640b00c441c0841d02e8108e20343c40084d44289500c0000c1007800c3c00155000d52240039003100380302203580301d205035003d00c100021070700590750b030000088455019401c1010004140d109040d10820706982d09421290260b460b021103403c009000c2014450341500c100160a4803103001c01d44625002000e000607101482060040d9084a1040409175291403000c220801034002e50f035891602d0315251000b980103001c01090b880c641a0032002d524070900c0746140700d940c0030a5000d0060300b4030b0104030070140f445022200701a16041ca0100140307052014064030702c00e90005401c031a45200010303 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 65040560 1250 65039310 65039327
    0x5070f0305071107053c031002040308090f06090d03020706030c08060d1b08070e060a121709030309031608060609090322080109050601090e0307050601090f0b0d0c0501 74
    0x12401c214060f56415260640800c5210450300125040300c12020342c4c540300381b4a6041050004500005034502202d400345000880d001d8807011030590f0400f8034000840400c82c0550300016091080600101030b81c0d0420040420304600014440390138200310100146024034480e4040f40181c00c00c02c02044201d8040c0910401d41c011420800d501c1d20b4082d020034006020000040c0c00740c03000d03464111545050604507406070035808250307000b4030b84421803401d0600c070580d403281c003546003418001462900e070148014080d0303000d030708400d000e5881c0242d21095000714001c29498001003185204035a4104041c0c8049804c5040d0350306c0040c03400010509101d4001c0c003490141c0366070360402880700c41c080222404028905111070014000352400d0398810001d401250166203010302030b400380704001603002c2c100c500b180310034404101681c0c2c02544038011204002e00c241c1c4441c005210110050700804000c0700c54200001e003417070b8102c0016800100e00401035654960f202414020707541c3c0f100e000d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 65041810 1250 65040560 65040571
    0x905011e06090c08040f021503040302010606120908090907030f0e010b0a06020105070504031e0606060206061302091516080304030507050607020304030218060d201809031c0f05070f0305 82
    0x1003002685a40f00034083c0303d002000204030100e16561001155605081400d049509859030b135101c1c5400c0c5000b80c020001401220007280e06d64240b01c06645032401044031082c0e102003a2802e0286030310074440400e00280640d800d0584440c122920040284140d001d0b51450702c00229042420380140107068030590004001c690401040050b8941c105d4122022681d000301c401070804407600140c100c01c96084002410705042000c0050280d41c0002c459005070070031511400c00c0003007071549100302e10030310b4069604011800c0c1060205003014001d0071300c9100040b07010034000c030303103a4030000b0320b40c0111000c40114a001c02c0d101c05000c1c04201ca27079407200003170009520b818207640010344034050040c0058254005c2c4400191a6140c03c0c1481d00e40c142c2c0002118100700c0405410514500300710a000e0044030703488018049007008001e0180540605000782d45001045a50f65050410310080d42c211170742c4541d11503c5c14520703889164400c4105646041030765000610003800c0e035402909 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 65043060 1250 65041810 65041829
    0xf0703090b09150307051e070b06102703060c0306080d030e06010902030612060106020c0f0a0e01060309050a1202060a0b03010903140c01230103230303010504020702040905011e06 79
    0x20701089840b4076000294103d0480c00300c0e41c80359a0843c3c00ca90038428443c8040e0181428041c20701000040c60240000a100c0c5082004079920308080c00a8900c004841c04005442003640ba10303503140c2d20350a80068017510010000301d0f5200d0702d45d102515200c080f0b04002a65a4a04000341201400402c2100010386818002100c502c50415500c0c4010b000f1240c181d5800001714403030396a201c401d4101001c50a003503602941e95284065103400f01111518064000e891202c2d40918040135007200b51a81d822100c00035900384203049006008400701164184124682500400d0103041d1508500900d5070050903107150060441c001d035034440340783c02d000340c1c182034418000a821404540d001d21199480e50740355112080c09130b014004640003510340000384500108070004054209041c0d030702941d50400403912440c840c2c0460103040c881c0c040700d50820300040c0000c3c6003940041118900041020440b0360803504c405007120301280c00e00c008c6041c05881d04080c440c1d2400391800038843d544 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 65044310 1250 65043060 65043067
    0x90b09070e011a04090209010509040e01050702060a0e0a0605071403160207050d080a030902130e0102040806160f05090a0b03010e06010e010e010203040303080408070b131a01060e060a03110f0703090b 88
    0x1648464540114051138508071b4022a038810603902c6201a81c10301c010040c000d00c6001031501615001307150a80304400140901000a40319000300d00405862202c00c500925148101d502c072070000f00760103060f14041050501e800b04100b201040598001d103c1c43c0707030344200c20110410203031070600c407540858055070034100ca00b0041582102074516625082c100490750005ca48002003c4c0c0c1440c48880c64510307d0a141c44015100542c06030054500c9602100d10304d881c0c3c14900c2c92000100000ea8000410900094600318490f1003c1c02e620000030300980421601c5150070b55541cac100b60821030032540c0b20820000e06d580d10018441d84554282001c1403003040c4100000d46910403800058140103858000c00c3c1040680b0b01124512500714540500342d00b4882090803a6019408044d16010200084d0210310b14030806114129061901c461004004400902c10140c008540900078107a031907040031203a100a900410400c1c280e1b5002698070100fa28021b48002034071781180c00c41c12011b0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 65045560 1250 65044310 65044349
    0x121a010617010b0a0905030d05040503060c09030a14010b0d12200309060a020703080706140c030108150a02120405060106030e060f0c130308070c030b01060503060907030f090b09070e01 81
    0x4000150644144403c03065940c1240c550660b2003110b65403102d40c00d88558041d20418542c028050b2096810403030555034182c880ca10194214000d2814241d810b411071010384000070015075504103042507060000c0340000c40d03c00010481422500241e8050020340c020144155000805500464005004800c001d00d2144265903c0c01040c00035802940d00003100a0614001c10240700103580c401ca5042da124041c1c944113019202d14071100b03480020080200d00017580c26001e0700e061b209124010304c1e081d0600c000a10300008040c4c8048000783d401c0003209501c0a01001c414403e43c0a1001130140c2c0d450910020308440e001d100c3c1c10f990390011030070310407040b50040074103402c681c1840f4400d407121100e40166041141a5000426542000506034204a80c81c000d1030200c902501c0d007002c09a03a01c50068909110448903654480c659170006106035000354041a6012602000018804500e0307880c0340b8006420360b1071402c6940864003c1000c80300c5400785501501d1380c1e42411015031500b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 65046810 1250 65045560 65045597
    0x317040c0302040c180b04060206091f110d18020f03070f0e06150a02011b03060303022a130218030c100309050c0604090c0305150105091306121a0106 66
    0x3a0100a114589030012500e00e24420340150102da483c040501083c940e4030325a02610f6841803003488094025640080d0414901151040c01250011155414540d4010403070b4010400703000744029180c0180140c0301d0b14100e5110700c2e2a0211401d00c00c80042030307140100300300140b1a005091081d803081f8070038090464080c205004840030300e4060416615143d00140b0324140c44181248800004240116807035815002852066244011300e03400b2802500c085007951214000034002d0382c001d502140152020345148980120f0502c041020803144500103020398465103c80c04106401241da002d4110481907400d003581c40441c010220403036002c0214004181008100701032507558900007040c04003e00c1540740702400200300b280d0f1103481d956014020050800c501e00000c1c81c240c00070340325180900b641c0100130816101c060401c0c4052040202c0305c912020081000341d02e4000002c0c080b400c5020248005101d92035107520080c1c10740c1a07540c4442c2c141c0c490410082c0c802d02e0300b14444038 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 65048060 1250 65046810 65046833
    0xa05031b1908060310021912090b130201091a07110d0c05010c062012152404030803040f050f0c010c030f031508010501090c0302190e0328031704 64
    0x200c40c00d020340b50780e81e003500007030508102c0e14501403014000195070000f0042852004600501902c40c0c425003a02170145008440c1448401800040c41038041f4550300ca00714900580644140350502c000c030744880c2d1441059118030808444104042000002c002e2000d0190b50618000d0312004207029090300e4001c1404207501c2080c1c144440701d00008188149031700701005240044040c0c6000d042c2451402c0010b0b070001c170700541c1c0e6510a41c040b8100c0102e007041e0001c140c400402c0c40740c8030103100e401041903000000d036090741034604010000000b0f10500142d403040d4001c3ca00650845079030f040ca581002c04e459280c02450b0001c0110841980c0c01c01d0f404401c0c07941501d0050f0286444000907001003c44400c0b103140b03403051400001c1c00a00540066040c0e40c80b0003421b2041510420054099008030180d06580e40d11071500001c076288a01915101c2e80401421104802e003208500034035030340415040c5200401001044003030680090f4400c03541e800c10810420b10b45040e454a411028 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 65049310 1250 65048060 65048107
    0x30f0306130c0905010807023d050a021801050f070f110904151505030c0d0309050d03020c04060537090e0303060406060504030c1e09020a05031b 64
    0x140400860856161006035250076118031004104103058454041e081078503a11802d40012000b8000030b0b4030714800b180c2100581142160030364203803043c2d141d12081020004d601c28815040c544240d0400009018041c000c0e0b2220200582d1024942c3c45003c00d0004110401e051140400c10a04031030300d26811600d000340c0100203205843d00c249014842410300306080d0b81c0c80a030340811302051105900981c000d1240f000c104010a00022041c00600c03440342c072540b6416009408c0c11a01402c0c141d070308003d014440d00c1c0003d0450740350000120040d0040100744c1c01039100141c0388295042511900b00604403c498038462108041d859040b840608880091141c11021805402082c400f445901510701580140903904104441640d0794004860380d80c0303d1400e0550004d00c05010301c08690030390303402c20f21180b052811b101300c0a05008180034140d848a01030b0000040705150f07440540082d00c0c40d560340d1552400c0100107008030075030100c0081a2100104014690945000450038400 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 65050560 1250 65049310 65049337
    0x70605040b0a0c170406090c0915050910090e010b0405040f030908061302040c020f1b0a050a030f02010807090302150a0e03011e09030e0a0f031a0f061513060302031005030f03 77
    0x5d544a01d8200058480b8080003041c0712a035060200329581c0c81d4025081a641c161050100c00366644100a03048005486001a50044140521540b00d0700e8214a25a42c1c8501c008100c9104402c0071400300d4800701e80c2503a04100d203082d0002015484044000100301007001000305041001c01015420404400248140d87d107060308080395000784128455804420113442440ba4030385409418848070b800c00602c84e107a07030100806c141c44c0a82c880019250000305154005220b54019210340b10040e0107101400040c0340d000005030768650007480c030007604008450312aaa003203400382200320314160305031281c1d050906880c2401350032090560a00408880801c441445060030781c0d0300304d00c0403285900210b04400c00301e4500d41060030141240e06c00c0a130002d090244070620510389409071a0207800b07480d0b4101061162410190111064032100702030b0385000c11480010303000c2c102c55403100300469004800c02491591074a03400c0300a1106901030256001c0e0240710984a01ca002c1115001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 65051810 1250 65050560 65050607
    0xa0209030d02010902030d2706082d06010c020307080f010b0906011e030c050409020408030c071a0304060902131d010e0309030303160c02030a0305070c0b0f070f02060f070605040b0a0c 81
    0xa000440c0010715807070034801e201c00000c2d034271001c00030300208048519044100c400045e0b0390f0840340c1c0112810010101241800582d241c0744011100d803107007800141c1e418440e420700400d48840502005424289200000464041c048107000640304020801d905120f60780c50f4900c01c60850540d40300c0004001d2500090400c4410b0003030ba130901543c0c0101c80c0c2c1601c04507001c41d081d80b00200030f01411061400325182e2542e200300703d41001038141c41841c1c0c21070081c00460b00250b503c4d00104111031000700340804e03620040d40c40f5402c4401d501c1d078407014a50364000d40c428800003803007105d20364100d050281d49030018520109a6038800030707042030501950040c81482252007039060070b10480d0300505940030311020b820000c106401144090310359000c591800a61000a00112003581c10032681d11418041562030b50b40c1c03842c00c0e489040e81c000c202002005c1482a226004000540c8100c0d000140340c01c007030800d0114103070000d04030f146a40c80c0c84c062924080d00b00400c100c1c0d1321404601101d0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 65053060 1250 65051810 65051837
    0x9021306180e101e06152304090f0506180106021e01110f040e060604061704020a0e16080a090201090e04030903081c1811060f070b0a0209030d02010902030d 69
    0x54071010341080f9403114942a041034558481c03113904441c41a9030001400004e85071140e2084140c001c0365154007041049a4000d00c4800303020f888051030784040c180c6030400b50b945950310159418030900019440c0e0710402c0200d589805e1580c85c0b11741f0244800188103605245001e5501c2d44a20081c4502c60342903c08003041c071809403c2034807510380c01d42000d61601c0303c0c41e034005d1040e00203025030410000b501000440c40e00702032064400b21803140d40c0321041a0410b14001c12017180117407050340c0105142d40041691501d001e13500d801000840600010700940e107100900102c4044c0a02c45050306062304200542e0b80081000e0958888042c5050180c48500e025507044045900041c00b5000115103540c1000d80b03070b0380704001c40302c04580034819078a04e0440c400d945074010100038800c064510500b4164202100a0900c01b803229410a01d8031034a5112402c0b81c03a4201d92400e00703d0340025840c2c11900b01400841303500360300750000380950031142e80000e807036642040701c160401501e20002d40 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 65054310 1250 65053060 65053063
    0x603090203120d0c091e1214060106120e01051510050409050f070801061718010906090c05030106050901030f02060d020f0c0a0b010b0403051507020c09090109021306180e 75
    0x20309499501240a5540001d0f40c640d07405095040000340100303545580005c0d0200d5000c4404410301c6689083e040701c181402c2c84070070746072038030381c5c042c1d8003681c40b09803076071107039608100c0b29010304540c5c0c80700c401d4030081012a8007552140c3c81240300e180d0420043c0804d510b980300d00d0700d400b1a001c841c813105e1178000603001c60785409a6401034078032600305418080390382030100d2014011b44440c0c0e140c102e00c0e81c0725842039485000307030303407541c00d41145440002d030100c401d0040d1103030790720041c40001c220000c49807510001c0d104640c04c00d89600c100543d041180e0315003482410000c21040d03540141d10740c519116001c180d103944102a01071400019144018a0281d04498a4180540309141c98100084002e80d4a8100d10340885050006038008141801c10f2015601100c0c1d0000080040f45215920040c03e000301034440d00070f40c8190f4950b465180c3d100441f2521443da24000010f4912042c0100300740410008048286079141c00c01c00d1281d01c5448c00340c1000800a402c010036800321481d03105 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 65055560 1250 65054310 65054323
    0x1f0518010e06031810110a030c03060512030310080d050f0a18080c090106030e0c040e03090916020d0309020d02011808012c03030906040b0c0715020a0f03150603090203 74
    0x12548400000704000b44c40d120303002d02c071890306101c00c11260b80040600041c021103104145851882c60280100c50419200b0381011458980500d0046a942d41d0348020487c4014a15000b01040d003000c41040b10303038402604080300a200107001400b14021045002c6c0c030a110303002803c00c182c200028010000c3e402584129072604455510164a6a683e032110b519020076035002c1d4400d420b034100002d60944a40034038010078003102d010344a54103504007044000e0813145401c0403a8042440700403066030b1a00c0143e0711a102c101c0f001c414403000000000d04282c0c07210380140a141c6401c8008005d42c852044040e100e590a0a084038001440c5403460302c01031072940011103540c20604800c01c01c100401c81840b100035007844003030000c50f10318501502e90004482c10b64896001e07600150126441c40c8100d42c02080e404040ea1618240ea120640603030103c0048100198000450500e035540c000445070788036881e490100001100e4810a01c5c4004051048808040e19901d10b201551b8050116 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 65056810 1250 65055560 65055587
    0xf0903061008010b0910050d0f0209040302010204060216150e010c0501090503040810060305030304080912070e160302030f15040b03030409050601030e06010b1204030c021008061f051801 82
    0x100c0d503152601d1208004060140c1c05041d5080d403d18104600078208004100d025500c0e4101c1248141d041800b4407100944e40c0205403040d4030004001000742c0c40300868280502c2c00303903001595450030400d000c0c0c9011821101e0f00100365503140c003081404408008611505180d00c0c000420846c8040101d46044000c0000f0300f1365440e02400e0010408000010000c8400c43d4041c5e0302041a0380a05c1c03000c403541d81c44080d01c281c008100282c009410500140706400000b408540d01526030107900e4a0440c0907000311400c3d00b000d909211610224440440312002507280c04d5203549418004442d000b58007034244452032114008008096445d50130951080401404a07500c3d96518a01c1102400d42540c4040c0404e180a81e85e1540c0c0402048a074141d03406484502c2c6840c00d04c8200b04203400d0018026010400b50044000050341c40302d5008a6000241c1d460f02084c0c2001c40070000e00215118894008042103501c4121254010040d141060842c804101020100d440162030302201c039842c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 65058060 1250 65056810 65056813
    0xb04060b12010c181d09010204031401050a06090b031c021207030509040606020304081203040206040510050702030d09051503090f0706080415090b04110a0b0f07030e0904170f0903 79
    0x703a241800e015441118040b50580d203251850f1807841c080549881540143d41380100c0000f030000c2e011600001c0702d900a80400001841d2945d0390311400d01d840010704413648565101ea00b80001c0b01824004c3c00040d001200b0b04100361190307240003903a265240321211040b0030881c096101203e0080c810880020904410180d5520091034001d02541c07107016413501c41d6251074400b0030b805100005480603102110010060040040036010071508001c0040303134414401c02003c1800d0703c5440f100e500441e51a11400d4903840244105800c001d50501c1601c1004601901006070b07513a000c0c14409001c4014018690741d8540c1c0f0001e0342000c00000407031025100b0745500182d8503501240a82c03040c0d0140000d4010000741007820420b5884000010340011152008500400c2242410142c90361008001d4440141c0c0c950400c2c6007030708403003418440c1070004107040c414107030048240107a10030f04980064061620fa9a094245a88001c0070640c440000c500d82c0c004801c034a08845204c20002c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 65059310 1250 65058060 65058079
    0xf0f0907020d020601080c0306010b0f2205011209020603011203030212090c1212030f0705090301111806030402030709020f040f080706091d01060e04020f0d060306060602190b04060b 80
    0x540180d6501280c902d00801407003028000070346503002041c01740c54150007c011b0515a4a050a1090b107500720784914042090108040c1098104045c1040714a00316107034140704031440c100000d0007407071140848108007410f00d0000f0005a0b030324800c43e8190307103182c00980844481414114000c0c022000059410014031040c40040003002540308540300e02220f038081200c0c45044110b40352940049141c040c240d0034804118007408140003180d022440d450f2550034030005800003030946100e286000f0346000002603041401c20f00c0b0304000c43e42d0006903460b070314500b442d9020950380d00b801d1103204101c42e804260315020001e04000c0b140100346600d4044580c54070707410103a44070450751260380c001c2030091074000f0b00280258006040c003c1c0050040310386a18140c0180d842d041c0c040310155002d5800c03c940200284204007070601000e1041b0009442401c600e0318500329481a0080000c0d0b521220300c500b4010005241800d12588c4072403898513a80ba1403420b0009420b281548076070044010 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 65060560 1250 65059310 65059321
    0x2030901090f06020c0c010c0c090504080c01090c1406040b03011a040f061119030c11031015050a080703052104030204050f060a1e0b1b0a0302030a0306060f0c020f0f09 74
    0x360003505c82101e0807003e60b0b40c0c2c0301c100d1005558100c2202e100400c0c0024520081040070500c3c1d224940c85405031801c2850150380c00005400c40340c00384011a0340e925580000d0080102c60700304030744413010681e40c4910b06800c01d1500b18081c001449070b1440c03002c1400d040d10807216002c040c2d6005041c0380481c405820344071b10010b02032046045502e031442c860340600003080d280c5d11082c00b02e150b8064940c6e010070803540d141c20030307410b07680a2407540611031501240402c2540d44210782683364080c411000c054181070800140100f540d22240d0306230320095047c8049080070500030140240b100b908550254401c100c561140142d5002940c003501d042c040040e14910186220700c00d41007160241002c54885440100c010b0076161801140b00c00740000b40542036010004080529a0801d82c9151011039001c452030001d01c51021001600701048042d4415018010309002d8092800e10841644804000400d100382c00400039214000040c0801d4007603c4031100012000000b80001c002071801 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 65061810 1250 65060560 65060573
    0x1020a09030b060901030b04030e150a0306030b06030d09060503090703080307030b04140c0f0c012403150b0f040207060e0d0513060e0904230303040303050403030b1c0602030901090f 80
    0xd48000e440d00e070807150000b0300c02d180211090b816264000e44d14011601d564404039540a0b90040d031a81210780343c2c1c0c00c0c8035840f0505000c0c0c45d00c0045542c020610604602d002e01c904000640341902039030280e4a14480c4a030018001030580d44c0c1840c01c0380e00ca50761301225030314007003075641702400030700d0000b09100b9000d030300d5041000c074184181c4060011102e2042144840001160080c48011062140f0315600d15000e008060b1074111500200300104401c41303203450940a54003594465918800401c104a004541421001d941c05c02c04c01049001c540030803000ea252500f018403540d400a0741e58100009036101d280251485801c0750101f040c0d044001d080c1da408101d15001140c00084c001980302c1c03086031540c1314084040c1070000b680c1c6590381c510f0302400d008c1d12186d42440700c40f150314022000400c0a90b21842c060ba030003003600e04113402c014049584140040c1d0003501c0c0914490b030b0b0410300c803254640c0d40c2d500080050b600d035904004280145581e507801407900841034410000d000b01c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 65063060 1250 65061810 65061827
    0x5040308070804051c110609040e120c0c0a0e1603020c010c0c020a0b0405060409021e300103050a0b070302090411040509060102030304170a020c1f0207060e0d061a0301020a 76
    0x60580b00300c02d0800c000034100e544c000000344002c194400c01e1200c800c075807c280e00a0300c1007180c054008900581c031140046d0800c0c000360071000366401d000c1000080c0010801500030401c42c01d5030303400c010074204004c55021202c0200850214074054503c0c11030300e4820760441d050466810b008204c1c05182c1c5600428401000c1000e0303201d01707900100401e070300d25540129021980002e0a0a1a081c0303001762076406500464a8a00340031001001c41031911064402010510403001150b08040d00c441c1d10b01101e00100f82d10044180c030814014800200d000526510203500085945401d54074000120042d00c50b40380310320307007140c1454015038200ca4014007800684100304d501892540d6007200480c1d5900003128040c00b8003000d400010417000f0b91600130035404d815403041d034001c0020580403c801500300441d0034043c8a0450940c0aa95814070501014202620303207140038039105000105601c1480501074915a610f465005401e0015481c0e420403080113170081d503d82c2d8084101600050 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 65064310 1250 65063060 65063069
    0x50f030f0403090e15090603070f03080d050f0103030f0e0316060504080f060c03010324050c07140d0e1003060807060c0507090b0109120312090b0a20030601080705040308070804 78
    0x18040c00c0d01140c0d800d403e403030070740c8641d5074114040200705c4c0d244204014148060701c010b070140610b01c404642d120302941094055030081d094940d943e180e407184d40003111401010b581c03490324010014000298006242c0c00c0f210030520f41803803c0080c40b0006400c1110b07e802242e941c800344000001d520b0b8006004e0001c45a20702c06803002e402c202801c5079202d4078100c030400e411107800c000501c00110214004060600150301800d100c41b00c51a4443c102c50054401aa4000d00895090300300103030840794021246080d409000304179142035024190190410207103110b0b00c0c82000016000d44203902650090145000307c400996848001030040c4940c9d880c00d9032640103da40106c1d0590f25406a10795912042c5d40d0180018030f040c4c0001000d800d000d900b10b0412000c995002c01305080c6005180d40c2a000d03298031042410700400c4041190810110f0046500c1ca00c48200401ca020300d043e00e60100084c00c140c401641c804a08640c0d074030483d00b00419516012405605000c1d0b100003070070559 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 65065560 1250 65064310 65064317
    0xf09042a11031812120c0102031008010e0a02041a0303070f020102010e12031906080a0c090506010f090311040207021504080111090d03030b010905030a031101050f040c09050601050f030f0403 84
    0x60a014840a44920950429420042259009180b40e003091040313201d600c2540000d507503007034903900c100b464641c4c4000b061050a03074020051100700001c4c99100e000900307400c002000315510301c01001e500e07240c20b400064802c0713541c2c2101a10480303480d400741c0590f400c02403d8982e902400c5c50003041071088958281e006619041840840d104001146001000f440503914103580c1c4241044079004a402842c1000070786038800048c4040040040c0700d100d07442071a405c5400b81c2400da40c9000c0301c01c01010b050402035042541074040e5003144480301a01e80046480d000c1602c00c101250280c4107000000307400407983c0701201411002900600b007900c400b07400a22400c920f40e0165011806520b6007154410065a0090300090295204002069040c1040510140d40e100003030300b0300c100a0300640c0420000d03a00072420100030321410fa407003840740c00444e2107414251101d070f001c1901d0380240ca030f00d0796903940494110380c02681135549070110100000e94034640702c2500030a0400988044012 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 65066810 1250 65065560 65065577
    0x15050301180b0a02040f090504020a05040e0606030d0302191b0f080c010b09070e0f010e0303040f090e01020301030804120c0b2b0b09060d031101060e010501080115050f09042a 77
    0x150340e014002c0b038044814410546d45000d04010301003005200241080f46e12508a02d00003c0300d860701e0041005d8000314501414061420303c0a250401031f01c458803004141c4100044480050121500c5100301da443c03078804210300c1c8102040281d0000b8180180c00004440100c4c410000004024081d018a0400a000400700601407000b003813030a030340d403101049900c00d800c0c8075803c200280c0a445078052420f1103082c0900c1021904551194000c1d940c07948007080107200d601b409000e81750300d4040e548000c41c91980f40d51101d02183c0228045c900c40e002004048005101c4005400c10142002e91891640c031074a6507402d4400a01c506945c49802030308107041103144e0220303c503c001c0c10303102500e820701950b82c9004103c103036805810104d0a10144c10000f003034105091007100054402031207040c0340c1d541020005045000140d00c03490105a0541011510342c3d440000d4549150445810303d403a007110100040280090462552140041903024844c0f050300c0010b0300c8200305140c441105 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 65068060 1250 65066810 65066821
    0x110c0106060f0807090501080a0b090103030e03070509060d0b0903040b0c070504050f070c060e07080f01060303030b03030a020d050f09121f02040f0312020a0b0103060605030610030b0a15050301180b 87
    0x19403e8040b118030b8089001040700700195409200a41d030702018a0790005a43e00005000a0118200b80c205900103006650500300a003410804903001c0e00040385c00500c1e40c50720a0024500a0355018020070303010101e00420300c603040405c103640280c03101e1041e15490b2040300311a42d45d43d10700d43c4142d82c404d50514010034080040c80603018002c43d6030340d481d0f544461040e100d14000c0c159500c0201c14601c00c3c0103000818250500c020340c60030300b2010010600d02d1a40c1002400d0b6802c000c030292003a001041300051003500090f0303d00001c11079050260f1503510100486806014100c0e107a078110440c48020743c416240401d022504101e0100c121030310004135034002c0e049020341e01912007ca040340d4018004240e10301e0080c2c00004c1144104d41d403010746951031a048040a1b132044030001e48481c0240520314060004907444a6200d048000b814030319140c00711280380c060b040a1241c1c0d0784d60443c040c0c000d0030303080c1c040113060080c3c028402414040440100310480c28403d84854583e40003080 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 65069310 1250 65068060 65068067
    0x55030501080309010f02030d150e060a050d0b0901090206160303050f1306200c0f0c03010b060301030b0402030f1608100e060103030f0504090c080105010815150a03110c0106060f 78
    0x40c1a10000401141480c03e80c00040d5007440d100c06020082d80300a0001c54101000303405201601c94214400f00e5019103080345d00200341401400302441101010b805102c0c40d01c40000c283c044070b070041c1440c80d190319842c811500503e031150020b908020b001904035030082c0c4100b50405210702c40e44e001c000c03e550308a0200c4c071f04681a074001d100a40421800c2001c281507800c420031090340c40c0d9980c24412101d451110941c1d120160751015908062449800c0c0503090082c4046000d09030000d104c059032a4000400da4441404000e01a403402c00c0400d056403030421840300724082d10000c5031076081442c180e03409010403d204816041c400c00c44500070f00d01c01402501c880445507402003240c1c2c0d00b1a50b090303d00311243c049940402c8000d100000380061031b4002d00c200828a80c41d034401a50401c8001802008024900507a49242e98214812a15212401483c001390906800c0e245c1580110450103081e91380d85041050101090b202150755041d03208004842954803801020080104141e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 65070560 1250 65069310 65069321
    0x306100807020303070c14070801140109060e010905130501090602031008070503030a0f020a0c0b0a12090c030623010906331409091009051b5503 64
    0x7034005030010b0002c00e803880d00488001d41e01c141f08032405008550312082c0a440d00e032640d400203513240c0d144c500484281840b200f550340074007030448041c0702141c1080340c0002c2c803801c10b108100c6225907901c001170401132b401c850308501e1a8008002c4c001072320319007003a001a41060b0307852032041c0020000064200b400080050403100094040c6040c004003d03c2503c8441c4066000350550007884e2504e000502c60303210400152903040f10349900e070344542100400036824004030803001450680100c01040c02d086901c6c04490340b144000c01d036040007680d54000e02181d034507a00b00364486130b0b00215446a6a070062001d42d2210a2080900200301c81c43e02a0303080381882911071480860042c0e010300c1d12440d004400d03400b00ea04020b142c00c101c0d80200b41c1d1200704454802408049070010301c80c00c590303400780b640c100c2c54150b0820034120320202d00004512804d14004600c0302944e900381600c162600b01c0c2c03020000d066460105e0f101441c80400d0f440380c552200944804030b104c40810186029101e030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 65071810 1250 65070560 65070571
    0xd0609060b070312020705150108060912071e11060c01050f0906040c030303050c2106010201061502190c03050a080309010f06140108090703060f0f0e03070f0305130e070503061008 79
    0x40b19030301494089032400a6014039015140c0d0300616030310230f02074408402058001d209890040030149811a078082c2429082c1e9600c4c95501d50401040380070a1107084000c1401051084e880034a10b4280b034405180d501c1d403100240c00a07004100b0000c0e140c0c06511561103a400031078600035a51300d9036112a111542201c4c0140400e1800c0001c1c008288240c0c0030f5039001c414a580d1910380300050000ba01c000403408e084801003812002044202c0d6820f00842d0010440c112070414500c2c1e001c0710180d1074900c02001082a44943c01c01c4200380103a010542c402190083c003611200d20081c100b01c540781d84100c903401c01d19800c0a0503c540910240314a4044850380c1c1340ea4264581c0c580011a0045809400302c000c0b407250780130103c08504103120780051070f4948800080d101e050b503140101600c0802c00c06100035041404102e010032600c00c0103680c4542e05141140d40c032007071255040c4014409030001144d08000204000700203801c44000c5009010484000031000d141d00d1044a55240440d02d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 65073060 1250 65071810 65071817
    0x3040819050f070b0403030e150a0c0507020402042d080a1103010902090f06010905120304140303040b07030c03090b090a03080f070212060f0f150607030e060d0609060b0703 76
    0x500300942249a00603003919031036280c8107141c68400d007404181504a2202983da10314540700b44030803da0140b04810714504050040c1140460a001480c5030a0700213200012494480005a03010362091b0b007160342c103d074000c1086442d40d17140c4c101c2c0f901c0600f00d5412941440d50407201d200903007611204140407922104010030000c6003540d1540071031103078502202d4256481d00c02d0100180d0714242e103c1e2042c2c070a4a00400c5503d072202c001007500d8081d5106900030702c2110b502e22102030300401200c0070b44804403a80c1404a0b81800464035510499000b6410003801080c4282015800341600800c58060354802010740d8460f501e14949105844015604c0030700624200005032880014203400ba000c1c490340e43c100303070031900420409511058100d900b0781041041018240d00d01020703581200ca4002c0d0740801d858400c00389042260251801032140f1008101740f410503211350144003001202038503968075210481410701c0a48014040da44045040000116000c4039800030b8030b02c025007654 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 65074310 1250 65073060 65073067
    0x18090a1704030c060e210105220f0f0309030203031809070509030604060f0f060602010f05070306150503040c090e0105090706021204050f0d0c0305030d0e01090201050d0e16062102030408 82
    0x5005071640804081c1d151b400040000c1d40d40d032285250034102c0000003c410000c2230700d00e003e0a1030f6a5114150400b0204c00d41701480413400f258503084920443c591221038a54822200d003000e6600600c0c56000943c10b201c0000d0b10345240c040d41d5079500250f0400e9039580d15503161040107403094081c41009640540c03081d400603022450f186c000150700e81010000003210303800c50004c40305940c400e80080000d40e44644042c900d1089034807846900c40c4c0546000c211060814024a108000b05580107041080c00300125090000c11442035000b050310100c201301d501500911940a4281240c20040602565100088542c000b1030300070000d07200e40c8441ea01e0b207800c00e41003007040c1041200081d00303c01d0790b0b0031540000d8040c0c082d01001d940a98015030303c80200c044104207031064454520983c1e41003021980060740c110f4141c901e0080009404200814550161464110651096510190322a0703000400a800c500191802e060030002d00c801380d0800c986c0031050303100a903002010041c080 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 65075560 1250 65074310 65074319
    0x303021507120f06051f021b06040b0f090901030f02120d02190f0501090b04020a0801020703051b0a05010c0e0a060203040e0601050c030d0f0236090618090a1704030c 73
    0xba071180140401e42000020815243c1700032074951924600204010b20206509490854041003c040b504680d2442180d800c04000c2c00b14010f030083d8403414610000c0030440100c009075030010f450b8410806400f41341c15680d203041100120010800590155041c00040710030f407070020590340344510342078000b010080700c0c68441014080015505a80e1181d00c0e06c000d41c00110280944040705009400010b012b003000e00401c25042090790008a090b81b041050328000317908402030b50300e202c1c00c002c0b001c030143c0c0f492510b007402d2980e4040010300e154a0519a1192580c000c11000d681c7c40c030544e100c0301c181c1c3c0c030b5a1050f6503074811405242d8030344006400203a0039601c218028a0700c140e420058030f080410a03111603069a0307114040c494510740200f00040545000416603c040ca85605030b0703840e0882103400407400c3e00b0100312aa000d041c0110006400e030715442c16018501d480140c039041a458102241510384c0c0190200721010039110700c01c03c012042820544045d0303600f002c0070003407486c580b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 65076810 1250 65075560 65075597
    0x2030307022107050102030906060103151508060d140604060c0903051e01060308030702060a0f0c17060307050d030503060f0409021513050603150406050307060c06020702030a050303100303021507 86
    0x30b49928040b6818100445000200203002543c010304c494001443d050a249001405841000e00301103031171155848108120f20014100c1c01103007200e8100404d03951070300c0300481c1101d001104041e140c444940400c0c070012800042c600d10842c000c5408000c00f20200c2070454400b040740c1300181c25940320040e5064a44d0800107400c1c007503051000002481e50750380c0d4a400705170700100c80c0344e000b41e0031590401800c1d82180c0984035010300d1b00c8104000b403041807100035000b000303c103071241e814654110001d046a202040040e0280000030940303a103501941c50f00800c0c5078000c0710310900401c00548501d50500b8280a901d50341a03004005008468000da211a115004549615a040341ea20780c005440d0b201c50300154041ca80c1c040d0101c0420050b0300c24031040d0b0303000b9400f5500071340c0a90070401041d948882c3c086a5141e101030050703991051800000c0c41e10f11100ca01810310700001040c00603c544ca01d00500880307101e03400f0745984102d6003015010b036001c01c1fa12800841e05084003503061070712 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 65078060 1250 65076810 65076853
    0x100b0a03020c0123040b09031c0506040e030316091401170c071704150801240507020907091502030405030309090a090b181b0a09092307090c0203030702 67
    0x2030380000410685100807859034040d500044c4100d18640d10501040c82a054003003517200300520001d42c80e2a41548411003000501030180803039503640c20200d2026511500f1004000d2401c0c01265204c0c04d002e6108c540220088190401003800d0520000d15409048100403550708161103440054081483d1001c1880000300b42c641c0c0d00900300580c1c1c001414010040c1e549401caa100f030b0f0340300c42c100000c000d076403114103599800b8002c0c49001002015070108150000b411807090891041020b20f20696542c0145200250322a00b00c0c2c04000700b56600041440803201c2e8100c10800e161038290050380c50b840740f07000f8150581c00410661070304d81013030380085800142d000800103044201d52034216207001c0c291401c0b6010a00d240d018039688200300311780c198003a00c4002d0422105180030010b10090501c1c03040703604168030380b4580014014055201ca1801c110a4842d03040700e002d512041b87c075514180155116145070960703034610a032000042c2c07481581032303800800411011455140d0180c4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 65079310 1250 65078060 65078077
    0xb090417070c06030b100201020c060613060e0f0403091502072303010c030e07081605090403030b030f280221010216060f05090a030203040e0c13030503030708100b0a0302 75
    0x11401c01211001400800118000b409195800651444000304204100116030400c4045a006021082c0b01706400b0860b5038200b03030216494a19070200c000098040c1040e544503102007648101040110f049010089202c0e030301c2135640038080c585031100f60f070050110129103001030384540d50611100d200210002c94901c0054807400750b041c05800020301b90350300c0c2109440042c0c1c681800741c49008042004c8400f030044c03640682000079100c0340092000e812072007914440d041000103d018180264080c1d1520b07200602921003070059106a540c0c1c58002120312400030140b0320b244a4110300b00b44981002503802050300d40280302c6c087d070040a014406899000c155804c12003614040c030303070b8002c1c04142407254002040000c44441c0d40c0c4210350b00100201d40c5600a54401e400195000c81101c0c19613400d03e42650311600c44400800d0039010301d081808481d00302203030200a21a0020280d8429040c6948280d003982d1910f041c1c010041c0070340301d0603a00401c140081c3c6070440c040e0f00030301001d5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 65080560 1250 65079310 65079353
    0x2031204060206010e1012061505040c020c0105030a020d110307020d170a02070512042c040b040206070314030705030a050703060f0603110906031f09020702100309030512010b04060e03010b0904 85
    0x2a220800011a0251020100c80031f9a2700c1c0b840058080c1011202c01c020941200c040041012401c0045d4440c0354055481d81000000000030b01d80d04101d90585441c9010301c00c04101c640705401c0050f4035079009481000240c4600d03840c4041c001d201d070343c103240020310b01c107860241a01c0f140982c4019400c02d60084400b4018580c0400d1840b00d810094002400b541c1d0b040011300120403140c2400c012004200301094400004100106240701c00030b6402c5941603c0300c5540d034509040c01c4543e14401210f95041c51000011301006992240186004101c1c1c500c0c10486512145000d5040715900e200d640c180c078269a10801c5041d009904c403203050083d07100034528207400710340001d5855104481c504801584504544103c070010342d407000140c1060841140b0f0481e041e00014050840c0c01e4001003055142d05c1808101072051007664022f5201030500392065071a10b1090101e60001d006000c00103c40142000040c54140074040300007802625118942c2c40e01d840790310800e1801e8014102d038 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 65081810 1250 65080560 65080591
    0x41e020d1406062403070c020a171501061818020c010e2404030507120302160302010603122618070602030a0f1403060f010201110706050402031204060206010e 70
    0x108201408981d181c2105001804071031800c40c0810045034030071015203180603107258502c2c1081c10080100ca41261145c02c1150700c1d091203100285a01e019074210308203000c0c2c0c8185401d507203000000c0d00b81c0d040e0000b54007107802da0f03202c41d0111505080c88100a00e42228800c0c1001059000c40ca400d20f200c101100240c9811401d000e0741d402c0d541c51901e01c51055110a50707a400080200000c104c690721108800a2a41491381340203080d8015981c0c06010403907001843c0d00b08034043d038116407505080040b00c0d48480c401d070401034000d290b0b9110a4510380040e1b200754400724031640284401c1141500107012600c07062030500d0411034000c0440b0903809080c2407200034407400708400002410147d00840d035880549000a04800d44e0748600320902034500c2c42000c46100800c10781e50b0001d002d07982e00005051510040b40946641101c05043d0344000032600c080c007141d0303001584594026411a140001038080fa11401c4c03040303119400040c1c0000c40180410842410420381140d0200b03103007030a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 65083060 1250 65081810 65081813
    0x9100903030b0406080703060f020a0f03020c0304030c2403110f0c12040f060f020a110d0c05130204050319050c011b080d06090b040c05040b1e0408030901020f0303041e020d 76
    0x22104d85802483c07140c1d10024040003080124000d0300850b460760041075081c01c0720720802404400c0d220130740000f4541c000c6a041400141041030f100159004000c0080c4039580741c446250301c1044286103418441424090f00c0c2d2540a402080141d001500368140740002429000c0700ca9003191300c80303103424007a014040c00140c0e41c5802403c00307810000c0c044160b00c4d02d880d002502019004c0b0a80c3d056402100305540030400301e18003403680c410141e42e440d8104c089490401100d0802d03812003580f1407100c0c242c0480140007a805402544d5065003120300a0f290010010301100d40c1010042c8658080031903244154030819041e07d25600ea20310a16540d0041e5075901c00c1504002c40d002440c60740c408082100d03d1480c0111030401c8000c0d101081601c000500c000d003103105078055640c860b440010000044a44c294521140c41e0250255544458503142c070706460b9031000c1030b514014450b002807800f20190101c00c60707001d5031b44000301e0441d50f1056044240c0c00300001800740ea0024a0440341d80 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 65084310 1250 65083060 65083069
    0x91403150106050c06011e03080f0912010218031b06130905071812020907110304050a0f0608010509010f09110909070f021234050d02030319020309100903030b 70
    0x14080c05a0352078080d01c075011540913030f140110580c041804990001010760b1010b2682902c42d05580d001140c280d514156480000a039104103603d664206200004d04580f41c20190b002e07100004108901c040303a02000c404140e0303100c03000030302c41c5c0e040d04900b28104140d103010030060000021081d0501215682c036458002140c008980e410f0124020348207040c036402d441019280644007407507005e00014015000b040380c989000f000542401080355a07030242e10010829600103201c014101c0c14200e1303c8001189110300c0d903101d041c0101c2c06e401c0011070300b443d044804906aa03d02a000d604c210301c0d00302404007400b0704192410280804028900b00c5840704003483e44241015125070191443d0160700900c1c058143e010003690802c148441d84100c950500c615044072990080d80d480007640d04110084c516142400510b14810742c11510907032900030015610030903070140708000c041140001c2c0c4080c0e100840303041e1a5500319800c440a90b80781680240d0115000345400550741e021200440c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 65085560 1250 65084310 65084353
    0x6040e0a02060403060204150807020307020907020708160801050601030902030a11040902040e1506040e0304090e030c0102030403080114030d050f1e0309011a0402090d0b09013908040201091403 85
    0x3a617280b60002001e20072006c044050200c42d00c45440c0c15803103403914002c0203481e4042c0400080c401c0c0035510220300046d10070011a400340251905540c200c503804c1c418000700315800c0c41440c5995003444000727100c540c02841050045c42c2c026029107000c055503a14101c09a900c200c0c02079000c2c3e62400c0c00c502688484c4944162400760314014184980d0304206400400c4006281a00c260b00702986d1012402c404400c0c0d070100c400340d05001c05d1000480546030300f540180e001c03030003a561021003000309040d8002c05160491350340280e444050003140c0705240d11003007ea45900c0220384100000700381d184521009141d9803400e000201118140d004040007140c1c416508644607030b445801094030308880c18030250902c0b408450071440d00b004080490301080c41020054103081d0200001040140203410078002d8014401080c0d94585100f41e1280d42040c034956a864442d0507041041c0c0b0709405283d02d58007580d0140c6031000550300d401c0c0004402c0f43c000c0381c40c0b03401d4002c2240480d01d114905031003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 65086810 1250 65085560 65085563
    0xf07030204091805010e01090206090d0303021606090b100501050a080c09030a0c090f0b03060703090203150703060f0e15040509160f030209060a030f03052812150e06040e0a02060403 80
    0x141c0031a01c00fa04144d42944d2001d18041000c0e407602135a840141e07143ca00f00d0300d0440040c1c030401952001414242d0084c0150310210092101d40d0224008002c40f95000f41141c80c40760b002c000c03c603105c0482c05030040c1214000e00340400c600f0000200b6540c0036071100c9500040e4200010714101c25200443d042140c0d207101150340c0c8616100c1440ba0494501402c8814481380d5802c0180440060000b952500301600c034006043c0e0b100191000e5440074460740204600001c0c0740b0501e402c04480080c01424503104450090308414004503030032100c4180b5078010350141c0003c0310301201c40002c10000f4400900852541d00c03800c03506110620300350301007100803c2408a43d161440c650b0040c0b041c04807008203070030b2251044200900014107107d554001031601441e0031a190705131600e518101554000981800306240030f4144140ca81c09843d0014180a20310709026035241c0e5800b0f011100b43c54010040304030110400038000b828181d200d044440c08071803c495041c16190007045455009800 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 65088060 1250 65086810 65086841
    0x170615040605131407030209011d2409030607080f0f07050903070e0114040603080a1d04052d06150f070c0e1608040f0f1401020f0a0905040903080f0703020409 70
    0x1041c0f01481c4c1c1c0054181d0384505182420b62030000c1180000b481c1050b5055814140ca80301c0703207500d8454031341a00c1c108150f01228011480202c41002c80c610b40d40041a0041c420f00c030340400200114840e00c012405070300b6800080c0c009485699540c0090030004085504010701441644030503513081018100401c01080055001e50500181113012402c050b1464011070802108000003075204049800c840031070300d007081018a82464003882c40d55410000b543c00b9003030405002555424014014101e1072401c00444441d03101c910700c2400ca18120b0311513a01c142e440c03098041001904d40101201180341941510b45045952000d18800b8070b50040c00d01c80900c50104001118601e01100c8000000d041c54001450300f42e440760114121000c000782542100030340c0310b00b0800c1090004804801400c029501c4400006206480b0340002a00f0300000380906000684e40c10280308034000540c2507031301c0764440c1c0e481c01d040c010b4201c03028100008056081200054402e014414504d0341c6d001d042 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 65089310 1250 65088060 65088071
    0x20d050d0908010b0603010b0f030c040302130c0f110304050f03030903012a140a0c060b0a0b09130b030a0602090d050109030216140f01030b0301060b04120203060117061504060513 79
    0x201c682c2111368106900d402200301b003006200b01c114020a88030101550542542e51f640d4803c865010790240e94402908030300415100740c00b030506c03a0442541c080709507555550b140c0c4d840c0d000700ca10000c4c2d801075075200d40040006100c1e0303003400c2c0f82c00300407218042d00f224980404400843d0071980074044007205a0a0701d5040741c402141106424110740072031a10100040a4480001462141d06100020303c10000c9409042180541100b15007410082c8051456503440c44564070703e52080c0809445000d8a00c2c030740300114664480c050303074000f01500034400300200340e5801c4001d512403050f460303102034143c0d0454001002401a07c1c4550300c80d5000e4440ba000c0c4184000303050125070000ca5461101000710b070003071344071041100c88400091801083c03e124040100c1e0040c140c0b50404e1054420000e400704001d41186d20380da001724070070f404844d09613980b6544140c6000d10070140c400507811600105450000da05581800351034010800035040d0f65900001d0001403030240030610080c0c0302c5 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 65090560 1250 65089310 65089319
    0x3030f1e05090f06070504050904020d0206130609060c0506061507020604090902090705040e070f0302040f08010914010b0904030c0206040504060e060301050a05090a0303020c03090a0b071103031204080304020d050d09 95
    0x43c0001e000e0f0451400080140e8204190050b0441c0070703e00403540240d44080004040d07503034013510301400a401900b80d07560341c0407010724640900c0040c0940e03000705000c40e50020314244100c0c60468611780043c01b0344030a485140800c0b20041a40e40310214040c000d005080250360b5008c000c000810380a06c001901e00a140705100d50000c008019005106050004103e000c65944000e54403c44a160502c0940104c2c54141c00038080c0c5c1c0c00c240c410850320600840c2c14541580003004450140e07600707540b8002c0081c226400d07265020801d0341c10110250200b00040e004500c030f441068802001c450a0a4403080410210790095100503902e91015090002608080c812035401c031041c0c0200303000d41d16007000b000c0d540e178a00400080030140c1c0011040c810a200380182d451088008120b040b003a69104040a00c0d13401120081d6801500300c035200c0e8541c5070000072916410340c00301c48500140d0302c0c2d032110102c42d000100306a8010a91880400000e030044c8091940701180703460340d18541c1c0c01c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 65091810 1250 65090560 65090563
    0x70f0801050601090e01090207030216080705011209030905060c0c0411091c03091806030209010b030601140a0912050a0515160504140d0201111515030c010c03030f1e0509 75
    0x1920392414003106070400d204240c50340e00417074152001200c0c050380d290020300c0c08a01c3d08140240e1444003010303085012030401408560032003120741c243d80700d40c1d50503001e4454504490000324010045016110304200904280c2e02818031066004140c2c0e61400c103e00c04281603641c03801115003080130000740e0040b00c1c80d11010030119840d00c0000b400035001182d401a00408081c040c24142c0031007124007040541050b08040007071540502148010750b500d009140c4650000d54625003c9009042c2440b14094071200340c0b914401e80e903075840c5040d0314200138103001e48030b0800107584274010410074101098003001540c001e0b1a0b14030922503149130100251038050700c003191b40410450104002c002840c81d00c440c0d0150407504480c517907c10783c254401a00ca040d04a005081c1600512122910640c04082c4032417103802c02c4000d090151151404040d00d5852010500740801e0b10552880b011912a50142e284200700010004401a4201d06920640c4c0e2040e030303842400c0d4480d810001e40010 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 65093060 1250 65091810 65091821
    0x411090c09090403050313020d1a0f0708010303080a11130915060504090b0f030a060f150303020307150609090804030204060b0703120c0507080d1a10020717010608070f0801 76
    0x80003804a040200041c0003448640000c0d001030100280400480c2d02d0504201041140b1540180300c40120710040c9007084a1520080c10701d075a0904413070004003180e42a6880910514003640c9003200341e800d6950a1341c0800000d000014600e43c0c812440803000358650041201d4180d590f8003181d594644503200e01510344960b41d502a18501440070000c0c603402505a4080d50806038000c105010780001056441101046c107075450302c10844190180301965005000f4038000380024080e007100704408840102c800e101c0100181c1c0100142400301c2d0840c0d0081d441c2018000001c07900c0d5994803400c40c00d5500480c1c0030b844038900000c08100b140303014440c54004215003681d203800d114050714060041119580c0c00f01c041340d2140b40384020180324208554840341d02202054551410901d90b80003000c250341546c40402c90808004800c1c5094140118040031550041c81124180540901c443d80290b9a01d01c4541d2110310118a4010501580700640220900034a107103140103485425a076 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 65094310 1250 65093060 65093071
    0x90108030c030a0309140303010608040b0c0304120318050f030d0f060806010b0a02030415050c0d0306080303150f1c050601150c020603150405010902040f080303061008060a08010203041109 83
    0x18001c200c4409041804020b40782240094200000c24a865082c640000c1c4498007004c289400b00100101d00c00380c024407400d015a00406500b83c45513030306400d15040744002d071001b50480a040301001311592080d001401040c2600000c0e285035907050f5569483d260303100708500c0c640c2d000880c080070206124400c20a800c0700403001405840d103061040c50322010180039543c019040060740110030380c001c01c00c6800074030004c000380042d010243d0006010740c00c480d01700c07042da00446480100d00c83c0709018143c16144200069880d540700c0c035568000041c002030845400008a0070310100d60b98811380c208a40d504038035103e0208450f070b880d10f50300301001600914040340e20042e00d100c105502200800959034152541e03980d80e1525060b0b00b518240800d4595489400c00b80042022502d9030080c108494440352203e18850300c500c1c00c2c0e9203a00040f100640c0114444401481c120310812005800c030402034404000d20740c0702d0900909a81c0300b00e03025180108001400ca109086c1003101c0741c0e119 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 65095560 1250 65094310 65094313
    0xc050912071238040c05010e01020c090a06090f0f0e1219030b0301180c05031b1e1002030306010f050712180b16050c0406150507060b04020705010b090108 68
    0x9800c061810b05103004520001d007016074616018401d9081100c0200b014280c038401c1034400c203030440b103941d0120004841c102c440c5002100005419405a140e40022900c160003800c11340329582c05019030088020303d407285140e280c003000904402d4500c1b40801018074017001041043c0720803a0842602c0c400403802c4401d6010549400180d0300d00c40a80b403032501c2c1e0505000445002200480182a5040300b065041d403030200030307040c01500c04030209400d41c411981020031603620400c0644800202000c0c2d60104a0701001c01c0c8186420300711000040b00241109c00401e4074030020070000d000301030700000581d000109100c000d68003c05a41c5c64589c491030890300d0700c034041e601c01c0c1d82c041030b002010040c0070034401000e00700b00d20700c0f00e04000380000c2e03004192119840c25141008200083c01035440f4007449102802034103081c010101501e03940394184024046111045465034868803041e00e40701e85e0341c0301c01d07006507895000405055016600114140004204200d2105410fa00035a250f = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 65096810 1250 65095560 65095573
    0x8030a110403021e01020309100816050c0a0305070f1212141504020a020109170d05130302031204240b090702010e1b0a030602030106051e0f0403081605010c050912 72
    0x40e40c83c000f24402154000c0c000904e00912480180d1035070007001c0701654401540c10110b2221070b4010071303141c403032141040100100d224141d000c0d142d91051961a00d41c60f0000581403001ca4080c8000709440351003148a92400b03040d9807038100c0d102c101c46860400040200c0a0045402d00d28065442c844d880542804800d051001700d0366840030740005020b00690700841c81e900402e0007940003e02107a089110071001c002c1078000d50f416580310a0622184501c4c04d40458404000a5035200f120b65242c1c0045183c00c803604d18078645060010401c950b0141802c0101c104e030703024001c900140060078100407034400417401c00c0000c0703076070010003071001c580c54032090710508036000a83e05903103146520354441c0080c00c2c0303021450200709500007504860000000161650f030107801091182c0d80500740f40c040c000c5e02c0d40510b84512820030b00024141c2c0a21051021403000301c010910246128241c80e10070031544e4645082d556440380d180081880403814041034241084000c480e91a244d014104 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 65098060 1250 65096810 65096813
    0x301051009060e040504050f0708011506020a05030d3903050906060f041104031703040c050604031208070c0609060902030c040209030a150b121b0108090d0f030b040908030a110403 79
    0xb0144a44030f2091080b0344031030100e410f026060145083c480c0c0603400303480c1d5050304c80003c54040d007166032040d8070700c404400c6c0011310f41d440811410303178180e80800514609a64103034104098401c01000f603035080d090b00c0c541c0b000358006c4083e007503030104030002074a0742a80b01280030b4101c2d1401020307150190840002c22590340d583e60381c0282d81180440340001c080003201e0f20404180141e810040a1161021b0000c001040713074000345d0b201e140f1901c1d00d00280303501d45050220502883c17200402d030695503280000d10b240588040c0340c0c481100d207004d001c964140d444002c10780352466003e0750b4650b5100c401d2420340c00c0900c20351032030110079201985007102050100380e81d2034030003c0c0500300c5c01c1d0b5032466903180d5205411440d00c07080c0c02003800f0700c011750b403030b11140d01c0d00320145036150400e4406082c3c050b0755001d0041d8610504040e4060180703018440c50544011010350344806c101990741d283e0b540a9560b074400c1c3c840c0b4601032509a502da1511140d01c60482d0a0300c0e0941c0c0c154441031000300b0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 65099310 1250 65098060 65098067
    0x6050901020c210703030e0307060c03051629100f0510050f0d0504120f0206040f02120a02060c031b030403020306061c0501020324010f1e0c17030105100906 69
    0x1442c0c0c14041c0c4403404100401545240041c4941102503418007541d0b0f000028181c0c051843c001408048055400b000d9454805640c03110100c0c800a0126405211100b07090012400c10708002d4091100d80c40c0c44040720709018442c0c1c107440c9118181b06408004c0c86003015000c02e0200141034403829450701c00b400c1c040000c49000100b0404004c01800040c042c3c0c10b07910084c15201094210401031000f400d1a203404100e0035101611400040e450080741d028503480010000d00541d080000b82c031a00c4066024000c03040c0300306c501d40c0504d10072140c6603030060301c40030018040144103030b0182d5214007035603100c0704601084580a82c401d90050105101681c1c000c29016001a03080f07841055114951402e02840669160b028006501c080100300c445040112071501900d010186445d0940d111401911918105000c9000103058000545088400045000140403050420044400342035442c04102424200c1c2c1c2c0045c0140400104600e00742002c1c0700b00c44108a0038a00c05160070710324000d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 65100560 1250 65099310 65099323
    0x4121214060409050709020a03090201120b061b031e0301060306060216171207050c0f180103030503070507050304030615050d05030a0305101707031106120c070c1d04020a0605090102 80
    0x1d07110302d6a0b10285800c003d004c0055030000c28040c0c20554030b400c4000c0e8047d00030854504180e000c01c2c4c500700754405c54407062060350680c0740000c100c0c900704030344458118110521105821103030301c4100b10520803401e640781d41d00f040b91a00702807180d50350304182c07005080c0c50981c1c0c0220103551003a00e000640828807003032207003954410b5801cac13101e4030b80858240c0d1900d030f921540007403d010002120310504c4000b00701e0025400c0c05031540070800c00c50005000c104002c000492400519020060001074810b20007541c2040007494101e042c071215403149070071a849503104039a901c1d5a904850022287d400c0c1d143d00500c4200c841d4044002c203034650989a1044113164010542e4607400a42c84a02c685e048501820a00f001410b00c001201e41032542c8500e540800e584c6019845284001c61604404880260114600c550000c0e00c0380380100368039130000c810403034120702d0042c80400e10700c03241d6111481c2e44110742004180b13424240180010f83d1040d421050070001c0030016000301d80d0300003c80 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 65101810 1250 65100560 65100571
    0x5030c040203040512030c04030501050f0601021005040302070f0e0402241605070e0a020c1b01050702011808011401030b1509060f01020a050d020102180906030a080d06050904121214 80
    0x541d4943e1245400c50030802100f08003601014040148074007000c1c0580038100340d074441c00c002c00980e102c1480c056401502210004c0c0140d01c41d0301d111f004804c0036080b1540051183c01111078894070340003100003070401900440000314901d820002903240010f040c1702c0390040c00c0f601e041c902c0010110b481161081c4100f28000901003000002041001c00c100c100401880002c540ba034180604804c02940c41902c3c140003900c1001007043c000000d4050581000704142c480528000440c1c2c01500c2244c0b00240c0d1081440100703078001101e00c2c0038003c01000c0c54604072a101c0542c11880c0c0f4905881011b000007107036400e032944841d42d80d281c41c3c010f0368103d00211900314019440341e0040f440c0c5028146d00130300b1402407803075000500e5015006400c10040f4184085401820b00f42403040320b0b00d04546150b4158031007006100446e1114006100d038002c4d840011a1407500c41d00821009082034500311007003950808100c030202d034000785a00c00c2d032070814014808070600c200c3e0580b280f04094038 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 65103060 1250 65101810 65101819
    0xf0308070f06090b01090b01092709060e0a020109120f020d060b131e0504080d0509030d0c020c0a0b1201060806010c05010e250e04150605130501030c050a05030c 71
    0x242101841403004010841e030758000018091140c191034080d8942e0b100f84151150b05040941c550703103940c014001081910300b407041005411401003d894200041d8001305a4510303602e0048802189440c050002d004004800912020549200040402c10598071020780181170500b41000500c442558020305a0102c5c0c401c03492914071700708000101300030f844007580510540351010311000c0ca9004002008105291620344031140d051080c156002150700410501d01000007200c45112503200580010f000c5044a04094418074801d04544030a6504005a40014440d0b003a52400000d58805801700303400c0d543c2414130310300e000c0740e00c4181802440140103009002600c0c50b48110052030600b41c0020081c886100280d00c001c1d20380d4070304210f4407200c010441c0e0000d928030103240316404a81481d102e0b14800d60307464540d03500b42e83d83d594800080c1c64644e2000141c558a241042040e0034208100241039451841c01c3e03a65072a01d0360150f401031508000400071590003041e1100302590596 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 65104310 1250 65103060 65103067
    0x1401050a050a03052e080c030a050307120207030c0b120a09050a0201080703020c011e180201020a240c120b040605011b02150a0c030e090c0409021b01050a0c080c040f0308 75
    0xd03040400b00c620b1240d1035114007000509107807990f04034540d1703c01315801c02040d600c0025a9000b455125400404003510b294070402c000c0c3e000032107040c41d0001d01c540340d10548030002d407640d4415102080c10f0b446452040b2001c0383c9040400c410141351900304a00e07100801104500d076540c07949400c032030030000e81801401c0e00000c1c0128001d804542900754640000c002c90000c01c19903080350328264441078800c41c900600f00340001c500301112980960160018441404241e880740381040403006d001074843c01001ca0310400200074040c0c4c40003156283c44600858080c6151321301140ca81c4003456101e01c0c1400020441039800c04006d00004040d1401400d002c42c0d10b0010900348807a00106400030040010388807580c40d4025034207840188a0b40d01c16010310160410410781d150240d600d1140700900708420050000254024a44e078800401140c6800a401000900b11001216891811511010581c64895002c03003510360080345041c1c0c150405040c003100d1400c80380b90340402059100d000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 65105560 1250 65104310 65104321
    0x302010c0816060c02010e1603050c09090f070f240509150906031006110d020601050d0510060f090e030313020d03120906060312030509060f06010c08131401050a050a0305 75
    0xb85140ca0150884010300000d5100d02c4024000c19401e0407008450203102c21244218040404a000301c940020040c540c401d8607004001d110b00300908082c8040c41241c0300c0ca0b40c03980e4144903810040c102905084e160918080d88107a4166500d60729144c0102c121340341002458008099030804041900c100e001c01d80a6160300e81c5503c1007440300d0380e100078007008100c100101d140f98101035030f4040c2e4842200b01034a00080d5610f00f614140c0d42c2c050f170820740042c08181003d1808084a42c01841243d001c42d900c84412000c0303c0680c0c01805000801f0300301070081c10280d005529030007049100541c910b1a2840c90042c00c11100c010007881030101200b044103062040398510722640010904218a13030b40c0e4a40f034401000039101c00c5800500c0d0b206210401d0b4001c0c400c1364851824980601001d541d4641ea1498500d8001e010300e05111800d2242808202007001800d82402c5040c260080c0c2810510803851141c5c8403c03080d81003110070400400d0340e9038004159464a08142004501c0c0c2e16003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 65106810 1250 65105560 65105587
    0xe01090b1215060d020a08030306030c0a030b01050402130506030403090302010806030a020109141527040e0d0305181212010e04020105040303030203070314040302030a0306090b0a030b06030708030c0a050c09010302010c08 97
    0x2404c01a6005401e10030105001102000450184070110b0895269070300780c1061004104c09488050301d44c100b00e1004002c60f040c203800401c21240340802c030040c81e03516040081c074140c04c181d909400140c80d0340307001d00071540c0204d50716810040c114001c01e00910240d0009200391198065661006410744649805454041079450028060600c136600c03880d400c20600b03400c40e441b010200c02046055180c43c0c071400d007849400a00c090084c05090740c0c03403c1a90590280c60050480000100229000507041c1400e000c030b8403460f0318840da00f070350702d5141c0d50076118a410b06070040d0103040c14007000c2c000180e8014007214100c961608001d41c4070707901c100c0c0640060101c5000d03440c0c025100020402056070120040c41c0d111505e8408012440d182c0708003c2c02c03a40043d40c065000b042c900030601c0070400810446520150050032210404d444100c2282583c00c222041e61260740400070390750400200303004580c0c0a440c19103405400350324540009010940d14400500314007000556005583c00 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 65107916 1106 65106810 65106829
    0x190f0216060801060c05071806060e0906091f0f0b03010305010f0b030c040905030d0903030e0d081501030c03180305040617040f0605100f0e01090b121506 68
    0x4c0820030b98505540c410141c0701031280d50400190901c40507a0425452440ea4000c03400b5450000c019000d811070454603480360340140200850b90710740d404020b03070003c810160225507403290542d42c0c05035a107039045941e0036580d0762004203059050308020740c122842440204804031009007070204940100d100258103800542c00581c2070710302900000c110a0042c001d80b40381550b0300d001c000485803199001ca012a80741c0c0000c88004900b401503c043c01001e0500010b1890702000140c0714a8401003158141540d40e10300146491003a070000e040c1d41000c001d05000e610f05410041c09030340281c8503110014003943e000d1410041003640d000d0103158050f200b62425082981c440f000380200070200a20040150f5002400400b801000c10041407440d001041d194180381c89142912340b201e04260003441c52000f01c0950010006146142d4024000c2503412515940e00007494001c = true := by decide +kernel

theorem cover : BRFrame.Cov 64928060 65107916 := by
  have h0 := BRFrame.cov_init 64928060
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64928060 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 64928060 ≤ n) (h2 : n < 65107916) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
