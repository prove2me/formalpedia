-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2859
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:57:39.814784+00:00
-- url     : https://prove2.me/submissions/f27e58ca-967c-4f7b-a28a-b03478229124

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 514028776 ≤ n < 514208633 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 514030026 1250 514028776 514028783
    0x325030203040b010e13021003020418060e09030403110d0c080105090f060c09060d0c0c140a020102160b03060121020c0c0f0103050103120305060d17070b100b07032712 74
    0x48001309045c8101301c442c0c2c0c410b0381d6080008000d19020703020320201181500d462800c0540804c4045113200903c2060000b91a80800000703415150004d07141c205000602245040d4008110070404038048140180b480041143c41c021100410301c1d003201a040b65078442d079000d509040c03c2080894022070b03111640704441d021b5a030307107039282020b0f82481e1143d4058150321a0302030111000e0b480b90355000f400308840d6428071000e0255144c8420480c182218004c0d01598003a50100c82196818044100d007264a1444810540e0414910000300c0c04001c01072410818041c004204c4221002c48910024100342c100315603c50792010700c1505c1d0b070303101071503603000b00441d406081195100e880703254100c0390031040311403401c60700c440114041d0030060b0032143e21812170060b5501003088200091031400a058040d584c4000d18500321005540081c40b103c0c1200c807040f01000081200700499450560515185c0105540c83c802c02c4411041d1309040403d4214124010400c03041d9003070354040d120300 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 514031276 1250 514030026 514030043
    0x81c0e09070e041a151b03070c080f0601060e040c03200a140c0703020d0f05060703020408010c03150b161202031e04060e220c350c032503020304 64
    0x140c6082640c0e2134044000398104000c5660361140c4c01880018220b40000c1005601e54500f805c07103414516001060280d4050b05a81c10030001030200301704020340286031002800c91503243c000040c0034505142c801c68000c6446d26280c48200d1301c00d910007426140c10400243e400c0041e0180c148241c2c000c0700d41040414000010b0034164804942901e044200300402050040e08543c00c0c8101c0d240900d01c02c4030301d0301740f440390a03000440c107201051181181da03500603240c620700000c40d82558104040d01c1c050600d440f901c51112511010414180c442c0c0e001220b581e1400d11256141140003a8405442e071244600d60003000e46d804001000ca50f84880400f0040b42020030002071140704520540011900f91405a28a800c0c030710040c8824132040c241407103800c01043c0200b001d82d00c0041c0c2e510001003803070b0031601d81c00000300715148060300c0725008044403020107602020403942c0a030807141e40b045c010002900f607602804802c8401075880c45204d00c07000c20030f0b4024020750020b40d01203070b0544c2d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 514032526 1250 514031276 514031291
    0x409060b03011b1d09040f150f1b17071803021801030215040f090c03090f0c06080a0213170a02060706060617070509120c0a030c031a01081c0e09070e04 67
    0xd002d46841443d8000043c06030b091a00c5566902c41d0416101ea01210b2008d95281a556821a00d1040b85c007034580d45080405c08405110b02209812025000002440400c00b48044010460b46403258440c2a9061180d0115884c00013071000541c00e9200075400b0141042400241b5800c0d83c0c490b04880c800e0780c280c0d8400350300c41050001c5010b0b60207400d003504040e07070081015a070260004030502d086c030706000481801319240c032080511100d105980301c0c40403490400440340d000c209142d008020180440c02e041c200d0fa425501e1f8412441030741a03441d616462240c0b81c2c4000e10024801d2a8020b0289640b02018a0107002034100e9100300c10206542a404000103414079200c980b04080c6642d9080c40c0410b80b908210070041004908075591054072103e0166440b079034800c5014501401c1c4103e2854070f140350100708003880911280e00004611b00400038104002500c03001c641c50b10b851400b030804417520803502809070002480c1e21418a02c21301914603044041c441740501c0a0303c084c040381 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 514033776 1250 514032526 514032557
    0x50d2706020c0705122a15030907090b0a09090c050d0c080d02070608010b070f0b0a1a270705281b050606060c010908071202061003020d020409060b03011b 68
    0xd40040403075003100d400070444240c0c1d1020314a00c0501c01720343c1c0d01c82c0c0300d00c142c0f201012034941b187d045a0020724280000510a42c40010003588004101826007409190704007004600c645001e44107101c400c0d61101c00400030000b4a0f1990301c050000174110700300100060034a040d030441e16211348070780381c0610910904014400709006d000d40d00070f034451508a07443c12003079450550080e4020b48010502c020b11f41d00050f554207406000c4c000700007000c540704c541c10480a090701e00d0f22164505c2008584003c18594500c0c0680121400305640050800d0703860506c246c1d03084c4503042c02c140594030b2001c510030400e14014004102d0f4511a500c440c00c0d1b000302e00207035640100c106406007099003e10001843c1c0e181070700080002c1c1c1e04a0002090f1134401e541c84019a82185a08070b645105000c4c140c03100d40e07410400141e1282ca04541188198074580101d0b40c0b00c050034101074012915000e40106000d007a41001031981c2c0054000c0011900a03069104117031801450360340052880c08612402 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 514035026 1250 514033776 514033789
    0x62307080c07210e030f0304050118050901030b1b160c0e0403141c0608060105010e030313060f051b0a0302010516210b13020d0f0c050d2706020c0705 66
    0xc090340802c01c1e500100d40d00c101c024201001c000b0400410103c2201041135031414410b54404d0f8461100560300d4904080c0050504a001024030b00f056191440030040c03079032090780c0a41101e42103034071443c058943d000f0420b18401c00c26070046400c40000303509081f0a03440070620b01d1243c02592992030032515105000c800e07903010796001d80001e50211003041006100302c000e0403a04410304000300c5440b02505454103860955020800c1a001080100702550304010300c80140324048029600c2c1882c2c0400000e40300f4070305c1c050ba100300a41c00d000311540c180207c0840700f06c12200902c40100c50030140c2030b00e966054002c4120010750801e400f1030100109445080742c010901d44881c0c62404401915901e100303410318021030030380e885102401c00f6403100300800d052824044805695501c00900e1a02542c3c100384150195503d0088901d00c140e9200050b00c90780c014448012a9000180d464004d1461003071000802c1000a001d0003c2007200640c0205124110401900d9400c0d41d260b080084 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 514036276 1250 514035026 514035037
    0x1081203070c02090c2b0b03010209031f060e0a1b08011211040617030417030306060403034d060601021c2106080c040b060f07062307080c 61
    0x1042ca904082c100500c0c002403115441581200320364104041e20001e034104d04118a0149008180080700354034464003806907070903840e8260300a518011410004c01c3e0b403850740c004440c11003100b01003d04285074003500038a00500c1c0b81c00b00741c4100e04088085070002c01e0360420000ca01644c00c000c903c1c03020f014901d41741c100c2d030400801c4131040d8543d80300e028200c01490840c5170701c503991704c07000300340360040e00131014980000d44015600c1c1c909000d00c0c0e524004880c401e040c5194414007c01200e03a41d0304040703d060741e078035150410040907010441d00518101c0104c00c80c030728180750015011115034a803078003403405407190644201644011600c0c1c589009407661801608040d0045490045122000c450343c549468403040c800c0e421500d200b01c156995204203006038644038104020002081054940501141c040110a1141000468078411a0190103c2a0022078203500340f06081c3d10007025100304400845160700320241c1c6c4e00e08668200c0d0100017190701000458a100c105400303844 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 514037526 1250 514036276 514036291
    0xc040f02091306050a090b01021c0c030930020d1403130906030818130905100606050c1f061206020c12040305061f030221010b0409050c0d0804030206030405030301081203 75
    0x1445241468003001c047c0461b502140d055100740b000288405580c441c40c4407101c0865903ca050003007091400501541c1241e0000c0c0c01c42c4015020181485450882e00070f100c580c10400003500030b40c5102003141004503850241c2503c681c2004a103100c0c0e404002000c0d440003200f0144803840d1180b00250880701d40d80030140c0b00c41000d2201c07103d480e502424074900c0f000300800407c0c0c00c4900c41482e00503104022000c851035009a460b10318001030324020f40006c2e0202e41805418103059282007603442800301c0410300700c0c0761081100040542d1a038840c0d4060702e038417401c1d070407142c80608003100030b0351207100251000c0c4940101c5400e50504c110a45060b02d5001014210300c0e161240c800f000344100041d0029a803485150020040c0e5a10340002c5001c1603070300040c2248102c00403014219002d81c20301c0d9006a0410044800280c40842c01801001e02102c28542034032690030070403001d0060ba000203411141c0081840b05101000014504941c055805c40341c00c881d4000342840070f40026100700 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 514038776 1250 514037526 514037539
    0xf0b0a05010503011a210d05090906040c1d150c01060f0503031303030e03030d0c03091109070e04090c0b0a09090c140706020a230901110d09170c040f0209130605 71
    0x100d07840c40d01d841c00700700c07101200303211b160b0480e480c2c050141000034111040c0042a8001060880c03030038482c816546c002c1080b11300b0416100c0181c00034103086a4043d001c0f10300060050202c1441e501c840a244402d07500100c1ea030b40f903000281c05140249568001c03000384038010000040c4501e80001180d951945800b1101040c500d5035038151050322401e1b0b055a4140024070400c0360a030624840c0c011805001d6601103072903241403c0c00002500304900e400c3c0200010020080c407180c02030380c0036100b00f406a8000a8455050400104910640d040381d03041982c00640312104c1c9a1020b0400d06407814448200056000c1c1c0d101035402401a00d4484013400040c490030004c038055501614141707280781050302c01c001c50b4201c81180c01444c20814241c5000110340c1440c01d5a10443c501881842140104520600343d840500103213003906c070f10004590044035910090358103201034400145c0142060080c02c00311030601000c0c3d0402c0182a02030b00e105815018000180e000e00b030308951015001 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 514040026 1250 514038776 514038821
    0x5031204150f0306030f0b0708090106080d1404090e0607091410050a020a1b1806050607060b150d0501031101180513060f0b09091f1509030f0b0a0501050301 69
    0xc0c0ea0405107140102e06050fa00c842c000b010807160402c0c05501840788410030310740e00d001703031024104c0d0350043d000c03d10aa03d040c80c240289400043c507800d120b2030340c0c10b110455810b072038408000361045030042c00e401420400101d04428002410900031405500c0e00303410310f5252200764403c5540401c4950f44003803000790101420780242c2c010810b244491055801d10200d6458840d183d5603c0d428403c05e40c80c60305010003201026140c40b0503091480e00b07003481500e103080001030440c02201c501030413890303540740c0c0c0c0c0380165108940711106528400b480f41d00d0309000303054280280424071054071707141c0e2204485c03030a640c441c40c8619155490041c00e204198148400e0200f8180b10740300030b190b00d0b6030300d010200706012641d5018000b407170300c400c885a41e1451078013030101003100941150403a5203401c8000c00e8007510b030704104042e51140c410398070066a007c6022241980254809003200ea940c1d0880001c0c48144c50019200d4008002e0030b002c583da9035002c1c1403c03100f00a880005243c440c104 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 514041276 1250 514040026 514040069
    0x105090d0503040c03171b0d0e0301090503040e13050601080c09060a0e0403200304080703020f09011a03060f090a0222061403090c040612050c0406120b130b010f05031204 75
    0x2d0f8403416443c4c440c02600700164401d08840d1107d074403e0815882c2d029900c0c45017540da1059200d502040c3c10360080c8040e40056507840d580e80220300440034100f901d2400205440710054054580399004403c640b15541d469004c1030f2502c0e00a4142805810840002441800d00100b4070084400448030551595126101201c5100400344d1190a05040e03c0c500408100c0400142002d4034000f400b80a1080c9035204012110204055942c040c00c40000100402031a05101c55400e14240e041aa0b43c1e070340701c0e4002440d49640f00c01460b0b00104107400d00603240c001c2d40c060025a1442103c0c56402c10700f040000c0303101c3e24644240c3d4009403070b02556408144d503001c080c580114028045a13441144140064155500e5402c0383c080d0002c080420420300104101d203010843d400d440401540342007400200c08806507900c007503c10752003140441c00b0030701d4100020304507507045001910b040d615090000c100c2031641c410a80b091185560407024a00c110048800315800501d4182c4101094030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 514042526 1250 514041276 514041293
    0x2318040b0915010602070e0901051b0a12020d020423030d030b0f21070b0405031e0a0b0a0204140402090a0510050c0f06070306060318030e1309050105090d0503040c03 73
    0x5298640718000c9014169054800e1608180070b4031040c1c010307140040c1408010341e00d40e40c00509181c40c9030b04100c20b1091450602c0b010b283e02c0c0d60502109039882c540070720180e5014441d200400d00c400d100050403008900181e0281041d144111002c0c118000b00c00386852002148a84050b40761b004441000702c81c0d030081d4484802140090f021100f50044400061a0301044204190b80d4000c115103681c3c055009000000103048000509810720b800e00b40401d503541240890540e119081c42660355841008000581549034494204020b5140c0902200d010f500903115181c05040c03a000d100242d4034180c0203640c401100644898141803400080041c2d0080044400062100411082c0e41265060010750180565180200550b0418402c02012100b407648000101407078014492401103484100c50601c03600b40c0790003c00100804002000042d01110302042c0600d0800600c08110064200c13610480300c02080d254003c8000304e00395940e10080f513009020415000d4148000703403400 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 514043776 1250 514042526 514042531
    0xe06040605030616020705010c05030f070303020909040c0603110a0c0219080a060b0a050a0305060a0b060d021c060902030f040f030509100e0f01031b050304060f062318040b 76
    0x420105500741e07210003203400c0000c01d0729040c403c1008000800c0c003564040141c40c000301030a10f41400e10700d81c561500d9072079001e1120021484030001440c103061501c01c0d01500c041810080407101039040910740000d4100d441d12410700482d0500000405800081c011340d41401c41c00e0b16520103580342c039030070800071004c01202001d40500308000071a03032580c1007203181c614502c0380d4400510141d02c803040200120080e0301151223614601001c1c000100d011a0543d08050010408103403c1d0a4400003011401484c201403449d61010035a00f003210002961030700c02d0382c926031080042d1070710b075000c2c08182d00c411149000907035038800206001400006451001c58042c1c641903040c040b0780b0000900c414550414500010380300c19101c00c0c1498200406d80440074242400c0107a41840e9100610408201c6024003c0c4500880060288505500440c95038001070b00b040185588441c4404680004011580c3c1c016102c484c0c070504a003807404c00460a0b080c9070f5a01c0440341c2d295035801540c542c00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 514045026 1250 514043776 514043779
    0x19031112130b0a0207020609040542040902061e0f0d0b01020f010c0f03240902190306080a1101050d050f1b1e09180a1b02160e06 57
    0x40288400140034214201d0284140310003002060006040214441c800a0140345403280304002c0b550040e070b1404200ea051080036500495595500100c1c459004203031418039803040005d48040f0091045542c1c001d056500280c1c50b0f40000d4014000e0104848030140c0007074004008108240c01d0480c011118034480c0724912210b0f01c1d151003260100c40380e40201585a03400f40d282d0358010440d603018820031110b1074000d0003c00c0180441071009124070811003520041c19607440940c6240c049952003418007000c90301802420681d94000c140013980804610034050310881d140c2c40c0b100d88603008040860742d0610040500312010b8890980c118840d0562605014080003604446443ca000d42c0e4450880c075294800203161842401410229030500390410392030421402400721136450a5207d03481d50030090588800c0c246020805003140310368501e884c140510100310b0074100c00c1d00600d160307486450404100342c4403c0420b0f6940c0041c91000002c00900c001c2c1800100c06000019508c440d0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 514046276 1250 514045026 514045061
    0x3020f0408012405061e030a0207020306092116060203070302040503151f05030709020a020c090411030705090f0a050a020d06081509070b0301060507080d0c0e03060702031903 77
    0x3a244000750071a5048505001d42c030010110f42100d8400e800500d038018042502c40d06d1070480d042122030b84ca41041000d10602010210214007010304035815240f526902400320b8005091402c8120703620004441e80c1000c400790468010040c1c4840c034180d40c41482807403000c0d402006580d5816029406c0281003004040c2c4c01d00c0000703500d680402002e200300c040f40c2c00230800c0d0300704296070000c0034401c20851850701c111603d041216480c0028184104c86681000585400ea1040202d003401c411004540d8070480e00c40c14882844004a52000007a500b01c0485000503070326020300181034401c680116030300d002c160004130141c2c040d4200c154000c1e5070742401890401c03400009011900950480d200b1135110350311481c0581c15100469820810040041c8982c51401c050b0005920050040b0010000086210010000c55000791003598205280600c83c41c40780c00802403001a55070085c92180c8550408505a240080110b480a04200904070700c0c2e403800c20310030750152906a000705c11005 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 514047526 1250 514046276 514046279
    0x6070807031e030504060609060503031206040f0207150c0c03050a180801020a050a021b1c0609060f02120f0114060a050c03220e0f07030e1903030e070f0f0603020f04 73
    0x803101124003902c025a80b00040e0368103140c20132004441440d0010070f1700c14a8a002070000c1d98000040d01c007420030100880c0425030b0b80c0741c007050290019158012400c0c2c00814080100442030240a40c6000701200401c50240b03080c2c1c0c201d4026018800160102e28104003d200396486540106074020015200c54480340d41c51120300c2c03c80c0d00c80c03100500058800300c0c1350110a54144100c40c00341c402212440c00e41c00c0380200207508100d80c11080528000d8000c2684100155501316001440e0070040c1080a44895000342c1d02940c03008041650002c02c02000807500707407240100c141600c2e40c204207000d0001c00c1805002c01948034510ba5000e01000b0301241740140010001891040780c005004d00c0040e12180340203203000703021381012624800e030104005a80d0359a101e01c3e40d001015103008030f44405142400b604060010041c4032140d95401c6c060f0f401e064154014595242c0b10030216250309a490700d002480b0319140c080c6c1840017840f034100304002c906c245c019080c0c0481146929140c907 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 514048776 1250 514047526 514047557
    0x31506060c121b0803010f061103040608071206080d0f08090a030806040209060408070302030613120e120f060619181a191814040f060e0304320607080703 68
    0x5000a0f07411603c220001005100b000b0340c141e01007000f45440d0401c0d00e420000d000d0240d40742e000f14020181040030420014602501c208000e1015128111040050580341c1d81255101d081e402d035081c007c02c4880e0395116250740725442c2503206908400c0600047c0c00c20303941c12600d0380d401400107036115400340720902c815600c41c40204018100340004251040c6948185403c00c10000e01500b02c583d40c064091001c80d48030180d10031100e030149000d1184071024000640070078640340000c1e044d0f104030000b940d401c800004040d4000c0c00304907461124041c03a440030001004c982c0c064540b40f004460100c003c3e0002d507030401c03103020424100804034010000e01040c100d4008280c6c0d03000d18651900c0800c8180800c2c03682501180600c0400e03c000108441801d107101170240c0000c1c54100340f15110381c28400543d100c07200708928081601d6869a4070032482c4800b0006890110204081c62030116800104410551841d172000d0074040c1050303180e480750041600702c560240c0900603010084900c1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 514050026 1250 514048776 514048817
    0x90a060f111b0105090303271905010209190609060c060621030305060103051b2d0403150504022d0301020415020f1612140313031506060c12 62
    0x20b00c09440c2c1200e80c0c044212000782c20740b000070341100c05a400c100140074040c62604c0050301194495501840503194409000b450058401c00118011101c1c1d942c0c4002c01c601074008015606c02100c90f00b500d882d0700242c088c1d00311403501c05c51012800d000300400c001809054059003e0740501c20000c0e041d541d278a1039160741101e45013400b00503545940b098003095050310030260003c4003840e080001d840c02034261040d08600101c2e20b030000202007600c802c1d815201201071181c01011509216004805180109581050000702c80c250111f0b1104002c0c0030580c41421302c140c0c3c0041404010b0074899070515804005940c10b0310440843d03c8103d00240c800340001c0000309441100200f000c8003400000b414110b0b00d00c440b0b15035401100300203002e052003a181c82c0603100d55044000303d00c401490003503c1a0342e01c1130504000d000106040030010003400d2440120ba0003000c07140c1240c0b001182c1c4408480c03007400b528010a0a5403071040104180c229483c401003c11304010036021481d0f01108403 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 514051276 1250 514050026 514050037
    0x115230d1509050606030402010c1e1103070501050304150207170a08060114090901060f2c0918060714270a05030706020c120111030f040506010e090a060f11 69
    0x8191200e008503800315104880d07000030060200100010708269000842a1101030b0000c1e042101d0250b00000b44000c120641c2c07504034020980c0f01821281e40f8120714064182d5000511901945000081c00e5005404980c03150b50b0101071101b000700e5100c40071001707401c100c2059500b07041250070801042d480c00300410a40e1103075290140b640c5041e2000615444076807400741c6640d54180040b0615481d1024703424155455820400300c40f65000908440d200740d0790358241c1007400c1c0c0d1031016a200d9203105d8154040304c03003541d00d480544e950210131100030500c2c504214003035000f00300051006120700f19a81070b0002d030310081c910304414041c0c210392508242c1701ea1110074001a4900c8228544460000020b02c003c1d00130f00560391808901079215a200b81e41c144c058009110000185002907221104c9078002c0300500b5107d05064825544811045070f04a400f0b214400000c940e52414101b0280704182140081120007880c1d41c0d450080e0001807007541c0043d446400c0102503000c104003500 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 514052526 1250 514051276 514051297
    0x1e1903020309060a050d23160318060218030303130f030c151d010e0318030106030b04150b0a0e040303020a0201140a0c090e040b040f030207080313031109011523 71
    0xa0301c400e45903039114111a00411100c1c8284400781f0078609000a003c240c991003e408211004108191601030707003c1e01400381511307201085595040e0410143e83d000c2c022241c041c0413040c0340a0b000d9014566248000d483c02c1c100c0d0b01c0e00310040c00011b5521011507015070700c80d00d849150882c140d0b4921030601c8a610403000c0064841444080c6030101c14954003c01280b03c0003070080210981c4596128404e5410520002049003511540c0e80c4003500304100840c0d002c100b410092410382441c01c601d807040d24007060b015041841891141c5400340c0003a00340d58082c0c00c44c10b80c0351110703502a4003d41c81207485000359501d582d41200c0c900f00d10b868046c0700368404440419801042c5600402400c2d9903000081c250414100340400304401c4029142c0c02075000c040c80780800014103059140c42595070040d0543d00c03001689105e843d0140c0c8200c000c8030311030400501501c0912003003181440c0d003401440d008052040b150361040348941103140c250495a10f5450805400d841d24060326800407103083c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 514053776 1250 514052526 514052537
    0x190b0301022a0d050d09030314040501140a05010506030c0304140109050c0a240c1716020f061c051b22060c080910050405211e1903020309060a 63
    0xa40610410b0b001814050a40000d4198a102c2c03410107820760060074040c8404c03030381c0d50103000c08040c00303a44144880201422504180d141519007503010307041301c06902032841c003840c02160422200303009090503590000c0925003159514003004055800040080e180035030b4a10b50b03064001400e2141c00c036860700940c050103000c9000428000c050142d0b6001c4604403c18480614101d00d00499a80d0300305024503002c1e01049280c204800002e4803008598100e02c8001107a0440308070903051030f90150b100703030b41601500c440c00041040314020305d014072100c81c0700e0201c11011030905501066102c0e1040011200466456190100c260040c5030740c3c04850704410034440d012001005a8401018503107000401c85000e50350b03a60342c034050000c140e8081c4504540550b402405901990007900000e407075207240c20601107a000b1040c0228099030001d001c0c14055a03407208000c3c040414101140004291006440c03103004c9034246880d01c07d03011804213018100940d035a410003000c2c150340942d5030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 514055026 1250 514053776 514053817
    0x908070b15010e0306130201020a0c0b04050315041a0a0e0709020309160f03060c0e040f02070201110d0509061e031e070c03080a0c0e0301060f030c1a03190b030102 72
    0x301d19000c0d00c0c0341c0103503041c090151140182680d00041c0503a00010490410b40700c0c504620040c2c1c900f1402e070340024484044440d0224985404501400403558118202d0b0016800350004c0f8540040955014001c020000124581408640301064110b02e54040000d10040350490140c180b4010b0b4125580098000040c0140c141c020070280c0c02501c09002021606d52500001803d05512440002c204980700e07141e8903052402000d50070900b16010340b061004010840c2848001c0d804290201c0c00b01c1c1d81401820002c03400050020100b03400b03030700d40c0703481c0c28044001c1100ca900001540340f20001002c544400100481d0055801401d031400601400c01c0496500101c4400c010f065030304000b01c070a49440400d90009280c1e40009070107400050b403110010313007212079440f0206100d40640c02d04a002a01c50348001103101164001c05800f03200d0740d298403500c460135580d5050403000c2c0c3c0701840818840d458400340240c0701c01010034005002101d00012909a80040844c40b202c4240c1044 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 514056276 1250 514055026 514055041
    0x1006080102040317131206021603080406140621010204030f111f02030f2208030a0f140430060507030e0f0601210b040507150c030207060509040908070b 67
    0x41034408803200d018185d003401e20104040308184800d2040c6455200e110b8001000d0107026411560115510800d680300c0808034100a404014169400c5903060b25003084241c4904103101e24a000d1079004000d46031a0b0180c50350360b5140404880a9001c65508000000009080da0b1a044205100d085042d40100c445001c11403001015100c1100c048504c03207042020550200440ea13115180311001500c80800c2d0000c8003901d00311200320100c0b0081250302107140013002028240c110340c9941e9814100680c601c0484001003025241c2c0f95042e0b00340824000d044009841584910400f408504641d4504020300400980942c0580d2080c2d42c1c1d4050100b5180e0600480001021102c024800c006400b4982595003005218101d2180e0302c82d241c02a950452100c8405625003103180940a41024180261541154894411f000440403a50850240a2a607042c141d98040c2c007d441845d1601c0000c0d00c10f9488143c010764080d540b403085400191000c0c0290015901034a1064810714107109c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 514057526 1250 514056276 514056293
    0x120a020f010608100621031d0909011506090e010521030a0e040f0204050d020d39080d02030322020a09150e06060a05090d050102031f0e1e0910060801020403 69
    0x10001b5000d075500360b00c107a00f80c13441011245011540b620b080c0c6031006c031005402031000d2100302c03115880020081444003c040540208000d0100b032080400c0003561448103070348443c0c0e18400c0128512180004000301e02c0d0950f9054031240c403804510301900903000e03140381558030002080012400e400b10000441c102845400e040c00c648120840ca0f060030000003c0d02682d00c02c200a1081d801c3c41106420051200c1107010180c0e229070381003801c1d030080c00c80342c007545030441c9484280103441a000940064006181503802c01a03401851445c0c0b11074210f0b051300c40d041d407601001044ca94041c01c006032a6030a0300340c02002c2804000814000024105582c05007550040702c1015070982400403507602e07142100e68010040c00c05130b540e4446080811800d1411910140c01c0754808010090b240d550002824103514003040800c3e81e15465460540000c1000e0301d00d0940032000c080c007094a401c10721056600496002e0864070071f00c00380720a00b41604d1442d00060141d94020804004204451 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 514058776 1250 514057526 514057529
    0x3050706050a2705040218090a021804050c12090703020a063c0f1403010b09010206010803120112020f090709060f031a0402030c04080102070804061d0102120a020f0106081006 77
    0x16038428450380070f51004a030542609003d500d22599001070454101810444e0210030307004040c0c4104001c0c58600303400c2c002034100c01a2170050544c2011054054a09441000e11880540700000c1c1841701d080c0680c50038070070043c1941701a22541101001595540410100178a06075403109040000c510a007000101030341c007205058030004668082000304910007030000b808500d45024002c0b603c09044031140004040301d00c001d00008000b04040d016100180f1510400ba005c44e60941d903100e100382d6592103401c010f0750701c08820000500c0641030102f00b1b0300070607000900441303d040018001030000c0c9015194440483c88440c41040510382110085218204600301005040018024120021403040d40d032440340f940080080d42c0079401c2400c0c0c0d805442000c0c021034071203116240c03203d410ba00c68043d142c08070301c140c0e000440f4046080c1000744070391030603400f401040360b19151040caa0b030800f14020042d4090441298480c0c1000d115600061100400a2401107007012800044841c00e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 514060026 1250 514058776 514058807
    0x604081b0a150f03110d150303170421030b0303030703060305010e03070b0c0306030106080a0308010609170d03050402011b111005040b2b0507051c0e070e090703050706050a 76
    0x1003140b80c1d501c543d000260181020090300380807807411020580180d65202d40c0307180e01d00c072907e420300d1001460b04118004042c1c9201c1d03140c13480800990a030110385401c0454004041102c0c400030180030240c03140e1010340420003811b0116640107080b0009003982c004540f03136400281d403000308001748542406521a011100c40244d45443c0c05519841c58030f01c0300825032000850000003003681a2825440301c40200030b220207071005240d087c036009102d0b81c0700b8031a200c00110103402c085400c40d5248410000c018112004083c00d440d18a0150040d00d0010b00690510540200b540c86010010070409042c6102c1c07240c000b0079540640410a8402c2c460004508001c0b050006000c041059006c079816104140300280c2d4034000340d0044502c00f5240404035000c0d90505091020f46604040071300302c005d000405d18051404900528801c44601021a84107540b2540007042001c1130418166002079188080e14280342d2280c036000d03e004060b83c840c1d00040d02c0001d55140d420f0307000b04003a400c00003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 514061276 1250 514060026 514060049
    0xc060604050601020a110d0206070f030801050306190c1205090d0305010b160f0c050312040905060d080a030c0c060507020a02010f0806030d0e0d120905120f0a030c020604081b0a 78
    0x103002c00000d5440802690042810012002c05801c0c0e40c0c450000810040d401081259a0a0140350003a0740110f419411004a52007100201d05458046449481024074600e4500c00b03100051001c0042c1a007144186c041c004000d038840451509130084174800c039944002081d1020840c03c0c004c0484805a01040303140702c040c0040c9103031415001003400201e03008403032000a00560f0a0101c00c85075079030300040c1d02d480b4122043e00b40c0c81104028104942401008000642d164403c1c0000100046030040650104002e018a094000d50102e1300c078002c140b03400369400b90103641e020203c40c81621301d0805030380040d0300001190f901c04031084121520745088125070030200003081c0d40c3c4080768060400e011b8036414404c21a102c4c00403500300c0a03004401e00403005101c15000e84441c0ba5409400d00980c00e0000c04030f03524800045410070400042c0007080c882d001510704481000c1c195104036400581040000f440c0030b0700b04010f1382e100c1451000b12030000d41c00c00c104414611541c0c81070700b0b682d0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 514062526 1250 514061276 514061281
    0xc030327030f180f152c120606030709110913020409050615040311040b04050a0501060809010603171312150f11090411090d0b04050708011104091e0c050c06060405 72
    0x20b00181e400b03080381d00c4540400c14410340005e042e21142000c0c1030480000450000508000141d6a40b041c060072050f68100300740240c61841540ba45030448445d5007540c01400f08200105269208103000c000d00d0504504000c0881c000039030f040e040e911a2403849401140500140b0314078403556400c0340b81200c100404102c00401c099140c0200d1001601c0c40c6000070ba51200b0303403201c0c0c102465901008100300b08525140905000920080c003a0b44006600c643c005001e4020500c90070050b01d070441855a4a041104401c05040e4807602c80840350318417459000034411040c4140042180c81200010010320042c1450012500d0055a00403880d00384000084601d03c544110780c0031300d0090381c01003000034201040030050f110f400805900021040d42c15418080c0012805018a2285060b00c20044d40d85010707900340c1390011508101400100410000344030340740d1280c2090b10f104d80d00903562100102c0c11100300e41441114002042001500711404002403024039031002003103d040003c0d0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 514063776 1250 514062526 514062539
    0x24081b0d03050a020102041206050f06030d05160510050c18010518010f03111605060a05010501080601050a030e030a0c051c02060a0e07170102190c030c030327030f18 73
    0xc040255000d41403010029032000c0f0340d4402c0d0101d030050b203091030b806010710286141039002000d0031030300c014222403c440071540b00d14010070042d503190b049585103420318170801840360b4540c1829000302d60030b20030032201c1030328a0312038021a4450048015125100c1c0b00d0805041301280780d80c40400c2c10007600308420442221900e20502c1c1d280820701e0700000d540120082680203040c00301c00400e200d4004115101030429203c840e0441e18840c1040d038105c2d460380d45403001a20000c3c0111404a180c113800241e10b54850b0028000e13070030082c50b022a0b150003180c134403070841c0e101c000204002068406020107000080100c482c90044141514042500541e0f00a480d28000b41c01b00e1003a03902c0702e0749440b40c20000c02044001d0420724165a21741030000c00024001d45c400701808c201003000314905801c00b800b80d10302210164160f114488281c41e035070703001c40081400d80380b245480da0000141030000d0041c00e01411299219444005400364035043c05028a00a03800a60f0900403005e07050095 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 514065026 1250 514063776 514063789
    0x302030d052107030e0f1b01050f160807080d0c0e1f03021803010f060905090601030305071101091205070e0a2c070b3c0a080a24081b 59
    0x1500542c50300c110341c3c0301d80c8030403005070601001c40e0443c0d00c0f50b8654001c0e01140820710910020118038061001596440103440c180180e100d0340c0620401445940c144502c0941c4040000384900b150768641800d030307515050940c0001c8070049400703540b040d0351041a03400690301d6551050407030b110004140c1031401e080700310074402c03141c4080513000309510800003410079140c52440c10080090014190352040500202410710601d60494240b50100d8500316002c66000d0690390982d40e4030f0300d002400d80b104960031070300a03d090b040100030000044c0468006d80c00f40001c0d41b042c8003801b0414030706840b034400000041e10904440749815201c1a00b503160740502e048a4000c01c100003800c181d049901030810a02d41d001c00c02c02d040005800701d00380002c070f011181d04110551548000c0388010006180e00d94030700345001cdd4408013000945401c1d8000e484903032f80014241c0020900880e0200800d141c040d9410301c203a80c1a01d0701a00b4800700700c061200040101d00b400395117943c1d40950000512 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 514066276 1250 514065026 514065067
    0x11211090d08041715060402120f070c061103061306050f0d14070821040315090204060305010608010c09080c0a0618050a15020d0806092202090406060302030d05 71
    0x229124080c240001c010101e0251401810340400c0e1003580803403240c025031505120000740070848170883c000b0f00c070351420340f082d541207400140e900a540e41d240101d03040c0c032040c06090701003400010b1004c02f0010f0903500070401003200f5408401d8490901c0014440400450301801e040d1608000d03050201d900d40890080303e8000450b01c0f40a4400542840c411941d030414001c0d51034010700e000401ea940c400201901c0448414042c20310b54030301e0340401c4499024074000241110302e400201220700b4455003002d40040d000400004403260b8a036112421220998042d40c05a51600240c00f52103800852038002001014040c00f50340e104200020b5145940d40070343c0c001d204549454203540701c00940050301600d4040d00201c000ca449180d244030b15501420f10304010711400d000d001065100740c5d80c2ba8010a00500107600c540c80c0c400c1198080044480500303e40620440400d0259442c00c1d030081c000d42c01400002080313070650051600b040031403a414810702204000203003014084061904 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 514067526 1250 514066276 514066279
    0x172209020406171b0a11030307020105060a081f0c030e010f05070905091e091c020703061109030a17070c0b04170607081f030f060c030506010201200307020c130501030201121109 78
    0x45d920180e90b07a081da903030116400c10000b01d01c00170040100c11501580314500440b011a032001c00c540c0c0e05d100b00d41e0f49400d1003400c41140402011880350110403504081c883c0c41041c2030120f950032580c441030782141e00c461300c1011a40d403108144269190410304a0000e0030085e92a94103a1400c180884540300072051038800c0b1b0b400c1c0000085088400340b0440d2103840c03130700141a940c0c451642c0029524410760000399216442c00840241c800907400c21207102d00c03000b03000703001140c905403070f0150001107004455450036010881c50303000440e886141c2c0082c04070000c074107892754140740304046115148112800a82d024a0600c0f1480b80c0081107076901240903d0f00303c1c90414001002c1e1007880c46980f0082030340c0c5543e4031503010407502e1f421101e0050b08036035003085070742d4400c0012801d0700c41d003210050207201e0840c40c040402c44028000d55119400e40103c4010049500204518008210b04030109940d0381c0011320466a11081600c0300078034220060101031b42110001d412031140d0741002c2d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 514068776 1250 514067526 514067581
    0x8070305010602071217090303161203090b27030c06042102060a0b0d14150609070c1b0512031902010504020109141f0e09060303040317220902040617 66
    0x19100c1c4011007c8410000e400f90036240c8070404a200c0c090440c6a0340401c4681c60320303802c101c0300210310034814002c1080d007001c2700348503544034009011820080201e1280800c0d010807854142a41d0420042102c50091001001103250508144a4030180b894008000807400c0c1d00002c1c010760300051031a0406048000000c1da08840e100181155032103080007016990803011480100c200402d11469000407611600c030280d032003004005092030103e5812010814001b008008541406481d01100c802600b6010300d0302d48a80004206552000c40040c44c0e07480052520312082c01301c02030744415121400203114900742940003034900d040c503001d0b042c2d14003008010b11001d0703a5030740000100e410a5140d00001c00840f03002c020070459180d0b5a5030b01820740c3e01c2c0400c400303003800421a822a03810491100840441034407036004c980c4189049404018045511041d540651441000400c8146401a41c0d50301d07200c03020f08186c08820b4000d41050412040084019040c9140840380c03102c0c0460303 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 514070026 1250 514068776 514068803
    0x10e09030306220f050423061810090b010f080f0601060e130f0e07050102060c0a05030405161e05010302030702070e0c0417030901091e030308180d080703050106020712 74
    0x981140e50322400f50503e0050801013410098000c41d441617004a001c0d040007aa0094000021041c241341090760520952203000001c1c03008a01d00701c81c0c00c6005100060300c88284032064281e003518000310b426600562000c0041004040c045032050003080480003070b0051010421104d40c58090520440040c09140007403401c195950341c0321f0708030720b4007549420080101d485101500401e50400502138501c1221000304440d03000080340b032f00c184a40144c0303905e00007216504642507080036104880751310a0b0451a2240442520328502038650001071103221401395054041245c1e281d0310150616204000f0b021035591301150507015140c044400c0400b41c1c8801101c80071611075603014504040d035000192074210401300082c0b110140036a00c0b1071200351904c07152180b614410006004c0310340301c210200b0010340202c3e0380c81c0d403100010744800680004001064140750030014800001182c0c442000b01081d010321803030f030250880c0d100411203203061038110f0314448a10400500540341c541e01 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 514071276 1250 514070026 514070059
    0x152d0609040f120c0c1e0b130f140108061509120c060a0e0f0423060402091804020a0e01080d030b0f0402040303020d02150c071203240608010e09030306 67
    0x1070940c2c005a201071003880820351400c0c020000d05401c0004c58803200390150014429003c000c0b030784004222810900c0003c0d240141c100c159a1180f0048044c5021822001800c02c44001a100040810745000003844500c3e50005003981c2000300100c0c418800440303035002c25a2110140d626018040e26000114401246040d1900e02c03143c0301c6075844400005e664003e550300c00d1003400f00c00ca0681c1d46034004c075449410001603550707480d0002d0b8902004a1348407d150640d01d261504950060001450715050b040441c43d80381c03060103025010305050060200b14107180030312074014a0016540c2c4001d50401080c1170702c0705000000001010b4507500140110b95450010200e9008010030031990765a81746806901d07030a0442c1c4010142c012141600e01d07030000740c04050300c510341c95100e0500c0c180e015038030075551818004c400c10405554034a6114041380314000d803c18000c0100300c01c40f0545c5400c0e802000075030705800000e9202c0f0402d041c4015503400200b540c1d044081250303100e501340c21128 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 514072526 1250 514071276 514071293
    0x31302010c050a0b09100e0706020a1b030c030b150301110a051308070f15030605031024030c051203180f0d06060608150f1315030203152d060904 64
    0x580603144c0403200013807000040f0001200e1442c4c18020710b080c805101220728460f1115454407808000d40c00c841245c20000382c02401924402088600340c01e41c4a4032910307500074180003500119840c0d5407400a00c4a00c01101c090000d2a40045009100901d40701440e40481e0103081010b8091200100703009481c0d250404034003014110b4002100e00407540c40c201c12028020520824a0340508581c3d0015118440d0180340150b170805001012400946590720340100814407500e11940b40d9081080c102d603104030942801103004040c40700c01c6a0404c1e00f007082c144501024004250b00420800458070300061400d42500002c80386807001e008104046904807407800c600425507882c02c5404261990041d01c8107002d038058103022448414030f5014401c88059210103603503ca0034422000d60a14802c0d003100742580c41c0e00b003441c50025501d0b80468942008002d81d000d581c075451003000700d0112184803e40b0000c0740c829079101c0d00d0f6072103642100d80000140c102400b03a034811001509010a05 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 514073776 1250 514072526 514072543
    0x5040b030304080109050d030606090806060d080d09050f06070203130306020d09210e0a030b0a0f110c0c030606040b060406030c02010b18161115090703080c070f0902031302010c05 79
    0x300005d1000034024500a42c45000c1c0d0b000310000b1078a41007010030f04911445a8500740c609020060105807581810040c82804c1d40c4c0c0102d0b80660204101e1001045902410140a10690081003103600d20f0011a051060081c11101154018010110740d00d00b05443e100c22603030845001642e50600059120141c4503220010f403031014403044100c908040030030025060f00b02551900d503011250400c000340380c400c1e4480a00750700d00383d00101c1c2108000d1b40c051850307800c8026001940040f80144883c0f59001140806943c3d001540c880d00a0300b400e000706680120100e43c10001000e002001032030710300650188904250b0744030f4245000b68000d600802131030308001c00000c100425818141e984c200110307955030017441c108040d42d04260180300c1483c40301c2009809000c80d14190380e030b4054200300091004115126a03200000405d03100d40007400c2e0903d20760040d00c00c0e0303428003e0400942401d42c0c00300d00d00d64410001c0046400341840080d0100e503091a10503e441301c641030041c6081c100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 514075026 1250 514073776 514073789
    0x204090501110f070b0c0708030402210d20160b160c03200f100c0203030415050c12270f090108013603052a0a2a05040b030304 56
    0x500c4066560903e80038141c040d11031402c400090340c3c1c26509021500400c400184070080a001144c014a000c0c043d800710309801d2061942e44400360100c042c034241810300b00002161a01203800711804500810501010015004000458400c00011f002c1030350ad209001c542c403000301d034a02c0a00b008090075070000f500800d19400242d200e00b0515070082d480d244a189032001c0000c02e105a04006000c440703250307001131490b10820509007003542c6100b020304049170b05004c20040490120101c840044003264195100da0f2140340e40c441c114986120b00030420303c9580140284601c03044942c1210740580701022100424403492008541110140c0510300e80c030250410022a00d03a6055000d40190800c1030000c40300c141a04049600408003c2aa852320115a901c940f0110740220001c14072410a94959201003403144645442d440310b241c03660b042500030300303a0347c014029590301a80004011089403541c82c8c2e0200b0b8403280c940070034810540141c2c2c5440b0030817101e580500560740185103 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 514076276 1250 514075026 514075061
    0x50c15091222140112090b060f01030603020d230609030d0c1101021c0b010c08030606071a090d02060609090303070c08041d061906020a110307090c020312070e06070204090501 77
    0x12501d80c444048110f0a640500140004054801008190280040340c44d000007103a11300351105810312243ca07000d91481410b06442d00300010041c4c840c2200c1c0c000d00ea00450503000342907288158400c58032024180d41c0d40030791000701070018504011003187c00b117132440703c00055148c1e40070f1419146c9400103052402e05503c040b40c60b00400180ba480000414040c80f4108130002d003d600546554001c11005050340c081800011480d040000007080c0d802e0158600c10050040d8070701400c8000c6c012a52030045400c0f0702030325043c494040040a810100841d62580300349071440d8610340c0c0c1c0c00b005082c90200010507424070f0612030322408840c0a884e040b8030640b4120110542c00e0141d01c0300707a42c8203004080c00c00458864408401003401a540154007038690307007520351221001e1a02c2c00c1b464030341c940165000024800140d2065000c2008513801450310780c5a0044000c000150080c00f074020b101082c401c00200f907542e40700311075a050341190005808282418401e0040010010001e64000e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 514077526 1250 514076276 514076279
    0x32d0c0602010c09050603070c0f0f08040305030c060a09030c32010b0f0a080316080f04030309090f0e060106050a17072a0b0f0a02070c06050c15091222 67
    0x15810b402400f159000368484142d207030381d0741c4184061803004440d038500145421081e40c00203008006040d4005000f0030940b9010801525108201d910540c0200d0725a40000b0b500c00a1079024803101c2d500406005040144800d00c1d00d01400352151103100600c000d81500201c10a003a548981c000c43c0001003841c8004001d0000c0003d00910f101d04000740715081d00366155800d03280260a00b41603c500101650420001c0401020040004402116010414002c02c590404504040e00085002e0368410a81500d000300840841c0d400c0c4e940d150a445c2032150b0072155840004060781100c5442c5020b039501c205030401141c411000c0d03890290f201e138500d028040080d92101000130a41407041d2100750040c00400684207004418400814004c0c00c03100140d2403290b1110f015a101003800300241c54881c180d9509045c00d0b2158100d84041072000c194221700720001c0000d00c452201540000341642031491680da620300426107800c100fa4000207074840c19000544410b40c10325504401c0d115441e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 514078776 1250 514077526 514077539
    0x405060306210115140901081b030a05030d02040e34020a05060a090b0f010e07052a071a0a02100c05120f070815131a1e100207032d0c 59
    0xd10f500c6010784540480310b45c001240740c145049412500c000c3d000303001003004100321a2030059403170000d9616009240a640100780c040c8001d040c04981d030b120050b512070030440e80e910050806024130969540103001c2c0e08580d0800b2038400381e481140e9800305500301e071403102280b034a024540000c2035801180305002c0544007580102080700d101300c1412000b035450769400048504c091083e00103611001c0301203403146000c1c0d001041000c0300d02e00030152a03030551104034001c40000e040390310305600441042013041c16604242030b208001d400341604d03181540500a40c0e0b102c05070021803070b550756204400c45840c0100100c500044400145520600d07002801748519141210144003007014140080d2040e0401206c2900202c0d00409643c00c3e1842440d10400401007000150300b1407282c9074042030140e640c0c404000340d010380184c083d184c000264080c484038400c10b9403c135081d503202ca4014800161407004040c866a12403108103600e8080071000340c41c0f250880c0c00030380314048011010808 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 514080026 1250 514078776 514078811
    0x1c0f0f110111040801060f06050a05070b130206040617091204051e0306040b15190b1615060302150a09061206031a0601080f0601080601030914010e030a090b04050603062101 76
    0x100c0d0075080104007071030380d2503805a2702403003500e00c8a00090fa04000500005807003250b1030b40c00c014151120034558110b9404242d031540a45c0059004c5071444089056400303128070200c0d80001c004000c1c2003c4031800c07403c43c1d4070340100d0185500c61240040d1300380c40e100c2a0b08a0011041008088404a0805007860080100161400c0360502c034942d148000f00c3c01d200b40c103040b580d1140d00400c1301044c0760020342c501603008000c1c44650700c001c006407a0040b03088654444000d0014900000b444c40c614410050140c0b440074141456400034040e103040e00c0d03001a00d0004a40c0c03581080e00f844111701000000500380707034200406009a10307101c071034042d10160b010751042d5400e807100210b1b51107101410b0384a0354201da007070f1700041c1035400040307180d40b203034002d03078480e6104001101c10b02d10403007022425181c5a10070607050340e001041e41c0d24800d40c008406c82c000c0c940d410400c1c0c60a41003401060052200404071801801c40362080c0c1c56500c58551002c10003011480204100c80c0c070a407040c8103 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 514081276 1250 514080026 514080029
    0x906160518031606030905060c070b01060c0f12020c01090e040b0609061201060f0603110c0a08160506152107030206090609041d010510060c02040f06171c0f0f11011104080106 77
    0x7030b24415800018270b040b0106045a90035034003d0001c0742c4036880c0c00c50881d0400d40c802c5088501c0b1040303c814100007071007a89079074101e5100760041d105440e848000102070030841d500c07400004140f00103010118194cc01f5654000c041622005000d94446001c030301a29429150043c4130b41c40c080c000035200c2220300020b4141da40c50355044c0f0050709101c800d0f064501400c04070341d0054001d04607007400100c8120003450003c00100c0640d4517210307132380c450b1800c100044543c00c429483c1008566500d1400704480e41c0c1e00c40f00f20b662101d102114410305c0c0e81d14049400020700035480041c4d4109103694610030703036101030001071051010f60b021f00c019680c0110b1101003403107950700b0103000c0740d002000346a0000039038501e0b40c0d8140e0b107840c00b502080064121440c040c05403d035035202c041005800411880d040140e04c10062009a01042010b282e03100d00001c0001040440a420414a03a10500f071003c1c1c0328482ca0300043d4020b243c0304c01e6004228850754107443c28400540056002c406410200 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 514082526 1250 514081276 514081283
    0x7151116120305060d0209070e15120108010f0c0206070e03010f0e010b0112020f120a060503030403030f08090c01090e07090509150102100b0603011e0e0a0509061605180316060309 79
    0x841900d13588140007110f0306111000350b00c414488001030300300c1d1148903198400c05000300001b0b01d5000c05c08080000d82e0101036103000b68168000103111001007401042e0085903560070800018031090030094032808068141c000300001c6c044032214941e000d400510401071000000c2101e800503420081c000c00b914441039000c40d4080560b90791a40440c0f080d1540401c1c8a404685400901040036500003402858030507a15615000840c0741c2d04c01300b016101440c400d40340c440300009c10820207010744000806807002c990011076008190f9a000400f5821207000c03004d00b000c1d54841c10310544d13009070650407983d0002c07100d0f82040b400f00441003410203110b40030780a8400400a01641000703076850511856000b420410040200903020981400d4040f44000d60703120054550400400803001900c001501907168405c0c0f2603030103014840c1c1908480091441307440e803124400090054003c2d4031611840b0050003a40300c10030b84050004505644070300a000519036124503000e0010004108140c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 514083776 1250 514082526 514082531
    0x1e030506130603030e0f03010603050106080105100e06010f1437031109010c1a0c1201050603060f06031b0f070c06050301030c090c091d06010305060402071511161203 73
    0x207102080144280c03816070750076603240500d0a00500911031007106803201c054040d0350703034003002020034401e2080c20302030504500081500d013814404a010564a9007145068050400038020f10f03a8000440c0c0c400c0b01a0390910031403419001d15440700b94060080303081281d444205c00240c19421b20305092000f4060460310f16800c0541500450840c1c01ea0180300384a1101003040d46803c0d80901e10a01c8564403442041c0c1a140d0820400d210480c010380d50301501c5107002c01c0c265000d581c9030b0510743c007401c81501e115045240000c0000c0a0303051410042e40201c03070002c00f00754401c00c0e0f600c950340c500010301c2c082580c5001182c0c000103d603202210559602070712031404141c480c45802100e040704d81001c0071138185410084040001d001030a680c3c1d0620822400015803681e1400b003800c0f085101116411091134518009020360707100500c40c0340300e60b01c100303c00d10010310b010300821640107005000280072001214410814440c01040710b01c841d0344c441101c01040b0303200c0c034510f410103000e940a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 514085026 1250 514083776 514083799
    0x6180311010b0a0302280b0a1b030c06091e0302100f060302100305090129131116020f180108010c0804080406080907090c0e1504140108071e030506 65
    0x8035003280c1040c1101580712100070010400340c5041c0443e4000c42d40d0101e01e110481051101c03d0b5100c040341d40c0807090a03200891058400ca800c2484040495100c0603592019070f411364009060102012005245c2d03580d5038001c2d000e01101510300441102903010003640aa01c904020b5a50b56200d4003100c00c15003090790344840c10109000d6030088a80c003400340324500d20f407200140c01601c0700070004810b035035940b525400600a20703446c400b060300c48074021241c051000300611400310503440140004905000c105d07224181d9400c101d452002c070603800c41e8201001d80c0300250044e840203401c00c0d440042c01e104020482c2440201c0c40c100c80c0101c0082042d40c810007416038040d44201c40140007500d080c482001032a020f001c44036802801841600c00643d126040e420413540c3d201440000601c541d02c0020342030921000390f28541d1070f0715405030f0520345040302c600741c0300300030f402c08904101030780b400320318054061074120f828401204801c40c1101d00c05a4010024482110b0151141149240 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 514086276 1250 514085026 514085057
    0x50904050907080a030507050f070f060f02122b2a390b0a0c03110705100b01020a0b010815070f08040605060f0a030b01062601140a03061803 62
    0x2c44004852640000e400c0502c000c0d00c050710315800007c029030f2213001d5800450315080091219a0141503c0101c3c40c1d1128100100200340d8039018103840259070001c40120540d902c41d809689182514604002940031041d225000001d035002c07840030702d54101800a103225084490441e040080d032414490310b6801c140c011940d01500c0d4203041c2954204101c9000f90031500b83c940445899114010b83d8401003541c1c5c0c0050204084074003012840d03540c0401d50304030740e05000e82040c1910040c50241020055200d0311384460000400c5089113654000c0c1b590980d000b400b4850030507410038085441ca603036501103244c8802410500c10500f04c2d1000015080c54007528071040106016590b5184c00d650b10f81d9900000c0002500840c0e00c0b6082d0600790f0303080c6d9168950b00b400b56208240501065240982c040c01032b4500c80e0740041600540c0a2000a10b140b159050b030440d1041d007a0001c1c50111403021a40781c00311600090803190409441510f800c070306103042410766120369a25036002c0703080d0303e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 514087526 1250 514086276 514086283
    0x10b030304180f0e0316020f010f0203090904110d0309050f0a03150e07081b03071d04081c0f0203070e0901050f061c0603291918120509040509 63
    0x142c46840382c040a00d52078041d10b190300c0484240f000b0900010402c000010036813441e00051075080c803402c0d044103000114200b20184c0d83c1803040a00b098400716986800180d228003c440c5840e0069510300009000c2c00108549540b2000018000070700440c2213040040c548100d40c013680780106590604c0400c1402c116520342c0440b90000c05007030703d024105140c500600f094907444070b078511412101051101c411303c103c030021000d98241054100b440400d040c104016503100c045140b0303018220b0b1608030641c020041c0d0165010383c00c0f542c0c60203801003072075140080040751101d06140c50050011036110354003d5000e6601c07519856807882c006401c0140c0706009001705600007010758a091607a0a2007805407682840c41000010215402180282110f1242e80195140c090040350f84260000000c00071a6102d000d00d0318040794900b0307450b1100e0450691403032400f040d45d81d40b500e205c982c070854512040c1580c80582c03003c0740070824000402680200c01100c2c411860400424060003000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 514088776 1250 514087526 514087529
    0x9010e040b0129070c0b0f0d1a0d151506050301080c120c24030c04031403031014010e120f010c03180305030c070c06030504060b040e0c2205010b0c010b030304 70
    0x14180d1400306040f030300c1c60701c02e4101c0e601c03c030350b02c0c01a41c901080c1580760704c01900d024030402c24944e0b02e980141003000d0031341d241c07000250002d40c00300c0c0c0c002c1c03c00d03214012031604c1036030052a8a1142c852a980744c40007404200c2c4d509074071281c83e100100340709038002c00850417100c030442203903407202006003006102c0050403403888013540310074440b4160b41400c6014111910982010b4415081d40e601e13080f1050b0320845a4138919200040c0038001c1010280108c0340c0d04010b100194110310b003541e400107000d1414040c0a2058480000c540d03250b0b0711550014034142d401030191808206004160381d0780e0b01d102030090713a40d03500303118031301005601ca84191502d0385002c0c3c2c5082800142074400b40c1c0c080d8005003074140b8824080155a0100f80044400c0d03000b030200395070021b000c1c07406090400c21503d0050707299201d907060007001800031a00141c002c20025045a283ca6106150311180e10f007640140c1c68182d490303052000020b40c0011540203850b1b880801e100034810b680c000307420540c0724440c5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 514090026 1250 514088776 514088819
    0xe0709060f0f03150b0403080a110303010b16020d050f0601031403121605070c061106070815040e0f101d0f0607030b030c040e0d1e0c03080604020909010e040b01 71
    0x85142c000b0600d40b0a40040c0722040070b0280d0480700c580c9a00e07481c0c8180c1d205800a136580d4100003038034810130380d108801509032045a8007942c115410446103080354840c440703034030304440d800581460541d541c08110683c05603000e421a110340040345d002c10b80350a407d12090301c0164030141411025840801110340c086c003420340c414803580e18900c1d5a01c90030864101c1c081004400d015880c000f4910200790400342c14551200502412081d05140c54400c0080602c406c1005000500c000e482110400c43c1d00d2071800c8801107000300c440e030408c5141c50b848203007034a00751240c043d4000000e201030b8400780316080c000080d130b0400d003c00c69840765200c030b001c80450700641c401000540300501c280e00c40e21800100500341c3c4c0703002c60164006010b03a000d1500340c8a05070842d1203e6007586420100c40040c10400303194008100c03013040b4015200d46403194011b003d014810300012440d5660340d0403504242c50040c5011042e50310390f0504042c100c3c08480c00c540801e0184000f0804030002c507103041e40d6041 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 514091276 1250 514090026 514090037
    0x4060608150114160c120305040f0605090607020103050703200918040f0f0302030d060e0f100501021015050d080415020303060a1202030a0605280522021503010e0709060f 75
    0x10503c1d640388004c86400015940d2541c0c003840465126119072484061074020703030b0340daa2a42c4c10710072210708081c29030b0f00c0082407280c1000714071202e0300c5000c20780307003482c1c6c0900b00040c0c503517504501a0090a40c9500800e40c100c150b80640c40c001c0c3d103000143c0201002511400500e81e01c003040c01e0300001c81a034000c4c09a20040300d030342d4000381102002c012040d00c284140c0341000c0c6000b000c0d005541c603503002f60501401e400b0806c1140450030240c50780c000742c19514519184e14140010f0745032014082d0810719151a078882c43d031a6062002544020100034002003054085403c0a18481c0c002d80034551501d20700e0807120240ca44004292805940014224600e0310300c0c044503083c4001e150364080381c0600924012802290f109c0c42024881e01c8038002c405440e182d201040300c00c15906007242c07210ba034035007000d02000070300c4040a0000341411810000d488445400050048182c50044002e007400000000c90710b150150ba41c24001c5c0320a413140030550362640d030107031001c18044c0d00c1000001d2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 514092526 1250 514091276 514091287
    0x403021b030c15030403050408030c010603020f01020607170a02040f0b03040209011e051e04020a021e0706091701090b160318081602040f0c0816020609061501020c04060608150114 79
    0x1100c03a0004d640051090500c00e1401d81d88140c082c0c11754210715030519150355140c2f010810360428443c5900340b40b0007440078140900d04044040c022116038005420f00c1d1005a0010340c0d0860b030b83e0b048401411155034125034042ea01d40613860f503507004440803801081c404000040c001c080e400461401c48402620002e1141080103001001c0800c00b0810b1880400001c0c02c407481e1900e200800100509501134a00400c914480300c0182c002e12800340f83d15800190b017006800d501180302e1058640f0f0303e803494140b0103035001050243c018440003509030300c4c0c12001c5c4103412400d184000b10300c42203600d05004c43c0c660003504154090f0251006445100704102c030044035019000c02c80e0325684010320004022000089901c1113503d0300100300c0c00304003840b00303000003400f00454911081c030b0184010805498030580341a142d220141406c01d2072030f4034824000280e8024014005580c2015204109aa079900001000c1e00c00a9a0b03c0283c03034182144000154030910040890649517400b0340c0c50300 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 514093776 1250 514092526 514092559
    0xc090513050a0f06170c030f0705041508010c050316090501080f0a0603051b091302030d050c070801020313060b010327051e010203061206130609030203120403021b030c 74
    0x1c04006203203030005580c0c1d00f210a808043c91207110054840144421000c1941c0e40e601c0780750043c0c090101c0d00c81da00030103a544003e0700000b031a4044d07c1042d90041212440034460f22041803160304045400c0d401d00c242401c0c4558404e01551081e840070078480c2c41107600c07803000c1e5000390050240c03e0004800700c0000d000c0b60101441541c200d07515034000204281d99495035800c000340704554802c5260641400c000324509298010b801c80f124403020f980414dc981c0c0042c0c1eaa144291703c210a00902007219191041c040c4901d070006d00340440207540e01c1c0b0b00400c020100c448015001c4502c2c1e450285801c5055210744128249030103c1041e6041050907010b03d091030040d0910100d81c24400c44403daa9902c19031802c40161415460000d03031241072010070052105403955004400f5440a403c011070740e020000401900d40e008280018040c440b818120b007180306003040c20001c900602d050100b050f034000750a0074510b00f03213004890401514403c064450000b40101540f103640496801003c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 514095026 1250 514093776 514093781
    0x1e0a09060503060d0f080a0201110c301305011b03020709020d02070602270d05030f0f0d050403020c0a09020f03010302040c18030c0509010e070f0804230a060c090513 73
    0x8500000c10303140c602a2a50745085402e03000100448204c000491f03036841c6e040d02402000c14480d4491000f50501100300b111540d19110020805020a203040c2e00d80b1712401d0014070403500e4070104161655a0340f981562000c013000501c540c50004411a6080c90301124010591024980c1640076000303103803038402804069000902d604c801503500b048044002a514401000d2921003010350300e100480340c24080c0041480d81d18400e0182c00c8040750080050004411242c41141000c0003e403541c400c3d0580108038000d0b90032822049180000780014035400045010004100310384460800c0e48031b003900700581c040d030310000008850600052005140c01e0304040c0b00142e0354070300900302c80079101c141c8403103155540c4152500703505690103202a051440b6160b015040108140d1182e0501502c001c000441d0562088200b2030315501081c204000c0a00b5144061070941146c441c0c0e031780140c4410707102d10746e500007110114030b0400d080f41003d0082c40c40c1402c854000b0001c035100e04401802001 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 514096276 1250 514095026 514095031
    0xd150e09030304120504051e28030b040305071a06101b0201262a030103020a03061d0d02030d0e060f0105061b030d020903010b300f121e0a09060503 65
    0x5e00c2014440480c0d26241c2001404100720384075800000c070080e15090049075540412082501480340a0345140c07418402c10750021070b41c0c051020303151036503981011112805a81001000d0124030040002d044c116032400341d00400c0100d4000010001a0106a071030702c900070000d0700340114140c5000095801034864800904480d004071940089242e00210a104100c5034815070048072145050480700750301c0c100349070a80c101c00b00307841c550458002402748421407000610080d11050742c05010480500803001d140400000c84a03a0b2240a0010303403a504200005407070f20b86840c64804052200140e0325002d6100900c10700c00030307420042441840c0e03004000428001c054502c0d4608440410001050903540280005840310b040e48105030a480c01c0c0030419206032018400c0a0004080c8465518090f2881d0700140030320855520755410200039680d8180140901107151040c0c4894900404e40d40c0c5e04519510450114489a0000390040c1464940040c41112040c41a03a010780020364 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 514097526 1250 514096276 514096313
    0x140633071b1d130308010e061305010906140406030c0b0c07030b07020a020a060f3501032001020706020d03090317100305070501021f050411060d150e09030304 70
    0x41848000103001c03250044581c041e00550094030104054070404101094000c03e01c3c0040014011494a0040440e00103001341001544440302140541c0e481020381101000c04080c18855980c2d298400001004c840c072403007441300c001e00b0135407c461070580314100582e9400114082a142403959019043d00142d1010701a0310440c05d0110200d0745101900381b0a910503802065555260f01c10300c10744541c3c0d54001c1082c44907a00440d031000ba002030229002040c1d86030302509070381100e06001003600b191801800b03100d51102c00481440700f285c4816040043d001115007501174254012170340c0d600c080c03040307600580200c0d40f0f24010a00c29080320342200e0092034100050120314000d40040c61050310186401d20b05400204108001400203100810090000d800c0c02ca51040e618070140031007200070b085182d5210f00040801800802c802000d03d0054113041e16019608442c8004004189902c000710140706000036051a803c1a050700c2512107030051403c680300e550340c02c001d14070b040c039845 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 514098776 1250 514097526 514097543
    0xd2a120e0a080d0210061d07120f0b190f06030b0607021f03050105120c130f061d010e060a050906120607090905010e090a14010b030114063307 63
    0x100c00c560755561100c40500a02d1000d0102c2c90703120003019291425a07404184094100207082006401001c4c4985041420f0700d00e1001130740e1241c1040700c00301544445003600914101c040b1800c8120f99000104545040d40d101a0146103100c0341603080d072152107514036a054a0005108152198000782d03600c41f00a090b041c01c18150b80d0005805141c04815900c000d88450078000805134140501e40c01013000381c9810544014480925032030321035a09046004913070511900c96441e02c50f502010820440d0303172040004036100c0c4001e03034504017000c116680d41d102c03c000100b00c0c1780c075003141c040c00740b08000d08180c0400e240c8018000003003002002c1c41d03480200030286100d190002c3c803990f485000d10350b58204d00c0500b4041000d003103c1068015100d1000b40b6410045040000991000359030703040701c0d0941d001c0141070510340c00340c40c01c2e048158065007010380182e081081140058003d280031a0340c3c0f03440414480f601165881d0f401d003d100c1282003411140d50390f02842c001004230780d0240100 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 514100026 1250 514098776 514098797
    0x110a3b010314090d0809150714070f03120f06050a05040e030702030115030311010e060412020a02030d08220f0b13080a0c1106160201050307170c1306050a08010329090d2a12 76
    0x20540bea145641d0700f500070461081001c0c05050b900e1140000c00590030504204a41c148008540454030a000720ba00071980c40f00500b0a880040043e100404c4d4014000d01c140603030306030007840380d0800780f20880200701846010815800180140031148a0400043c60143c1c0c91340c4803059100b89441c01c5100754014810b001d03000da00c0034003064021950380c0c2c0b80c052072428401010107114000036540102c0c090201714941c0022894840001819042000c81c800c0d42c9507041704031520303000448004c100c2c9a00141d41910755401075501808030340100d0701064140185410b2160701c1c8a4020f00ca40911504071a407001580510080c42c0c102d4038501d07196105096412511418030000d030f40d40d80405c0e03c04a4070707050011701c07804410301601040c0b6000d802c00c3c10b190744c0a481c0c0401800018400103003030b21803403407042126040b40746000d9400203c0300c00307003410a0165200c40c10180500c000032207402440c50888801054804040b0078241c3c440b58030303d104d0315031b0ba811042c407610901c20462003119 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 514101276 1250 514100026 514100033
    0xa09080a0906020f030a050f0309070503061501020d0309030e13021605030d0f020918040305090d0308090c010912032001110a3b010314090d080915071407 68
    0x54030440455441d08020103050810191a0030840c0f000c1d103c46500800880c500b51b507020f4280c951506031520150345907100c05550741d08000040c0c001c10f070148600c10800c1040e440c81e4820300406902a02900d181648014041b81940c10540300540491000d00c14800f103403d00b0b001095a0100390300d030060411210a22280f590810020255065030012620101e94561840303000701d4200c00701d104500c0d15618101180c80f604501c00203200c11410000001c00b45030186048989241c0003c00060240715039140c0038003101c2c426100340300c1c1c078803540300741c14480d502900f5508207540400080580300c400325a0708444030510070b080e100000600b85404031489000340251282005060082c0343c86400c822002070030b28000881d044002401058110090001d8904211010091700c4030a04030301d04150050307015048604203041c500d115081040114100807907644454025036454412903281c989006549908055020405001ca5000b1560450042c0300c013010106544a080381041314071348 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 514102526 1250 514101276 514101293
    0x61c021f02070e012607050d0804080105101a0c0f150103150b010e01050d2c19050615031005040c0f09200906090405180c0901060c0b0a09 61
    0x108140c604404020250010640511458018144442843c1050340c074102d500442d083d03400c0500c43d40c100900181048000c4203200c02409428082c02c2c0c41d80b031820b80e20385021640e01c0340c81400515480c00c0089904008090403c00031141e420200ca030b48803d80c6a60a00c2c1580490595402ca110300c540c03038070045005100c2c042541411990344070084d07140d814500c903540c80e0100180842d038036150b840111aa009664041008400e00c2c6c295102c08415110400404054080c40890b032101010a682855040480c28241c034003401950b4500e1200c45224130701c1d01607200c004105030007413000905004142030300607041341c200074111055548191a81012100196401d45103030b11041800d00504142c000d1a500410342140e00700102801c001003621a1026920113800e100b40014007040745589060941d022440c0c010410083c0303080103c950b0205501007204d09805001e20a05090030303103014082c00b81211500c0d160416004096520111010802896040d0650b0340d0404800468100b4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 514103776 1250 514102526 514102549
    0x12020903100e1507020f060a0f060b1b070b120a0903050702060a02010207030e010809030714073807050303070f03110301030b09060c0c031209031605030406110303040b061c02 77
    0x46020f45202c41c0f442e040c26803032440040001c815036110300700304545007000140142c0d020b0215640001c100800148007005400558402c0401c02000705000841d544103a10202c40000398100f11894680c0c0d541d003804960080c0307040103503601c40c585d001840c818666000f10084900c40d15100346490403540c0000d400d90400c1d11041d0050794040781210800d900140148119402400c1c0781039586040300700c096903485030000c01003c00f4480306030421002401c0001e08064004c0014040c0212910803900200c06021001c0c0545260100200b0703c110500d041240c20300d03600100518556030712164285c0e8640c0e00d90002c40d04243e52283c8400c1521125000f65020710310a00d03c0c0e00c8541022100e031860001c1c0035004008045040020740c104200010403141c0c60400d050030055150f0f00d0b0743c226400c6004007241c0011001d0f0403c02c500403c04040001c0003540e1044e21011490518000410b64038001107400801443c2c46401041a910f000e40403030681824050481c00e960600380d011a208c06081d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 514105026 1250 514103776 514103801
    0x4090506191a0f040903030b0306010b0d11071101052101030830060f0a050910170c09191b08070210050912090613081b06030402011202090310 63
    0x14881441c07041d6215001d6500c00307039081c1c2415002d24480100003080c0b50f0078911158402c5540380d80c0f590406000760032848900f900241a07500c10340e992550904240c1c4502054000185010002c40301000c031070f001c1d038001c0340d002014503940f24802c00065556074130202c00100e040f5404810070310040d2041d02d80a02035440f651040751141c4070414004001102c00441381340440c00c80e150b109001d450109540ea0000013142d10354031404500000c45c000c403035607400c0070b030700003c03180f0811840c0c0c010031000c801201c400000c85440400c0d890a190780310301d803a141255020000300c001c1107411001d685900410a66010000303080984c152905511422a80c40d20012038521410000c0d01d940501000801d4402c040041c0018a400691a07803111600000405089008a107180a0b40c403428141c4007103e00c40c0340c2c4c2c0c407641c035121400e166980c00700101c2030300a000082140c000c0342c00c0031016680169410b07101d0318180c982e5090210060b40221071115010300c54811580902c140a000d01e40c212240c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 514106276 1250 514105026 514105051
    0x405010c09121110211505061c0507050c100e010f06030506010909241a0d080a0c05010b04060b0702040b0f0907030c0c0c0e07020709050105031b04090506 68
    0x1400c2010303022000d16400a00344034a980048404280010452501ea02089070340c040c2c4000002d00c02c0c1d4249078018103201c00302c10854a0040d20499135400041285415403021880c81e40e9202000f07454402c25241c200004e03802c1510014500c4103401031600600c050a0144c01c03c21400740d03a5251841e02415026266114120700c00300c0c25082c41100c1d03032a01c400101740300c45415a151155500b0040c0b14000400340d42e4a064814856241e51490070919080003420740c03400141c507000050314031002500414080141001e603603242200b0b007064100c0d40311781d01e07a080c0a80d0074016520300020703910075a01552103903502c140c203a85920440001e021048031454a0740094018007007190b83c840289405209690001c41c5c5c2030340c6003221a980310002d49404544000315103000c950300310707a800b07005000307601034140855030000f9149651f1107001542d084901c03039070356504901c00380d407000e1140b0740e01500010181050b14034004104a1240800703040414200040d99681349400340854040030b4584 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 514107526 1250 514106276 514106291
    0x606030b241207050105070204090b0c0d0e16030308061f05130906120b0406060f03081c0623010201021c0501080d0e0102071701090605041b0812070602071505040501 73
    0x55419480000041080d2182c4101010030190140c2d0746040303014180c1405404100710003150780c3c541220b50460341c040007164050078110300882c82500556201b00c2c0460502058000c2e0041c002004150105400780da402142e00e036413810b89500c3c0f006840b068206011424800d69022000c108280b004110b035106903840d051165042684610368025840560401d40200003400300001d05442c4507800c03004d020050344032480d03c24001d04203a8013624101103908400428052450081c0c0300c011005202003030b11035100d000c0c40b81107c006018001c4006080b00b00024182c205c1420b1140300e20f41070000628120101c2d0f02c00c094038200702002010180c40c0d000500c85030005100c6801d140040c0c1c100031605504410020b51206910302400f000c1550b940341c0c54025003000d401803c10b640d009001040b040c1018102004168107000009039107908404002840795400036060340c205001203047c1d404c203004c07955164040d43c00030f4010340c0c140e0b000002c1d84055091a1003910b010301d119500001d04117 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 514108776 1250 514107526 514107571
    0x120a08090a06020c10050a09120501140a05040c140f0402190207120803060d1e06050a060b0703020a1e1b091d2508071404050603030a020a06090606030b 67
    0x1c51504104115000801d0024064581c66a0b901c1c10b2500744c1400d948070b00100404440380d01c200c0e4000d8480100400400c4140901035009510314401594012031070b54400020105844081e60000d03c0400240010051004191440305200c1c2d0010040c030407603400400010240e8103c5540000512908454600d00c143c04000c484001c02021890309020701031511110414000200520b014801c07400120301000020000910304060200f2404941d00c0a810818010182200d24160440c545000840c0140500c030039580c032140d042d0300509400260750f4646558110030310070b400006200042d40d5000031403007554546214203060640c80c580b40b9040070f000965507541c00c1e03481c098800c108040e4498002041c0c5100340c0018291442824205c2c102e182502155948101c0c4d290050320b002041c1210380c1d01d40301076010400c84051010303844d200205900c0344680c0e01c0d4900507034041048540002c21507001041001c1c06100000b0b8925500d40f030796050240d00b164481030812428880c00f465 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 514110026 1250 514108776 514108789
    0x200c0d0c0e22060c090b0316110f0a06090602090301050405100b0612180703050106060c11030d17130b0106031d0c0108130c0b0a0507120e06030402040506120a0809 72
    0x50030400810081c0b64294240c11035007004481c000e4825500c0e400b07103008043c0039684034002009080310f22a50f910f402c2c402300e8070009821081d000021041007641d0074003c3d00081c1d1040d1502d489016015801c02a81e841d80141b02d1903000f02d40003602807200c44c1c0c0399582841090320650150001e4810059849811400c50b07003d622124440c600a0040c0c0c0301c0f9040041079203500148101c81018000002c0903076918018031540018036941c200315010030300c0c9504c40d403403500441c4560006c0201910180030075072294213010b141c01c0010b64004a5042c5040360708415508029110845070300389581d0388500030884000d82044021030340301c101c500c00500006041c082d80c00701c45009400c0510314040000d0860201510305405030b000d58005100f400800c07500d8000410013076140d69a504001480580150000c0b01d09860099038881031850032805076142803407202d0014520b52569443c1d0342084018840585255041600040c0e41600040c0800c50411000c2c041c00910342c54041d0401040034 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 514111276 1250 514110026 514110031
    0x20303070f1502120a02030a090501050a1506030614060702120319081609051210090b09060106091202131103151f05030a09050a1209030b0f040201200c0d0c0e 70
    0x1070b491040000c4065a0480d041c095040f0203030540140c0e50f503c0d03910355440908103210b4050300552030b00052081e1814180e0020f60704140f0641a0300d0b00c03654904066086840350300c02e2903102007060780340d20514981071008081082c4010b0039900c0301d0000a402030302e9a04020782003003000185400d0b070a24550454085540701c40c10513a5400c00011000c0001d00007039180c420f00d4010001517010140070716050000c54040c004031282001106030b41d0810300300211045d01c254015000d400008501148a4018003084d03940c83c46040c081c1d1a2254203000509800e90a0b081c41580c1c1e448181121521000040d400382d04094030303d0100c45004820043d00414400400c00e072030403002c115145450b003001c00e8960200d0070400000b00d400d400e09080d41009041c000081121481680d5190074517080000c0106170b902590000100380d03201d80c2c45403030800040c1d0300130340812140700e101152b0750600c0d50b55410503010340703081c0d80f410350000d408251071420b241d0f422a40720071041c1090141c0100b01c3c08640d03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 514112526 1250 514111276 514111313
    0x27050d02070f08030901120e100624082a0309030d0c03020c070605030406150305060f090105010b0702190503191502070b011e1503050103060b010c0201050301170a020303070f 77
    0x4140c14581290030b031381e80c8210311016060018400d6a07004041c0355070700610200141a003520042c19040045078000e04183c01558103610303907481c4c6610586080541d1008040d102c2c2c41d102c0d81c0e62580c240d00191010710100706140c15113041e050740040843c0c03602550040b05020b00564441c00324100c1c0302d060315030f10314507001018030501c00f4242ca8100041c040c4200c80450406680d6621281486005401c10030b0309203440b5405d19000100700607002030041d104100c01c0c01001a00d4480004030340c00c3c1d86080c410301103285014040c1a01500c5c10384142d21180c01000e14507058640d0300c07000300c3d06144040081130542008000290140041403595241c1c00d40844070031071a2060a80d00c44000e02c0041c010252840c1e07400720010308207002c1c0603240000d040052035001c9800084080100500001d00003114003c0c00c14880c0c82055004880d01c5a01a0f4141c440c14210fa081000600b0b5808250142039280d01c980c008000150702c041c001042840d00038080d0300680c045a046c60028402c0400921 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 514113776 1250 514112526 514112549
    0x2001110406030b04060e10050a0f0305100b01050c06070f02070f051c0f05010f0501050a0504020304110105161b0e090a2105091305010e0604090b060427050d0207 71
    0x4042a000108a03000e60707819040018400c02c1d14804035008203d140c12251a1030061424402c40c61a200c21990880c0c070200c07640320034551200802508503485200041c0168020a0821078086241d0451101510180760150800c41e00c05005454401c00380c2d003000101d8030038041c0328441c960510000002d4a507083ca20542d40c1d2520001c1059001c0741052014003400841c3d5800030001000303580303507120b50406c0082c00101c001602c9500149020703c07559215011b89a00080c1d10b040c240243c0348030301e80200301d540d0400012001520254054459412082c0f0314820709070009110759400c2c54802441314145c004242031521220030450041c3c00c1c41c107240d02884400c4005030380c11054001d00035802400c50f1b2020207201d415101802103460701580a0f9a0703007484000e143c800d034050350484541e41a0040a51242400e1104440c1d1404010740070b02040f02c0080d46900b0f064000b031081d282c114280540801c4515440d8070400c890000c1160590404500060340b25070402c0f40b48003500000200c0d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 514115026 1250 514113776 514113791
    0x1090b060f010f021914030c030c240a1a030f0330011203141c050106050a050403060b0a05120f0f1603140c0310060303080c03390a2001 60
    0x43c5d92803c1d42c90f40c501580c142c401040b0700300b0640756404aaa15640e20449071607241404506880b038001020102c1680715a1380340003018004d440c2100240c45808031030001580302d2403c0000a40307403208000004501210b04902d1989003003001880d8010700c0e0004d1900d42d204181c070520032110740031510407101d00030080b90b0b81d691284400d0302d044500c9401c4401c3d5042c1903240503141c0c044080141901d1481c04030390700c2c070000c005030341000c4d0701d0b80d2401d8104516038a4820075206400307200d040c0070004400f440207100040655001000204005007101a0343e9903071000505402c80d500b814089503041580c2211580c00100003440c1c600500a000d0507606201460480500e0464800039010182016105614060500c02c0035607682028060b2443c00d21120301340006048140301c01c50006a080b400501c022088005680c050b0104200f0256858540c0030084a080b40200003504600b500894150320407070344800070409415180c58444040700107035400958002060341e01c03081a41007101 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 514116276 1250 514115026 514115057
    0x2130902010f05071e1202100c050a1b05011d0d091a0901030e0a200603010f060309020303040905010305061b0306010906180b0408060a0e03041215090501090b060f01 73
    0x81061021200c1e260450711848541818505a06002e17804407003454400d41c0e4109003c40000c091084c21400d03000c4a42a40301c0c0043d01c0111200c1a088400040c41441810659480f03040c0e1200440907610644c5034078402a252a421900d100c1d2042c040e082e45000311986540c0280300c42d405000302418070020440c170b003840da410400392448030290720200c001a901141d130b01aa00000c00c0044040c110740505041e4a0180240304490900b00c0b070081d20258a06120f240c0003080340d0584041d1408800301c28a00801a00509220f0310204c1c5e050105210110b403074440c0d80315050003540200c009040b00d090191400121210007546440c1c627074400c008206241c4d070401c0300042200c1e11403502d0a4524404925035803062a690051000d4400014001502020000d005802119410410010613910700110fa80c3d178402da105004c08052900c540c00042801c0c0d0400780d581c5d885840d0086400c6038165523590840c2d060074400c4178049400824030116042c00711807050301e06400c1c204070019201c000c8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 514117526 1250 514116276 514116287
    0x509070317190311160b250c06050a1803170703181b05030f030d0b090402031b030c0402310f030f06110720040515120a050f01090213090201 62
    0x5011414140c48039513120003040040308031941404c0c2c0082c40740300d5209a1420326403445013510000d00010b18108224140c07000807001c131320f0b094600c0d19140d01e007006d55071b03a01000d0140203085144040d13a600d4940c13100c5451203855200d03584a90f0f00d002400a5030b403808070060301c0c09002041014500340400311300c00c50300f03083c1201540c0c000e0002c12010159055034905080660070490301802036405000f95400000b01418100315124024407a20390140b081c04084441100d010b50306a00144403140c60301420200040002d801a01340c80c1e0b414801e0010405030b90003c500324807007007071204801d10104031180d040a040380c0640d80d040d5101d071805500d001c448420740000b8101c03040c0b5078200410405540d20440585c154209000d44641035820085c41d94041c17000340c10066035040740520142d14042c441c45200d541c0c0d0141e0010520941c4085c0401840c56441018162282c54820380c0810300411a8000000c2c0d410008101203c2c20b2040c0726910f031005407400c0407541400401d00060b030304a03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 514118776 1250 514117526 514117567
    0x20d0807210207060902030d050912030c060f040c0302030703210807050a05210901020a14122403070f06110a08030109050601091706040b090a0209010e09100509070317 74
    0x41e1000d40c8400f418180b4200030041044000d40c03500c0740010030864a031304070340075010402084403007115405c0d4102c1002c1e164030800316800e2036a0401d0700099441d4004101c480d810600800c042820b00e900d950110b81740000c0c0c0d13041610300d140c4400040040d00c0111026401060440c50000300d00d080000d0050103c1c0a6400400305000002c6010588600395040c011000c0c0e0000b0555507031410000c1e8454001c0d40424110000140e050081c3c1e0410140d8004030b078080840c80903a10130940d921a20184008041303540c8030b040240c8510542c0722a58200305175400381401c0c1c0b100c0b000d100d00c2e02801031311400ca40341c8900c1458110341d60710b0703020440302003c0c0e81c11100f0125001c11640d45d8840100c60800783c50b0001c00c11001200c2441400c0c400c0040d42a1240f031150081d081c880d01c0b0f1015081c0c1e91481454001d6100ca1408014000701102c180030a400c16032080846a00200b28403c0000341c44044980440552149004100f072041c1c42001e00d004442180c040c0e450425540c96090083e0080d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 514120026 1250 514118776 514118837
    0x501170103021e04050a0204052814130f05090d020c06040e0604090503040305010219110604060b031c02010b100f080703020702010905090411012312130c0303020d0807 74
    0x1101c031101c03d254040301c1c2c020320310b90010b100b00b080b85000e00b02c50b40250405d0085601440800d0b043c0701410307207003000303040720440c0c16094001c0c000e00d4182c04d140000c0c0c14855882c5c2000214542c0300301155203002d0900001a4254085490700e840b00c9040c5c03a141c0800b84410466100c400c07400080c1c1c64000c00c850658811441300b10303680e5141000f0801030402c01c8c0c4d0081980c031001400000340081035000e00101846160700c2d0415507040001120403122180160041d900014003007000200142c3c0400041007028080c0c030b840e108a00105001000b4140030440581d44410300e04010f0b15003061a45004d1a07142021040e2030482c07100240080780081081c0709240e03000604c003056a025204400041400038a815401d01e010b1414440f030411035647c440c085803000d100c030340c0303110800c2e4010f56060400700451824000c1c80c1221900032003000d4160b5018008414030343d000300f02d84204103c0030358026001003407201d00180006220b40c100030009030421103100c041c143e00560310040f44418110 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 514121276 1250 514120026 514120039
    0x21070219080a03090e152101090c170606030a111e03030706020d0516050f0711060307030203011e050d0201140c0d08010f08120901030207150e06040606050117010302 73
    0x1014000080e4969402245061081140e440c040661051081d401d440290300701e24469250040c0d1301c10b9007200d8541c8140c2c00620203a151194544040d01c03441300750380410012030280c2d410f44620124101300c0d040401c40e07190104150010800400c08190008015001004601c0d040c1e01d4640c4500d40c07200c80c1c85d2042c0f0b408020005507400485000a100030001c0607070381d992859103040c800035030020f030f40d14503421f0400000030000001c3c0c01d4014080b0300152901443c049084d100108958858001142c0390700386a100b16260380c644001451040c482a180103a07654144921802030000002d10b480c010310408800348401c1e22401d056410305542800c00242c2c0360300d29000100e40b0700804507007107a035109001e001203500c1e80c0980302d14100d410f1182402801910790103601d4035400c555a0081c00341c5001c2100301007a52103680101581801035500748245506046903d09480d004030383c05100c0d40c0300e13005000500c1181d202d0387c0e00820007401c000c1d408802100c12801c16040502c0060322403031 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 514122526 1250 514121276 514121299
    0xf0c05180d020a150804020f0303030603210d0204090507200c060703050d0e06040c080102070302190303061a0301060801151d241902030901121a04180203210702 71
    0x103c5800180003e070600c005a202c0c3d012020704010000c03c0c0448041e40714041440f8035084a090200c100c1380201030140c0a400c42d40b41024528540510281c05001c0612080109607036040c0c851029001a142d01000840c03503042205000b403000c140c0701d0303500a2903079030284204410140000c040c004810103035107070798488440341000d49190054181006440b414550030b448803a0000c86c0851040380319046541c18682c0340d00d0594201e028a090003070250f4849100b00d090b81408050026120344a13280c08283d490300ca5600301d102d049102c5c075a910002010005010403600500301501601c6100c1c10007804005e401e10041c0035110003030090380e1143c01c903030340500346483d00d0080d403859500004480280c070703a10f840d4480c410740c4150a0300d9221b105040c21054a140301100f10f4000d02e20581d1841d4040320030358032100003050b01501401c58540c400e02c0d00c5125850310f01030700d614801850400030300c02c0020700505049c00b081d501e02e0400c104c1907880183d060540c00c4240c84a50742c05030382402d05c21 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 514123776 1250 514122526 514122529
    0x70b060102160909050d08070f320d1a0108040803060a031205090310020a0206010608070201090b070e180105100c0503070c0b0903160503030d0504081c0f0c05180d02 73
    0x2030a40d030300000c6805402c82022400010b41e40144005611030400c0301e024089880c0b00700e8840030309a568800140b5240d8241800d00d1150300109002200d94203c0d074040c2214820300c031400701100b03880310308401000c90181c3c4603414a01ca44403107500c0056990180c1102c0c0c100092043c5030040c0010302c40c0c0170102c080f950948504c0090400f560344050201c8200300140c0002d0310a0f04036400c0c0b21721a109000054001c00c0310342c0281ca0380aa1a40c009054603400c0c03400640d40e042008192004542d0380c4d0030b403400410580c03035085004950540368000c2c1042020280b0101506915241c0d03000054440100460344500c600724030004118a440702501c00c0c80d14009003548201c09010380100802c1001143d4494540300814007154100d00f00c82040308805006108144ca52082a5050300140540e001d040502d1b00b080b903000d4406c02005103410340903424100d50b03c003110b8680220b06d80d25003c00960b110140315a1241200906005080002c82180850104801c01205001c0d000628211045 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 514125026 1250 514123776 514123783
    0xf0a020705010f0b1009030b04030c02031c030b010f02010e120f130f0e1b040303050a030b0405100503060108010605150a051309020c010c0801150c1721100605070b060102 75
    0x5959008000344180b2075074001d80c1020300084c0020728803840b100c06200c900300e030103440d01e1030890340c0c00112500300c0d41d40d03524240c50840076288140e0f014001c1c0602d40c454a0312040407840c081a0f5901c000401c4490702d0b0004281c049180092030941e031423705040040030b400210165010641401c2e196107251034036540b2500c2c0190311140525101003100458040540c0b0031000558141d446904100e41e241615507000f400f20100034040074400b0041400403d01c124000d082e40281c40c10702003028085140802c08a600c21588140441c05043e018440740c074007030002d9801000410000e0040c1c81c00c08001030310035010702c00008400e0340000340c032101e202e00550030b91b64481c01100d1307900311036551295004080e50000c40d20001552910903807102c11406444017a0580d402e01d10312040740581c0b1a4140c40542c1400000e039a9030b19515440441203100d94010300074480460000e800303185a00110300c0c1417030f03c080c0110515070351141041c4219680b11090f9584c058000c180c544207030312890300503401d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 514126276 1250 514125026 514125037
    0x901060611150702100e01050603190803161b0803060907020d0215060a031e0c08030703050a0c11030316021201060312211803080f06060414010509060a020d180501080f0a02 76
    0x401d806c04800040d69441036000340d1062a05030140c0e4112070078450b005800c902e001c00014004042400030440006104c0100055004a82421304695203600620b194103a2038420840e402c22000040100500b41000c078903802082500050001c118110006500c549910001101c0e41400100140143e0b03030380c070034a90041d5000703400700c034000301e400161542510010714151546140581c000501242c008125400c0742d40607a11036003081404c99007240c41d019070309001d8039652a42c404031652541c052000701050385a440548140344624414440b21607506010718205e6454a0810030124444048068081c201c0740b0f446450700b410400c1800341c004514000d81e04403460151036200c80102000e44071079240c000d4071000c40c1581c4a51942003180d8003150f080d40c00c039509000030084003401e2100401c171040141861414824682c0105200d9000203408100503030020342c0400b038244d04940344010104c0341c2001109001e0500001034041c0354041c19080460028000040525070154103948 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 514127526 1250 514126276 514126303
    0x606090301020d0501080a031103180904050c0a08100e011107030318060c05040515090f01050f040306090c030b01080a03020c06030a2a0810030507091a0a0e0901060611150702 77
    0x85135507101e008083da00c00c40d400c0224041022214203005a2100006441c01d45001150f04151501404240246403c02134800c0300d0307604c00c42510031031079558404050080c101020052801e00d100e890340c10152a004580300b04140d1401c100444c0104400046070240b5400d420301192088601c401e03001c007050000c8000c1c180c03a20740403a400034940c1c0030300204110383c0e040350840c00320358180d500d04287e84208004568840e416903801030b4254001c45c06418000b0320850650305090380c944030f80007034400c840030031546560044810310030020714540d943c1c00340918130020103000d0350503038001e540e5042010045100d0310f40440003503207100503034000d607903980302da4000000000c4c1814903903036440c540c19081d000881c00000009400d00c0d418941041100d0b08200201502d6103050030850080c4030030342c024410b03019032400c244165150403007000c0c018136207188140864602650401e0842780703541c00002c101700d09068910b20603400012144080c0c0030022903140e1701c3d256210141e103490109620103 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 514128776 1250 514127526 514127531
    0x618080a09030312020a0806090406060b0d050105150f0307050c0703021f090e192a0c030210090308010b030a0b09130614100b0d0b0d21080f0606090301020d 69
    0x40c012648041d040e42142c2c826203035082c03145408001c4105a0182c1d00700d01c00007541040002c2e0103890054007030b50b0044e0080400280f05910740040c1d000075804410048a451f444a0041280b800e182c1d000645001d0f1040d20035041004003946e1f4040c610000c0c04540812001052008221000f80300c0348005541c014442807036a2404482c0c5442c0e160b500c176070200400c0021070006054555841c09622034421240c1200307401c0070401040000307050b00e0002040f440121840e080c4144071102d00c0d400020103e071521400800f541c58000c0ca01542d0b8588000d45030b040041820029800009250544021002c62034a170f543d091001c03801413000d552115444510304092000441c4851041c0442c90b010341814450700151a50040c001d66003954094298042210b0800c007012410300581190511220041085140345000800440d000d40080d81d440705c1010440c1d8602c050b102c05c1030140c0d110307801c1003110f618200e15650707212980185894041d080000c0c44060550742035045620036030900e1004c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 514130026 1250 514128776 514128787
    0x10e070f090b071a1302090c070c090606050418060806070f110106030809190506030606090a030f080a030f1b050c1203090307020319050c010c0f08192a061808 70
    0xc40d1028280f407640100450340440450042685d50340961407441d00601855196243d00c1c0030040c0c0d5a00c208070690340000c43c8000030621090714003a5900070000da56860740c4641c04d1001c41c2c44031030300307611100c1a810310341141040130600101d10b290780300c130f1355060018076031904281c03d440003205032400c054554039084000c400c0140c41c10151102c0581500c11498904641000980d0b030000c40c01010341c4508284000703401d0349840d100400e0201c4000e01012207031a0740b40e80d41001c2034150350040307d1a000105411082d540e041c41600a001c90024050040c110509043d03499201c40070340360000c0180008980600c174008202804210388955001c1c0d0f42d034a0003130042600d84d0400c8108034824001c143d18609203100c0c01c4c4d403403031206421001030000941c0c0c83d80191340380e0610040480b0080071440c003420124074088094000c525801c030b003e0811103480c0500400e05044140429003142d403200800b031400140104086040e41d100c03400141084204101d480c020035040d800030030000000a5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 514131276 1250 514130026 514130033
    0xb030703060807080705031917190816051903020c0d0210060f0b04090b031e0d031d0706050f0f1b060606090d031b0b130515010e070f090b07 62
    0x1e003207844141c1a601004d4580609030b803108020b01c02c8980c1a8000c540703149052110081041c2c0305071054555003842484802c072280640c01800e45414140c100e0310a400b8031981007008954021456140403003d442d01401c0604103025800c42c414a03501100b14460742280603a0488003007580000c100c520b005031409009580d526503074000104603060030000110505880030200644825100f80d80c20542813140d40ba00504e007487c0d80d541d041c822004480c820340f42d121722644d405601c4002500b8101c607510b034080c0a0b680400f40c04800c600526400310140e20010501005503095407421682c0c4900040b5800d2181c0182c100c6500039841c0000d50464005a603451842005030742030035204180d94450130010140110069141c00115180840000038403070511042c00107040000787c1c00300805a1500f0501c030380b08482c0501040b810390018001d1000170810a118104d02c2c141c94021507042103e11701646902600b2807040c40140002460814015003810025201d0600360070b40f2200d440c02c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 514132526 1250 514131276 514131281
    0x6070605101a0702041103010f0302060d0b090f0f15031c020c10090314070b09010807030227041113140d0506090705101706090c0903160e0c0c070b0d060b030703 71
    0x3e0040b4400c5240c050001541c01003082682e0484d845c043c01500e4403803654003801016441240307510095650361300b07407404c1c5580c0c0328620360203004501d009800600d40205102904074002c0d05000f00b8124410054a05680c0001c2d82c20b0341c080c5451200d81280c0780c940702a0700d40f170840c0725441e501c402000f2201c001c20758030a0710f0f4801c507070049511500030116243c290b07481f45440d004070107209008000e000c0055005680c80c07500034286113001441c2c40b4400300d003021419101e4080c4101c06441d120104054605801071140c2010800390a0349440ea600700d10703686150349480f1741109015184180e202035620b80d504140b48070b4204042e60141d01d01003081c503446220b540075440c891040d6138109a80c81e4480c1c140710b0100d42c402c9009401c651688820442003000c01054402017003400c200441e5151000c0c4070207129841c055020041c22428040850150340d0000c00c5500107103018031003000040400101d84c400c03030b0310240d0880d9950b084092a40b010313100513006100c410400006020103180e05a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 514133776 1250 514132526 514132537
    0x150d020a1b03080c0f0904150306110f03060f01230d150303081f0b07240519090f020604030f05070f060509120c0d032c06070605101a 59
    0x2592184200401d540103824648a82a00a000079601a00055403010f5500042000c40ca80b000403600f020080c000040c140c0d142d5545a11036007022000c10003c000c10fa00585100305d0480c1e90b0b8038140720102040d54013300000340114031401c540d10443c0b0042e40035600121681119540b041d50091307330702e0741e409015482130f600014a28503081c038402450b40204410b00c1901d62554a4a00c661a2000c280c50304112207407092035012170991001030210001c100801544e4460400c0340300000e07130407008010844540d4002040c2c00c0c2030070200110850203d8451005a403846d034005460192414181840c0c0b0b0301d103500a421450006000c01444000b0f982804024480c004503040706484011800003900d0f98480e110100d4810f105081d038905d001640c00000c820400119881c0ea84940f00003445140803c00a6011070403a86008903441300194440300c081c81c2440426810f44020008200f00f07106047d07000c0e01c82c940e00c0c00444c08009000b82020002c2c01030302884400c04d0340c0c90f84c0c0c2807140d9000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 514135026 1250 514133776 514133797
    0x31d0d081c0c0e0108060a0b0a0f09050f0a0b070f080d1409010c0905011103090409080903060c073c050c0315011a130e07080126060411150d02 63
    0x1d034485204004907020b14116040180c1c1c921200c40c01030030041d0360030700c4090182503200300e03690004203803812080c0c003900f85c0c004650707a40c210405141c01c02074000d8070103400070760244030211590078268032100e6980d8100c40d001c0c24501c0c1d64041a080c501452020300c1c0c001071505c0780015050051040300c1d08004407564420fa6401c1c420344502000310b007218040920b82d8085910484104429070050380101441c503283c900340d903c0c181644001508071410420100c84110000c6100796580c1404c000460380082c084240e689042ca80c0d44030040001040d0011704031501c0c141207280320a0078140400824a480b1061007415040b045c68401d4951080315281e60207071103003240309030380380e1030300001e4038101d450245c002455403201e080c1c007800c141e2110f581c80d04e0801618030b00040074880e068880d885580c4560700c5110035410055140a01d2450103a41e611081602d024040d48070004950190411303404020408080015008070301d408400c9054100702c544081035070a0711a00c40c3d001001d40304c51 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 514136276 1250 514135026 514135057
    0xf03030807030c0c0b0a110304080d0501050105070309031113020c0f0d0e0a0e1305030a031a0402030118050402030717210c0703060b040b0913021e0d031d0d08 70
    0x5541c0011012241e69001c0100055401100d44000c0b03046003d0058200c01d02c0c02000c1540c90410640c0003480d0300c2942c085030b6580340050042c00d4130034144519070240c242440c006181824035140140100300c01d0001501210b10b642d11681a03a441c03030041035001000b0358003591291050b41c482505d0300d40e0700000ca984c500440c407103014060b00c03550b600340ca0814010000b002c5242441e504800b91075008221100f42214502c036000030030020000350410311070941c0c001c101c4014422040b9500c2c41506403039070027035005000500000086031400c10250f0400780c03000940f5038490000901c2c000c0f007540400b01d125003e041c112204a00815210300e04025031820b900caa561160a0000e6881400c03051200c540001d8000d00015005410030410204010808100228124002520884241d0b528104550702d0103040085013000400c2d42d8417811003c2d062541c21030b800d004a41c601c403111100800700114500e42d2800c0340f030a13000c90012014003801c08081da0707006240ca081a54810000540c40c00d9 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 514137526 1250 514136276 514136281
    0x91303021c02250e0906040302070503060708070804030903060f02121302030703021908060a0f0c1106070e0d060c0224060105040515190f030b0406030c06050c03040f0f030308 77
    0x1c00c8a150080e0604a5801090300c0241c0312203220822540241100c1021041000021580c04108455000c0c8500070050122804c144c41c0192425078954440c40c040c1d040700c01000841c540108007a6446480d41c20411041e640d2441c0407150034043e030f08003c0c01c01e8542503d0580017165903000e000510026406003150761208000d424036400f076070788020f5056000010034401030900d0301600c141c1001d4038145034103890301c2e811010300700301080710101c455a030303200c440c50038500c16801000042c030f466082c958a40003400d4100364452000808071000d202020100b5140c588400c50106100ea81202d410045428070b08002511a01ca0b55400c1d40c10426110a000710306000d44526030041070141c41d4140780520308402c1c0301c0c000c5002d092556441c00309010344600c81c0c03079244031840400700a075204804216800009022a1010440c09010b945080ca00784005441610528161913050070300644a8118001c21442c1d48511f400c2030100100b100800110740c101180400c0550b4401d444000e40755 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 514138776 1250 514137526 514137553
    0x303182607080414191404051f05091803070b01030b090f0d030b01050c060406140c0403030509040e0c190510080903070f1b0611061005090a050603010b09130302 71
    0x1d010301d0388050400202003004100c9060074021140840b840a803805d030680d40d0324054002002000d03840500701d006240030a10082c0703801e1007095841011604030340300c00040e403030350b01100c001c040c06554060051403011800074034400c0300c8880504140021650764000e1803800d1010484280b00c00c8a81a11b10808034440081c0410320303080b0304c41d0400080c44c200c50040001c030046c00c3c4605906061200401c1440f0b1098410b00c1154800d500070100400d04610000f5a00048030000349141c05c80c0805010500009600c1401c840048508660200314800058686424841e0051582e5840000c1c0c04c0d0f5035130b840d010000c0c220100c450850700c0c10580c010b00a0b06403400c0780111644030340c0342c200304112800100c0904503945d90500403034201e18480d60160b003850250243c0d400400101384641110008004100410b0380d102044e120041c10b81c0d440c20b00491810724000d8440021300d030311303040080e505460940c00201c003010001d00220071410001d540232496800c01c00c058005024051513a181c5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 514140026 1250 514138776 514138853
    0x1d01060e09030a0f050d0e031201050f13110d02030f180307030f1b05010c0c1103120702090408270f0102010b10030c030e1b100327030318 61
    0x2669901000d540f40c2102c000045462041d03443e8000148101800321600f1a490b5115145034060408004c41c0c0e03072020460200c070b10a005a01440c4100081240200d0701c0e216201c40300407000c00341a000c94541d800c504202c05030b00070f4414416040380301104000c000100c0078002ca0041e5610b84a443d46c2e403000854180e1244506440039010603c01d4942c088000c1c4628813269503121171018030541c5000c190384490039070794800c030240006240c4032800da05106a102003c4014181140200036224400303512544038010b0b1080a4070034030302c0c0300020f01440300c420100c502440c01061113030b2121001d1201d0041046500607518054003808091408650051052014420780207111641642104204a0151221284039401c054807051200741c2e10f00e0801102c0021071001c207207169002d41e900140b0080c01988500041010700b44460980341540914141403c0b51101c9c62000d01801542400d402030006c8112a00c6a8168841e03201c2c1440121710032002c101d02e100c0e000d0084044124050042d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 514141276 1250 514140026 514140031
    0xe01051902090607080903011e06050a0603061a090a181521060509150903030402040c3006080d090e0a0e03031603060f091e0e2109041d01060e 63
    0x10405420441d06000c41d002d1700c040c008040700200003280d403004562290401d103810461440c001a25240c1c00d111620305044054040d06507403408001e0710b840e121110790443c40425261a10803000904204181ca6400300714000d000c401c110b2105032171a0400100040c190529a1224000071003400310310951010134500c00c00300720850203200390700240c5424008140103007107542c051160161049440d0392046085100d49100f4024640782c0c42c00740180400d69005400e8801041140050104070200c41544400b00740840e034000d010915928119800802181d0840f0026201d030180c8642c5d2a640404140c0c191a10081c20400d20389800c00fa6406079424504504000c1d002480058000c0e444141c0b0010710b040c4921b00030848070380e95850b0346051483c94200d00c00290f242c05046800345151910304000c0080c4c20310401c407179220ba40c0c403141c407070950301c450020802019203028168100c1401b41d94014800130710810444a2142c007180c10b06a100c01000540d50030080001480380c013102d5200e2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 514142526 1250 514141276 514141279
    0x3112701052710090509160912240b03120331020a050307060c111818010b090f010e191104170106050d080304031416050f0f1b030a060e0105190209 65
    0x8a807901c0074007039003611802641004002306200c0004c2d0240d490052800c40d03a014205203189200700b900c0d01c1e90031519074114040c071141070064001c025200007920800081c1c54060054a0391503c0b84854540c1400e140030080000542c04064400c901274000250410b2003115007a1115580c0c40c00c1c99125611842070344c0201d107080c40c0c540003242ea02101100d802c03000a194510700c408030010f122100340280c80007008004060152000d000013403287c04811401258220200c0ca0311102174048070b00c0c14001d282c101c0410b9408645910340c8001d12082c0b903900003100b404104400701825049030864401c101d0440c2c01001011856030303041c420f490564501811b140310301e03011520351002c0c0b58400f6000b10304010190304ca11303e095140b040508400513501e241c5c50541c01c40740c00c9c41032a010b06a400c1ca6041d0308105981c0b0100000094501c1c6070520f1110101c11042c4550002410403a1000c2e015244078202840c1020403034042d844188624507a002c049040c4103034030301100403400760340c080300e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 514143776 1250 514142526 514142539
    0xe090708070203270307080a1502070816110a030305030901110f0f07031205010e0a06360e0f01150b07030504090f022206031127010527100905 63
    0x5800046103407102074020a12166580c40c4c2061000402d2510756258030140540d00940c44000c00c1018010781942602003620f81542041c3d650340300c03c056841244546241909000449802c0100003034070070046000041142d401c6990700c0c2005040c0e507108940c042240d500c3c00104c40490340041c002e944d1000224201035082c04c005092040e966400301c0e40641c1030050360700347d0030190304050103241e019040c4c20740c00f250070341458400581503c0c0e4503004072140c1c0b42c074510507052403069404004503d00704c090944072112400c10242d0000e1840d6020b1040c0d40c00307070900a011580301504203008851241004102d050703a9130003103941070b00802d04000d000950402c0204071850081c0c2086901d0320444000605c0d068030319003004c4d00c2411800070540e543d12806410402c182d01403141c2030004000403030306c6240092900d035612034503100d43c2030038420440c00c00100340542d22034030030359040000540780d1011050049035000d0096080e61005445079041500c0d240a5138402c040340c008603040503004 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 514145026 1250 514143776 514143787
    0x60402060903070f090b010210050601050a0c020402090402070317060307030c090203071709010c1d18130b07020303040605100e07360612090507052103030103030e090708070203 78
    0x8012981e0720400240b5850b120324240801d09003061000c0c180108802e190024038040e6000001e403c0c80500254011854685410000c00e139802108850400c0814600185100e048e403001500a004800c0c0940e0860310121303940e41019045091058008007114840445e0395901080541d14065030000610040368038400308201d20042c0c01658004209041c040314000c402e030051040004211802c41c01a910360628440d400d4210140c0c4903081901c030400020080b50101098000504030404e405016440d00001c240100240d1606003e96018005d00704034249120002d42d2a001600c0903541e00740351101040c03d62402c00d5844084500070030002c410380e41e0700442502e5008031810600a6010301d80c20490141441c8181003030308807103003100c0880e02410413a00405e10f4001c010000c08992a211600340442c50028042040f0b810486081c1c2e10440700140803600550f400040002511011002108140d0403c0d0004060038064501d20780968a01ea012601e0130810740d580009600100300 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 514146276 1250 514145026 514145029
    0x40e0c0d2009041104200412060204080a03081006050901021209010c02030a0303020309070605030c220b0304050307030f321b06060a0b190c060603021801030201110a05060402 77
    0x8604065030000007440c54034024107000b080d8600400c850448000701c20121404081c0f90070b10907481820102e2211800704910100300c20524480d030300403490360111020001d003c09c03c03a80c0498001e841104280c61020b070341c901e400b414684e4166150301c840e40c04a5004151148608152441154140e0040c40520041c0d0309061059024400e0b15040040b48100d00c3e01680f41002088110361083d0350050346c82c41c0032812642000225040f00c0c040020410502c1070380d1405030251040d450528605a0030140d01d10644c0d802c0c804541d0000d15290703000703c00c00c41030020201c0680003141c0a07271569188100d000804076a80d4802c5101d0442800e90300160510000d220803840c00e21007251242146080350700c9034081900ca1892021441990154041081a09210340d4803070040810301080c1e82414000f10800000c0c04800062400b000380e07a5540714184449500168025a006840f90315105207000109004010901041c0d000c503041c00000803108c040041c110000680060280c051525035a0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 514147526 1250 514146276 514146293
    0x70605030a06050d0515070c0807080310081606170f3603040f06050705030a03050901060f03120305070e15090d02042c01020a1d01030f1a040e0c0d 65
    0x40a81c506942c0d5124003140903114404c0c0c245600d40100002d001010440e0884007990400804660820000c9550040050210401e503011a40c0c040b080315120b5072102e2212505043d1641f1484c101d118402105804a941500d18810b85985035911404402c80004900703034014103503200c24030b240d0b1074400116503440c0b15410580c00c07102940354a010a088601c6488800c0c1c07100907400360340c1c100040400483c2141e440c0d1a0041c6039606181c0c0c10400c89858654480c010400e888042c140c17550002581c42e202907000c0d00c06070220040ca060704540704d040c4016030342410002800460b14010229030b03410301925042245207001094a445100001c01c0501e483c0c10010100e904003215901d11401a03459020700c0d4040c1d00c502c406c40c041c1071034a41c42e1000828001d59000f40d141d02c104214001940d2000400156600003031550785440c0a2200403001040d031000029605ca2070700c00360001d030311800261050710070001c030341c14041100f0b200c0703485413200d0200c01940d034400c10703403c0010000b40b4404c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 514148776 1250 514147526 514147531
    0x120302010906020d06051206130f0317010b030702010b041b14040b160201080115020a0623040c080c01140315010909020d020d0f0203040c03080f0c0114010501020114070207060503 79
    0x9100108441c01c01d503407580c05980061400d100c0054982009000e0f90800090050041c52002e00501107070402811860803138151000141c0041081b0400c0001d15000d0044801c80c02c110341c907540c901d03613944e01c40c144071900107656460040d400d01d60860032600e1705019030001217181c03030310f030b072802881d400e0b42a20320080010034192010824440045c40f400d020010300340705c00305d040c0d8004240308c1c188001010980b050304003a91141402e0030381c0102960004c0c3c850017459204000040e80c0407061a40586441021700c480308820048042108014900102c1800c4420301070849032880c1c0c1140054442d48010250742c40f65880078400680c0e04260400c400f00103240604083e12080c0c0c4550b4128160780c82180f45041098000800540c142e1480c071801c0040ccc2a0004110700b142455030314002c5c0c00540707210182c035134840800c6400e0007030f290504903159030100c2c1000304180001c0070b52580390795209110301409546000d2003940030f03603800119188a000c5d01d0b8082c014240c00c0840948281e00301 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 514150026 1250 514148776 514148783
    0xf0a050111010e03070606030c05010810030206070c0305060411010917120306040207050703061401121505070e1008060f0402071e171602120c0f040207210c0b0a051012 74
    0x840551480f80c640500c02424618050100030405a0440c20034100e44000c69000c0750411000e0401c2110145546a4800a49070704850081d95000113060000901041d5000075000f4012507007800100000c0c02d80719104240284c86080000b9601c1600700d6540d0301030000440300d90880c0407140310583c0040c00441d40040028001420007150343c503494070b0311809400c00c03240d1603070710142c02d841d2a808a102070b00608003440d40360000080d0b40c1e180034800c1401d03d958800755031902d0204003100c0c05070f14240300300c64025040251031070228038010038a00096401d2030155920f9407a00840d41840d0080340ca255400200e0140c00c0c00e02c16001101902080c002074980d0102c04007140b09036800c0000400d038030755644996000144081c01041000e002c07070982148075601c10b505084058940c0d050140700e00c00100c4005850350054101196160505164203020381c440f4054503012507001200300300050701850380030050340d5849424504441d410f81c1c00040c048145d0b034040202e11090341130b0381081c070720 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 514151276 1250 514150026 514150031
    0x3040b1b07030309020a1d09010e1c081b0c0a03120b0109030210051603120c0c0309090c0309081b06090c030c1c300c0c17120301091a0f0a05011101 65
    0x80d6861681081f4008002000016040c1c0c800c3c0100d508090080c421590403040103041240c5260071070f103848900000f0500e0502c400000017601c1284200c2c10014101b072a1013800350f0f5400c000742c9103512004410011008640e0380e0501c4000144a881801c00c020b5043c0c581d8090603046400b00700e502c500600721401000000c000c142605192a13511702c1c80780344251607004080d00d03241a080203803070420042ca0100f105444a98004c85d92107031107a4110340b80002e002940e0101c921084020381522400549120000142c0c4802c0c546120f041d2901d000c8007a09807002500c0f22500b0684541c150070340c0319810760000d042c0a06920740501c200700c0002240a02c8040b0880079501c046c4102c07c603c10801c806502842c0001c400a0402c0740d4640c7e01e2a58505003440c4802999908005030307960017409200c49a8284071a4400e03020016011a544960b9405131250307900c250860240103658040712644000415180c510704192181000320007004200301501401d2400448281c0d500740140d42c07440d0b4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 514152526 1250 514151276 514151279
    0xa0605070f020d170c03120f1905060d0503040b03071b0b0408091305040b010e07090b0f210108010f06050a2303030d18210504090e2103040b1b07030309020a 69
    0x40513000108110407050016540340c0000c8001800c0c0e54400501640c1d03020140010450320f40340d440d203151503002d0315010005040c1c460310040703100d24908880041440c03100042c0810b01001d0500950b118100315900c8140403810010241413803056070000030300301000000414000b555034400b410076104041d00700901402403c41e5a01954000d1310251349602c4058014000340906044c180d61001281c10001e00562921a0a5100b0302c0390b13000b520102c100c00702c0c01c8002250102205a00522041e100c8403032940c440542900030100491030050341441c2c81000903c60401900c0c800889410b41800c3d080407103400c40421480c00e01c5629039038540001c01804403407070301074814804096405603050452900e14945080f0744e0894808041c42c402d10b0149034015207a00508507420b42d081528040baa40141900311071410300340b030821300d0740da0741040031402e403c0c101d40b8041c41c0f00b507004021004142e10b5003a0ba03106810101200c02020b010100143c2c1c020034020340010f02c41502c007400030654603 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 514153776 1250 514152526 514152563
    0xf10020f071a041a07020c0108060f21060a0b150703030906061403011a0a1502010e0607030b100e060901140f0f091e010203040e0c091504050a0605070f020d 69
    0xa01074140307106008280b400740010300400c000041103030103407282400c609040410010703549804400321141008183c5000503159200d4828103000c400014248445070544040310000311407a0702120348480c41640c001075401e9003540202c6141c001c0c00717402030101d0010410f1052560380400030503424540c5485180001072003d204e210010085442c0070881d10450f83d0801d0309440d40541442d038900c500044034950340e80c64143d084101c1d40c1941c8910200c110441050740504080f000c211550300400c02080b00e82509500301d60014070040b41d01d040100c4a28206507108803180c05e54907000501440810200e500402c4210702e036201c428111410039003030745000445540100490310349481d005c0340c482c0313290401072441e080411025034111406220180000c0d52405940b0800c5140008100482d02e0307203a1080442c0c00c2c008011307100c0460743c1d20400c81d02c3c1d0b1f554020b01c070b032034000c803401e80c80061000c1c4908103941051b548500c02c408004003503000c104000c07010f000c05a548640f141050b1028 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 514155026 1250 514153776 514153793
    0x19030e010c150e010b09060612130c0305060601171b0309010605040603051509030406120903030605030a031107091401170c03150604110301031e1106070c0f080f10020f07 75
    0x20000405000c901854280741c5282174420007402c0a000702910805c1c000141d9500041d192508421131140c1699526400c80f803001c0710740014098118070180c8408400e0220129641e80304840030b0303d07541851032804080341e120800c210f910380c0c9a405584004603c404511008581240c1d400e00081070107915100040d048031060740c030803111980b100501c5e04a8403444003e10341e20031082c00c040d604013458070501070400030000c004016a07540e1000013208250080e40070001501010b0304271101e42200d40f5025000082a60348030f4041d1140020004040507240141202c1c480c2c80781038100390385d2a00e018038650501d2002c0c03004103070040c018600c2054508004100113010110b0702e5104a00303122040c8411034004662001e0440d408200500101d0302508100803c400c0088041582c00401c0c00c0100030980c1022601d9031180000a502c07041c040710f140c1d5030b819200c941c0d410500060390b03840b02c41d43d107115a042d2988070340c21400d1400d0111003035901504851040c403c070340e031400007141c0c1c86940 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 514156276 1250 514155026 514155053
    0x3090512010506030606030a030228060504050c15031612060305010e07030611130e190c020d02011b080403080910050a020d05060a030803160c150209100219030e010c 73
    0x200307a42d2a000c21001385010807203c0c0e001203056028200c210880d13100203407030b02c0b0140c041c0a40d01840e4405d1208000800040003556034010f0410401801c042c58041c0e100d6101a504504c01c2c032002058501031212081124010001010054002110b41409807201d03018580f2001c9550f50740c05000002c95020300a4401044c2c0ea140a000150704500c1d04804480121507290906c0b0002c0c406d4004102ca528409401d0f1942d101154000350781d115260032000240c00e0a049080c0d04140790303503440a4002810004218260f0000d000c2501c501102305400310307144c540c00c0e0000e40c80313502040229010f142080d130085085425109102c0722080702d807060700c205880010036558002040c040c410258802c1c6900040200d401c0d40401d1310f561200c420f0350102800c4001902d00240c014a01c1d140203106411314550300c15510000001480c2c6038070001d42100403880e001c0d106201505d4640c910116401907000220a84070507034034610b803002ca90041d5034422707150500045039000b0700800ca01d081c01c0403 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 514157526 1250 514156276 514156309
    0x103270c0509010803070b0a0b030102130b0a2a02220c020c270103060f02040f090603020a0503030309150604090203030720060702030a08030405011e060311060f0a0804030905 77
    0xd0169291800380300292005a01000d0a60020302c004000686981405038002c284610046021204a80040e0084c45200592038070810f5915001036495081c202a0981c444551285100b9440c030940300350702004100544151154056040300c010b280c403c00c1c0c081c146200390540700c0c0000d120b001710411540081d81c0e507000759105201c1e103089803034200c018003400c403046284c0701020541c1c1442129065018000180078584410b140c141003103540d4160350041c85070400041e5080c3c0e40d01c2d6080014450760200381c0c0508145040400c0c0340c140081140c0c001c00c078090042c1890003030300c0305443d007080c1c01030001c686c05600d448940d005a941000039041150103000540c19241c110741039802500d40d038007030040c0034410500040700546c5c1e0200d14400c2c03154010709201e0740c03030b5201d1420500600c040b15092442d44c0e00c080c801c000c2004581e1004d000d6a20443c50264807140c440104001402400c007103035040481086448604c6201c0c400b8076801c50301c40e04242000603103603000545060060030108 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 514158776 1250 514157526 514157543
    0x2070804060203090f120a02120f0709021e121f030f0809090a0c02030a0809072103020c2d040f020c0d0318210e03070f090f0b030c010327 61
    0x70013149000305012440752070403102e10700d403503420081c03942e220b000e80c00300039114152059207103c0f001d400b803014003528888042aa04640c2d22003444000a41101c1b4a0943c4004a19051404210507804551001d41e9002040351140e483e410189100f25818107405a038540c0503c1c00000202112410032049210709401900c0e00c1d03450080c00801c00000340041001810301003118041c640101c120781c00c03041c5910f89118907998090081c0d00e072403200d520401e1219000041056140144068040150700c02d50a498517111074a04122850705821040400701000c0d80038581c5141c500c84040b92902006000400c0c10281c0710300718070482c1c1090754101055000a5548031104ce418443c50034800c00c00080c0c2c0b800323008141c60f141009120413480e2415407a595182d00d80082c01100c1800d40130000800b240c07045a01c07242c0501342c0312000d200385c03408582403148207444682b031400783d101c01c0d407030103002400f911084800460151600d004058810800d9400394001c00c18917a805820300307030186000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 514160026 1250 514158776 514158787
    0x50304030c090f052406090105190e09011e15030b03060a0e010b030a080703110a08040f0905060d050c060a0905150921100b1309030f080106051309020a0302070804060203 75
    0xa080540e0b40040c801041c4a110344450220b40a4180225107680b5043c6c698a1301c0e4820500162160320803e03034803040e0700c0340d150542c907401ca0307001c41086030701c260659012120340d0381d85003e00c0da81100080c000208040c1040144020340416032441162110341c900410182c2514020908183c02564540d006580b17812000f40181001d004040707020905030000d080030302d4180c4030b0801c0390080d1074000b000c00c258201c1100c40000e0400148032042e401c5041681e5030380e603c009902c2d845415100380c8080508110015029141c0058421405c030f4014001d814260140420407100e940114042e0080c07203103480d8040b40c1d03900e40e810f0040031003506c0d101590340c1c1d66501c2d00f009010110012140d44203214400040165580400c442e061300c0100d90b401310b1851101030001c1d800d9050071098410b06890300a82000f03040c0d00403101a82c20250b0789408074166241c0328101e85500c0f802e20b0442c000d0102d20010040304040e07034014100c46080349030042c100850380e5542d0009174816405140186d002062 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 514161276 1250 514160026 514160051
    0x90c0406050d02010509090901020f0d0902010e01031a0d051e011401050405040c1a090405040f0c0605031b0c011104030f0c0b12040b06120d021630050304030c09 71
    0x3060060070080328405050140303030740001c0c01441525000e6010b403e840021490245003501a01d500313413060790800e6114008428407400030400c41905030b00183e502c5d41664140e500a100c1c401c100c00480303030040c0c800d80d14a4103000c032201c01c08c00110303514417442500c0c108021103920783c0350020b50200700200e880642d15400c41403241e01a0809403203580741209202c00a0300b100154001c5910201c01c4040e2103466440040040c02080352032500181008104006c01c072414034078a50091207010f510800c55203c0d20704803841d00080b11403048061400301d0402c1c1201008000d0220030589030000704545149040c811801c2c1c018cd80205c480701905d031500d0042000040c200c20150040c002010f091454810307800d0303040c901c0030f4409400d0220442c00310741251142c0e420b40b68415500b5041b240a008805e00003913847d02d004241803484400428041060950216801c6030400480c1c40c010900f150120818220000c20380121080c2c842048000002a8101c4650005200504002072060303034081 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 514162526 1250 514161276 514161281
    0x3050f0604110a18053705221b0807090204170601080607030e0c0d0c03200d02100203090415051002060c03011e0906030302030d1b1d010e060c031812070b030403090e090c04 76
    0xb230165100e500b824a00d6990400901c403039100160700404200100c2070000b007000d024140725004500303070b805100e0022a10700d540e81c00070b100b181c0241c6201540808161100c0b03840c1c900a00480395160032130404118414801c0d00481021790040e420b40f03821104080000e000b00600f032100311810602c0e0780c41001801121801001e40c41071001801d070920400c0e00c0028000c080188000744a072441703603030010041c0d20070401c1d00c5050070060300820901512000d10405c42c101841000e00c0759944c01d8141901c4c501c00304040c0c1c0940a81908181541d0030030301c1c89107000c0607010b00c0d064003841221300000d0f07001443c09103a00540c040d401079552045015541e41c140c81248078040e41ea1410420320761a07059114020400742c0040305801d170140364040f00101d641084c000f542e50342c804800310759015100000b200911800001001015480d0403171400d0088043c18421200000d030412242046010407910045500512a1400041c00b0b501c0302d10174210382d40152549840b075803040410f00c0142c249031 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 514163776 1250 514162526 514162531
    0x5030a021b0c0a0509280b040207140d02030f09040203040812192a110c13051e010e010608060f1309262203050f0604110a18053705 58
    0x4d41d0802d0103803900008144940641c00010281b4001412846903910100d40c444013100340b00400a541c0c440090a0060307012115000e4803c00340200f81c4607400700c1d03000104440b018120861018180764110702000020b4000800550b81c1500403c018410390000a84c01e43c42079407c45885001c0166005000c000c40d0300707801030300145102000d40c05040300c10a2a1500b240e80d0309d40390070400c46440501c0d4034101300c11401c401d40c00641240c00303640c89005a0308014890304010b10030f044407600c00020804020000c5c82807150340f4a00f030005024403071158074096440f0502038440d03108686810046503ca1104c8543c1e140300a9032002400d040003002060307113105040d1400100d49016543c48104660300c03e02140030f200c0744604444803c4160100361300c00065800200f5641d81081030380740c09845020456086484045910040e401480c19800c1e0030262110800c2c041070a440032806d080040c500944200601d14192841d208030b84c0e1111000024080040048044140c0025060081e142e01 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 514165026 1250 514163776 514163779
    0x111204030b0a02160219091b230f070b04020f0d030807110a05030f120c070804210605270f0a0209070924090503010e060705030a021b0c0a05 62
    0x100420004641100319054002c1d0075031000503501c0b00e581104280014800000035041011102c008084070085c1d0710790011650ba0b60390a000c010030549a03800c502c800c121081c0c0219600021100d140c0895181020000c000401c030145428240002204c00340c10901048900940303003403c010860400c00d400107010036054481044601d91960f000d0105030f80208610108130342c2000c809426030003046607603e226041000d07240e40d114804600c100300ea009030705428071891200d0200d210b0880c41421034103107039080b50940342460300b070000c0050204803801885000404446544d804103807148981401541500f007242011007501080d01c50004008203003400e039401408407050790410204001081c5a41110001296642d9090580300d00b251600040d110000030400803100103194015410f5002498031503100c0b25035a1802c00d0f09950504a0f14002a0460b1002c104141d009102464000402d150302500b043c41f070448940380d0360081410f01403a0740c407030881880c1d241043d04031340c005402d0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 514166276 1250 514165026 514165063
    0x70801110912030703090b160b0415050c0708220b0d0603021e03030301031205072306130515040503041d190b0a0b0304030219031211040f090f0e0d11 66
    0x113542c4029140c02900d03c500803007050001110304039418000c5644c3c025a0340407040300314034242400c2a01400700340715446440c01d460030012400e045142d00640700080e074800c103810b2800140304490009640f10048925180c074803503c000c00d80105010241c00007090f210f00c0000c90a1860040100c06ca080354030303d910143d01c003001d8180b503840c08400c0328103403508004200c0c684001c0c6501181c407481400d50180032122a80a48101501c02c00c415080e00c404280c02c076100e0ba114001017110803044040c000309640c4c01142c19418007686882040c0d4042d000368140c80c1419a00d0344108080f842440e0b8209104a816080140829000081880440990305c08003d00d40b45e00300850f4600d98240076041003d44048001820503100704030800440e481c074207113507410f6511031801070700da0032010b41d03001d620034244101c9100c00c0a81000b2f8030101c0e0421300800351481d2800707091000600c030414214403040d0f1550b020001002c41001603001700b032459501c941c12100740c0310003542082040c0340620350006 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 514167526 1250 514166276 514166287
    0x7060e0c01030506181b131d060a03030e0a03050d0f12150302221503060c230d0212010e060a15050f1810050d0c021f0e07080111091203 60
    0x11100d5485003100311243c50314881d25150a4400c070050070200d01c00208400c4009031400001f840c0003916000c0b10700e1598810110b01800c0c0c064549036504903084e80e08544690f1007000443d00c83e4020304003030f0b900500701141460301c03519003a05181030652004040303400c088004800c994001d10703070307021030508440401c0600c40a518040c0f1b1a4a18800a0310500c121001001d403a0003940e00b001e40722041c01c01c1001105505005078503024140c2c442910018035242800040c140101e0012a8500130458a0307241c982c02921007168980084010206440e401d2002a0080152403d5a800303003045a103410114544182000f002035070756040342030323200030f0f040c0603043c026000f809680001e296240c1541e140c50728240625030410a801c240b607403091206900b500040d4200f80101400c0c40065400d11008450704010780e0341e0704507420b601c020042120f5440e00b07003011950003000c41101c102d084d2241c240d5030343c45e101d09444400206c425424000a540c20f120b2420541c2c840c200300b48403010f9420315 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 514168776 1250 514167526 514167529
    0x61b08030414010e2103101a0c0f0109020a05010302070b060402030c070b010e060a0f0305030316032a0905040b030a0212031306020d03050a060806040210030e12040f08010501031211011107060e0c01030506 90
    0x1203201e1080200c000703140e041507800c0750165002e68500c0d055130f27070032140d40e40481031400c3d000c0d0000020a9003c0c01c0c0091021400d0f512a00072600300c940c000000c1d40e5a600c03042c00380b01c002c2d84024801c1c558030703406101440019001c9402e043c000d05e090300e060103c0b41850410808000104d80c030240c1c41d000b100380100300154003c4107496010103000703401d55900000482c280c0c040c20042c150817402614184102e984141c0d04003401c4180c000c16590f0980d880e0f04c4105200c00c23500451011649540060502e500506e131401c900c030101c2040100303070381c200f028004c034001401500303400c16000b680100d00c1d4480c8c40b41e41481030b680e10400040040c07055920704029030351240c4010780080d0043e803489030702d0901e903402500325113900070442c1e04403850100d610785a50516080b44c007a0414084120a0000c1c11071014004c2da0b062340d402c0210344040c500000405c0d21884030000c2c1800081d52075184029900408101500c5100e0013030b40b0220300020705001c0182800040d2500c0e5043c980f425040c01100d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 514170026 1250 514168776 514168801
    0x6010b0c100c0905090a1a0301020903031602040605040203010f03030f03140402010f14030c0406020f0705010206071215030b0402240f1e0d0213061b08030414010e2103 74
    0x32090788000090500d41000120748420305a0041500104000e0601800321001d500041c0c0b40607801c1c0503040a8060141090b0030303442082e0529515920a012882e400070710a110005018402031000900c60795907000b09040e82c03c2613004210610700c2c1d0804005242d000004000030b1042490b0421681c94007034001d80c843d10018002038100b143d80b008841e03034136010300721501c020b6400c0c0c03000a482740380151950443d0781c01030140c080140101042c68583d06000079202083e00c0c0705802420356591800da0413105c03441c0108168200c140c42c1d12224540704240114180558040d0350b940944e841c250060058203014a08075500d15000300c101c1c0e00440e803001c0c0540391217040d0145025030721007160a500000482d50101b070740a00000090002d2aa0500e60003040032242215103000d000c1d0f980e01d015281e41940ca4404c01c140545034068000258035600199400f071b100b405a0320b4180c80d0a05642c2c211140c00506030010380c8103103080008101002030449800d4050b010642c41d526044105254 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 514171276 1250 514170026 514170043
    0x302030304170c030f0f100501080714031212010918030f03110c07170d02070f0b0f0c010915050123100c0209040309090b0607020d140c2106010b0c 65
    0x300d02400c1441d100031442d050002019440c001411203005003400b03540e041e240c071000d00d240e0000344201110b81400003c03c1c09228100d51030031016103800382c50500100107401208283ca98940181190354003161912400b83c805002c0340114600b66605100f01c0a040719404042c00d0300f12101c4880c03280000b0b920488094115281d0300d0041406000e09a40d120703640210b0880000c1030041400c08545500c104200181e08129101141c0d0314080c0510180d80b105054007582d010301c108000240004d401810040c1950300302a44e005241032020f860385800c555050381c0480d009401040d000c01c0641650040f036001d01034085040c10024190000341d8008102c40e000c550146015510a9110710302500310f4030342c83c0d500903101c4071032460071307140c02001c01c41c441c01842d0306613160550700300d89800d0050a460a113903020344403a85255044d11182030100484035412598800c0c44114240d9446415040c2c10a000180d2440c4c010740620800d6410315405030000d214000c0b061000803180d0500007034007403 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 514172526 1250 514171276 514171289
    0x1a0f0c0c1f0e0a05011a06070b0c0703051e180103050106020c24030103050d020d1b02060c0c0411091201020315060a03060803030f010608150102100e0c0d120f08010302030304 77
    0x192916400c28114000c0c101c01c2c82d04400c94041c2c11107810500a0640040c006d51015160154801003901d00708542c81c0104c95002e840840550b00062001820700001c3c00c40318002c0c01c2444c1441e4400140381e61003076010118030003080700400e04600004a0189507101003600342400d100765810004020f581d0b4040030035940c419102170a60301100104100140020b140d214002a660760b100c0c00d105681e50200310031440103121700c0c554007034042e106030003021801c0c10000ca121554959502000a1a0001258000240600030f0300500b156201d1154401c40228074240c00d44600340304040041e601b200b210300d2110345e4010010030840d007603043d108011200080fa00303591224100c0303e00320010019600100502c0c03100005000c0320008910714503040b642640d9402c01140e603285054080f00c0440040079000d0303403001803652880c8001d80c024101c0300034070000320341d0008403c0d000a1554554810252515104002d4076602e00b070344000400760a0480d23003480ba68551450340465500c3c840e40c0724a2 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 514173776 1250 514172526 514172563
    0x80603210a050c0a0303050712020f0702210a050601181a270406090b07030c0f0f020a080f030f0601090b0706150509090106081915090f1a0f0c0c 64
    0x404280d0b006509840c07101c21110122060012103180c0540106426038401c40402d1103110640c460203038034004c8401812850070b0903820000c4540c03d0050710007910385170141243c420100c1020380e80e030070003001d000e07980141c00030812545010031001e103106120000018941c00d207004583c3c4401c045031440c1030780c1804d65010f8901041680180a000d81000d080c6c0c1032500580e0610061182540000068a0044900c1c0019480741441a02100d40001200001c910014010811b487c000c0c0704150ba0b0a5460040d215840b40940e580d6846501402c4803060991010091014495a000317415038031043c00c2c00c0c280d8007035040030440d207254025018000d02854507880c001c0e4040e50010040310041c81c01030908403060600d0389072207002e0501e0303008566040c1b1a842d101a50002e0301034040240a03003009014500320200003951001d0210a40c0994001a1110f041d1001031012646010305d265045001401410302da074a15607881e2015080c101d800e41c0a1050440c0c004001c1810784042d0f6110404 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 514175026 1250 514173776 514173787
    0xb01170f04050f03190207061b060525120b0a080312090717010c020c011b06050a0902060304080408010b060a0906030507270303090b0309060601051b0d0e0108060321 73
    0x840e15207840382c503143d030080c000442c5ca018841000b80a200c0d00c11596000d0f1200320741c50380d0b4201d03464540c18013500459004181c201c0003040300d0794030040d001860268000103c5000d00303100340d404511680a100080c840c1040103130100d039240f1965038103c10444505141e1441d160019660b801819985c14038140d4040125038140020421800144032461044005840359202c2c58020001d25440d200540a9202c070280550f00c6800d880c400d00c2e5000030f01800d079011a4407010b00401c4000c0c03c82140c5540c1d01c40a40250703840101552007a445100c1843d81c4504144055083da070612110a000d503205100f00b02149421040340c005032840c51030000b1361a5030750481144c8038441e0305440c0503401d4500b060b00821200c03c4407050107030781c040e0f1505455542c4d1111312600c00c0c401250f400000360007400100b840303584190020023015610000c42c0c4801407659103000e040c07000300c413030303a4002c01c3c41e0a071048140c0d600701040070f41c000b0301200134186205e10b0b58184100318480510850b10028000392 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 514176276 1250 514175026 514175033
    0x30607050c0f07150f0905060f0705010f020f130b03091c031b030222260312010e070f08070804020f01020f010516030b031c030b130c0c060b01170f04 66
    0x241030441c402e42811034551555519000c500502100303c1d0800117030744000c00c42a9a40603100400455101901880c50071a10261841c2e2a400c03050013151103540364040701042c01d91900240801e09940403280307507a040152000340c404116541311060052090040010f83c2c10b01003a9022425003020508030b0f0b00e0750064003240100099544001318004504800c221150b041e0301402e982500084200300e0000c50382504900c24009110345420050038000051038020b00000c00c8440d0b44451044070700f01a0307100c6010340b400009030411202d1401201c100000d03940e00030788104d030f0b407101410415054240110010101200180064000d8030104c620600c140d1080044810500c05c4000030400c906040040c150200f903a180d0b0000020305112020070f99140c04507164400b01c903007450380b102c10240c0351400c1d405042e551000e50b50140030704016403c0c030401c4e4060683c07244a2603407600302003005403901d841110800700c8454100090141d120082114513501560042d0000a40c40450303543ca16 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 514177526 1250 514176276 514176283
    0x10504090206070213090303050901060b03060d061b170703050f0a0c20010212090c01020d12020708070305090301060b13060e2106010e060411040501030c020c280504050105030607050c 81
    0x20002e41140800d9201e218520705c650080d0300c00391090381d0511243c0c4600d100c0d982a82c0d0240541c841640040010804620f084098902c20a22642e400700c0d43d803a00c0c0321b407845207440071050780b03000c2181422401c0308010001c00440e44240300382000c2200d42485414654046001030184034000c0d40e4001a591250003030410a0121440381c0e02000c03000148145d240c00b0390008500b016480064801284000c00041a074a20404c0180d00919100c80c82d1102190303884000d0006040b983d07400c0201c1000308005500500b02075000b41c940a9440e031044c1e09050845034103900c1188014828040740e116111029420300448400740f0342811110803030000140884001020511400301c51041345034141ca01003400c0e4100c46807650301e0006903507600140015101c0c0080c52580c8410308100c08c0c089503002c2e91107480c003c480d910480f14040901030124003a81100044103801c191b8455070f540040031100c520a0140100341d8090209500d1308012030323990f003c00b800d000140000400e01c0000044e080 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 514178776 1250 514177526 514177537
    0x322050a17040605030a091b0b07060e010605010e10091a0c1911040e100501090b030d020312040b1f0602070927020f13060306020901030b04020a0906180f0e07020f070608010504090206 81
    0x140d12001004d03600c08050804ae88400c200300c0c5c5103400c044241c03002c2081840758008880042c0c45400c5844442410001c55000500d55181803040544012510b0340b031401440a4050000d903d803a40c81e64041c465a24060560105080079803a848015000030350500b01c1010810381a18049610036000c11fa00f81003032210340d2a80b18031031424000041c3c2c0207194015041082c0c05800380c5d002c030f902006040b43c691041d10000d03400301c240e010208001030526800c8540c03008910100282400144907000d03107440203a40700200581c02480300303000c031a07200d100f0a1103043c50181001c0c1360007007600e50704150381603c150188c8200f411039062031198840001c010419540d001c4200030044c1c0702d1800304029003009001600081c80c080407801c0314241842180c1c415030f2032b034580d41001460410300300d461481203003440f41041007094001400f0780c1c01c00c0256018000c88c0343d4518182c5004140249403c02c91900c0c40d03441c0e44402010041640c0155000781074400949001c41c14004078004070703800d413103403 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 514180026 1250 514178776 514178813
    0x40b180a0b1201020904060f0b03010b07060e01020c010e010c051303110d0828030b13110906161208040308130305090901060503100504020315060322050a17040605030a09 75
    0x42e2000024840040d40185000b40e422030303007008015203403284406565500e0203a48155882000148014142c0802518000d8410100410441d405854290a9800c203d0b83d6441a0b0b46540020316400c00a0068144000c402d1414500305100b441c80c22451000300d00c8007416426420310181e0544d01c90a1030464681d801c003807016139558640d00714009007008600070f0390400c5041088081800d21901407240200402000052011800307001d140040151409400c4005020083d0072801c1d110030740038100d2661a05a40303d250003041c20b1100f00031440d4540c180c20044100d04100c0000c1d044100c0325041050141ca1401648051500b91590310038401032a43c0490324800000c0d281f03901c1002540306104e413800c1c40d0811fa95a200f80820f80c0002d59440c241e89003da07102607024100003018640c0a4840d41c50501680038410035411486c25000080d01c99810507401d0b00d040c8003030741c0c21301101c2e45100710401d8a09458180c0090040c04040e008104e182d44980b45036040c010391003014029140e4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 514181276 1250 514180026 514180039
    0xc0d1e0c0c08150403020c061c020313020a08010605030601150504031e02040908092e0c0201050d14010512030301030b130f1b0512030c0a060e070315020a0905040b180a0b 75
    0x2c2800f0704142d40b14121011001440b07412400c241070b08004080c1d41d045080820b01c0f0107128042031410001c0e402c000c0103c2c035040c0d8020342040140c1d4075100b40f403004142500001840c0f034100024142040016084050418030200146072007950000469044030b80046200c07c1141002600c61446000040003a41c0182086858070a000c00e0500801c07000d20112540035089840c2101c400303014100c4039070400348800e42141c0c441401e000e07520b44030f0f8543c8145080c2d0702c3d04450079082c0b8112010050113040c031005100051086080041c181024000c1d40c078019402c40d0301d155030310200800300500940d0400b194400030000c010b4646030102031903a100300340d56080004100c0c040c40c5620144a8980704995088082c2d43e0114007208650f80300401002502001481d901ca90014156026000c80244a40c81000002c6603540c109014003d0300c0e66005a03032400c401000a002c030750a504120711892030000700c0e00050340c800c0e40040706020420b01d001e8036507482c28600070041421070f510030303080803 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 514182526 1250 514181276 514181293
    0x605090307470103140309040f020a0e0916030b0105090d0b060306010b13090e030408060108030a0e060f030f1005180405073002130207080c0d1e0c0c08 67
    0x482d1031103840000316060450361040c400280c2c1e45054a1808160311400140401400400c0c45410000b8504a000007140c0c541101c0c0c1000c01d04803980402038001c0c1e5035011038403100d0705520241082c0d102104030780054080c01c0101d4405a80700358400e45030145544c0b03130302da00d0140c8d000300107a680540d002040c200514200d41022404503104032181032081c01003600100e4103011800550724520b110f025403901c0181001d040c80e000708050b010002080c0300c207000c009410802042400d0180410402031a2030703002c803132000307031040701000007444c817441d401e01c10042138007101001e403035114844200c880c400d920b510801e8140b19042d60050f5070081c82071032001c10300e800300d410307941e0040f4032400840c2e00d0242e4032095852020003c3e94100c0720301e2200b005940c8890283c0d600410319034002842c02d80b480c0e05503c141c0003203a010100440d00614089047c800601c010300074402c01200c14244400361041c13208101b42c0e0b4000c2000b40d0303414840c61031800310510003415401005050b80700121110340 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 514183776 1250 514182526 514182563
    0x5040b0309241005010f09051e063c22030212030c1209030d0f030e100903020c0f130f0605040e030c1605100c052506090e04020d0605090307 62
    0x81c030045500c1d4242c020f814100003055480390300c0341c0f030094440b6a075413542681408204000b42d903a42005480010504182184554501c801424284002200100000400c822240f0f441c1c10420701a18802c2c60a46050008160281140c0812808012644202c980f91200311b5021402c1d42004c0d4100703203007041030480750600000801411100318200c400001e4029080a0140b01e2482da5a400d074001840404c038075802100403514005150401040007141d60010380c0c40c04500c5140c03c0030071901c51140e8410f164041c0700340003800c2e0003a10312554000e00070380418901e1146041e04c1c0165565508010842d0b00c450b0301c8900034120081003401328151720702c0501e64a4110060001c118050951040041011000c18808440014090b12045200c04000b40c030380101d900070a480f680100c62840b01080c500e2416044401c0c54208403040d1141070181c0140442c56542040010310526030521000d40d85580c4403030302c0f0326807164010810390344010070a825801401401441c0c454150150b8040 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 514185026 1250 514183776 514183843
    0x201020c1b010e2b0213020703020c01080c13060e010c020402040905010905010e0708041b03051501030309061805040207030c0b070e03010c03050601080a0e01110403060603050c01050a05040b0309 86
    0x4038402d0740e070f01001140080401c4071641c002c240e0303084e421920030032090b20400c1300e8400c10500e0f80014000c041380d07001c50a885043e684400021001a007200808264941e0490b640c41d42185a101030b2a0401000035080303415983c480c06090248a02402c50310040e0b03124010840700c1d1a8050029911a03554055645c0902801e000b041040703402c4c040040380e0703100b111408522404540c0d44030542a200c1d6241c2c600d0200703101803000360340a2007210102c0483d2040101c8105c400a21490840940c5107080c02004051607405c00002c0140c48030b102040c41d03618120120584d0412500107a5a41880c542680e0700d44100100074244101c0b84100000140c00007603113024543c0c04e070000e01000ca140d11081301100c0e0201d0b040742c08500700202083c010a0103034807904246481d030000040c0c18440d0320840505402540c0304640c46900c0b8107007803041080c140540c3c2c13802034081c01c01600304224510060900d000d5030041040c41a0080300080140f0710070040040c03000d403440564103183c102e0092a819 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 514186276 1250 514185026 514185073
    0x30b060906010309020d0803040c05060705030318062a1e0408010b0105070c090906090512130e06060316031e0608061b03132f12030304120f0201020c 66
    0x1164200c1000100d86501a001d40c0d074026900510104114529542d286e50640010740152003200588030040b9040e102d8100400289015800468076450088040708003851540b1040016030010402c3c4480742007102400b440001c00d95200040707185100c0b16180150045046254004c0809590a002c007004200104156000513000703000c080c00b9100107507858407030003500425101045400304810070050b4022404944030b184c001c50400b1181c0c80c0c071440c000041072141c459030000130355084407990005410004020001c0c07404001c0c0780000015410f03020042a48104040040243c000b540c840e503c020007015544580d2000518801c88410062003540150402d601c58031000c42c03000d00c5010003071580045881e928620315640c4010b00a04a407010781d049038005d90780c524012608207504503e041c40c04030074055540c56072074402085008003802e03000a00c00c0c1c004000b407201082c031344d144a031481c8440d410000b0040e004400120300a10079264010301d94054a542d0b9220000288070114 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 514187526 1250 514186276 514186279
    0x31201091416090501080a0e070306020301060e0f130c12060b0304020a170a08130b1b011803050f09010c240608070501120504170d0b04060e04111e0307030b06 70
    0x10841ea100740314800603592a00c40b800100b6802282000381d03600c00c80501e507009071400d00201d510003d901465207040420380040320207940110040c0001503006c01d0548000070100d8030256890f04c244082848a4600c049c2006c04546030445a40554004d0004003101d4402c08401c100e030507030700c0040040b5500159803c80c8106001a00006c061041b5500c0082e80725101000c0c1c1030b401e1081e99200c04580c4003a2f0b4043e00006441c1c40018000d00e100081c008050000c0700c45124650f451500900f1070742000080e0311113a10095098022030303444402d0b51000f01c24440400d40e50b40c001c400584443c164490001e1080120201e1a814031440407068803291700f05041c18041f941d100c002040c0c40f5441c6026180c00694580d680981c41e806682006800c02c0c01811441401081a840d16070a03901c10b07500f2141c1a0340b502800d0300710303041510448005241c110340182c035038242a52821301040405001d079200368108036225008881c102140c000800380141210030866031b03442c1070f403c2c0d04022200d16 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 514188776 1250 514187526 514187561
    0x13060b04020306030d0e1923040507090b1305060f090a0501020f1f141e090601031e0203070b0a0c0302070806010303050708180307030b0916032303120109 68
    0x192a541018001c1e6070190710300801500d11498a510203c0717000c0c0c2d81c81700c00f940c400a0150b03103034040d914103041940948a02a90542801e202644003408000003400144c044d52403c0c0400c04184d50261280082d15861910140d4401c0c48006420b810340007500140d83c044000510310110020480040401240c00c0e1605203525941e6001640c43d0315000001d0300c9941c0107002881c003658502042c115103540d0a40b40000c0358410400410f0b030008045550a25031300301510b80c03002402461542581c0282c070180103003110341c110703038440711100c80030800e0b239006c0d1400b105000115075003444840003030260f6a01d0641c072a4540e5030010100203142e0019005406402004100e150340411218180c07601902c51a1500b409a5141980c0b58080707162202414108299400c1903601404040002c50103081481c2590800071081c078101488040c0d9122a42c91100041001552801d080c000002d102c0c1490340041c4500040e0702e083d449641014500790340d5440c004210303108e281d4045c1c0903000d101c0640 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 514190026 1250 514188776 514188791
    0x161e02280b0c18100509010507080c0d05090111010c021038040c020a0503070f05070e09010f0c020d09050f040f050906090d18050f010507150e0606180a02070c08061306 74
    0x240594088404c040c900040c804101109003540150020807646106803503461500d0116410123040c100154002400140001008007a0f5a40320485a0300c485002008110f0796802210103540c50f001e05811441507074031001000700103030585103802041d6020380002106001c10014007100f121403501c40c0c62080b031a211021088600c0051418030083e405001540380c118591204902a14810000c855a1281d04000305030700c0d810448040c0102401000030404008503100d1038150348140100c4801c42d448070060a5419a114041d40d00711141508d0111241320940c01140c043c081d0741c0042620700d4101820b100c4001800241c003480748050308190354402000c00c4c4101d56561020b058a00b83e4902c1c940c1c24442850107940d95401240141016850003400359640b00000a4010102c1c2d007087c0d95046000c501c0d80103014042c3d001d4400c8582e5007041c0c002c0d5a50121040002d0b002031006903000c1402010840e200e0000c0703001c2c0c0880c2040712018942400c00d202c000001c00d404032103142c2445070 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 514191276 1250 514190026 514190029
    0x3102010c0618120903050c041a12012c0a1203061203270302010815040212090615010f050f030603070f0308040602100603020a0b030601020a0605161e02280b0c18 71
    0xd840f011703a07074000090050000c0000402024100c250000703240c0c0100d603800340d2015501d401c000c07664003007010f0000c030f2052041006600545041e95503404010303c0300c002000308510200d22040441d5005080114a00400004a0050510b074000c50001c88004529100303068204501c919503032a00701000c903d80502c025007400e0707070b50715220007800300721000046010455606030000680d100170b8801410321405e142071307016110040c1d80307075090742d00007209201d040790780342d4061132000c1402c0c00e0480c1d21000c2041d00a00070b00c10b4600542c840e520200c04114543c2e0203000400082003058580d844443d180d040c01e83d9540c1c401e01c0380f14090710a00c3ca00003000d5000780140c00c00c0780c2c4c005000c0101d06180c100b5211050f800100403504600a444880d40050301520805010720903c00c2c0384545074100300c0c4003a00d0061080040c414451141c4074102c0a40c0d400291170ba00201104c440c00c1000000c05a04034092130100801421356030501c0801078400c1400d0003400d0380c0c410000300d200c903242c0f80d8030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 514192526 1250 514191276 514191287
    0x6080106060818011803031406221515031d011116081605010b04060501050c0a030e150703020c1c02010c021903081801083102010c061812 61
    0x4100e00200d408840069107284803030781c3e0101d00040040000c1403240440600c6600389001c0181100440d036220300300c034080d107601100c031503120710292540541204219402182a5a00e00745100c610b5200d04041031a510001e80f142e005100d2038031911480072003e000a40036041c007000791002c134641500da050101d6814018282c42600c00401d42d032a100420022030f5880300e00e0760055801050801102d00f2024001009245007401400006800342a40e010001944c81c0395101d0b80c1040400d0000f01121200410b880003000d515046c08240146020b010030345001c001c00260986d40004590f4030b007416008a00e0410321002241c11100c60014500d41941c040c030b0b4000d0107400540348803c00001402c00d80c882900c0f2131320318140c0e000501e0345ca60301d102103540f0113404c00030189945e134501109540c0050f150340e081205980d07115a00c50383d09818964507044407000350744481c8458866000e590040654981c0303150004000c0c021203480119010070100b41a20842d15003e0880f0040110391054 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 514193776 1250 514192526 514192529
    0x210c04180b130b010923100302131a100e0618030c060c100e010e0a0f0b060d02060d0b01030b060a1815051606020c010e070608010f0f05130f110d06080106 68
    0x342603000c517400d04491034000c0407010b0012840d4090a41300d55440300e004201036101d6410440c02420850441c030502c07800a10061030342c4881d83c01c1c1401120022401030440c0303000c0c2800c5da1010500d110740b04007120403603580c042c0c0341c1d046040040e43da01c80103e0403038480582082a4119120000400140a014407440c010b613a02c5401c2116008050710107034000d0090b01c80c011001042110f5400145810300d064540121503200d200c40d5200c2c1004502e514150b4862400c54013840c0410b02500410b8240c45000504284959200881481c0e6030003035001e82885100502840d03110511114003a002e0085002040502c100b0103c0000e01c403038194400a0002035280d4806040000641d1107051100c1e101004072000c0e5000d01000c0000e0000f44100202d41000e20005d2540d0b0303142206c040c007882c2040c0c00901c41c410308100c00344204044441d080f01191700594075603510130a483e5030170008200420701440303500d0130600c041071650190409480d500c03091030f4081084941e00d0b4582403c03220103 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 514195026 1250 514193776 514193783
    0x70501050a080406090f050609030a0e060306012304030812010305010f1a040c050f0d0203100801090f08030c090a03060209030c09041a0711060708180c210c04180b13 73
    0xa0001d00014807680010400328410001940e06c80038a66940c2c2c1094030440380900c075070340041075142c3c141da4000510b4074120300541c0e01914504040c000204954054043d911010a00068641001c407401086500564200a10540b1622084a054181d103400c0c4400d889660038951044e401410700d20403140700542048000c8241406141400043e240c00d00106081c800f003442040920540c0c9001819484e400c802e0059032441c0a0f0001d12500c05107400819003607143c072000c03400003400100700c445d5068003e14101e80322368032000344154520943c1515600215101400408c0021640141982080460940e4921104041401388100041b2009881075040307000540a006440d00c0990308554580352410200801000080ca000f900740c441c031001444030000c02041000a05184062022a82c050907810421800103809024504880800301ca822414006c0502003040000e04004002c4d00502c201400001124040802c1c01800ea840300c00510019040c00808032010203515803 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 514196276 1250 514195026 514195037
    0xa05010203120f0703060e0a0e0d02191e0f030309020f01260402030f030a0c0b0105040e0c0f040f0903090302041103010f0909050a1a0901061a04090908090406030f05070501050a 78
    0x20f48503902504160050010b1040c540d82c0c410100c1c888070b100c15014400c07407880700045082d0358505042440c09141c01c00550454220090078150342032054504120a900500c50360722000580341d040f094100d03820001450194001c00003006c05d90503030087c0003068000c5464000d40c004540043d503d842c64136401c0901d00100241c1c0008a100103051150004c1c000340403212000901c45a075840c691180d03008002060412240d6410002e10441041c0981001d40c1c0c10b111500502c0e10792513480d03260002881c4a0080200c5907542a100c5902100e50b405c0620010710100306141006402842d0501099005a0410701403034a10b003c00380c100c0c0e040310421300803030844518101d054002011446800c86050144100b881c01098002c50425010740302c1c0355401586003007140d6040d08569056002c11a04013404c1c02e105a449000c0007903604a8200c0c04c0d0101e411102482c02100d01d00c62a41c4040d0310a00d02080881400096141d4900681c442e4003245d0b000380e2104010342e030a0003000e044500080c2d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 514197526 1250 514196276 514196281
    0xa0506031005060c060f0105010309112701060e0f032b0e0d12020615030c060d0608060a021e0301050d030c08130b031f0f05040504031704110a0501020312 68
    0x41400040d41c1c454100120400c074070307444800150a5500081c0c801c0c107198070841c103110280c446078426034018074007400d04104500290340c50246216040409038418424101001c1c151000c02c0da100c030880003080d03014009c543c0c4614000c0e10282216100c00e0045100060920b560305000030f00c4001e901044140c10a421418a003c5000141c440c0c1600c00b00300b04494440341c81d0b103a002d0700c000110300c6036140701400480e800000b45054402000c51040c1780e010303e2007941c240c60104914192000944080b41d842c218042050007504466010040611428040008814040d0302611429204180c1071500c45d4000306250303140e01082c01030603801080060000e000034040c1d10740c0d00003e4420740307070b039402c100147da1610b0190440ba400f034021108000200042142075501c074641449000ca50384400c0c900701007070180c0c0240a8000d2501a41c2d40310046020706020f500404c0f04141c00542080d82c600e0300c0d2615003406e40d00b000405004080d0000c010603258004025590f03200d1403100b6420255 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 514198776 1250 514197526 514197529
    0xa02010b0f06180d0503040602150a021e032e05120604030e010e0d08181302070507030615080f160f050130020703210509030304030e0a240306080c0a05 67
    0x600c10f150300c42e5200c460300928400164040c8007500003410641c01408400c0c00100e0018844880204044d0340c4070301c10400d1000070360081c1944482b4040d4001380c41c0d00c903540d071500c000b0b4100c4804001c1c40401d041d0060f19040112610301a001d0761402d40351490031a61341100310f9550f00040e89c5c010701040450681529952142c20b014140794001400403855847c0ca451342d06040d072005540841c1c510107800741c24001e00340000040000201010118030307106843d12002c0c6c13501e04e50b00009040c2d80c5c50f8000c0b200360422003442d20016014160907202183c01d526565545e9080d82c40c3d90700072040c40c40701c1c0094000203289a0030100c071411b031a03140d0246481003030414550103c0c0642c6007a60908040c501e12001917101500b8400c0c400e895003642d0b000c0c0f003950030241c030a520f4001a04c15007050308200a0301030100a03a030700250b05081102d000312070303e000291140b250380c01c2040c0031400e40442d41c84044290341036040d541680d07102004041d0311002e03c0c58403000071000c090381042030908100000e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 514200026 1250 514198776 514198807
    0xa0f030318060e06090f07141504081e16050a0b0307090b0415141306051606020304150515010509010c051203090c12070e01090e01090b07050a02010b0f06 68
    0x948186610401c12440d40c40000312000c2c007107035038001d5110300b04200e1801020000e6800300c0c01444000d102c0280340280140f00d11a800c0c441c60700501e1442480b10105c04001c05940280c0040c00c04d88442c4900980107110050b098a0034206030301c204075014060501c4403c0d8075090364000b07042906410306224000080d50300207051f400401c20700000c000359071100d01001c0c10103084481c0324400c240c264110024111401e04602c0c0c00e07842d0080290304083c641000240040b0740d02c3e82000c07034071000b0808129407821910080035009500000c05c2000300100b04000034800000c002041056449558039125580c0e10701c0c450b40d011071002c1185065540c042c2c1800c0441501c0f0304e0466a1815070f404859145400586000f0300b6944030003550350302490005401742100c041c10f0010407600e49041310003c0900b40600c12001c2140c1e8404d40340c080c11a081d0040c0e40c06135005840d1003164104032a00910a07404000d07414011752a0a17091141c83c508002c650388030b014000c04460400078004e043d04403 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 514201276 1250 514200026 514200041
    0x6090114150901020c030d030c09061701120f050d050304020a14030c1c1e0c15022e050709090c020705010804080d0e0604060507080c2803020f1216020a0f0303 70
    0x5500c00c1038081200e560f4104510f81307c1401da6940070413031244039800a0f04162946e00690244400407000360b98200c5075001e1141195030918000c007550f243c0b8280400443e2075000007130068001c4184100ba980d0b044402580158426540740450aa841d00200701d845080c81d01240d06400c1941c0075240c9250800c0710860700c0170031403882d0549040359030314241d60198507003899911441064200c014003100c03400e010020a00000603130b0000307404071802502c510742c1d0350410440b50820152008041103031144002da856680c5410811414684006400c0210f203102d08108036051250320140c9500c00305034502100c0040c2c480c80c0c41d940341c684e1a1105030704007009901496545407990140800104040c6000742c0c0540c80000322418061001000d80c1c41c000c4c00c0008c1c00c002000444092003003441c0d508042c1d030070031181042c84003031a03000701d020388258507112440e00d501103400302e043e680044038280190419004010001081e60081c0d8035100030350005026205a40d00000c0424082d801c800c8 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 514202526 1250 514201276 514201279
    0x50a170627010212010911040e18012316031118130516110606130e0106170313140603040b0c0c030706020306011b0b0a02090607050f010203060901141509 68
    0x1e1036011000005422600040c0e1491440e0504c140104130b001c269118a024102201600a142c54181001020509405081d0002011039130074116507001c1b0a40c4007440310310601182e019a4200c01c0e400c010360303030002c2d00d0a500c8821081541800c40340a44030340321441c166031812900b0048010b508050040c009008960444944444504c000245104091154441304207411043c41950b00007072515840d140d0446482d404a0107000c22595109040e441c549011400401d1110aa0303500c50301400f0386501c900c5000201c00c0c2034a088110100161940742030741800300032416602c0e0384012a51802c0c6803401c1d006002000460080303205200e2003070f4807400e0500d82c607203440c3c0d44040d5940343d0b51120324152507080d4007105000d030569000d045484ac103445507841220307040003a201c089070020054005a08580e0000d0a080151140300c1581c0510340c01400b541c6041c0036046599001c1c0d4070480310684240c0300c080002c25000f4070546418082c0e4400340030040c050051820307502903a88040a600e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 514203776 1250 514202526 514202581
    0x305071404020405060a02070e100501021e03090d03081902090f0103020f07120302040f0b2a120301121202030c150a060e150406060323060118030b01050a1706 70
    0x101301074448400401242010fa40200aa41d1400c11503100846000e012501c6c822180b5004000a80c0c2c000b4103500340740d0200111640060744032a000c0d00e113110f1204540e40004141c080d5500381a0082c040f0307031241d6101c61026270318081e601c643c84200d100310040c050b40309100d502c0c100f105511a41c00b4007803940c0001c0c0a42e251882c980c4600c00b0001500a08600091b0000f8091189416008902004050040151b4107201c072003807400f041c514410b64002d43e5000c1d0207101c0081d4040402900407a0803184a003d940da503100e400d081ca614180607019540e201d070008400030141e02c000200c8aa01440d2006481c40341e1840c0e9104803a50001f0740300064040e03c0350004902c0d020b0f2814028060481d4100312140f1961110920080d6003646e8440c405061130201c2e07100c000503a0b0011000d4469002d2564a0b0a40d02c441c01600c6841007090406011340600341e002c401c0100060380305060760000ca40e12141603079a03402c4885181e4201144e00800d42002c4007107012a9404800b51081c1e400c0781c1c200 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 514205026 1250 514203776 514203779
    0xa140a03200a050313180b01050a0806041b020312251d090a020702040f060b0d020d02070b070f020c09011a13080f07050a090902090c03090a06020d05180703050714040204 75
    0x502c3c4ca15003059107600d11030004030b4000c001010209400348541802c640c02401207400450020f051402200501ca06100c0c02c0000600c1a90f110b50041050310461070410026402d4000300a45d02d42000f5000d001c6013800d0740100707191245d030100c0a000d1071103416011402642d0810100c40d8181d40c40b038005000101520004900d40c0c6010340c440c4520b90794400143c032030340c19004201c00d0390419644180998503240c014080c2140c000304642098164450242c0c0c0d4211180d00000240b040300406446850440188030b0000e9101c00f9a1030218955401c03039100305000d00030004101e00030b2080c4030b08407060f600d100c0e013152407c6000c1e10001e00f480442183e180e640d462958107005800c034040361181c01440060000d49040700c0268003400304c5400400c03662800340e0200c1c41c540d8020f0002c6d01c1a050100c00148800410001404040e0b84120b09549640c0c1e81341c0500042c000544912400d1508145494a01040055984226074010000b42034940c54030041c2440408039000c1507410903000c010 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 514206276 1250 514205026 514205033
    0x601030c2714061f08070c1106030c0301050933270109061707050904080403171e0a0e0f0f0402070507090516120b0a0e04050a140a03200a 61
    0xb801e034024038035010000140c0b41400800c80e50507601d64426601004460340c01c400e040d4400129584108142803c4804256508000e8140080c0240e81c41d444400001000386400380d40c0040c5040700e0040e103e5002c41d4070380071005009080028a009806801d014400507165054564040c81420141603c21803002c0c2d0360391101d400c107a0714014004a0080300c01000b5014032071248000402c002c0c0b0b4405006035004030748036124503d901c1203500c20540c40c0e000c00c0c1405062003c842c019503115a200410241603458031459030070109601510054102c650822010003030221440301d052644c410700800705103000c016241444000c801d8001c81c0841a0148640f01ca04c010640c19001e54020301c1c0b110b18003060003003a184002c00601001e0355924803044c4854004090140c100e0114102203004140c1a012440c074002a5000d03841c001049010b100c280100403580429080c0221410140c513100b80c1e05c005c0d42d03150300c031000034000390040040c0071003801d00c0040c5000c80300400e401e41d0f1485034543c5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 514207526 1250 514206276 514206281
    0x8071710030209041a09010b01020601030813051309030306050904110409030504090c18050114040b0a030b040207080705060f0c07030503090307080318060a0911040f0605030313050406080601030c27 87
    0x11360854103240251900b07044604901c12a5038041d00d10f40007844034000c100300003511200b041c400204810000308180014030003006a4002801e400303412159403460440d050400f4081802c01900480d02d41000810a82000340b8100e108036000400d03528299010b100788001009105401e43c10007106000100d00c8004038065032319900d06940d00e0900005500741915011205e41d03000c00d040c020480c4440c40f210b000902034034200c40f40e02254a44031130401c40c090f000f0700381c1c030480300f40c0c410700c00251001000035403806003a040740210201e500550b10251032040c0c0000c241c8880b0398044081c019100068443c0b0300a51b070200100b000d480c180314045d41e07007031050380050b200d80d041607000f0000102d04060401120303501041d00d40c03060140c1c003da515804504941c00c003f00d4000d07611842295955500c82c0c1040008000c050b04a0b981c940d00d06402000c40301305401203521aa050080000341c0000000300070341a01c1c1c000e41c0101d0414604810000080b2021100e109002e2105020050044151 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 514208633 1107 514207526 514207531
    0x1090e150f0f040611040902121f0b0c0114090d110109080403030804300f0212030609070c081c0c0c0b01210503040f030c0608071710030209 62
    0x2801d182c0041d09072110720050034140006c0c00200400142e0050142c000794051144464440b6a80c0c5540c500c0c6d10246184801c0031040248251943c400041128201b443c00000c0e2040003151a04000c1c0000c803600c21554114040c6c0c2c0c02c100b50800038130708901070814000c10180c070b010760b04c08205010300c3c04050308000080c000103081101e8080214404d6420748200b8810803901c0d100500030364415448440018040343c80c01c00d11074000200c101d400245035014605564900e000e100900600401e44010002101c0308400400c4243d4000c11a003000b8440c0005000c0c4a8900b40050702c071341d06841401c1101d175a0001c0c01142500c80d0b02419280c0058119405031440d00700520001842803014000d8003001500140b540c540495801c200c0307101d54000240269074032020b54181c0c00450340c05c40480c00707010460360624995003845034049428500001d02c1030b2030b90042011440304 = true := by decide +kernel

theorem cover : BRFrame.Cov 514028776 514208633 := by
  have h0 := BRFrame.cov_init 514028776
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514028776 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 514028776 ≤ n) (h2 : n < 514208633) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
