-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3787
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:40:09.644866+00:00
-- url     : https://prove2.me/submissions/a181daeb-6cbf-4f94-8aa1-8af798f9c610

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 680935251 ≤ n < 681115107 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 680936501 1250 680935251 680935259
    0x60f0b030d23040e07090f120c0b03071110020a0912120c06021c0b1f2a02091303080c0f071103070317221a2d0c010e07 53
    0x224070b892010080c0901c002c0041e0700e41c0d01000401c21030300646950382d22141d03582070401c03004007004400e006a5001002140300851007140340e40c1c3d07260080c1c0d442031900000c3e60505a00340e0443e0000f410303500602c400c00603807026400044c400401084206400143c80c0c82030b0b040010320610083d4412060000c1741c5840c000400c0c14001030148480250900c00c02e60842440d01d80020720500200412140c52400d80702840740385508501c00010b011110742010007100c1e02d481701410318821004022450202c13850130b41d1ba05442c28400d03c040700040d030052100c480e0f0041880e0550485450707682e0040c2080020405030000c0c006174010103900034050411091698080907032048540240c04c040b140102c01c0030660f000c100c0b840c0030703581c80345c0d0a49045240c1c1c52404243c0d0003500b02d81170014034400d680700d07410278011190021903a24020080401c18000d8120038141d200e202844400415415007170f602400f804100c61140300d0303850020740e560070008a42400c403442510400041e400c0304200704 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 680937751 1250 680936501 680936507
    0x110d0305010b4305010b041407180503120c0105090f0c15070204020d0207120305070212090d17041a03010305070521010e0a0b0702160905090708010603060f0b030d 72
    0x54400c5040052070080c40700302045042c400001e0704082801080021801c05001810302d5035907010f540315000902c0310305518000c000a607039101e429441502c8000e0b000a050a21400c7d14441400700a01411082c0341c031a008a802e09060003004504820001103401c8130030800d101306035103c9400c1014000045907a94040e494503115458a8072440c071a00340c0c0703800750100350111160303150300400c1155214540c0c01000c01a42113008180c0786c03040318a5686c20200d0007405554403a9055601070902618400740b0b040362900300d03204c042d800c00070788050f009c000b8129a078964840b4060700c0c035403901e03075113050740542c00381000d40100a1640414001000020300c005940750a5030402c40380d1b403410b982d0706140090180d03494003290515609200c02848400e4001c02d9040307140340640146480d0b90344010040e40d840c201c130740c68240c00000c0e1910822419209511040e005201403080d646926a1500ca150035985150000e132000c039034030030310303020444c1840c411a2407c400540c00b030715003003005400c05 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 680939001 1250 680937751 680937757
    0xb07030804060b3c0a142209030206180a05030d180c0909113102040915050306150d080c0c040629041511010b090403110d0305010b 58
    0x800842c3c035401c400c4490750342c102c059100805640c40c03040c0500e05400070100c04164900c40107031010f07503a0440c41550300b00561100c1c02c0d1010f40420301e6000c1020414058402c82da00301401c0400da00b004102080340050060309441406640180a9030500000075007604040400c8241c650b0b00000d1904005a000700a0b100014801382c0c1c0014070200030110010340c82014000180350100c060404a40c004c0340d68013001c13810b0702030507602500c00707008d4041c04120b450710b0020001d0300c00380804003041c1c0501c041d001504000e14400c0503040c260780d40628029a40d0380f49400140034804a003c1c05070341000c009550780541c55894003135103414500042041d0074000d11000e4034080c6d000560b405440801c01000708a00c0000d0070800c1040d9132a0300703088005981c0c081c0700a503c981c0c0803602025600e40410707a0165822039120f500b0a0440b52070944880d5002c04520310295200d103140e002039544e00c54114400c3d0b000b5114071f120410a040c80a0a21300c1c40107400040c0f520340030040c88a020901c040e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 680940251 1250 680939001 680939003
    0x150f060327070b040807062709090c0b0412030e060306092205120703030c0201060503030a030b1804061b0f0905010c0515090309010e030c0d021c08070b100b07030804 73
    0x41ca070018551010704a09105480d000800103030702c0068001180d503400600b0404440e601c2d42d41c1c0c03800d103d554480c412181c3c00318410358083d560082e41400800819402240468444c10203204155035030000c40c400d68000d5031080c40300c0f050042c1c14074245a0805903884020314215000d52071072810000003420184050416a10400100210596510049000d40b100e0703822404580080079481c5d5500081e90203203c0407000607051080d40014540140114019540b00402450a25011690880040c0300e0342c00f0880d17001000d528040040f1100c40030b454010342c000c900104458074034088003500c40c8400501c80080041015442180943c0070554200350364003440c04142d510428200f0314030b440e20b0300210040010410007845000c0c5000001840392040c00e884402c8184040010581c0310454000a903810030b0313030045504018508122030000c12076104208803003054460b114802c4580000c0300494803c17000e00240042c001d03603164080d008082c90022240f40c001c466a00401002020748 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 680941501 1250 680940251 680940301
    0x4150e010312180e071e0e0f04180b04030915050a0c111207030605010b040503061f0f0e04020f090103030c11040e030d050a0501050103060819050312150f0603 70
    0x305085100725480610641c4560000b1007943d20741130200e050741000e9078428007081c01e403105070b407a80d248252001e02c0300740d0b02c0d00c1d01040f00c41100300303012945001442e1664402d9032944001044035114403190145030145280b11014a40303490081c0c2110115000444070b5200320304810b210542c4041143d04407401c1c1e2800c20a18250b52600303c2e880030039040c0043d03000c14010041181810000340c0c03001164061241070003103980e600c4e42d03442c0502ca54021580c06410407000134a010310403404500085001269001c84190b40e6a2031403040071458002110ba00c000c0c406000541c548246440f0a85c402140c01c010701d035142d590007501031054a5001010142c1c1c0103d52016503540d5807003054181c40400170350780d494075401d044900800701200e0002440d46464008a1554800d1044505480000c001022000c03000421001c0a0604140858092108000041d400a06590954041d007040110100d84124407030030040921800c02c0d146020384401d004104a01028020000402000c40c07 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 680942751 1250 680941501 680941523
    0x6060905090723041b1d0604080d05031f060824090a051504110c0601080a02010c0201080901020f0a031b0c0320030f0a1e0c0c140319030201060504150e0103 69
    0x30001c00c019017617462890390002d001800003400903030000720700300341c0c220b03c0150714007a150154108402c40c000e5000350b0b50301d548040241403040707015000540d003008501304c0b0102da4240010480d4468511038010300700003000d0f0414091041d410100b409440c80f2103c1540d26a03800d900081803d03010028030180c6040e0300d402c08240c40080300031103002c80c0c41001d8030900c241007141d07054240e00d610100c941d18040c403901c0c000296044001c94490010340e8160f54403031a5012580044032001da002e40115a255800c004051421028034002c00081c8955280807410400071600582e01d01e24100101e82070140700c9030b1040c0000c3d80303c42513a0b442003e2029a2100f00d60304000e039442c5000392200e01c2419000020b196010640107021484580307020351080100d0301c900a41129503241000d8020300407a030958050280c0d64100031301031001a03020b0111060580c80c0a0314803905000d191058002d40d65400091001d41024050425146007201300081e8480c43d2110751904524140f0025100c9120f13a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 680944001 1250 680942751 680942819
    0x306100e030a080a090e0912030705041707090c051606020c0f030706050108010501060c211e17060a120b0705040b130f05100e012307060609050907 65
    0x1800420200d160140c00c4520b000e40d03600e07240c0850784c031884504003c26aa03520010b440d20b007210703110707208012001c09410400000d4104d52002d0304082c109030107210081c403011609149190498075034200880041540c10724040d0002c044034000300d900d0701041010021030201404580307240c4445a440341d0016030b0b4a0110310803c0c140744046103800301a010002c0c042090040d281c10941c143c80401008114503607031408280d5071000001d10061032042c8034480d40d0061804a20090842c0c0c10a0903c00000c0368441c55007091032070394264010114050020b001040000310301b00c141c1c803c1c4c00f9101c0d0413141d414864551665540e914005100b010307600d000949892041c07054500421003c0100ca8480083c103441d002e6107a610700562485140a06000031903140101558400e4942a100c00c1d801400480044418001c6000888131103c98020380030905501000140f5030940103510008019085c182004217640014140d01d00583c0401401d000451911003401c070303544910340300481c20701a9 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 680945251 1250 680944001 680944007
    0x1707091d0a0318150801080706090f03030e0f04020c06151210020d0608010207030f1206031e030306170312090a02091603110d0501030b060406180c050c030408010c180803030610 78
    0x40d50481004c5640b19108120955004200141030b2034416003900d22164032004120b0b40780c1480c1c80780554500040c5d100b000800c1c0103110070719a6038406440c1d21040030760390003c0b8043e03038003906021f4550340c00b603402c000000200c03c444800401046032000c0d100c0380f104900582e0764070a400210825540000c14402d241d2030396000200500c0441c000b50340750341460401402c08400c0e0041d05020500c6c0107078540500c400c03032141500f0b481d8010158204807811000d440e00f0002c005e201102815071b9039138049140b003891090001c60300c0c0454019a5566901c0700c0e00301a07504060041c80150303000b021058016920b10680c640e000c071403003080030031086680d6002c90140c24035060015a42c4000034100711241c0091708600d05a07400b9400b00340c1c182d11414144411981140301e240004030148040240404464220308140c010b03e142803800c0890078000203003140d001c1c0d441070040b80e5507403625003a40c2d50800505140c004629100040242c034000155032a0301c002005144955a500140d48901e40 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 680946501 1250 680945251 680945297
    0x14180a02161406010305120405060711040e0111040504150b0702040e070f0602031209030c1b0d0b0a0b030105071e08060607050d081504110418061707091d0a03 70
    0x5000b820a07110101c501c2d000d103071503500a000c1a2041c1c010880ca1040d21100182110200e58000c0c1c41c1600d0404103448421002e03011202c520707070154031460021603c41017406507003030b0b2401402c680c41d5103500e0301040000310342400c80e0104081d949040b04200b40c0344198290354903141c054402103043e0b05803080d0b02c3d0428503141c005c00d41d142841c01c80891000c0d070000181c0807107508402c451010b03899101c070303d13a660b000307030059a840c41e84008003001780d01c1c00e50101d4990031980a0030b801c1100c030450f940c0007400b500c11104400e1030b5540d01d2860320701749000d0042981058060070004030168004038045080481e1900e048140b01e5104085580c42e01c440003191041c68005042c3c40c2ea03605011801807643c0320a171510648803110850012480c500f911070005016400b000340c40c64240f8081c0166004500d10840b018202e5607150300150721a800b90380c1844480420015007280d48c1003442c46821580020842d031810003481c0148460350b40d0020316180081d415080510743ca1b0000e000401401c4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 680947751 1250 680946501 680946503
    0x41d0105040b010e1509061911150f070c0c0b1c0b15190228050706020c01050409051b131802120109091103010f0902091311150f1314180a0216 63
    0x2c8400230984150b44040e0040c400354020301518101254945040c8411005881d00503040d0040c0e0080f402c00c03801084070700c0444e842076501c4103440d42e03164145071054101e440d10170425071052140d004100c0d1a031050a0008004a40d103000450501d144172041d23002c1c03650610302c5000d0402e20418035a00800000b0140340c9107038240840700e660201ca2081c8800f00b42c004407414420714001061050000c100c9071f03015181a542c040c00c0074178050300e007005400084d1400c0c08240c0700c81d51491a40d002000102901e4210300034420109143c1221000c0326940940d403110170b14814040c1981d10162500141d04503540c1d004045030b09162410141e81401d41081c515038550301c0d200709188060001d82100100900031141030800d039032001c0884a010034a03680040124080202228036450210041032041c0440325110742800440000c0701030700d0b401040407000440311030314200000e0001c401c40d9420704406441104007001c92442e14600e0560290804590680104140300c1c8040341c400c543c0542 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 680949001 1250 680947751 680947777
    0x503041e0609030e1f02030a0309020a0f0e100902090a03080a032c010608010203250c050601140f01051201090203130f0807020316150c020105041d0105040b010e150906 74
    0x182d500c0c500a4968840c076409180240c1e143d80900c20190031840c030002404156030080d51800e10204021801410443e900300ea100305c52410114080583c40d2501c1c0103086200500b80c0b80b41003035541d41c0802c1400c0d0b80f040c001e180c0100074624180e280c0314950000c482c1d125200316103d603103800c41a000780582440800b008400e1590806907103210714000300e000d0341410001c00100751105146800e074031084603440c01c0c0b9000084099005141c01502c400340e2009480c1a903a0500a9a00c20303003425802e9100401282200c04e680c2801c0c43d0841702c1d60480c0c5801d00b0a43c0c40d10040249810721010148a9508081e81c048005100807002324800550709901206600c0042d0312894041d80c00e03003150b80c069001c2e100e0380054040010300c1c20402c5040d00c000d0190310b49440b0300030385c00311203207840404102d041100500c030000d03000c0f04034a202060b1141050104c0c070207606101c2400111f50280c00c15504118940012a00039210b29a640144106001801c0d41e0307001e016000c581a84610700a843c05 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 680950251 1250 680949001 680949011
    0x5070c17250302010c0206070809060304030c02013f0b0604080105011a040b120915010303030b01141c05060402090909210708040e060307030c0f050118060503041e06 73
    0xe044400306141805040040c1101d24400300107030410140d8180e400001e000c40d0556280d000549001805840420f1280503401d24010601c8042552600242c41c01c0f4003095410010f00110342c3c1080c0d08002384104001d0482d07015480130020172804a00e40180d80304c44010407460a0585160703080003003505c0340500115621980e40fa0600e00a0800344903c0900f00d02001c0184c6207110000100c40071208600c03074203030030960072031005400d510000c0c018401c0c52240300c3d400080c180490001d58000c5d800782e10001600c0d40c41e5000074041401582e2804c0404904201c40c00070b50740740c90421600d8040da0740f400074440d510307640410000e01c01ca0500c56441003200042000b00d00002030000d22500003410708289030070142e201d8500034040e803c03009001c00703000c1c4014042c2d43e012046050b405a002021078030002c8d680c1d100c641e400381194000c0c03034a032960000c01303110030b50f0000c1d0f40c0c5022403604807002d0f00b99803801800034014000500014500b000040d0042103640c40341e51544083d40d008041002 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 680951501 1250 680950251 680950289
    0x402060a030906201b0705240d060e160c031b0201020705061315030902090f060414040606080d020304150c0201020a0804060801050f0402070c1e08030403140601080a080a05070c 78
    0x100a0700321703842600e20080301030012801c491010804c00c04854000d090f04a10000203d02d00c98031a608203504020b0030030503c0070f01c60403515801240300604001e40c280f101c9090217550040c07050078005400061140401e19500080c0c1d001c90715024481d5000707041c0c20076800e1840101c1c01c11484e588400d611910215100b00c50202f420362000803a0031402e1030600c035521048040e0f055441010019511441900014181001e556a2036070711180003417000803a80717140c4402a05881c03081d41c040e40e99554480c0140600b01c0104448080e60856000441c10075140003d8000500741c0c6884c444108403005900fa8110390082085103200e0398454140c9440e19290040103220f00700c2481514880c0c0c070702c0000c44800d81068401c903803003070303030886001e00c0a01d040540b000201540809850f5555a51141c00600180107002030005548648040032070994260303451850308106802954507500a04141c4001410100c1142c40081c07081c14450340340c0c5a50301300a40ca88005611904210340c048a10403 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 680952751 1250 680951501 680951561
    0x3170c0f0601060809160b1303050109050c03060a02071e060905060a140a09050303160219031d0f0306040f020a0f0b0c1203100909060209100c1403030402060a030906 73
    0x94143d07143ea9840c03050550320460306555411310090703528050076841c00c06108507043d820040c40c248941400d035500045d60b982d6000c3c01c4801420050b030b002c1d00303e03440d00c6149140a210307868120210710420740c10300003640c0700c542609194051580d2040c46c44141d201c10044150451401c4075000b206403030941c98a1700503800a01119034101d000c012440c000501205503a1141ca010990484021810343e5902c98203022480710f10b02e5008258031a41900d04054030b44190314034074003403203540d48820030000448031800301d2a018146034800c00c890195210980ca0004540da845608074800035000101400031420803001500050540f4681100208131252100c000300040c60190007244c4030341140071952250b90000350303840c0ad00e00300c01403400c011300c0461740c100240b02401454010301e0441c80e0030000340c1040c010031003040490280c0d000e1100b408018210032071034582e004051b43ca10f00e000c1d4009440c610079800000306150740e8550403401e0013407560200c1301d1650039215060080b103080041c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 680954001 1250 680952751 680952763
    0x3280302060603011118012f0f0a1a070e1c02011206053001242103141c052a0417280b01050105070b0103170c0f 50
    0x1900903114510100d08181414840c00d10408164086a03090000e00c504c0d14014884040344181000000d8020341c2d0000d000b4000c0c80b42040440c14031000003071b040507004d420138003182d51060130b64111070344403000b10340c00318910000e0121100c0c03054402d5032558800c0d10070050104000d5006141c440b1460281ea2903c01400701c8036001341c03182c0089d614101400e100340e55890080d980c2107180c12000c815440e10180d00f0281d854100c1c420121780f51130b24510b40742103840c04500794078069914542d900310081d500d0301d6600a407805c080e031250145240d080283c4071800a510003002c0160381400881c091005c075042e01c02c601190b51b88030312501341c4001d902019003002da44080d29074402d0340d02001400004120b082210020f50041420640740c855a00840d010b042000c9110740900210b040300120b060010351044106000c4018120301300d824003d00c0708505030491814001c5c1000000007050030030030302e181140c7c0d03c881c10f01c024200602070704e00784e07004400008406205120142820907400f00300 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 680955251 1250 680954001 680954003
    0x318010e03030601030501140d0b070201020f190809030a020322030b07021b0607031b11031606031d100c09051009140405010b12040c0302060d2c030909060328 70
    0x2091081703982310654904040310f600e000c41d511030803000006000407155800e607030740450180001818603418181308400d9034041e2444c240e050401c0c0c0804c5642d039400001142c0c00c01c5484005500300801154083d56038894454590911080145200307441d00012810760083c1d80d0080a2200d01d040041019507910180510307034000d00c101c165083c4403410070000f580c40d400d800d643c80300b9440c0d1a141a005903045184003c1c2c4810054140c85070072034804010422034610400e0030b01510a150560043c101d40d25230152002c40701190290440d40580040c600805802c4610700084003d8079034402d640c8601558460f0760041a6003005036201508003030014212401408400c1610a40c54100702c12200c3c00d00858000c0742c0c051200e84010031500d40c0c20340c0d0241c4180e03480f615441e140d400051064100c3c1d03c84c0b155483e114074a00780031555901404800600b421030010510705401170321b50300e1b80680a41540196001e100084d510340c0c040000902c49441e030100d4002c04544941800340d0411103103c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 680956501 1250 680955251 680955257
    0x2061c0506030705100c0201050f0f0f03161707080702070e09030d0f02030403080112050c1809100504050c10030b0a060f02060f190504060b030f010b031908040b0318010e03030601 79
    0xc000242d90038200001c0c070840704196101b00c04441d03217031300540c3d198016014521241800340102848002540028540e42401c01b0a00741c8a181c03e0000360703502c2c0203c0341d40e00308001c0c0f60201c6009034540a03024640101c96810440c00703e542d400412858607581b54091443e94111401340f080c9054040002d148220703110324207120301c5c0c2c0e84440510503440152402400107500c21300410541d02c0711030080340028414400d4030400340c1228002030a801902444999002c00281407250f411402c015800003140e141600340a58a49a03c07040d4503201243c900c1405400700360003008040b4480d6116510002004040d900110780b142001001065003000c4000075101f0400031502a9510307841851044004c032111009002c13044440e1000341c1130241045603100e0b1580102c3c0070030354003805002c11081c1a00000030350501180101490401075102501c0c00c208002d4455011641d000102c1c1d056500031800c1640e00d4403520b50100f00c02c03060a04807030055203841d55202500c100400114020503090ba = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 680957751 1250 680956501 680956513
    0x10f080d03150902160c090b121f02090105040807030506010608010b0c0703020d02040b0d0303050417090d02040203091c05031b0a0e04050903041e09110705100902061c050603 77
    0xd2420740c11600c030100211441c2e06510410028603400750001c211075100310b00f5036144c141d640e54903003e60344059040b10695a80310400c2d00796906050003c151400d40900051005400720f420a801c2e0303c81421010781040c5d000150003480341d0095003164001c140c03a004444109682e41412516500280540c400054800000041252600041c0ca81d010300c0c800280580910f190308004c00b148550350f0480e0040c2e103c0740c9003070640e41c502080081c1240a610081520300e040c0c42c141015260349001e880c10100140300074407280e154a10900c01c40ba40c1a40c4c0143d6070740b60740480d0307460f0000d204102c00c12003006680880c107142d40400514081c0c01c84805802800c041459411b0382802120301d81c10008116400c000814075068001075080450707203050b2071510341c640341402250749806403941041050106c0410900303003d031040c05c507100700080d0303450305110080d500c80752502c0c0603200b07502201e91a2a5210250b44e2250f08464030b40e0364100003025000c2c201c00c0200e014200c2220090b1203030040c4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 680959001 1250 680957751 680957773
    0x80414010305060108010b07300f1e110a0b191503020f060703090b0a05070302060a050c030f0703060b12010509060a031718060c0a05071e210b010f08 66
    0x1e8000c9600034101612514407581c20315101030410b4200702015112201907040302d4403241d94011100301142c0c040c81807494140c0c2c0c1503402406550303551002c40308203d43c08040001c5802003200300c03804007240d454081d003410705401c8051b00d4079100103009003002102c4014881581402411209508881d82d0b003400b02100c18000352150380e04502c40650010701c00700020b040c516041700144089446414601ca12035103c90004010390041904035001c101c000904c1c1c000d141c4c04005190707004c0303ca80d5080c4403d143c5811003291a0002a01103500c280320200400e00d03240c040e40100014011362800d41d6101c140318509440c00c03190a1103154021404040415a20f04001c00c000040d2a040b080b04400c1c40074400c01c2d07810302c0d4800482d6480c808034512203050159070700030040c44c94a104800600d07640206003006400e1170a0b039031140034068603802d82e000003582d40c40140822144600100c1135841e444080018071000310520040504110000202d2242c16581c4500c064a580c0011289101c0503 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 680960251 1250 680959001 680959007
    0xd034103011a0c030f07021809060a06080705030703020f010512041a0105030606030c10030e070308190503010602070513020702040e15010923041a0106021005070516020d080c0a08041401 82
    0x52011001254004100c010b2014000b135001b072025a1000c7c1110a05013100070b030030300313011501b0703540280107410000501c2100741080c080c0c00b02402083c406000124a8a40007030740d62002403000901600b000d120072196607000d00b00751011108e010010700107600d86851b1000034201c40e046040c0d0b500520f03000102d918100026024865000980240340b010260420003a541c51340400283c101500d51301c0440f0484e100340046c074000d512502c02c040d02c032900001a24040f1040f40024420024140010442181d00290b01c0301159000c3c1e03504d090b41e900720307031110000e40300302da40c041e400c94100411801130190000309015042c080003420141a62900e200c18269054103003e40b422220000d020501042c4401559401500c0781d07070711070000d01c50b0000000803010268042c1c005a0000c04101300000664003400c0d82c040802e1900d181f520b4030301060221500d40750381c0d02a005e0200001d024081000c00b004952108406030221041182c00e032a049280f036120740524658500c0080c2c018083d540 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 680961501 1250 680960251 680960257
    0x10e011401120b040c0819060b0d020a03031d04061203030c0318240509160e0708070e240702040b040b0a12060209040f05150d034103011a 61
    0x2220800c000c02a0140d1203803c025100644103440354080c210002844c100100b014030101c94600201c1c4000040d281080700442d071040401178010030008180000680c0c4204000040d00d50505001102c1140d0b0102d1000c2058148107854019140070404641151078101da0071280d8400d0364144000f4802d560f0450030764410000303000c1074106000604001401145e5980b81140d2620704c030502c80c500e001904010340300c069032110701c260001d48001030789041110880025010b0b411480c696414103007401841d840c03000b4000020440c0c00440c01085903203642400e001080b100488085003004001f20981d2540080e00c220321582c500354000103107003454001d9408070740009002030017481c5406043d450481040d001210700590030400030450762b03510700c2502240540b03408002130130328141c4803000428503011a128440c4803503174107074000254030140d02d170003104038140da080a60507101c01c448940181150056001c54240c191044500904000746048a44188414000a0941c240008144 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 680962751 1250 680961501 680961509
    0x3010c032f0f07032d080703051e010305073206030c1c050a0b0117041b03210f0906080708070e0402030a0e1e070302130e070602010e011401 62
    0x340010740c51100058005140341400112036054524080154120642c0c1e903020741c80440100350132000c00c402e400644000400b0400c110b080c441c02c0c4c080d104e040500f814000810078800c1507155400101e030300d17005010f00d00b0717103150200060b035465840340303811900c61344103001700041d80000c0c0259002c880c1d006864002d801811200f2a17514a861034240401503000070300001d4040c86c00c12611400e489020004040c1600914000402d41410000302058581d1752188a04101d010301120020101012100d60040d074010b40c5010b100d02000c101c102c1181180d44090225a2040c1c54042240103000a0101c190015a283c001c0910901020f642c46603440c0506800510003c00182d5000c0c021482c00f0340000303035030500a9001c2040c10008051342d00445988040e151120358008200300b04010350205450501100c3c16403000c040301c074554845017844043c1c42080340c4800381c0c0d02100940e10160340070010324180c0d80500c1d200c0b403001c1d01170598209074049961900003403120040fa0412403070305031 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 680964001 1250 680962751 680962781
    0x9140402010e0411042d0305010b0301050c1c0b04110d05220b0708070302040b0708191e1b020307080a17040b04090507030b0907030b090907080c01050d0603020406030f0203010c03 79
    0x6061128240c0d00800c1c061152040d1800c0c0d206c4684040080c440c0e420055200d14000b1803022601c106041c2902c07800f801c65120074005001c40020050428942281c4c542c40302d4000816a20400c0000d0240c854000c1c0c0c125202400500b414003051984c022500c2182c0341055052486081c0491030b84000320200050590038290000c140303650b215402c12508210145000343c00d0603280d519012180d4082c0c402161101030002c0d0b001080784034080018286039441c2403d00810440c407040c00051f2628040000420a05080180d440141a070a032801103402a040f900364980383e0103825940c10001c2800c0d600c0c02c03460360240c9075140081040300c0503100c030303411010b041502d0000307144c020701005070424041c15160108066162142c02910703120301030a42d800700c1d10021400c01d010380480054155000f40c0c0090b84240030b5a03000084182104000703181ca1540c03003005502c0d90300100003e4000030741c0b00307003020800028070040101c1d4852181c002c600801c5407021130305050f000c0700d048508509007 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 680965251 1250 680964001 680964007
    0x3090303060108070c0b0112114e0606010210111603050720010f02121206060d020a050a030c08060d03110a05120d140103082209140402010e0411 64
    0x3035100f1424643c000e00c441c1001c040e180956920850083d409130000b0108201c071074405014440d10b51000f5140785402d549020f10766200e0080c0d84c81d083c0803c80d0440940124130400c42080341d1080e60070790b06110f1517401c2c006030380740d019000740c0b10841a144c90340180704a443c0c002c02404180310340503910610380351041c5441203420543c000710302141c5082e82446070034001a0042003031142a50800c240b15418031203041c00704000584581d56002c102821580702e5040700c280c110b5248200d070150550100d205010f6590322000a0841c8503003000810440d001192034071516401002400d05101c150302d040c000b00c3c0c1c07100803c4840d00e000b00c40c0789501c1070401e5894004280564407652840b140402914481852904d519160104000d00301c0407880b000601b0425250300f80c03144488692180e0040c070300d554915110030200c2d0007400503824111081414400c002c80d80100c41c0001000c031400b0500c0301142940004002c4e000c2140c00782d0118400505200742c0b40303890f10552580080800190381 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 680966501 1250 680965251 680965261
    0x3020d0609020303070b0403020f03090904060f02040506040e090c0916080a0f06030b0108150f07180e1e0c03070f140d0e210f0a1803060c05040807080303090303 71
    0x4650081840658100c0d5a03490410050b882c2407006002c03050040001808a00381858020720384528a102120140c00600c100413540d034824090581040d00101e002c250f114101c031000000388580e502c4981d001c81b00041c0021400d410720280b51291160f8815102c0300200d14050040c025001c44001c688094074801202542d80600525900260088400102d0010000000c808c4a038140c10039541e40c50504010000b0803802c000d01d2004000ca0b03104954982880b0300b0040d10010302a180c00284012001c18201394118036000b04000c1c9281d900c3c200703190a000d0300c0516035110f03d800010041850740b0010310480588170449010740000ea0b00c0700001401400100d8013142010b0320300300e4400c030412030b02158080500845800c120300601410300107015200c0101d5440b101181c1020084084c003910954400400648040035158144100100946a00003039108070035000104414a08001100c00550007009041600c49503022100c110341c40e0003440ba564001220100040d5000f040050 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 680967751 1250 680966501 680966509
    0x60c071203020715060b07020406080a0305030610050d050c1b07061b230f060703060e0f07050d0501080609150609060634020a090c0f110c030102070501020912070b03010302 76
    0x904d0190800e10000d506a4101509440655011801e4400045807481c154a40382c07044500030241480149000d0210341d40c060024000200220300c40d0707804210002003540128101e41510002910401103845c0245a010480c1c0240240750359a00ca4400d1035011610001610700c1a0f034500d417207460300c010031500303040600d188689088601e190140340a25840548110703001c0826020000742175055166059145401d500510540805041c40707001c00120611381d803e1608141d08100313466039a83d441e4810b580320b01c21904001c00c903514100000408800200301c140c0500424410713102035800c2903200d044801800c3d20703283c0c0c3c4020010042085440c2910040c140c81c8401700001000585c3c80c1c40c44040001d000444220300c07060f4002002c1103140010321007001d0305203440d04005e00340b040080100150324a2066505000000442450800003000130fa20400c100400942d0703585aa46003c6010790084c648950040c10000d80d0744445003004a50b100a41d8240c014083c2076070300c0c6400300 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 680969001 1250 680967751 680967757
    0xf030605010f1d040b040e010507181805060103180318060203040e1501020f0f0d03270f080d0c0519051c021810052101082a1c05060c07120302 63
    0x43c0d0700a546100b1030b44986c440b8010941050b9800000107040d00e000e482c05400d02c2274115410f0b21604401405002035107040028031740c001c18541001606036103041c01078000308034820050754802c20120042041551020350380a1441640780d524148555403103099959009600a00104519103800500c8010f5540c0a9004c0d8403014411104003640584a15040c070440e6105204c260b00603040406940c2c2c3c060003402e5080070070403080c2c00341101000000c204411600402402c481c8254450300610003418140c07040205020030800585090000261503a8040354118444501c1e40d0706a08109005805891442152081c0700042c600360700f10540080d030005070b03010101c01041c5039540345502c0320f02c0c595902d0703c15511201e50756110440b04025007188080450306810740e00f40180250311011508416282c101e200d010030a9500c902d0700e00010740c03e4281d40384c100c100840c00b190601702a1700c8040c1c210b40910b00303588980c0c03690382d0040245e128100c805410780c4c0314045040110391085e402 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 680970251 1250 680969001 680969057
    0xa11031302151b060a050907050f060a030615110c030105070e101814040e010b010905060d1b0806011701080d050315030f011b0c0213020a0c0b070f030605010f 70
    0x20346014820b030790aa4401d4041400f1007520f0780120104036a412a520486070480c8010008000e01440c01000900c090b0a0711303440ca029400109244001c2402034200c40003a000d2410404805134400c50300505401030400c0c1040300c1d20448110314614201841050300600300e035070741c6180a20a090030301040308049050801040750000b61440707032030f040040c4d40d000340251a4042c04500780c08c404110035101080c41e16005a45454221030b2170740e810002c003004a417401c1c1d904036281c80c10700d850f1034020880c415806c03040300d07040b098501d15aa03000e501d00340301d4030007600c80000ba950300b030304409414202402829407a038010241c80c1000e500030740c00341d0350003200c1c044100200b543c140c0229092450804080f12070380c0d11070082c05100654904141e040f42c40e2803030803240360070346a0002220b100000f40900300007a40099007000c51481001c1010f943c1e034001440030818141224000d1503034518000740c00009243c1031020810398403500c80d608000516980701500380c40d0403080589034400c0c180c4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 680971501 1250 680970251 680970289
    0x1103092a0913060203040b060108010503031812210d0513031706121501030b0919200a0b0405100e0d0b06120d031a01030b030715030b0d0b0a11031302 66
    0x2502d1000800074001584150300c2400c1e22222400c0c030b01d0000d454404180c010034070a81080c89120b81e8940200104010414110f0701a03804c21071f039854250510400c100420560000c80e00045a21024100100642c4051030001c00c4240c3d80c40442b0420041d074031100800150581000f1075144d1030880505411100040504070408805030b0160315042003080305110a002c00401002404005103505500000c1d12009d003040241300c2490f0004c4441c400c00003008000030858501c64000000382c200f078000c00c05400c1c1140d4680b01c40e0642d000760030a109281c0f041d0740310100541418402c203080b4500a2001c0c1089905206585e02d40a949200429551300120210a02d0b02d40e00020042c0d1038001da00d546000658505818074a00101407420030181814205050070400340c60024038442242c44941c40f0b02581d00319000101c000c1c14022005aa00403100c040440601030400303842d9004c0d40c440c035001c11010440c0004203001c1d020840d8180c4218901d01c170394402504140b4882c20045210407 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 680972751 1250 680971501 680971531
    0x5150d020102120d0f060e070206060405150909071a0408070b190c0501090b07030b040e010c0207121a04150e06270c0402070804051c0807241103092a09 67
    0x103035005c800c0358100c1c3d000c490300c402e515060000840d018007049801030b000750b41c01c1c02603141a1a24107010350b4070041c8140504076038000640615024443c84c0e005d0022101d01610f402054840e440c1c2c0b40d0458011451580645040080e03070641e608100d80200d980d141c0000400c01c0480410740701c030b403591a41580d80f55220074802c00000e401c00d03801c6105d8001a1400523009000c00d060004849d540c0c1d482004a0389400c110400844c0c00161000c101c0b0024016050014501d20700000b0300303611044040f40c070741302000074001008400c42c0d546c19007040d282c01c104507103101130440315aa90000e0301c5104403800085040091803201c45044405404c51100311240c1241c0307400420101d0780401d500b6074244900ac41d00303000a1806692081c48a05901d00c00c02c030314040340d11000b18901c21200d00501c00034412011988236688450032008001907001e08005a010510320344c5159072088410000f41d0164014a0640504039200b0305100f1416110500e040219403060040f425005050040f20031441 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 680974001 1250 680972751 680972771
    0x9051e0c060919081b0603040b0c090109030b010303170a0c272102031203040510051b0304061a060c150a0603020a0f03030e040c0e01030911031005150d020102120d 72
    0x142c001030000c0c090140140b6904410741030990b00e8503046013003184102001c01c282320215000620b0550080c491038482981c0358049401600c1070412940b008200840b04030002050580094001d072040e0070740544402d455440700e0010040b1075800040c0c5c0c010851030350362858514052070700760802d01108410a17000307617140c0c00e6030980c29800e502210082c075280041502141414040148101070300d25050341903050a640719a22504503604c0c04056a030348100080341502e414440501a105440203682d07640bc050518001800700ca0691110701000e80c1c400d00b0160a00e802200e44459612014024041e40e5103942501020007500c4400c1c80c03a00c4100200159607070b0720030000104906030200c0340c140d14506d8003a0201822001301c40c816440d00500c030510795008038040e481070900f4600013803007040c10315210030041c901c0d8a0040e0140304201d0540320900d025032005001c1c052945d41446400da0200030801c980070302c4140240141c0041d04200d4600c60b403040a40008024560702090200034 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 680975251 1250 680974001 680974039
    0x150d0620071208072c040b27040609020414060109050a05060d0f0e0102040b0a090e0f0a090212061303031b020d0513120804090f09111203071509051e0c0609 69
    0x50004c00d8104c40ca240300c0c2074402d03260900c11204040c2013035420481149500072036075448e44410802c542d241103100000b03820802658014211140d00130401c01c0742d4182d81c01c941c84801000c4801c0c5020400d00000030400d4a0301012036411a50001e20341450184200c048a01030481003602c034188a8880901e610011401c0c0060009001080140c540307403c07030782038000d214180945c400b00803460700009000c005454086542c0c1e0184da10180405c07541c9180c03001c64842c030481d0300d501d04640504400d103c130401058941960040c007940c0d0901900fa00203402d2001154108070001c0035910040f041c6800d02e003d08007501c55181544c0c2541e40d09030341c80e03a8020903100210411520140000340a2024002030301c00c20400d201101e40030041c2d01c0c2a44c0d81c0e410105100c0e2219031064028400c03144039a8800c00499645640c003505200341015408502009032201e081c003120180180e62103601084004200a002e101c130040040051402000500c011035005103412a0400e10070b901162074501 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 680976501 1250 680975251 680975297
    0x412063603020c12150109020408070603470103110a030b150d05013014030f0f0403030f02030a02070e0c07022713020a0905150d062007120807 63
    0x40300300241c42c0c24685020f003054000c170160841c44006205000900a2002c00240e440a03141d41e81400220705000c0100503129020440b4075551203c5030740d0451801e00c0d000001034204004514410300c051411200540940307055503000c1070f030100c09025419180f48070790010340781d17040e0203004104e644510b103110f80c00c6030707000c0744001c002c1c107454130b0040200400c00484040307035804010f003070202241e031442090380b444903145010b000000460444480b0400c103008861800030400d00386070340c50007440c0d850700ca41e8103d44026000f10302000f808007407244c0088121840d61420b81e004c0c0c89002d080414030306200c1d00160803102d501c00f0501042f03005844d1458500b511514500b100c860302c1100224411807620010725101c3d0000c01c440c2c0903001a21090519130607940c102801050955445036920418001c00700000c1d4070028185800d000d00c103080d804070306441c030b12a4200714400303281d00c41c0010034820100014001c10007941405d1801e485200030b580c03c01d00c28a0540480c40d80702400b80c1d8010303 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 680977751 1250 680976501 680976529
    0x131803031e06050105070b070203090a17250b1318050906013f05070312030c0503010b070618022d1905150f0412063603020c 55
    0x29903501400c036240108000254207000744600620805050800007041c901500c44018080f601e13150214070014001d1066441042c806441e031030055981d0001480e010118140540045c0205010704450001c0744580d044400390301050030b02d00c06d141c000b450200c0d5004031880102056500701c0420510342d2041051014031411801043c2d0b420410403090600c03d060340304c0c51012075000400f10002c0841750b01030051184000ca0355034800402d103040040e40c0340c1014000d010340221013001c001c000a007a0741c4030400c0c505944c104a00c61107030354161141c0c4028001c40e89062000e0082c0000101c8680100c0b140400030382ca502883c1c03165501095443c0101d20458140c28072824015034001500918019400c800300c485c80c60485810403603609500c00c80c040d55024603509a0345a508906800032524071420354500340d40c0e9241d1300c0300700c0c007001c00020f001207481c1418081441c0d8011100b5004440349141b5400750443c0c084500158014000340c244110207600400612344582d40d90b0b640c5c06440302c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 680979001 1250 680977751 680977757
    0x513050603040b09161a07050c0a08070806010b0c0a0b0c0d1a18040c1205030412030306050f01050c07052808010207060b0901030f0b040609060c0914011d131803 71
    0x1504200d0030841c1805e44030b4168440d1004a09406c01020110003907051165401d20070280e640e45d0a81002400d04180312034030b03504100030040020381d4450003e0713005c0c00c80700722100340d8141366262148850648a480c000b402603034030007150440407074881d03140c0641103280c10b00c40c01d14111540810106950516200b1035480740c10b40162100c90904e107d0598a909071402110b4144c03820f40c0e030f50305c05004a801811035241c41c0001690402c0010021a4041e29080340c016405140c14940100509030714011113004032046480a4035a50007801a500000d0700c2c40e024012990402080c4010803404002c1705180641c2e008092440c2c006860000d0b000c0c240c000005aa80c0c450360400c0000d4900102c541c500550040c001000496108003003582440d50040308203445440340e00300f01010b00180a0050a103501d00100f404545420445480407a90313036034050180c0c021400015900040551b5250070421019000c10702c0c1468080c294507501c01d501d40d000540c1903501c818031707001504001401c40c08 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 680980251 1250 680979001 680979023
    0x601030e1542030c10080a0b01200d03060b0304020102030d0c2a1a0f04031d120109142a1c080409151d090f1b01080a1506051305060304 60
    0xc0b402e0130300c52503100480950300c01421802c0c0710001001940014000360703089a607961040000c0c2e201d0b803d43d240709440b00340302c8140d040001041c19154965613242d4404070b850200001600000d030420b5a11071078050300550300b0089240c080201070808090004100100001801c0f00516880450f4001c45a03981c01300f0003400c0c1c0d5240c01c201c41e40e0b40702c0100355044c40d642c003045084c45900081591159052401481c030181e200001c0e455140b5164495074408800d10003009828015807099102c0c601444107801e80d804150581601c600d04010440d035580664240801c00c2c018050400c02004000380c040712458a6241d15080c03904036840d01190a4000054208910205c41c003541d40c1801c0f80490444e119480d0000c4d240043c1c0c0198445003001658034000380c4000001e102002411000000343c0d50203020035501103403c045002125400f1a0020300460705d8500903120b01c202022000400c80e400c1c0b81016401d0360300742c02c49400300e603a034241a0701c0420640c60b12009940130364415074212030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 680981501 1250 680980251 680980381
    0x4080d020c0c210c03030408120a12020706020307081b09210102030702160609081009060905060a0204080d0c0f031b080c0303040c0801090c0e1506070b0601030e15 72
    0x804c00c0140314500d482030780244000e1000c440003140e0700940701c0c5c04484441d51a415200b040c0c410304000c01a14204a202003030350004e1003816002540714032015580d10070b1603900c002e101c00422025054420304494240103150140c280100b062030039a03000c800340409000302003105402d99108884880040c0c1100c0c0c0c010001c62000b2a01c80068849400c003042d4941c100702c035003580c1d43d6400000d404082d40300e101450602c5411b0b031065503900e4109007541c0c00341c0741c038502da20069803041c400c10480b4400d000d0442e003d28400c2d6801d40e100360703206004000c0009070341c0701200e003d80301c40d0094080c04003014400d07000031650300007408084c0054000d0360700c0f0300d0141810344a000480e0300c40d60307059050003000d00010701c02c850203200365020b45000000f06c2c0c44c0d028810340140c48180b4059004000012040280701003607451030b20940003613030b06000000d20f000d211912440d40406200d00348003002c01241e01400ca0001e06000115040f41e9108a550b6030707a00c4613054020b00000c090300c5070001c000c1030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 680982751 1250 680981501 680981503
    0x40e040f020f010206160f031803030615050705070302060d020f03040b010e0133030b030d0203070b01241407060908070c0e01150c0f050105042904080d020c0c21 71
    0x3100c0b2a802d002030080c0d4980405500164283d91007001d0402100a640703c0c00719019a00940e4250002c00b0241603490036482c014004021601030391224411051022580034030444c1200d01d4540e016001d0300e5450701d1035080c020b054100b9569501c4154081c000ca805150419010710702ca02d02a40d040c644a5140914241c0496010b800612400c1444000c0d1420120039210042003c0c2e898544000e540d040880d08030002d0205a082e00d515006980351030044580c004043c14085004fc40d01c205e45903690110701e840803041181d14031402202622101d0f01c1805802090700c40030181e0300040c500304e403982d94034080701c1c404281180e09a5002c10110103000d98440340602500304000980301950600c12414030790b00810f600d08040180319548481088a004000061185d005000f409141454980080c100c0c3d92031114038204854000040f0500d140070407520300841d0410354940c40d003001082d40d0b82c040d50040c00702850a00c15440d4149003512100460288001c64841c00e030302da289869421 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 680984001 1250 680982751 680982769
    0x916030b030a080a0f02120406120e010b01021f060302031501090c1722060204090e0f07030c351b03070e0a15080601080c0909061e0a02040e040f02 65
    0x20600035440002c100e00010f0580d003c80705001c21508000e036001303601c0c50080340f44c000c401c03020311004000842c001030f440d50840302149a840d007442d410302400103004152402ca07658041000d0050384160707030089a07013450441d0402104400d4202203851a1039801292405001c061200090080d200040281345007900c80c5421200072840c00c46000720b601c02c0800d8807190043e0410f0940304841e41c1500508150040d074540b41c5921070000c0d512542d542503d00005e0045805c4500703a401070b101600011040469140262075100301070b80a01400c00b00b4103124a010441143c6082c804000c42d00001c1c094035452009028881d030003006410040e01c6500300700c031050300c0e54a000c1d501c5140c0034402c203213000e41085e60101502e0f034001410800c014030b400c125807950344a40000c0c0500b00010410820120b003940c02240c044d101c1c5c12180d00c44062669849504456101019003020207020850710302d101015049030602001608080e02c1c0c808003296000e081d9800c4420301044040041141802d200c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 680985251 1250 680984001 680984021
    0x90503120f040203121614010903020f1218010c05010e010b0a1a160203031603111204060c02040908090a0612060b09010f1b120305090106050a080723091603 69
    0x280c0c014a00382035000c281c0d900c1c1c0483d604030802c1004038009414480c681d200e5030040b41c22641c07d0701840000311005d0b008002400c0160014082c2c6401c1c41901403000070f00b41c13400300200035010f14000c417a100000c0308080c10500c190400c1907070180500421024000c0c02850300001c800000c911030103100f000303001c003c56804030082c0400326840040c00b074000d100b0740321035141d80103010000990900c00241107200d224045504e2080702d98015062640c072041120f1211142c101310303028031000401a0b001800780b40300c0d0308001b50382600ca10005050a03088098468402c85429047c08840c50000e10026030b1074010000160b8403000c0e05901d40e00f18091070000b4140c00325103a10300744810000900e1040d22030020414491000700c040d28480c041e03803455410741d0b0041d1941800e0005100e006014020503a10701103d0360070404041035a00e00240e40c042200e0180c002814620b02d0900080c0e040f20076200103440c00380b003044040f5690748490104a215040750050400b00c03840b00b0030054100d80f103144d4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 680986501 1250 680985251 680985271
    0x603091e030509120d0909050408040308040303090e070e150c0f010501120c050a050d021203090402070b09010b01110d0c05121305090a0603031403090a210e0d0f121209050312 77
    0xe0700744500c580002d011407e4a20040d0041a55602d600b44080c1600c02d550005107440800140082410303801041b140c183c8002c640700204540300c1100840b2007200d0f100c0400d81c0700c0d000d0f400308a1411208401000041c2d00b000582c2c8130141c02080c02c40c04c482c001d9120040110019280d481000004580c070f5010f00703411148e0003211824003020940440a084009000b18262040700321907040030030035a1014000140b0941d0b070350300645452000c0b108140c0381c040700381d803c03c294000c003580180e038800d20300c0034140000d00c000c1c0c0c1214000c841c201c4c1041c1c030035501da004440e03c01d0740c21400e50000308400e800300a100f0000e00d103070609000e4610002455903031814540007050001950203811512420700f10042e46840791103a00790759041020301280140300030000c4101482d0b00c034001702419901505a00c40700220004003040c0310f8810405c1d400181802e049070901e100103005040303170043c40c081a1503e02c00c8031203440c07900000c541c01e458054030658004104040d201e48002da00d42e0348403800034 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 680987751 1250 680986501 680986513
    0xc06250507050114160f110616050d020301080721120f030902180103121706040c09081b0a1208300c070c060f0c060b060d0f020d0e01020903070603091e03050912 71
    0x1c03501d94684030003034801f03210303111070031403078901c1c12b100e0816205064512001190303296912800703142d41d9440c80c0301d00d80a000c60500711943c0940b480f598295540d4200b00e00c05124501c001d4201c0b00240b40d103100605051340d84d000c180c05038644148541521800b101d04140650450506261207500c400b01d140400032880110070340818261007603500058256400700e0501d004202c00d42e5130a500e6041900c807803107001121405801c06000300b040d031032001d50b4007403e01515800e900465860040380503041000c1041684000038041c4640d8019444001507141c0d20701c00450740c0901b400d07090300c0e4400c00940c00f2622500f44480d4040d5103000700000d0600510000100b000a455800c2c450801b90041340e403103000701500d031030b100112528050101c1081150b101031484000085d04480c080c1c10072142b404607844040d403070501c219150014001e00a0582030f240000803000b908450304121080408d021811012064810411040c10b1103900ca10b9212080401800540d09031583c41401c554440 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 680989001 1250 680987751 680987777
    0x315100914030a060507020a030e0f1c050a0b040302030d050123041d0102040906060206100518070509030a0b090606090601140a021903050c06250507050114160f 71
    0x2444800854003041c1503260401c049030002810034140100143c042d45c140703000c1001040d408904c0c4230300740e4460386a105010b040340040c04890703036030001c01030381044072444402c1103100542040d070003080c898030072a041c02100e80d5402c1a00c42d000d403011800350344049205903450b1140d014040c05480000300c0300c45001c1c041e4034846100824030400c05e00881e920030b0005003001d95501c070008401507031002550b803143d03a0801d25004003054482c400050064801041401d0414002ca1046030402410386080030480c4c0c95505d001080503003000241b090030084180e664030280f1202d88050300030b051044c0301d85446210941440002402140728080700810030a15070b800c944107005080d80c0e81116602c514403840c081c0d192607c071740700342d0303881100c02c9612404040d4000003e0000400380c500f0f46900e9162114151001c515606039a054001012445070001c1c0c42038010704541c42c01078002007904e040342281700240c51000e403800c01508503940d21128200e40c11060b4916003203414a0241c0d594054 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 680990251 1250 680989001 680989007
    0x120b0115030b0306011e090e1e0304032906120a080c0109020d140111040f0509220b061c0203060612030f030c1201050a050d0b06061905031510 63
    0x14021240156081851484520710a90042e848494054102c650ba561a07256883e4020402d11444136103501004011640c1c0c201c6001e855101c140e154002d182c60120000e210015402d0410841c500344400c0c013000010403401315030600200140c08000103289030651280c1c0042c00014261805404074580d0a0103450000070081c043c20340040070340d510f60044035a81e5000d03002c48040070354040740d642c400c00180702e00c0c4808040d000e541100200306202c51150710044c0d030300880c401e840d01000b181d5401c01603418403124055015080050142800344101a070206900c200070b41036540c0c2c0104010480d00d0304200c1040c0340c07802071441b4080c805481d19800a2350714100104414007035240c40011100030340080050b03030b04203c00c680740700e5140d00e001060340c01e064102d0009158541c51172000043c140c24141c00c01c00075210041c0a00641d01c8a640b2001205c101c058601034125104201c400c83c02c031650003240009880c5590340d80d580f4140500f41107070088901000500c03c2c0c040706c074004103481d0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 680991501 1250 680990251 680990273
    0x4060e101b050a1d032e0507031104090507054f0b0721020f0c060304020d030806030703061104090b090c07021302070c0e0414070e1801020717030403080112 69
    0x4c8070044907640c841c000301c0c1c00c0008020030312104903118513907084a0205031350651039040c1c1580c4100010b40d618407044041d101c0d07042c81840c482c0c808000902014034150042580709510341004e03440c26110003186805101c804c2c1c100380c002c0000c00c0740c00c0703101181050f04c2d030610f6031804034183c1400042003075007040c03003220b00c92031040307401c00030316007003040556011011200c2260703842507102c00303034440081e4440003030450440040c01026904c038100e19000003030b07a014540280c4150600761035a030382a0342d40640603100941c0340c4164400000011641d0080100e0750349891856604c0c0c91030701040405680080c40b002d48a014200200078012a0b9982a50305c1203404a500388200e00310266408000d2107414005042940901f002040007202e100c219401213100301c01d04d500c0c48054043c20fa445200c4da006a074803054201c0d01007106030703420012880610f128036000618010003036599000d03c0512080904060001004000070b241d005a51540107003001844c601c1441415502c0d062000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 680992751 1250 680991501 680991527
    0x30317010506040b0a02160f05030d050a0e060a1e0306080f0102250215030a06030c05010f171008030403051518031614030a0903020906100206060904060e101b050a 72
    0x42c80102e10642c5d4a44200f11084005403c8070580f00041e0b2142d014032508186400b40c14042d10801422100c03451044080f2494012682c1c0c0c1d603003040d00310f5002c0140a83c058928041000b41c1f01c2d540c2c1041030943d050015a50f00e094034009001071825820900701540100788081c142d2040c011084907040007034200000306580f1302000310240c500c0c400500ca940c5c240d1400e4074460004030801c0000394440d8003120940e030241d08403c02490f0b440c80112019404185031000185243c1c02a1500114122006d030b007001455124100d080c1d125964140741d034006078420307581c0e5880150b0602c0340a21030002c40d40c02080c101e000100ca4104600b11642d28030803600419259801c10f50030a050204880d20103404d4900c840580341d031100080e9000788202c0346d03400107a10070301c038880c0412000c4c43c154050869803140358002d404165120340402c001c030b060050081e42c480d81c80f8104495420383c10720640408003004640020854111810304102c0d07005081940c0901900300454003410360800c803110414 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 680994001 1250 680992751 680992769
    0x1202070e0a0c1413063b01092106150b07080310051e041109151c020a0c0c0f0b090d060e070b04030326010e090c0d080403031701050604 60
    0x1c1c0c140c441c1e08883d08406584481c500440105102c2c441150080798242241d0540d035031181c0000075180d03c0120000c1e04481c40303040c24411028954452020010b416040b5414102404400d035998070f2801d08800154910400300800a0391808200e014441c03105205c0b07100e00420809828022088810b00c100b100103420900b0110001c0c8444c0041140d44000e000c001e031001d50751350300d840030f0030b003030414071581082c440c0b403c1c00c4030b085484988005403004001300038035a00046a60640800840c1e01c0300300602c260400442260950003c10f0009011021340c0355a00d0750140c243d070824007440400d940200a800441480412442243c0340944000c1941192404050412498504020300d0321900c4000b4070b016810300041c4100c0072501a2003140e010351200c1a003a039550310150910f500e903145000104603e10010302c6401d0f40c01d001541d0281b2000101d90181290030001040a007100e50101c502c4080000c040c000c041c0d200810340c00c407641041040c1080d50401c800603159000700e002d48001c03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 680995251 1250 680994001 680994011
    0xa0e09130510020c0f2116063b070306050c0c120901091205060f130b0c030a11070209400320030301120f120c1202070e0a 54
    0x9a0403044024461203600c00304035400d181040a409000e03400c150342d0114203002d4050242c3c00303032034085071100307021544035224421343c00e00f2070148080ba00200f14400303081c404110010001071880c490305035044411404954104240090f00304c1c2030b1070b01c440901c004030ba98000303504260400900756040ea540700c03601080d280c1d10b514410240b07002d095049007540c4620355010210044110040403031a1007a65100011a01d60b05884194981410010600d500040004045811601c80e46801032000c00300d001d007281450300c8506015a0549018849030000800d01c640c0d402c0342e1040080f581c1810300442d0503c0301c980c0000d0b004100c0104101006012051600000f0914071078000400800003503280c0c0e000300f041d41402c07283d04500317002c8005c41e00c000c6003410007141c00c694560412480b83d001354035680c240490b00040e80c0006500315120f03240006240000388600c1070601e10b44280780d540110030001810542148050419454150f400a02042c400b1143c00c4c401294403520307030100422 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 680996501 1250 680995251 680995261
    0x100b0a03030e06160f0b060301051003150c020a020d0c0e0609040f0f0305090406060e090a091707170706050601122f04080a08040807060201060e220804140a0b0a0e09 73
    0x4260100130a000784061a003407242420880650fa48601030301c4154020851503458010840000001307000151110043c0d0b190010800566084031503410400e1050750b105c59078560210b00ca50006040c01c17102800c03900c0b001c5c03012804104109601070400c803112500c0d030400d511407003200c01c00050003412415003201c1e000107150142040f10801e007030103001000110780c0c40c0300040c40c400e0b448036010300c1241d126010850100c840d002d1001d0207034100d13000d015104120040609a41c1c045401100c60541c1c02a0041200a402001e00b0445001c1c031004a030a1070450700040158400e00d0445094900c1c00c00482c1400b500380c0200c3d560401c0342080c1000c6040480884811805503030b014200610801000b9002c014850014004640541c4115000035072140c1069003640d101e80103006451418000245208840321198a40307201080b0a401d2508510f4a800c03827580c1c4035810a58442d010302c0c00021041c20134030690001041d0030a0820b01f05119404011b180240181410384140d0b41000490 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 680997751 1250 680996501 680996527
    0x5030709120f170c060603060c09010810260d090803090d02010302040302040c0c051c231b06090706050c060708090f03121e1b0a0302120405100b0a03030e06 69
    0x181c1c11604103201003501042001c06807019489103203c4c201c5401044046a100d080000341e4038054052080c0c201e081980d1003004581202000f4920310080441d05800501030401c44186406542a01c041800800d041e4a402e0719000c0d030240c2807801c0101c078140c1080455404403d591094100f1107020741c2c162034900040f00a4060f41c6c20295001d0b2030014143c020340d400c418500702d850300c070741c0580e6900031341d05030180c81e50380c0c500740060b0128680403d501601c4810f01c0792070740b42c0c240d4028800d0802c1c090070080c282d4441c81d000d0748061584014240b00403010200700c010010911460a40c0ca04007600e250651502c4010300040103202e06400031400c4607400780013200b03046c07070b01004507520740c07a080c0c00e403904000b0140c402c01e42200c03c0c1aaa102c0c88103020811a12031201c00d040303003500c0c14484041d0901035226441c90410198207000c1e1a02c4000d0032031006005034010801040300044003d10390007200d5049295510444c10402d042000039045486441c0712001200c3d601e88070203c141d401 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 680999001 1250 680997751 680997773
    0x120b0a0302040e0321040503030712110309010b090c07030509090406180f11090c0304020d2f0a08070e070c0807020628020f030f0d0908030112060c0503070912 70
    0xb0752080c00c1501c84440200004090300440d114189480381140e80c0c4107410a500f10309503000b800d540c00810016414900903190b0003c1d980703c60300c00080c1000040300000c095001038500c3d480c184d440302d8001c0c1007480c0c2902140e030040402e11680707103090400c6d0781c0a0000d1240008060155040c1c800040074480c560b440b000180c4080a10044030b45980c1ca4040f03c000c8010710102c1d85070007201c3c03282c40030741844961207226980b441306081c6580c85503000c00c804280c40002c00c07202c0680c0d0000010b42d0f0b101100b068000c480c100408052109041e0f0b04002541403540c115460710b6204a03001c00c80c0700f141301c07103041d0007002c1401c00390303c1c5030000e00f440c42d01c0313100701d580280d009140004c440c01900d5041c0a10611030740c42c0f920000d103407c0180401c82e112084c00c20440055401400791608400c032100c018408091340802c000b804c40600c0c0e6415600e03070803d034081c20400744403515150170710480b80100e600c4400149402ca02d0751601041c0501401c085014503419404401c00d02c10400801000c4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 681000251 1250 680999001 680999003
    0x7120905040b01090537090c09050d03050304020f0a06020c03010b0607020f060a02030c010c090311100f0513121208090729220f06030231120b0f070c0201120b0a03 72
    0x2111b070746900c50081000c0000c000c2c442e0183d500e2400c0303409840107111705071107404d81e103000300701400d19107040d02d0880f45900054001d981c80f410b00f1303503a6560341d40d941500400604042c1c02074510089003030f08143c2114076044506000710420032a03a00165620120103000050031544161150701c00032040380742d800b810402e11560362a108411090340e0700030003004100ea1091074410540407400007800030b41c01c140211200402c0420380d83c04075180c000d0000d40300340c90300d106c0007154a51391024210207400c1032520a6076440a002c4016294651205006911031084070081105901e0030026603d034155400030701002e00d54910f00d16010910714000c8071307010221304250020051007440509041d0050b44980d901c0d0304020a40014441d000c0c4c000c0d1a40c152525080d030500061800103240c072042040050402d4808200c4041401d00c10042c01c040c03a0f9011312888210361600c1d04034440006000750031041441840986000143c0c0d0102485114501d0408003198110f90300e40481e40802803030300 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 681001501 1250 681000251 681000319
    0x13050c0d0e010603111e01030b0105091305040b06031c0e0f1e01110c0a03020607020414040615090618090623041a040515090a020607120905040b010905 67
    0x48596040703001508a8001d49000c0c0d94400c00c410101c0003001802c41c14039a6400c21003d0004844407550301a9020760b08040041c18000d05c2c10a0030700000f203240c181c111504852583d03403801e202c140100d280c0c0d0a90b20001c164020000d5441014109283e44003070708020b020400490002c004545685d41911207000010b0880784120242e00b0b0240503031400054140c2c0010300130003081040e20301c0010305820a020150042d201c076810f507000c0c0003a83c3d002d40b1050742c200307071140f41c203030294542e40380428030450156000003050180c0c000c40c0c10444030b0951085040600303001c01030000743e40d150411201030142084c002082c0e1031500c1c1c2213002d09000c0c000d481c4034909008018140061510a29200718401c20300d41040030382d041050441807406036009400b55014007003190301c4020881809822900c400212a484038440d800a05140d000d1281240d0003882050f5000c0d0076a000401c04010b000c2c111800c1c003600100100091070b5070340a109551162100403014581c031010300362000d585440c248 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 681002751 1250 681001501 681001511
    0xd0603061b020c01031a01081b0c1b0f0603010e090c0604080f010509120a080a0605100e044205041407110321150301060609080705060913050c0d 64
    0x5041c4000c0080712910000036010b003450540701036209104110100408101802c100503074440115030b525001041e01c4040031400c80c95100b880346010141c05040000402081e6601640000c0c03000303008800e506a00410100900c0c2505a444a060320306461044040c0310440e07a034082010f0ac0c0000784800d541d04008009404501d0120116040031800d04500c002d011036110b01d02d4090792514501c040d4060560305000182500c1d10541605030000c10b5031601148060b210400514403100c86d20b0050081261010f0306101410315001d0b0900301a480103003c0c85180600d4420700c8110844d05d00c08a0001ca000d00c00c100d0a841075580764050040500100036491020f0f083d070f251150b0550740c501c0031414a0400c1d4900080010856030b0003c9081c82000389184102c03014040014040d08413581003a500090745d2041c3c609100710f80c002d0002d9601c4d500d2840c030b0303c0360396801c24080d60846802504108900c40c0251941c1c940030b02d60261400c00000c0a64a4001104160254a04412509040c031b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 681004001 1250 681002751 681002771
    0x206040c120f2f0901152607020a0b0106020c0d02010e010507050a0c0e0903070f0201030b040608030706091e03021c170f07140a080403080405071e080c0307050108010b0d060306 78
    0x1c2d0081000c040341c1d0881c8100c555241c03d04006001409200d0894046580c40d1a00d00961050580050418402481c021182010300308240700303030011a042030061348000108001d20600702c1c0c040303004102a001814104400c4004035002c90440340010303052000c50284001180d21071011110640e03004000d036107000030300f0700c0c2411500b62584640d041c08940c0e00c001c194000c601004030b45c4051b0b40300d203003c4204091940150064100918040c0c4d0080d41d030f400005540c80d05000809505206000c00141e003001498154100050000908401202074407811700103500015440c5042c1c8401ca45101c40761701c030301c40403114a07010303140e190300310b0021406211035024103a000a0003000f058440c884200d2a5410600301e600890902c10300003094100441c0210740544126a0003d0140042e10200d41e240d9011140854984c6410700031400c00306401c0101c104d081c0403000740f02c80114040c18010b840e00340003c0448030103020b0046040d000080c6000b405840d640440c2c020369011900388440903072 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 681005251 1250 681004001 681004043
    0x3061305120a0929070b060402130902091801150c05010e030a18050418120c06020a0203040e010e0c030f0a060306060906060201150509010b07020301020c160302100206040c120f 78
    0x6244100c1c0420501c2a49031100c12450405000420b10306910103805c0c1605906c41104092000d01f015805c00e500b00b1100c001e200f18800303c10040c0c14a81409030352400e459090001000031403e203105640c2d04403005100b00703000c1c98140420581c1610348120100905d0411038010140103020000a02c00050300c030308503503000881c10090003000392030900b40395600c80a00040e84d030159590241507031840e504800080030030092040c0c20a182c5025034682c0c19595400c4101ea1051840d800544d02c040750400200f00c80d0003809001d4550b42c2c0e5030410506004507095024040075103c0403800280340000307035070000a644060000e44d041402401110b43d640c1100303008100134010b0f0340041d420303c09248010720000d114076048441c09004041d403686854004d242941013480d049900d5502003284100300c540c104070020305050082c41c104840ca10314810000e000000c1031013501590000c20820000c07a01019183c0111a55101010380c0d0b6011403522041e02c1c01000c0005080284021201701d00f900 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 681006501 1250 681005251 681005267
    0x5180625020a060212030402010f0c050d0306140a05030606010818061003060f052406040b0403210c0819113702030c210d0309030210050603061305120a 67
    0x2009942c20503000303403180c01c101d880c0c2010305060410008100003080c0194822210802291110b1500e0b82c10034a89940c2c140c10105681944000280c84100c01d004000d0b1212007190364040841d4440550ba16040100361142002400079042c8505030740003580762600f6680010001c2c41c000203441140c508005c41c0703100d42d2904e02003564282d02d80181c10344440c1c55442003030700400f012080d840703036000c507035402c4020116900503964100360144030004040141402900156211703240b40c100340d83c580246111414610749240e810041d40d0519a03006c521920211401240c03590091401003902120941d00c010700c10150f41800e10034900c0d18498400c210354009941d000c00107108040d100222408243c9411840c00030b503040e0031007070144032180391035401102c50071100310446154007040a542d03800e00c0c2e18060940c01217915400e8000c101913040c8410283d50903e840208620b080030004a075032040010320200038181400004014040c4c1008081e22084141d07041380c0d905c000000c0001d20200d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 681007751 1250 681006501 681006503
    0x406091a0703090b0f07052b110d0c02010524030c0d08030402030c030706021e0f010606080703180c18090c0f0501080109270807020306070c021f05180625 68
    0x4c10424003140c02d00120340a07950040d0010340d641c90600c405030740030900c41c02d0381410a00350b0840440041900614501980c1681c0c002d2404854032070f00e50f1001e110a44102809103070859150000b003003952444001c41c42d0202201310991142c034020700740464138102d007940200d9406106d01d5421003c0180200c01103205920a80646442c01005402e056884c4028001d282c05600b08821001c0075401010b44065420412002c0350301042035104110308480c0c0c0744d04001c000640c0302040050301605030051624030240d0060000d9190400c2d241c88540801c58040d40c00c08a000c41c502e40c2d1101410b4002088458020450011446d13589000e160f06c031031184111804142d24800018481c403541c440c4c040c501d0042035496a06520f417040404501070300c900c0071105501c0610644001d82c60400002c0d206900c0d42d2207000d2040c4590041198a9060300c0d6a0401c40003211051480700b42d00c1005e4400303101c0d0341e2aa552500c8c1449000515034080c3c8681e0309403030721400a44000400480103125001e07 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 681009001 1250 681007751 681007763
    0x1a040c0e01020c010c060603020d050a03140a0c02060304020d17030601030e0105061f050d0f021201050301150302041104080307150e030c1903090e09070602010b03150406091a070309 80
    0x120940000e803034034256140040d01681060351480101d5002d02560103c0c14407881001a20640320b50005640c2d031a0101d05a47c1a0b0110b0311a104041e080821381800383c452001407401e00341c2100d00104030f040e440d00002d02032500070010400f151106040501640d07400310038044404110341441c0802c0c4c000b20b61007400a424010b028600003c1840384502518010701007010628800803111701d1161030140c0007040040c10494680722040901c0f910402c041c81140140e55121600c54094104d681a000144664900110030500d418509401004c4035415100440d00c6175a840e02c0b800c25000b564860769040c00300242d0b1a0411001007881044401080400c10690462543c2655a4060301166000e81d0344220350328090325050800340a6014401d203460480d554070741242d00c4409a0523940706800e680011030030b200d55502800340c0114a44190000d200e80080850030021540340680081c0c21540d5482c00c0f44188200382c0744101060480c40e20f00e604a00784040300030001c05003d2003d84003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 681010251 1250 681009001 681009011
    0xc0509041a070504030f020f030a080a08010e1005030604031110090606030203100603080301231315090c0f080a06120c1703031006050901090510200c01050715060302041a04 76
    0x2c140e01a81c20344055a030400c002e03281d199803550078084031440e00c1c0141c541c1442480307101070000e000100203000a4030599904100765141c210485140e010181952568032142c07441409181c90015002d603200b0f4040c034180c0211854800c1182c149035141030740300c0e40d1074201441201402310310707046401243d20030f5040700c16100e0306004420441c0d0103404000d00f9914100300400c401e281d4100241461032008110146c01ca40742c0c000141e4040155050b203071b119464170004842c403101188407100a00e0521028400c03401d009200800481c030806002d0180b003242008070392011490750068000c1d01c41d1001c8050201e24600b40341c0c10001080c8114240e0f19031441c148040e1002c0801682e000e0303209000034120301400c1036019580c076000020000c5c100911071000042c40c0e0707101c0601100e480c80c02d44441c0969901108a00c80d641c03508a008419070340032144944143c0d90120440d04000c2e00b0500c40700b40485896012006045070798000b03940181001000404000c4408100030565022142009 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 681011501 1250 681010251 681010261
    0x106091a0901020706110c060301170607030b01080a0e0f061503190f03050901050913050114031501050d14010e1f09020a06081302040e030315090f070c0c0509041a 72
    0x300e442041c03202070050308003541c10000e40e80600d5281c040c9007195000c2d51180303030300a0086401900240d11195144040160001c4810014024550405150b2600340500d940f8400041d00b80d00d0044c5c10400171a03603c0340448100c2c40203000340c442c2ca80020080d00c4013428042d21401c80070301030f0308200748240540204138203529400090700c1c04c203030b503c1201003600c4031889c0c8042d03681e60071203003c070b505028040009031119078800e10f0804000b10000000112035040015130382c200e5800799051400703540100e12032002040000c8015044a001311000c1052080c645080074940c4010082c40b10317150300302080d0070700e450030218624a0904000241040703190f80c11b45800141d88292001941160f484a02804100c0c070031600305500c60840742c43c0c21404040390380400d044400c5600d40401030b401c08410300a1001d5840690340524404940508a41c280899004003d10b405081401070002a80000e81080300160141c0d00410005180d0200c5107407604020303800c0c20003524041010300d00100090 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 681012751 1250 681011501 681011549
    0xb090309030706050c0601090203060103020c0f0d2003040b0d0902180105090f01030b06010e0a050a0e0118020a023a05030910062603190504080724080604060e010609 73
    0x4172800b034030500130040c503484c0c49036240095002a10403410160200208100704c0d000b081008041d018010082240c0501540c00401510b051481d801c80610f050f41541c4c8108000800d80b4165003100803215500c0621f9280200180002000250440010f003001060140220f00351030490f003090710910a01da40c1d01031b902c01840e0007400010041c51304000450455445003c2000c4032200103040b211070036031210001a8000800c1c0c0c0544d85802c03810700184040b40f00c01404e8210009421003c0d403c1480c11840a91510f4480800d800016100b848800030003028420003581098407910032000c4050307000000300b25a2088500c81c8280c458808154130031001442840200d0701505030160640d10119100791240c00300d030000003070354031080c48603160842c0c4058104241002c241c5909a0b02d52821001e0341c1800030617030001c41030401e04080d69040342c40c2c1e401c0307242070f01d0003d1a00140380c1d070380c25000800404094020152a40e000d000100d00e180d00b22040c80107903020740d00000c54000700c10704c0b08 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 681014001 1250 681012751 681012757
    0x30a03050a0305190f020d15060819020f12161e2328030506060a2d031a0f06040905041a07050a0314070c1e0b09030903070605 56
    0x50000c0c504102022515110760f102c650840ea903944044042c61040d40984242c4191441e4846a55030000e03000c50002d61922860181034401c8049281c0b4a02d084800303000c0041c018251b04110b1074502404a00d00305a504903100107034030080c41038494034041105800d1042c1102e81030042c007145141564110700030090a030b00c410501d040120b00114009003115020002d403000c50044190f5043c4c400e00c0d09a00015000400d442c03101d003a88100641800c0040080e0b44899205061903c410f005075600c1e040c0c116050100c1c242402600350070a0400710070f8012121a041c841e14a480300505001d9500d82c02c038188265400e1183c88245d61908204150300c1000c1403130640c41030f002c2004101040b441c3e04916841805080e15404000782042921119203084038180c00140c4000344070218146c16204a0003900190710a2a0781031030407200107062008031510182071055188100c0801d00100c40040311560b500a040002070700f00000f90954a402c008070751440703800b0350b02c008903015100c0d1041e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 681015251 1250 681014001 681014003
    0xc01050a050a0b0306070e01020c09040501091209230a050603070c0209090d020a02132009090f0919080d1e180b0c070614070503040b010506160611070c0806090c030a 73
    0x2a1845e511028410340b0158410790849043d40546001c10610b44e0b01c01d260144198020800402d89484c6440d044080c10900c0395a2340038003441f10300c10702107111980800fa81c0d9076000a20071104c88060000102421001e9010701e900000000800051760fa100140b00b814610903984440c45031504408542c440b86e218542c800140d02c40c00c0240c0c0945880000d202c00e03038500c0000018070283c42c01180c21700c12580b211080c4060b600281283e1136081080045074000071401d4803252500380300850340c7c0c5a41d9400e02220040c42c820154074240000c400444d0180280681c00300043c0d00d6812140c405420b2400c00020841e26140422034400403d02d10b0340d5800d42d1010000600b44c1e41d40250001e03c0c1c001800c144c44256695070509511a51002554055013a0743c41d0a900c07864180f0700b40154280507003003d40141802d1114203050080036076030319003440d0320440100340b074010b001c4030003094060610058100211540c0002c1c03618004114503000714284026107000590140605544640f1900 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 681016501 1250 681015251 681015253
    0xb0c070605040b0f03100302030f0f060a05010f050f28060e0906330417061006140c0309130c08282a030f0612151508030c01050a050a0b03 61
    0x104840d80712211100541e4041951450141c17180d40701d0f000319181071a20498ac081660205041c655690020066580d100b6507601042c0000d40c10400307030343c03810820791068901580a0314000d0a5681c1e0b2050305030824244400c0240e01c20001808a4046410714030030000030469440102c02c02d82841000b403132041001415003400040010510000503100003240c84403007400500000303554800d240100000c1c0342c0000c036174400f40b40c040308080c00c148000d4a19140c10102c030750f00b041050f402504049095102c66246c58a40b003c1c03010307003030840c801d00b41d456500c035040304240350000f0025803000c1880c00055031941502d6982450b140916601244074000342d40055007a140310082581040142c191404001400604592000300c0d042c12414014000303e500c0391400136086080344140130003803680c90184403044a0584910f010390385059001d40d403da4940c0d05022040740c079008408001c10500003141d03070382d080407100c2c140240002c1c1d031000d85007800c140105032045480d000b09d50054030020 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 681017751 1250 681016501 681016507
    0x60304080f030601021612020a0806131217043c0222140a05070906050904020919030f030e04050610080402150d0b0f0d0503070b07180b0c070605040b 66
    0x48441c0782980000b461981103105070241c8111200401c0c04410082011a003c03184844003403042245401890b040559164080020041c44100d5403440381c0c021a00b00010180804c40000225140120b8424030701058007a101844104800b4004516100c0080303400440e04204802955844110340d01f242200c2c520760356810005880c001040440d1b140407101800c0d00361800161040580305440c2c60104500440c03010008902968010290311494915004000c5c500301074000d02940603807003540740100d5004c1940701c8035445034812001c18800062045095a0f580d20380003036681d92106c421000a002100b1486050070140a29401010002d01640100030162400c0b103102c0720051003a640180c0507125941a800018002c01044402403004660b0000075014404e036000c004a982d802010300704004408203801002341c40210760712210b85210b90316034141c1100c0580c142c900d1548a4172055600180218111000f0400840c900302911111503442e002910203008070311610034911420 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 681019001 1250 681017751 681017767
    0x13020a0e0c040e09011505030102040f0603090501140124031401150215070e01140306150307030b0603070e0414092509060b0c060f060f01050903150a1a06030408 71
    0x116460a500088000303200b0308140d0b54083e0714100050982d80104280d42d96000c140c81c01810490700703c060a4264000d500c5c00d490003446055220140c41108201741e510041d4000b0884c081d004441c0351410207840003042e5845880780e040c101402d041c14804c882482501d00c1c0080d0282c055046681303c014401d40c15a03181c0f40802c428410040701c10400c5000b503280200100c064514818001c1c0c1d61543c03550280c0c41101d0000d84454941c2441d88510746052007007001c030340c1e01c607020351024841030000c49882e84c4900000b40c0c0a05490f5030340079803140003c0100300c065a4401101c0c06254412070342030264a91310414240200c2d025245241141c0000020a0036104002c407403080041c800b524000d500b5036162000001c490544d088410412000202c03000c030742c0410004035402c40c03518240140207080500c0024941083e80710000d040c44000300e460102550203000c241c2c00041d05510300c80702890481c00305c00c02000300f01590280005e000c003001046080c9101541d126581c000c818034500417030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 681020251 1250 681019001 681019019
    0xf1608011202010c17090a1d01060f0903060203010603051014010806040209120f01020a030e0d0509090a0f0e0604060e010c0e21030c0601050f0103140615090a0608040b13020a 77
    0x25450007641881031045982c40085c2605008031a07480724426820780301c80c4403604208401d50682d11420b0b0210403080230701c10180c0003404040c115122810300d080c1c40c01100c081514401200c7d440a010780744080f000040e00c54060b00400c4c8503d4100c0300b21140d068452007601404401124698001420140064050b00b4958010496020018400180c80c000707040190300d0030500004d13044c010303500894a0b501c5175401d40984c0150403000c501030400d19002c000c0040840c000c034840540701d80141004120701c44510307404100b85100c040001e008021a80c98005da8600f800c4e581110303907524003803c40407c0c10040c400c100507880c466945c0344e0b40d44d01ca50b00b0840005043c00e00f00c15800301e40d000e2100240e804000500c441c00b40040a4030301507241c902003101d114a03001c41a414103051041c0c60110144641c0e44c0c84c0c1c002012030f00780181d4038038203001600b18003600300341c150007003a2100c002ca003d03500700b400d40e4403603481841c0d449800d5503001d0610800c0c505544d0000d40000c0e11940c1031090901d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 681021501 1250 681020251 681020279
    0x9090d0818030403030e030c0a120b0411040c0f1121030c0c012c0736020a17011406070206031306151d010605030c090d080c060f160801 60
    0x34401c0d008a8482000001942940e21a0780120701042d02003a034517000b800e050060f000d841d0011151040100c4c5010790f5100c1c1050066001040320044000080c10010460811886401c010b0000c101c0f001c48460094450010318024502140c504c04424003000d0001981100103081c040001f08000704004107072000d508094048191040140880641d0f04424071410101314005492001015891001640000c02d0081c050f0981c2d085050140407202c0300c0254100240075030160840610a006950000600108803200d41c0900000f0310003601540406240e900d02115110f410003660788000d543c00b0030017080c1d0515041001840000c1c058038000000e580e00c651141c1141c02c500c510b0b540c850341220f00100240d020980051002d00c00c0c10000d10110104041544882401d541001e902a20600006006159514000441056a880d100310504005511043d4191034840e90008151038200445400745000c0d4008005000b44c691100c1e85805140d42d5154140c0c00c0e401c22202d03500d081 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 681022751 1250 681021501 681021511
    0x201110f0c0f0d0501111b03040501020303180a1a0a06050402041a0703090b040b0d0c03021215010e0a09060503010b10080718030b0a0f18050705092802030603010b09090d08 76
    0x400034100001c0840d20a00941b0140300d100c291159842d000352001d03c0300c1449019299840f94030a0000307102c42d980020449804c5030111403075071040d0701d10014051400814a40081c400075004000d048020001c00110780030382e8a0300e105000958070303401407004a014500c13461110300b51042c0e06a0220751424014000e1a02915101000c603844020000055015602c0000c41140001e188640301c201c511802e203840c0c0313183c9429803605880101000701d084015148107050720342145008200e82c014102044031000203450403909607518800702c00180814881e07a8020750034110706000c20f14013103020094640039030700d885805856001c41110780c1401800030300180c4811071030110200302c0018046d0700c92950a100416048840c00110003650f80d88820818408465005503000800210b0a24142d59081c1e4650156541e100710020f503000d091200403d0410303a4a014045a6609800640c8650001d030003d1140c506404140074030742804541641c2207070411907c13101c20710308c10b8400b19000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 681024001 1250 681022751 681022759
    0x31806020a0e0316080118030e040c0302160c0e0903070807030e01200f0d0e0612041704030b04170406051911120a08010803041208031305190201110f0c0f 68
    0x1c030b600400030034a8501403090303400d102c03000400c040101c1310090151f540f402107071810b4281c1e4038101e550081d0003403400302035081c4195103030301080c10320320700c03036030640d0305680c0f100403507440c816076a09001c86103c00a0146920440c075070000603244210000443c4e120300e602801c00c503d001c0700d68a080b0703201da241d6102c060410070700000d03542488180c0b020204408034183c2c080d02009250042d22703464041d0100300c5505000c00d030300401c0c0690b44d80350262800f0350805800407059a8075460300c80f0100f1503d0424200201002c540030051280179036809103c1e42c07003000d00035075580d074668003c0c1d028010b0f0300c203050004104004100340c0c0d161501a44210000f90f0030b01c0c0e8400b01140490781c0c1810712004440c10aa9008100c20625070742c04079904d801000040c0c0514541424103108482e0103c69501c003a0070810700201103581d811203030f000078109a802005a070443c031b5085805400e00c001c0660103034001090244840901d0324007080c804200d0348584001e0407203111400c107000c1f044c000c1c28122640 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 681025251 1250 681024001 681024017
    0x31203070212120708070f0f14090402030f071d060306210a0311190f082104030903021e0315130c0f2c040b0c2503020607031806020a 59
    0x9011107480180c1080741c00f103a0440001d103400100140b00101c0245250b00b00041e10200c0c0c02115004042c41d00a00c101d890801c1e40d41c040001c0d400118402c0100d0b441e0440c0c400801c204c5556030201c400e50281180c2c2d42c40c07444040c00711800a40004034590083d0744400e04002240310351600f00c0303800e03c50000113041d2040d0b81101141d075034200403901c03405902282c0240c0714a11100402d200160302e4038001c4a020300a444962620505181d4520008002400001d00f80f88030300b009407400d05180340100440f8106244c00d00d0024401143c5200032400382c07000c14207404c0c0c100c207944107190005401070300a1811840340c074509150300c2c038054079a40300300c1e80510506000c201900140006400724801006005180a040c2000d0400541c006a03003ea42c1041d400030513288040541c2c0c0198101c01c5a107516200e031741090740729100d0109072840042c060504041d10f00010742881c1100b6000fa000d42d800744c0c1d5400380590603039034540c82c0f0754004035240c400100020764560103407142218500d40400 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 681026501 1250 681025251 681025273
    0x30308130215070f0c0503160306020c0c030d0c15090b061e031b03190b0c0c1507021609050c070b0a06050a0303121b050703030e25230312030702 64
    0x146070f015110581d00c40d06a07800340030910110290b41001014217a0041c01c0c0c107684000880050603590200509482e000600340a104404000000140c640182659000305190001134020340b84101c1c11181a54031180d00d02c40300c90a03101d0841e8541e04000803460a945402c10041082d038440c04152030044400b07132085c82c94500b00034401210400010041246140c002050301d4122480d06501603020b1440440740080e4205600c0ea8114003031959050305da0351559103403810000348207842202076908008101003281d0003d84419a800d07a0001a200240c40c0d080c0c2c00f040d01c1040b50480c01c0600e0820100c070008011121542d40003a1100c0005252034582001034030300540744c0c2c0203400150149003101e140400a100d007050a03030300a03400010000a0440c0500075009050000c0e0030301d42c0d9200086072020301482005900c0e107516002e620b0200c40000002c9050703c440c09000e10468040348030007141d0421200c00407058800900070010500e03c0c02d003a80f400d5000038200781c11401007540b041 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 681027751 1250 681026501 681026539
    0x90902030c04170a0218130203151f0807060e040902151905090307060827060a0c02010207080906030408040b0403030203031608060a0512011d030a020c0303040303081302 75
    0x260040c0340d041e400c0d0b5982e52074070b008580690340303e030b0b050056604082c80c01c800517036820401c0d800021500c45210055940c0310b6005031000e00345030f0040d415008a800c48600c2081c0d220080b4070405040480b00102c90071800b1401c10b01c0d45d9401882c217030354030405040c04124050083c080d20120000c4c000b04809405901080004101c0c0d4003d5000180c003180f8406019030310510700042e00494640303142005894000280d5440d11407081c64148010403001c508401e114443d281070342c41507011b0401540d6440031800e40e403100104d0b18405130915001d50f20712028418022071b01c0e0036410103860750504e440d400c20080c2c0d40c2d00142c012111164200800601058031741c018000940c040c0d00599100e141c42412007a1003460298450304005413501084520342da00381c00e80040d2541034841110085951030000e00501c1c00310000044a17644000380c03081c1c041e002008001128036076081da142001590141541c0b4041c5000082c04604040009240a1850b03032245100d1070005210403910184001c1d00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 681029001 1250 681027751 681027757
    0x20705031603020c090903040506090103112805040f14040905070b0d0b090106080a09050c18090106060503012102030c10030209100207080d08041a090a051c05040302010e01090902 79
    0x4607020581000081c0354040c03004000941c3c0645500d04903240c000500790726442103004a511a200104844015074441e03408654805034156525584400312883d0005010303035650704d1030107000d9421420440b24450b00580d41112600c599107116241060b00001044201c0040c01da04a50b60714200b40204000b00004001040d40428003a034446900745800c0580b801d103071105001c0c08480004100156100e0011544520b800d0b40009000442d442c142d404c196070a603042d46e00400d0840d8030045098bc41c00c006015140f007034000c202c07241c4c1d210010342c0c9a000074860f42e81c3c00d0002502030a1400a20a103169a00d8402403d5580e00d16049000600340303034081c10804006940400c5016480c185024050500c200c80e00003085060f15080004d0ba50300040c4600c0010401080e02080400410328a401c00e517400d5015413003401e00e090311800780d5680c40b816041d00d140c03203150f21410608280c1da2602174024801c2c0d9a0610b09825a00155004541d4460312410422090000108030f86c90380f0203 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 681030251 1250 681029001 681029017
    0x6071e152a110c09091603080301080d021b1009050901180e0106030222022203060b010201062303030f0c01020c1b0a05040203070509090405010f0e01110d09051509150f1303030e0102070503 83
    0xc1103892b541071200f120710b40002e040c1d030241550f0003011420f10090b00c0150419440e141100c12075800ba160100445000c100f42d40401c1d04640104000728140c02d05101854980f41002030401031003108010190a032001c900c0041d4102d8030006a40328841300e079820740c2c014095000009482c0c00c103000040c1c10341892000541c200e200031091f081c004c00000c1e01400c036000e0009d100901c241400c00140800b121041c108140201200c444c0072403080d1018001c0e07030081071031102515141c1c12107004140c080d41c01f0400400190040c07583d40f00b0000e641c0804000d0428014100507021350030300c02440b00a52024202c1014000c0c140f002c8685036a4110383d0500c12881230001042145600104c0416038154400d41c00c03240e414952800382c0707144100140d5442010103100802c41c45007a01702981401d10031014901d040c0c0c07c4004000003404000ba020740d41e030180c2c03543e80741e00d07075a003151043e4001400d40300c0602081d140b030185004030340302c1d030001114000e140300014580600390fa517170f40c915400303110 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 681031501 1250 681030251 681030263
    0xc080615092d1c03080c0a1b0f1407030c091d06091516140904060f0b120708160c0512070303150506071e152a110c09091603 55
    0x26030090314148007800d03c100800030b02e2000e445030750b80d9602501c0800010051a55060301103100f03076442d03104840503a014500010401d01054690500030ba01d482500d20580310680580c003d0807003170a0015924040343d800c41d502d1207080341020440000741056002c11400140700c6160800059002c0c0300c014012501040205007004000e291101c00400080542d0101c21030210081061908030b059000440c0c00c0104165841800c100040d00800c8240c10850244620303a401240c1c203054040100040e207071b0613540c000241c1d070350042150700ba03038100c4128820a406046070030125004444041903035104105a40441044050542c00b5411498003035000a89500c50908071940100321900a844240c81d00d41c500380c41600c0c0c0b214000603420701c5100031030b05568002c040c85a81c01030314030318910000c03082c04101009401003612520031080b900e81440441100f264060207010301c9030320700c00c0840241c458001e1300703030400c20b11030702c0208100081d01907408001c1e66400204951800385110710 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 681032751 1250 681031501 681031579
    0xa120f0b0a0c1205150616050d050304030207120807080c0c03010e10060e01050f060a140412020f040b0913080d0c02062d04062a02030a02010c08061509 67
    0x20000340100c1d010f50400707860714502414000103e400643c220340004040d541c85644900d810480b003071010b846d80e03005d8290300600b80c10a07285580301c402980154000d80c215804151a00303c50243e004031621300402c004030800c01000025a59030107490120f5a42040c1c032001c6681d0700c0460b094800a40f030890680d0043c51a0101c0d000d49031181c10080c069144c10302c0e066604145c00304000b8910064400c0c07061a000c02c40212903481000b403801d15a210802050301d503035403030b0105880c0900c4824200d02c6004018271100786400c080c03007000c00b2880024140c03900d6444c0c1010710100c01800100541d0000070030040d141c04000e0074021032050500942c010600c41c030304000e920750300c81403c016000d90f50880d840c1000300c0c1800076041640054103c0030002e2400036140702940d8a0006030040c02d211a0280502c1e03000580210160040c410307160002c0c0042c80d445801221500021510755504c80003021000c0800a0b21801410380303401c02404a4911041d00c12060348140000a1b203114003000c0c003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 681034001 1250 681032751 681032771
    0x703020409060807031502071e030f09080d081506070c0f050f03030301080d0e0109170609011a06070605131401060305011404021804020f06040f0911090a120f0b0a 72
    0x76200b11401484254081c00803c2e045030744003031200d082018a410301540100d948010310081e90490032480c4a440c4c1d00e1807040916280c00380c4000007084101d404101c0702e0500150b0804003142005c1d05828990b07444600d99204e55102c07100c065000300aa820100502101c1e000402100b00385000c1c03c031401001032828684000c100d04090070a880030300a400074001005095400255071920b00803074242850040640c8004842c0b030011503100303c41108d01c6498407601c0d2000414064021a60003009012120b4180c0c8200f40e101c403182546a0400000c01a200100c1c10300d134001c0e0b4101000792030040e0708001c10748807051002d17800780200b0b1260750341d40010400c100302440346600c09820100001300c0382c60a900024400e5600705450500c1c6540b6000050456840e140340885610006010903255610350034160300c400414018509103518081d100e1485130000310568641c890020448401d25090495592103d502c4c150700711019888080100005404074144ca03104520300c0c40005014804 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 681035251 1250 681034001 681034019
    0x9020702040f060f120213092f0109090509010f091b080601031104090204060e07050408011103090a1e05010c030507030507090b251e0c0905190c1707030204 69
    0x110852110003d10304001000740c6102011003104681032055030f0031000c40c003800441c510140e40005070604500d000c541c0e8040101003901285201c12101000e40d269a00c036202c3c01500d503a400da89800704407200010016030b041a002140c0c4203081c0c1c0004140d50303030440038010645500301c404a40000121400581951030b00400400a001d42c4005114a514640310940382e400c029252600890302c500300842951103e402c203070010600d03000514002e01d00160014042e4011380030b20002035090145c1d020005031202c00780ca0280b0009070140c5030380c08299540e0115050400304034103e940c01d0a10300c0c80442c90038400e40090141580303012503a032601850040480300d00038450302c1408003040d0180140004401901c8580d0b664002000003d05652000c66001d919030500806540000343c087c04182c030b0002464440a2046104062a03625a0a4038082d03070b104a44440110b0a8204522030840c02078002448003c00c0341842d07504c403a00c0e00e003c10703c214021940c44010940010303082041c402c0b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 681036501 1250 681035251 681035261
    0x1050103030908120f341506060c020f2106070305041205210601050d1a0405090604030e2b030806090c0f04030b0402060f070b090d030e0606090408130902070204 71
    0x44c600d80362910b071080015049030280a0014142142d03100c07200800782d036001d1400c405210a070340c120845030500d85454160b50030380300e90341c901c071510781400380000c0c03454081e9030740907401d5900912405c90494500184034400d0449481540d140111408100710207100b405020700410141d600418230740f0b803504005501c2c1c0c3c0421a10030400c02c04005540c0d042455808151030340074288400b0b80c8036215040100d4030390164900c0d81d9003040c9031085540c0300305920403100101c9841603a06021658400f660207841e0202100c015000c60208100c020f021700c0c0c00082d50030b56403a94101c002d03410800040c06000e0401500b0300f1404a03650314143b007403520305100d20941c04090140c242c0d01e01626a86251000e01407407000078290060600401c04558556054895140c0c11501080d2220351604054a110310282e84c164420b00810411a032224400e000390410131441000034080c070345500f4140700c0c800c0402001650701c5402804407031b86e420714648087c4024000c010780941c0321003c82c01000101e403 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 681037751 1250 681036501 681036523
    0x3031606140a0506010818030702150d0e010209031606050415050f07050606041d0a030302030606040504090c060305070e06040b0a030b09160e060a02070501180801050a050a0f0b03250801050103030908 88
    0x100600c1c4080d8501f440000440c2d4409505803686080e803c0e0310310000009000c0d0891a44160381004050301c107868056002e040c0383c10048044400006101206c000b566813240500c0f0009081000103224070408001030018180003854030624003022a400026a600501000c451302e810100c2071101c0c61401d80905d251040c20f006080d0300100842841e07990310601204010140754010001500d25502c58040d1402040c004d441030000041c02d01c3c0c4401c02c402d5600030040480e1801c03010a507918070440881c280503001604c0c1c185001d0400113500300980042c103000d0200741d1985403d1010b034681c0d91401d0300500140e510341100c1c1005040243c02c131445040641c0c0564024440e41411550000d0244121003007800e003076004592051b040403003103040b0341001401d0340c24102071011604171980103d201d284100010010a8002d803900070035a4942000389038507038004180341d0515031320f58860819400709175910150665407440324500f540c80076481980854100041080081c0050051240e51 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 681039001 1250 681037751 681037771
    0x3050903010b0a320a03050102030106020d020102030709030803040519080a02071202031e030d02040311010818071e0515041412070308070201110303160f0e03031606140a05060108 79
    0x12420044c0800180c03034101c0584c1e86082650600030400c10145030640c00241003d440305034155180d01313116020350300c28402c0a006124030020250014418801d90f800740e0b0320307540c0da620142d18540700d1880035000984240c41c6400348240201130245040207018855204242c841d84610f502c1c6806070400c040c07075002441041e4100801001030303602290000c0ba0440301d00300c1d18005450108054a180250490705044c5c40c4002404401d2100c40d291042102e40244d0703a000c141d5542e92401141942ca50075108060303031242d0020310880713440b1303004020008100c2c680911890380e40c000144640740c0c9010403d143c40c90029090000c039000d801c8a00c01e66000b5500d100003900d00d40c02503540d5030001d2201610154001c0380c6081103a10032006031210702c00d07203c1141c0c1c890070b0140d2088001400310440c03901159821440056007406080500e0241400402a41c20441c035140d044202101d0352100b10f4003540d13950003c244c46601032a003103000b0203000c3d1001905203045000034241e14406042c0040c6 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 681040251 1250 681039001 681039019
    0x2070309140d0b06100201020403020d060603120f0203030f0c090d2004051014030102120a0c0210050c040e0a0b062a0604020d020f131d10060e061203130303050903010b 74
    0xc1503c0024441d00600292a051140e00f6406030403402401140c00007548215203000c204140103c58020350183d038051340c3d0f00c00e031245c007816055402c0342c001c0a60380c0c0560400c0c800107100c9012541c040c0c6d400000803c2135841c00b0441d000245880ca08503504032107819210740c9031001c02250314049620000161401c0090b0b0070222802c0c07082424070301c103480b01050b81d10900303512078a0a40548100c03903403100d1008400d0611300341e0700f800382c846501c10b50014850360740b40c640c08440e68001e0901481a1400c401e02c2d240c104011422013400040c000c0d41c8454035805010314a0711504000c109103003244915550350041c00801a40b015412485803c1c40d600c450284070140e990108a03280080d81120100c00c0b0703900c040b01250140b0b0702110848800ca02c0c00100343c0f1420100040b142400600e041500c03019201d202190b011100325024a850604808001451a0414030000c0d040021840c0c06c0740d041000080914440074041c1e00100e000400100340818503003024083e203104858100c80d0300c00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 681041501 1250 681040251 681040253
    0x1120302070e15131e0b010503060d0201050403170a020d0504030210080a0b030109030203040503160e0412120e0304090c050a230d020c06070809060c031303030f02070309140d 77
    0x59940500c1c081e50b1244034000001c00d41c40303201440500f16016000e0003050141c0900000c6600070100a440c0c1e01115018079020800c410841c42442c0c060381c4142c460342d0454035001d051007104c020503403040741442400c02c00400484c82485404103107082174505103a0714440110024241003a003045c07070090210034041840180d880f01d5020898840074900741420744d990165000280110340e000d240c05520300100d0f4014140d010004109980c41642240c0c00c000c0101a400d041d0001d0f4030980c0e5120241001040c005101010300411602e881d00d00300300c0304c6a50b00750100c201c4003901c0c41400c06a00c0000c0400c4405d030749024031001c80314107007082d608000040402070a0803c04402c1d65141c101c0514042c14200c1041e0156003c0d0b41c001d00c411034840f812074105541d03a600a9501d100410465000100e08100000ba014441c444c80c0c0200390958407031104602c074190410f07070304034207040d00d82030070303d020000510241249034000c0e6580c0918600e0034004001103011090740714051540002018 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 681042751 1250 681041501 681041503
    0x30403030905061c0b040f1e060b071a06030c1207030b070f0e042d0f0612150f0617060f0a05060102030724020703091d01060e0d0302010605030f010204090501120302 73
    0x907000007105003c03540d1403216000400600c244810b41800c50701d4002300800c1e801185125848011052104002e01615205034070020f0040780001041e004208800301c1079054001d4039140c0102024086588034440c45000400e80420f2040c008017036804a0420010300070014030f03668014402e1305200109806840d8001d1941d0848480d450090b5160950603007114140300c001094500d42040e06032000740c0c0c0100000181803941c05001407142401000b14449810804051030036900c8605540620440950540034105401c00704d4940c81c4c0d54903000030304402d001620000100000081c10051a112044404090b0090300e450a082d20309020400700b030340c0000c2120302040e041044070000749039100202c1c040d8608400c0a9a030140007084081c10903400190113001d0741c0560903070000070140343c11800714078a401d1050000240518410480c6401c1480d000e0b0034860203440003241e02da441380c0210b49042c07003408010055a600140800054085124450140c6400001c030400d88915807402 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 681044001 1250 681042751 681042787
    0x12170a0504030f050a08030a02090102010509030f090d030504050d03173108040305030c0d1706030309040506062a07080c131d0609101419110c010e03040303090506 72
    0xf850300d409848502c09010080100380040d640c844c1055a8a00d80701012501079080b4188980c0990b00f00000314407a144007005071850001e004c411282000258801c201ca81c00070313010b040c0c040c06805c00010806444441043c140a40641c0303503c18000550b10344205510f9000f4030750400215401d115403010741025056400440040c1d070700403441c410505240c507a0b845aa800284980b00019420203141c0000c01e5001405c01d480c2c80f82c0b10402074105980c0511041110f0055040d001048000780b87d00d46680719a130011005030000b4203001c6181084040480e11076103592428400e107940d060ac040c01004140302412081003c5c0c80052840c1011412200301c3c203001c842c0e900d850b65041c2031419441007804c00c501c0100c200b12101410300010141c0c1f122214000043d20909000c08403940ca59040d440c0c5003d40f41c481c03c003240808803c03074120004d24110080200c0c601d000c00403103191503c01d0041604100182002c1d50b603452a43c41c0103080c007086548150b000e80414000000f0001d044212 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 681045251 1250 681044001 681044003
    0x71701060e130f2309030324300c010207091802090f09070b0a0206070f030f020f0405040f05190902030c1f0905030609100e01021312170a050403 64
    0xa28003907440c120015460210780b01d550007485203022040502015a504104c540780040e140c0765110b013074031000040110303c088030a0407036640100007081044400155a82c44c0d290005406280c07450011b0018011071170580c2e520a5441404400e41c100d4603aa01c090748120780000c0c001d00798403250306c0000c0d40703c614a116580c070407075480c0716441180c01c07000c010008465000300b099540740b600000880101e80141d03015850751041041c0890084028002c41e1100400b68000385190f03aa441c00440c1e40044103843c0d24101360f1031300c0d5442d842c00c1c00fa002400a83c2010000c0a4480741044140001c441410083d03403070380383c1040d040c0504c0134240c0d0707131078070700c80d48540d4000c40c42285c01d0020903d0050848159a08400b082c950001100054005030001e43c00c1c0b80e660119182e0b450041540d6040b05854090b0207800038032120954035041e911120f6030078100c070005424110302c80360001800c4007650203086840c41001c485000c0084078050625880642c401c0c01d4100901c040000f8054000c07400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 681046501 1250 681045251 681045257
    0x1002010c0e060408071404090203030304081b0c0a03080703090810060302240a0c0c0f090e010506100f030207050c060a0f020708013b010e0102091206040807080f0712090e07170106 79
    0x14906c0d40e201d54106841240d00a022a03940c2e049c2442d0404090340519004900c405049641d481c0b441008a07140d080413500802c03419040d4150b8442c96043d6014440c100c00380070451800040d420300912038641000700344800010f200e451030051000350400300c0c3c040910280078841e00c040b030000000555861004034135140504e03c8403454141c2101c9035a8001c0c0014103070b90480052140c800360402401040508000c0c00941c840314107101c44040022982000b0030740340780008040c0d0b4801e0f4094665030b0301540854600780c0d1840d021900e658010146a00064900c8080c01401c0c0e0301000034400034403949008100002c1d000030300c00301c6e50a03052000b03122088501b1868401760a02805130418081d860020000840081c0031f65000758010030501d03001c2d100c10f40c1d00b0b050307004020900306c0c41580c01c030400a1a00d1095a281d0700700c0da0101c04c000c0003c1c0c1d03003406090040b450840d520411419607445042c8591300305901452032800c01022041003107203a0400320b0904000c0e100050454461307003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 681047751 1250 681046501 681046529
    0x10e0901150c05070f0b0703170f0105091009090515071e0507020a0503100b0306090d05120a09050a0609110d021e01050d020d05010e01060f1d0f1002010c0e06040807 73
    0x40f0b0200d0415107154498050b0910590000c59145403420080c10b0709403298440040041ca0900403000303081003100e00030082c24a070001081a81007403001c0681c000103419048034040e80304d10081e01201c1c1552025a034551100034a03040030800800791a4000b603c80c1072003042c1d0a10b060742110080c0c80d8542c510b04008011502000310744818050740b0160000800340c941c60207022407840000c14030218260b200340f0890001c100d07066404102540008260f5031094900340d904203d0020201d00a4000e071961b070b0740c501810020074410b1007580f000320300c01c04010503030018604110080d0b100c1240d015121314000400100141c0d80c41e44403c840c44101e03c030b1003000202c8180141c03114000e40111403481c070b0002500356a803e800b680418117803642c40c20301c0b02c550390321000101e4402a4658541d400f00701c202c4100580c64002d801c07c84036607040246542c0b099000c000100d10507101d10009036001d41e440f0002c0103450f0303070041c1d02e0b00100f801c1a1540e90a0510b002401561000c0611446c09003d0401e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 681049001 1250 681047751 681047753
    0xb19110109030207082518060e0c0d110319050603100924050f060925022107020f060d0e0307060501051e10030c0306150f02070b0301150f0e1806010e0901150c 70
    0x9410680089c40b000c2c0d0b03090030a1030100f00d5201181c5c024140c1111280c5441c1c10a8010319504060b00d0040300010803c021042801d40c06500900d005000783d54540f00b00004000c032050180910300c06948140ca555041461f100c0f881b0072004c1d42e904c0516507030b41c1017004004503100307200b104552104d0200c44c81c003903136110102041d04018000407046801203520b20384035800f640000302c0784c0303441a04081516040b0802603404410f400b409100940c0843c030040005c1c9149030070005002010300326000042c106406041003469984101422180245c4030001040b1500d0001055041d403101d20100b100c3e0001c9403400100032075800305008091582d952036072048175100707030b20601c0900504800f5204001c0c801001034200342c0400081c200620540c2c07808038460300c070801906d04aa4500c00078680781103240105480d040d1a80c6800ca0030001040001035090b0740701d6022200120307200c16039000c98140b80000408142254800c0340c00b9400c4040100002c0c00d100303045c030480b00b00924044910480fa = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 681050251 1250 681049001 681049049
    0xa060c0908032b0e16050312180409020619030504060b041e0c0c0c030b010f0f0b0708071e24020a0504031103070f030311060703060b191101090302070825 68
    0x114400c0000c591082d4030660015810704c17003900c400e0f54821011650f0036a0b40102c80410362184c0000d000340c81d40440200d91090420703410150b1818030007044c00c0c0c146240e000c1d0001421202e485020006a09c44050000380f003001d1040702e0700040d095906000d5603019681d084950308140c43c1410035945d5503055030030400e11403070b00d20f8201503210b25100550790781c0e41070503e12810300303024007060240c80b0240058100a900e03132402c2250000d03401d042c1414160340b14549940c01904c020368460604c64820762a5100c2018400490342c885d0103130030480301b442d20428000c0303601110441100c0344108005101d5941000070317203003101e2f0700075044441c04000c2004070313061800c0b40d4089166000201800b2040540240110301c40c4086401202c805030b40d104821010303204035204403c00501d0401c111500740c1071240e00d0b00c89010b9a03003410703024162030013116070840b00305d44020350060300216824080304030188860810a440610900200b241ba2540d9418070b00c01486299448941007543c4502c01e01 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 681051501 1250 681050251 681050261
    0x8010f09091a0a0b041a1207081911040608030706060506180418021c0303111207080a0b130c02071d0c070609080a0903030e0108090c210a060c0908032b 67
    0xc0282c41804210700307081c071080081000301b01c603a01c00e600401c0d00075074600c4001850402c94030014028000c00b40c1daa0b241c14900c207180c0c0010784001000080075200d50b210390040200810489005507526509418240d0807100300e608018850384041020506041d0341a2440c10348144c22103002584060306603905032500391811000f03400450841c601040f614370302c0d11070030010303010b0b841c2440302e542c154814012038480c0e00c0e07d21014404c0003011810180c4142c0c41e00d50301038030b1010005903d6070480001080b0740d048903c4900541c0d210401c40030742c10f605000e0030300100301004501c804042c0061100e428904010800020f0300720100307640c0d003800141e03004098243c1d0010a183d550341c00c58030340140130410070301003034011070321102d03000d211940306044040c4210307007110180600000d060100700311000c010380d852042d00006c0c4040c00d841c2d07505002402c2c2c000e100d5440043c41d500045070140100903907520400e016041844403c41d001c8104840601440b145110505940303030032015000100 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 681052751 1250 681051501 681051521
    0xb0a0909050a0b1008040201021e01140429130b10090609050f13030207060f21020c010b030a05100908070609050607110328051908010f09091a0a 64
    0x3401d00050207008002584588144101604c4018189010b070710281e41142c2d099900a0060f4045c4c00c5d10801000b41c2c2c1c000c003d06800c518001f0541840540300c038440c0b041d0959003980c0148015910703100c2241104444148400044a140081d1814465a070050941a00003900d071180400001e00c1c5880a800303940701610812108000050711540301ca00100350444648002880000110f190081030306c0105c42c006c1c2d031540c02400b001d42020710880c2c5030b12440c3e94100910003800411500c60201414020302c040101c0801600c40c1803070318185007565440400340b802a0403100250022a4011840c00c80904c146500030582c0e40f082d18016000384500d12001d401c4a140420200810401052160192880e940d41b03030409880360f66400d85901c00c1e08001d4800c2401413455a00c858803014000500d40d400d814000c2c181141d10512104000c40640d80c080040c02010040c860414042203035005002100802c208a035820b07628640444040480300311103182202c005030190340f00760000c1802d1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 681054001 1250 681052751 681052769
    0xf09130c15030c0e04090f1401290406120308280c021006050604151d0409030f02060c1215030a020a1805060d0206030402010503040507030b04030c0501150f0b0a09 72
    0x11805000001d0003064440e07001030000b00310385020701035032a081c01189569500300003203460140b903039507070031307580c040781360b03030040c000d540f03507d450821078140040c070032058ac1e81018000503000c405800c10084503016040f5090b490107415500c00481d034441040d90340820f24500060f1140004844e40400500c403880f0f0b44092424000341c41c075020342c0490005001744c2c00c241c05103c403541b11402c02102c4d0081b40144040b41080040c9040c40510503503a03420a00340c0003600144848241c070100c2d0907103100c10429408160329441640c456581005240d9105601c41a06410916140001c00d0b0000001c0c05803a14201d401070000c0c400d940600c4812030299001301040641640c84414002ca00014552a041d4600d4030000a40904218001c21031199008040e2841c5540315401034919410150042d141403089040100000c3c0c0d010408a008501a440c0d1009240407031400c542590a4911202e82401200104002c0383e683d140940d03040d6104000100e46a0022103000c94500c5541d034851240703 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 681055251 1250 681054001 681054029
    0x302030a0804090c02120a0e0103020706060306051024031a040c11160308040915171b042d020f0d0b01030b030303010623092701050f09130c 62
    0x401c2520340081c41150960302040c8a07413080c1240a0b0f884040e41c0d00034114840c000c20030036099600c11281e854115605043c010300380100c0380c0328981200d006401c2105c80c181d0324018040c40d4030382001000000c0c0180c08440844030028500303e0000005816041d0625440e80c0e0160005100780002c2d024640c03000d00300b0444c00203c008014a26000b46508061500601014800348040c0031051419260068a002c0c90149401a50381c02081b0140314010b01c1280d120006c900b6070ba118804040d40140c0c50018114815121b814003255406881c4d014031851500035547c2041c080581c828a045005a1fa400350014180044001078400c105075030505030000205810091100d0303001e200e980e01d0a980801064040205160f52817000303019110100340c00c26504140d4202146040c0c440d01c0c4c050701c81e203082c00341c00710106241d0a0040d084d100c80d118621145140c60149114013801803004440d00c10140c800c0c000801c40240700502985140300c5400008010700c00e40d4a6400300404c101905e50754 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 681056501 1250 681055251 681055253
    0x5040c0b0a0806010306050a0515130f06110d0905090a0c030e01020721030501080304170a060c212009030f060c030f0a050c0306040b04110f04051c05060c0c070302030a 74
    0x880400c00301e5101d4086451b100e00440d03030b030030700580c0c45041e61406041c2941d108162040944d182d00300c151a40f043c1c1c602070300c000c10070b540032982000c0103061540711100c40940002e015401e01e03480750045410054485401c000c0b030340c0c544603070a4000d4a40400080c910300246c80840c003400e0b281000413019800050400100710b440c00030692103e0020307816813208404c3c401c0440548100b8490b0120302ea0060000344043c960390406117002c002482c04a41e25074201c1d036074550035228002c015002140310300240ba4440710f004d00b02d804d400200641c1c10008000148000c00513802013511400c50f41602142c0c12400c0d071010000390024446d00401c5800e00d1038000c81495040d401281c0305600580030501041c00f00c0c4550240c071f8013441e00d51101c6421940ca082c28000206a201c1074154004e491ba491034000f80540e0008102080f10607090680d40e608001c01c0c0101408003940c1c486031b0001c5d04d441d22012078008900c403500040c2c0501c07810754400d8038400e0b4a00c1c10140b07810196060082d004480 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 681057751 1250 681056501 681056507
    0x20616180308031603060e09070302190306140105030609010b03030423040603230712080705101b14070f0f0c03050d05031009140406020309071a0a02190f0605040c0b0a 74
    0x1300401a0030780d401c4c0003460b01e0740740e260400038068a03112410b512202d0280014504007a208130050b940c5c4800c9089940d51307454a80540b418000e155404007151380040c812420140030490707102c0c50035002403041c16a060082076580c07051f44075040a00d02800780d01240b40e0905281e8091403c4020002e01c40551241407039244100140365a081c034240340c1818030f04034040452460221011001c2c6a044000305481d4172200c2d912074542101c081c015090b42e003842059500c01d0b1201e10b40c1a00c9001f10b40390001001610401d208a080e9082c003106101c02400101280c00440c08541d10a04500d0000c10524101c82d2072040e64100600900442800305d2045034050003540c49080c400e200c4c0c207076656440e0080c608039600344004107800c40e48940010081a00c3e81c00668000a04808480e60240d4800303d00401201018807103426900c002170040f4034607410040107507c008008186d401300c40d042d03030301c0c10014800900024022500c130300004080c0004914010000e04056544a40e2800002c0c401 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 681059001 1250 681057751 681057781
    0x120d1503151404080409110c010c02070609050d0b0a020f2809170319110d0915110d0309060209100c0b010b03190b032d0c0102061618030803 62
    0x41d50100e00d400c00399581d082244a009008503044091646003034206501c480261a0b00e04608001010401464845c14003d00c2688451400c0f603010b00855401c0c4940106151420307808140304003c10070a110100703614251003600b1102d41c0c000165900c5880b9a1a130756406009031141c0d042e1040081075045d961000c03044808607000c0e5551101f429212007010b59042000e0300c0c0b00b4020780c23051101e03a000c0190725180c24810141420a040321101f540c400c41e240180d80d00b988400110280c50800980500b0312400c403401c106030414540000014101d0381d9611001c0d40c1c220109a2203003007100620160368105c607041703000680002035107a512100a0404030f0800801c941c5503541e400001104025441660302a544004014040b08503130207103400501081c600300356141c01103c81e1800e0301d180c4541004076041300e04e072524a4180b0828038032400c007004004c442e4103641041c07041000300c1914094203000c0e030380a030401200e0b07880c40752140c190f800483c2e0001000c0f41d8000080c42003c060044103 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 681060251 1250 681059001 681059033
    0x6050a03050c041805150603010b1804180305030c040806162705010c0503130e101a040501080408130602160f030c0b0702031f0c030b01050705120d1503 67
    0x1050245840e45800c654142c0f160384504001d03012000074500340358000d5000b984e005048006680c583e0101c49000911640c001e0f41300c68111080007605100e496a002003202d04407104480401801e803240c00440d0130341c5802e000c014100000000000e015040d841d0940d00500007400c219441d52804414480c3c1c103042c81003d407804100c0d8845181c00c407000140502091030100402c101d0300c0c525000054a40c40c01003182113940380014072070610807120300380d400c070018014041116120b0400d9480300804401d990809560030000c0c7c14241e03020021a0201c9044400a1030611080d1303945085c40d41e100c0c06940300b03c14400c1e0b403c200c0010483c2c0e002413600803000b5401b4900e02c03c03503a250700c00c0c0025181c17448001e1071030350207400400051410401601c001d500207000d0303070038400307010703030301041c0102140c0502d00c00302c4d69088000c600c0381d031504c583d1240040c00c2c20301a160000b00e07200d8599982c0e01c1d0308408010080064039108610440e0017010390303003140c0c2008040583e01d81c0f6040c0004414030b50 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 681061501 1250 681060251 681060257
    0x8090108420405090d0509030708031305041107050a030c0f0623101a0a110604080304110105163005070b0a02070c031101091d0601020606030d02033106050a 69
    0x3102004516043c07095500918002c80244a07404580384155515042461603542c0360042c2000007500751814030041440315100b40740030904a00b45020070003210140d854220b0b24000601c00ca9000400004400e12040e41505010803e2a82d03490200c0d501c01401e14010a510300f044582181d1401c0100d0b940b11100c0c103603245c000655a125007200080303c280c40f80040c1504408910306100c0c16203c001e00c0c0c007500034504401c4015020403403a20b410002e43d411155143c0000811003400305400d201803900c1c03000d10b482441e0103446070014880304818400500790801d0a111400341082c441120f5003038070200c4a00741b00c61408514040d206411030202980d400c484100000c07003000d010b1080380c0c81964406101d005a60842c1c07918202100d0300f403410307414010020000b040004900141561009400c00c5855003444d1a400090815a003e00054000e5014601c01c07004280c010040d50001c2e55640e111800c0301700e5038002641041e850001c02c1d10407840080300410499800310050070420f81c170303031 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 681062751 1250 681061501 681061621
    0x3020c0f09060d0b1b0f0a020d020114012d060c0209010807060c03050c01110301030602091207181a040203070807081602060a05070201020913021306090308090108 72
    0x100a1106000302282c1090f40107852204800000344d20103003054204480310110740203442c5e4000d01c883c5940c00b180360703840780f614046503611043d64100000100c20342d40e88000c1c00f0488031101c507107004980600540b0a21040c11084c1019041d100c5000001c1045040d5001d0030036640745805410020202c1c0c060340681140790010a040400050300d4003212a43c1d600d8641002c490b4034200c0d4907420110700c1e44011754944154020418216028501a60003118016520600001001110020780280d14015000344100700301c0303041c10416040d1900500d2101240042c0200300803c0ca0024102d0740755407183c4003002b84003140da441140e0f248641041c2d183d5494589403039034511020041842d4040059000d0b03800141d000d43e043d004a40c002485000150030b00d0241000035150030480364914910960220316180805030b4040e840000301200d04050003c942161258141403051406850602000301c011402c00c940e486400c52515130fa009840d145a0702c112900e0111610040411600c84070f46 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 681064001 1250 681062751 681062779
    0x5030105010305030307030b01110a0c05041d0a020f0613090902150711100c0803090a26090613180e01060603020c060a09050c030a06020c07080a03080f04060f020703020c 75
    0x500c00d4a0590307400c00001d60460766000b1080b0050024034500c0c5040110004412921a00401c011403c251080070200401801d203814042260240d0075107a801400184a800d40c071a0302199510801d50151010355495084801040c3c603841800c2016002914042000890340e4855001e019401e1080f2105c0c1c42005601201e110301d80100c44010b030504498503074844880c41d181183e8000350102c0c1c00e1030008640140c0701c100488d0011240809281c003d01d404c5010042c0034103c01240000340c0114038881083c86200046030300413844454040c280001b8610390504484680800620a400340d5070301008406240401400e1000c00700c030700940c2003810128606000b40280c90350361031038600600265035100680401741a0300da00070346090040110358455920140541c0c020340740a84400760356120248a82c914100b1180d008800d83d0304000d1507040000d0f48900c030303e500a40508550580368403242080e100a0a020140f80c400500c0000c5110800d9004110100c1480046411581081071 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 681065251 1250 681064001 681064003
    0x50f0a0506010608090a060203040f0c06020f030a230408070f060509090406091a070f0219050a0b09070f0e090c090103020906040c120603061e0917090609100305010f0503 75
    0x510940100030350007007030050103158440c10700d01d03a02442c5a81220b864100c0f98031204102c2e030064a0540388940000d0824050205820001c4000c06141c8000d100e01400020300540b43e010311803401c0200a2249551503005000140041501411300305140d601c6030749000042e0ba40d80e640c480c01442c0c48072054002107060140040c0e4401800103000b6562a0382c0700e1346d1f0000201980ca0007100d41512401c240701180307151102992250f880c94664503000554a80040d08c1d00f0310541c0b4140a1400811000c0d0008401107240010715920203804041a00c40104141c100040d40d001400c40b110b070070078001a07101308507a0345400385a03680c060310030001100c01405000c0307600740000380d0000001c5012070381c80d0400307a00201c9542140c0c039002c0581e000b60f40064042d24410ba2017900c545448090300a521464a441c0017142250b00200301300c500001d0340d40c190a042080f00000240384046805d04140d240c5404641c0f500400810100b0000c10f000e034044e000301028080c03182284038104001c511820 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 681066501 1250 681065251 681065263
    0xd18060c0f080a0614010c150f020d1d0307020454021f02030409050c070209091f2309060f060307061409041e020705060703020304210207080f0604050f 67
    0x240c05d00c00343d140c4400b080c005403488140a0750484101900071044100003103613207d03542030440700110241c1c1e11030420000b00b040d40e00e4003110f0745005104240300b000a02001040352116030b41a9408036507401304030700480b01058007001c01e0940030814003550481a05c0c590020018640034004144064490b684142881c040d200c4025040407009c0380b04401c0f5850180c03030400c1c04040b40704880c0740c141c581003100c003501e03000d0b00c04400c9658041146411460407101c1190b0041c0301100812996560121412203a0007502c114186565900386811000440782802d0401e100441070000450820001e9507640d49802c5440b4a41c5034a0031020071403e2401043c0079044509a84d903081100c1206c04408190340d21000340680e010b0780d103180c141600d407041071b01041d028405400068903403c00d41041c03400d0140c020a0201058410020070001540a004014201d0f50200d41d00510902c0064140c0c03804209030000e807900c0c410000706150f400000900c5070321503031050080d10011540103030610f903030390 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 681067751 1250 681066501 681066509
    0x80910080604140606160606150207080607081b0a05040306090f03020d02030c1b030a1a070201050c07021011010905071203090f0303080105010c0501020906030a02030f0f0c0d18060c0f080a06 84
    0x40041105c0324101c541015000c1b290b80c014070b80060b0f072035a20804c1200300d00c1d01540e40c0c0090b810000081244104c244501c948c440801c0c2440c0060740f4100c0491111100c00c075003410750101700030590031070321486030007641c0145502c030f20304006c0140d1a04000a012440800842c01803140d450810b03115031010041e0f48440022000500103003145124080b1041100c5004640500c9030700318101c007141d04001207e08291400410740d1a40c14019800ae082d80c00041c201c4841200400c040c0c40141c0f141c8565008402552504804034000c0480b0207002d0b01006402900c58030031140d000c10240d500003111414103200b900d41c007501681d41e901b40d40314000c0ea484041c0128100000400480d4025209070402500c207070700040c0303000d2614000441681040d600c0001145d80802000800b007080d80490341c0001602d1080c10151406e000642c00500c00e034000d4181c26034440c190400300c10303200940204000ea0102050260045401004003440c0c1d0302101c03080082c10440108650b45c1e00c611850040e1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 681069001 1250 681067751 681067759
    0x60f030412021f1812050c0d0806060a030209010c0611092704061107140606040c020c090420030109150516171b0307030b040e070e010e040809100806041406 69
    0x2440c01c02c000792000704141c0c408100311001c0d100c031440010303540002441c4245c489844941d00e03001020f00305454038071510440d1041c003900c04140221540e81c0010303244020358031b150241c0d0b5205503078012501c045d40c0c000020009420300014418005002010f04240d082c282e43d00000c0d440d00040d5909004140c05010302c100d1a0f44001c94003044031904641c00003295030000500d8080196514860500003619141140d009201441101d180c1400b901120207094802010060003250024014440c09400285007041035000d20b1049034131190300b1244106c005001704804900345c00d008030310400c01d1802040740c520b000c0000d000384092050305070350181b9aa1340d080c00b41401c1034149070715080241c02d03841c2400315545002414005180114070406480e60f000c11041d00c0a01440103403600d801d403003480d80d04031072005d12248071401d80c07950443d0b25401e0415801d48803802c0032074080c8240307400700e5005640c10254840b00354200b2041405581d05030780070400620032118100080409403102a40 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 681070251 1250 681069001 681069043
    0x20310050415120609050f0d0201050604061409070807030b041103090c2202090d08040312231e040b0c0312010807272702150c060c0a030902060f03041202 68
    0x1040007540b003020317043e1007181201c0784180c2821656280c00e22a06090700140c0d1208100007050406008500080104030701801000c03084000140b2050030081490341001162800611110710030340080c150035102410405c040c503020044002554000c5528556a1045000c0071741e880c2844142c9102c400c2e00d821424410b551442442c0001e940110200b5a10076507919203080801c000070014801103101d0203100e0403d824000024005d4403071140b2000390b9181d03104a03081941385a50407100000c103071010394102c17144084025015801680c00038004048045130005080000000814a148100508442c0b5030781e18811030b0341c1c5100300d016600d10700503001c031443c81c61410340030000c00502c5040e5000c02d80000d00c00c07010380c255518045040c00e000f11950440c041d03040680f020304644505e52802032408041050050b0740f00d8000d012032010790700015000c2c05180c1319130720503036025a0043c40259101421407007856280c1080d9401c0d01c044551a4881c14030314000111100c0100140440300c1c4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 681071501 1250 681070251 681070253
    0x20715020a0b0a0f051302270106030b120111040f08010204140402090d150515040b0a0e130606090207020a06050901080a020c03040e0412020613030207051e0402031005041512 77
    0x45030003902e030f05090f0b0789400407210800000d000301c611418001e807034544552080c1c010007643c0f80b140704014a03207120881e401c0e82c51545000f901410b4524a050101e04640038402282c2c5040030000110705039440c1c101c105980c1c1c00054001c000b141c107061142c000081d11490080e00300e01c603501c00d000b250403031940c00f00c400b814150060801404001e204100103545a00e0b840c0481d01c104009242d0307030303a9680800003401d01c07541034200090740540d02008100301c0640070503684081800b44c03203000054400020018480e240c00c202803141e00a90511080e6904d580300b00c0a500b0120f8200d01c28418150045896442803060f1000c483c070507074444450340c89140c4100001d40c04561000702c940010040824404030410881e0b01861041d80020364560044d40020304085001d407212a0b06000c0c1912100480d900150100c00d8510444490f080701500c030340c1c0003c400e401d03075241580040c004020070400224000c00341d8222402a10203012011300031140c01e58405060150600b103241144d040c00c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 681072751 1250 681071501 681071513
    0x7030908061014040902031005070239120a030206090606060705031204020a0b040b0918010501081f03020a1404110a0912021302030c07060b0d0807080d060f090606020715020a 77
    0x8030030500044c0000914504940110781442c01215085c0803103038031142440507071581004031484002503801d25040040058000c2c004007828008a0414449103c110320344550744c1c01d890108404034001160840e880078a40a51502c6048894081d43d020784800a0704a050030b80c12190b05643c0400954941041740385c9a0506c500042c10030398000c0031480e40490808218002400a08802c411403900e030b0300e1450030006484c0401c5141e42c000c071110401000181d800114054000c06540c4403180c2e043d2414150b0540003c89900c00ba5010300c04602c0000d20440000d1000c00005055806220b0a03a500701c54009a102d000810b80c0090490a410040d0290702c4409626052004040c510021031140c401410380c3c20a0742d000b0080403001411000700500e40c4a0f5294290f0203640109044600d922a0002c1d0302440c02d02900d0320f100012003c041e45d05131760114010304001d41c481c104190300d52000700002d208600614001d0310500f40003144d840d001c402c8141d01d18a2950050003d01115a501 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 681074001 1250 681072751 681072779
    0x80d05070c0209091b0409050a030c1a07080712050103030e060a020f0303090606031e0304091d0a0302100b01020105040b18070905041a06060304111002190602070309080610 76
    0x300d01040308510180740140c2d90700c03080c24000c0c0680c500808902c1c11900607003048a00d0148040c0c4501e00e400c0580c2e000441c04a1203682c0184c16003050652645107042406168000031308092007481d45074200900326800000240c0141c501d07035685486d10f0285074900303040754400c4c08043d01040c1806458401d525080008100c070066600c19101c00300742e0780c0361062035a007054503014100d4101c00108070042c2070030803c00074040d0010002d802013080480e40d01d900d0380300c0d03401840482526501448540c2c040b210501180c29221811203540c0742c2c20b420300944400d624210b5481942c100815002298030502401d4000c1d40c222220b0021526008a1541039031901d9007140c81500030841e00081c1050380e40b09551041340105d0a001c00c3da051101c2608904a000748494030410081c402c0c0030106002c500b00100000007594008941c070809502a49051321070392400b080c2c800c030450114200300664015059191198031601d00203501d8001c45901c40c0f200302c83c01d9144820703640040141884144003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 681075251 1250 681074001 681074011
    0x1e030209090c0603042006070c0923040303050609091203150f03160e07050a0c24060306090515010b0d0527060f06010e0604030204230906010f0e04080d05 68
    0x4a98444550308042001c3d80c000300e8003030b83c80102c2d0301c2121944000440500450f00303805c4401e140340008954420a5091907400b03041a00c581c1d400c503040381c03861800c1c46031074102a0b60341061150301d001d103030040c00ba01c01111042c0c000d000075070108100340d00024124030340c9540000401c0c2103685543d0680d960f070100c03452042d4020440f804070b007011b88080c055041d180389030148117541203040c0200c902d281d04018054800300501000a02d4929a21071203240c00d00d580042c50880403402540c80c0060310b40c10f801028485480c009000041108562000002c0f9104405683c1c2c5007941d10340c240040003003481444180241080340e82c82244072948810303030001c42400402d2140e000d04400031807000c0c200f400c1c664541d00c1003043c0403070000f50305405641700b070091a0000311040e501c2e0114009004e148802409503882c0c003400400790b400406e8220b1005a086040051460450010b954500342031084414041019101007442007240300054403454024242e41d00c0d080c00420850010240240 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 681076501 1250 681075251 681075253
    0x1e0b060f0a051c06030c03060b09060108041e0c06052a060f09100c08090c1516051009050106030209010b03010501080103112706010f05070f0308180a06151e03020909 73
    0x403a078600000c1ea1064070080d6000e2000e606d5000c0c19440c1c101c2c2111282e107050f41c800c14a41081016036a804000786a02640c000324100855a100102c81c40006103580d000b0010f510098020480700e5001d40640b25140155020680c084101600d04d8040883c10b0200c902d07a070410741c00941c8804c4500b035440d410100b40c2e0219480040802d4156085400d01c01d15140018000c81c1800618102040500e00701e00b01240c04403880f0317002c0c98500401c0e108030805100b181e490a013448003880001c0c0b28514400000d0201405551b009280c441e00905450208038440c880220021038a05072039816641600c0c41a100c0342d41ca0707405c64450f030281c071180b03410450b031080c0c41001e615002c0c9040d881c401c800c140d050500040c142050000500149010141d80c0c08001080c400400031410983e1242c5909816081280840c1c450174900c50b4060031405c40e6200d24420028050100103142d4040705403040010b202d051104e44609800009800c0468400c6511803990000c4c009880e1807961240c000500070 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 681077751 1250 681076501 681076537
    0xe180a021606020d0b18090c010f030b0d0b1e010f14131d0d0201110304140a081902010b120309040f15080a110102030c060109090c091e0b060f0a05 65
    0x103035510301644d00410107890600e0304e410500307000c0c0c2445032580412640345d00c0400c1c0303689400960541d44900c104072440c1003043d070141c41150381d030080c1e0000c080c0341c02c0917000c41c20010352401d06003980351007500e40340300122501644450014185000c94140c484060310703140584c1c0761000790791050f144586030383d03400400445858503000447c440c420900c001c108100003010382110b010b50402a41044050640e41003003914210341c00760004503507102d0b40c015905039900301001600e901c0c09101500050403680001999080484030001d460b660008550091140045800078001140403040c91204291b0052002c1080d0346844c0c0c0003880003400603c00004c020a0412a90822150799070145040c2d41048159205200c1c0c100d8200800000a0004528007600d007840c0560b1442d0501c101891656214010003c11054000741c5c00246002c260900c03203031300110840c00446074000e4002404d0303807174520306001d80c0c1040411380340d282d207010400c0c0d8240602c0354401d4410307901111034014007540f00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 681079001 1250 681077751 681077753
    0x901170313090507030c020304050d0212010b18041101230711060301060507051009020109030b192a180b0f04050a08060402030d031b110313150e180a0216 68
    0x8500c400002c18000c100440c0318100780313001800302c4806a141b6021500108001d01064482c07111402499074103580c54801000075100707503401084464070351607202000032409200c1007060030509000781e0140180440d1ba4042100545003a400011007002c404507000b001000c2c1c41000000d05106406003444840c408100030000d10300d58001d80107800407038000f03d010300900804201c12503030740b25210804c000f2030300fa0f500080c0030102c00d4403000304241003102c001101d94201403840342002002c23100500200c6000c142840c0272040c80c0340e081c2540e607900b08441c8003151191404d0030741503030007000b803008881c20300c6070b90308d9141c0c00344a0552406004010000d5181c444080081c014120382c0c01400c0c15040c86d204140c2810382c481c00920405080842c0c5c0400c0340160107820180004a0400103604480d0300d0f2a60b042d40624401141180012000024140d11040d1120905e1845998030785c00c098a41c0c08000301d801416044c000d003420301000090058820768020410200c4400c3d00e01c105440c1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 681080251 1250 681079001 681079027
    0x1030c170102181c0c06050a0f02011a1c08040906031e02090a02090f130603060509071401030b0a17010e0d020f0a0f14030d0b04111908040305090a080703050607030b09011703 77
    0x143d102a00140f030000316000400c1c1d005509d49100d1189200038400800c82000d0a5080c2c03401a50040c45176200584120444185404502403c0c4d405103110b44c50355030b6404200000d00c050f100070b40e40484050480c00f0031840d14041c844a16600a00d18070240e25502c02420094000c08901a040305424260314010b640360854010900f91280c0041142c604500c1c0c0b02c0143d80000d8102259a403181105024500d840300c40401036043c20700c0d00140f0201e1000000d800b54140b5403207811001e5007409074041e20441900440c1d444003028040380c10304441040101e0761190800040b150782d400c139205900001c3c5100d02d50000c0d180c044d0710828230800d100880e0700d0443e40410841c3d0001603039010000c20a0615000d800030030708040f80640c0c00c0100030a4809880d880c001000001c00000b403001404050240c4243c40c4070b1440503180141c25921884001c2d569000c0340010f0f01c580c0300781c00004181511038010000160703005482985241d1802c1007503a900c0c410543c541c50140002c0c8114420403007 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 681081501 1250 681080251 681080273
    0x110118060b1009081c0318050a0b100f090b0f0306100f060509010903060c140409200301050303070b190f0507120e07260601030c170102181c 62
    0x1024100000703603100703004204100112482c10716428045514030822000c0008500e0380f10580c024001d00b1805450048220002c0900c00c9601607518802002c41e0b0031f0000020340d8803416413280000c80842d4840324a02c0000820324812188445000c200c2800308420b0b540001b540f44030086c000b010009014000a801d011040701d10b0a91191300410070011520035070000802404107050603840c0c481e061000030080360326408040c080c56180c0f00c400a4240c419070101c200001d84c2c09201e9220b40d1551150707030140170a1103801c034000a103560f070010041524822a4100d481c003c000354540900350380d44a0310500f0003000c846001c01c0c810040b40b007a40c039034001c403030741d0410030100042d142c0341030034001e001c0f80884c4407401d1505240840c41c0da000c0c08001811b106640c100305001c80303070898a00303c1556803054548468550301881c00004204050404d0310002d84e1103560342c2481041c0042140d500301e0007a4180078500c404000303140c008a050844401d905c201e03034090b50310071060303480c0c4034220391070 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 681082751 1250 681081501 681081503
    0x12050a0b130b01060c0305180d0203060103060f14250210020f031b031003021509030a0b0604061d040f08090315040303050a0c0e0f012304151e110118 66
    0x31039030503000401c20002d076010602414160170480d1200482c1d8400070218000e400341880302140306202c4072403a80d600039645040903801001c5030074541c0c50f07151010182c02610520009103040c035040409420005858610131400b2002d0f450408581c0404841d10581c103081140650040100d80550440240010448a00034007003265817810b040440741a1440b0500415960f10824014041d880700c03940c0c010030440341c04444200940b101c904000490744248601381b80d0603c1000d0014080000c9840024401c01c4100c030204070407a41d0b07032590700c2d20148140d0388040c081c1c0c0c0480050005441c250012107018042c4c028181054400c0000c00e1901505001555185c5420001c010405034107000f01a0b1014140354180070f04000707000042c15900305000410b01c60356450307640d000180d00c500746440c2000398035240840f42403490401081e0350b510902030420090102144404214000d0740e030041e00302c282c00400804040c0d144411900031890035003401e0300b13540b03404844011000b20b0074030000072 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 681084001 1250 681082751 681082771
    0xf0f1a0c090307050103020403023a0b01050415050102030a0360050f0609030601121a040822030203010f020406090f0803040b0a0c050a08070b0a0b0a12050a0b 70
    0x18038400e00402d45480d00d95841281010300411007440180c840700c440e008800041e80103001d0200e48240c06091515107800081d1401d0130802c038100030f21600801d40c1d8101c030820f40b01008070b1045000c0750341421840740103290250348200003c180c003500c00c0d030100040a8181515481d650b01d401000e0b01040d404808011202c07000315812040340b494075806250860140900e110340e000303005c0b00d004019210b40305d060b00c500100c001c20031142d00d4210031035004100040c00d0381c2c543d684400300411804004c110950f444480b00044981da41c1071000c94074059900040c1690070061100c8811003000041109800b0201c42c030000000161024001c910180d64101005a1035a003040c0006021070784d6540680c044500c102002c001224002c02114183c2d90480c03001541c407240038000f50344035020804014a5841040040418861140e0282c02c17002e2040301801469203640a0580c1901c0c04040c5043c2d0042902400308214125544810035841c850400d0b90400041921201e0718180708950342e40003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 681085251 1250 681084001 681084007
    0x907020a0201200d0f020c0405010312030f0f02040306090b090a030c0b090f010c051b0c06090105031008030c060103021c0209070e0a0801061511030a0c1b2d0801090f0f1a0c 76
    0x1758042c4600c055407007055404112035851a103654140745ca100c0600341c245541e64014a07420300b00340d003060388205d0300c00d9401c0d59281d50341d01d003410003082d0a40e411351b4020484400719041c4035003ca407450509415a4078220f0007411078a842014480292031001c80f4841e88500c00e05c40761081c052259841c0103070f182c95403241c243c41c1c0e000200d05d6030701c0da0300c00f8aa08024002040e942d50102a94801d82003807030311b1a1a5034a868a410049036560401d034080d11011070090300c18500007604505991007030352014910840308448200710385050030021350052725140003c44481c071680e81f4010031807000300212012640c41070600c6c00c4942c25084509140050401c0304000d5401030101c51114107420002e603e4003504040080c441180030900400c03400540c0341c08000440c050758101d01505030000b400018103060122802d540a29000d041c020428003500003406100c1071080841150f0080380400f1425559601c040700c0445880049803585180743c220341803401c020040c2d52003003031004e010f00d81d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 681086501 1250 681085251 681085277
    0x1e070c02010f180e06040b0d05060105041409030d051f0e1503061e0603120301060e0108090c030d0c02130903080702070e100b070f061a040b0907020a0201200d 70
    0x40a41401c0c030a08040c41940c0620004050010700100125110083d1400841d205c150000c1d02810ba4410442d61050f081d040f00d0301842000b103035646c1260003c80d0100710280c1c00c904e8840c00303100d080ba038040340c0b60000e220906403124190000d55000300d6090004241040050140c03181e00003a420034084d441d0f511301002494184003183c00c55445044004103160701c0c00d62a90300700840c0240468003801a400049041a14200005280c820303058410584940e12100c00415292540c180d4900003000c000102d420050049032410072540c01502030480c103420260151150b11501c01c040740c02c280c203c0c1c450a10111b007485030a00d07481c425030715040582130040000340b40400310b0b0403105d00d6813009000c1c8008642c0c00c8240c0c504880101da84252100b80318108031900101e4004060120707404d0540e41c0d2020503060150a007001d8007110100b25180003c0107003c0800d104588a1001d030303000c0e02c0b01001541c000c0c1402050519000300b00c01d04071782034010341070030032000160b805c000c9030b80104111 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 681087751 1250 681086501 681086507
    0x2041b0e0603040206041512020a080a0b0d12030c050c01060312110312070e031608100608030f041205070f09141303080a0c0201022709010e1b031e070c0201 69
    0x9840d4004440442c00c6040640004100f44200c2c0300714101c41c65035403084c10710707180a4184050b00c0c40c0400011501c4a40741d641c042d003e0790701200d0f42c039951440c9c05000d680038604102c074204281e4201c41840300c01a0307401c001360018080070749400e052040030702205091040900642e8083d52180301860565401ea4a001c0d02840c2007507029043c540040c405080794800400702103600c80d00030310342201d182d001c20300400e0600174410f5052081071400803002c01c0015000484010000b6801403c0010355901c03480300f603c85c000d5045100380110200000c0201c448a2a6980c81c1075008509544640c0c3e61100a5402c14450381e111103210350311a04120381411013540d00c903501a46052540c015400c05550003000b00e4001803aa90784150740300344d402e200904c05d60580e5500100c400d16844d00248111110303047c4906040b485100d4071803a00081125410110000c3c0101ca5030031414803191141203544d07240c2c2e000100720900c14040a0910f010b9008007403d00c2d40110b82c48c1d21902420314081c0001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 681089001 1250 681087751 681087767
    0x6050703110f070309051503040303020703210509160b3019060f030503070605180f0303060916201c110c0108060d03050d1103040308090607021612050a02041b 70
    0x364840c07140c4c1c1c3c7c4824420a05001125407280c1d1600e401652001075280c15502003108000c00112603100d22a2542954080d91041c0e004204103011110072510701e004003c031491540c01844000c03642400a01061a41103103203054284000d41c0e050007038140200100c1030303104104c0f0248c1a030f00041400500c0c41030584211700140c2011510350490f02d066413507044d500e1103001002060f0550712030024a560702e0a100b0143c441c091031003603c0001e54000e60595483c0c100742c55041c4030f215150b01003401d0346854051407400810f16122101101288030f10541c0d18079072507900c4002409610000100705108608002101d01192607440030310665401c800c0c81c3c9548200342d641403004401c1400810b43e644002030780c0180d0305103000d030394400b2090042005003480381c1e05016582008014081056000740b08284a55083c0007212203075566840f040382d440ca10080b26503521044550140000b00801200301d241a01070412115444115070100782103c41060b002da00300707280000d114480340d500c0042 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 681090251 1250 681089001 681089009
    0x903040e010b0403080f07111002070e1e0103030f1e0305090f0d1b02130603121736100605040e0610140120011d060f0406050703110f070309 62
    0x12150503e800e644d1411501d20074072100190140d0089030040401850315190030084c0009407115120f41c007201d030042d6071003070240608990b144412000801a0030440540030200c486200c070100c131a4690345040d41d4411074031668004101803601144030010a40e540000c42c1051940c0000340751030011041800d110420b940b44200d074001d10b01c0016841e42c40324a440800047c4120144c000c40e0a10000ba1a40070101e607120226003802000000d01009060480d5521040d1b200d510720b4448003003105040388811150100503a481c409001d44042240a004071065080450b044094a080d1070103032078603600b05d5102c0c41c0c41da1603003030a01c071034141402100c021525845c01081541040d4285070114030460043c1e00c01080e03201503691b010fa01c66103007a170006810016000c60000044170942c06050801c401c0701c0c9082c450202504600400101103100d401d070b4100c0d4914980701c503610a0054440a814003003016210305101c0300001c80440281f20f49006070881554400c0c1300c0c034000d0052242548 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 681091501 1250 681090251 681090269
    0xf07032001090b0f0f0f06061842041401050405030604140106061706040e03120421090e0a0b01030b030f031218031606060306020408030703020609010203220212060903040e01 77
    0x414015464000d510700e60300032202322602c070385468000d00801c00c507100c1070400e994400340c4540c034010300a440c8803886403c012010488054400e410b01d148440d00008511786080c0507007000104020031600030700d4404c401c0c1c14907095151990303840000c4c2c602407007a0b8040d141e01c8034418200600d25000d1044000504290402c460402e00680c07a18101c03010082401d809076458016a02c1d000700d00340110b607a501208896190f450602d801d041c04203510b2034132151500404038480002403406180e000045480003000e41100356030b06900480540007421007030303050507240c46400102c1d680a000080c010607074640115240c980c10701c100e07038002001270508503080c04214100041e0040200c200c680c1f5103c0e80d6145030942201e844c002c1d0042003540d00181082e4408900841c4110700880203082d001e0080e03086440584415440c0c900301e00c010381c1c020b18070003c1d00a00c4a00b2000d582c48bc3c3c444030380001c02c10144100d941d0036990030440101c6240b622030300f0004040c010b00044078606030260a40b29 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 681092751 1250 681091501 681091531
    0x9120601060e0d0204061d091501030f030c050709060b07051603030203071b050d06020d05070e130e1002030f060a0602070501050d052a0913020f07032001090b0f 71
    0x2007005080c1d01001180ca9014180f1641000159291504034800600c0c031543d000c054420001c9182042c5401903c0d03800e4039001c0d140400410303191800d00345060300d400545500005200c2d03034051f00e0f105c3c00c0b910201c0d15401140c100045400e014400e520007003c4c0c0d6010540d542c092494458105003506c00b10524103500041c00f440443d50000c140d420b2681d02c110540c15410701080004140519503010303039840343c4168003030b2040090b150054100450303034200501417500c401c1016200225010013564010b012096800140d103529044203005907100b07030175244086100c1c10484140c0e40111205003900181d07406000380c84c1030007400c00c1700030001d9102404403035050400007000c52099103640e084468494000c03c01807080302926003000b040c00052030100841c1c26040000035001000c0ea90301c101c500048100f12425075000321898240c4843d0740d140742c190709990548440ca2001000080050640e204c1154804244200b0041d0707401020310168030719281080030a0307200300402c0145030351421 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 681094001 1250 681092751 681092759
    0x1f020c06060d050a1202030a122a0c0803150907050a17040c0e2a0a090b0307020102210105150702010c170d0c03060801051f09020708120a0209120601 66
    0xc220141c0040048039100c0d800900d0f030500f5441c00e0200b04014022403100709088602c1600000185405003035a00c5824143d01c400700d6420803110402032003100e100f20340071155001c8841014800c0405004d09083c02c0e001c0c07064443d0080c0d600204c0f0390009820640086004526084c000700e0b50180107841c00503d8500341540080101d10b803410b0b071203105008080402c1c01c008003140c071000036000c4465408160700c4c01c078005640e910071005e11881300a4201d451411013111300c00880b4090502c2c0d4982090f0645440400c11503940014801000c5540c240817100801b660f130403048880c0d000311954031055505110400481a1242514403c0b03c0030411035180183d030000c2446c110580c2140c0445850043e0305c040d1004c2c0e218410740900300c42c2c0303001c46000029070141c1c003050594071440001c00c101da48a03440c44038071001c1e500d0050b5155501c1c500c2003000722110b0300208a01d40c46644100e05125596103442c07800802540c100c03068540126148102e4240031040c000c4614000c03000b05225450 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 681095251 1250 681094001 681094003
    0xe06040515010b04030303051902071b080f0c010c060605030712051b01120914060a021e0309061b0403021509011209021c080c150709060302040305060105040e010b121f020c 76
    0x80c1740720003000c0c540c40ba00050340c1c403407814509880c1015110802d6523610b0031450b20310503111141082c064440d420783c10109500c0400105074034028225002007200d0310480d070054454610280c400c031901c98503601c011905031000d1040d000100074443d4001010841f5262440c00d20a4244601c1402d034840c04072110280e1b0b000b00ba2200010440d540000c04586a0809400070407102c500180e00784100d10a001940c0311590040000b1000d0898001d031014107501066540e12098031448540d600c1407010814408140c901c8003005004e4031511840c0966a80c00300f0300881c68808400d03900318000c40d00c0030180d60400080c0251070b5441908100c000c206034001485040e00240d1009007500c5d0404940402c0308400844002d098007070201c5148415001c010003030762200710740040008140d050000340403400390081d03505803036102015081c1a130a04c41880018a0304e10a40302c9950f4a4840302d8200707485104905070b03095030480181c03900844460340400c003a8210f5052042c1144100114200c161f0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 681096501 1250 681095251 681095257
    0x5090a09020a052b06121109370b010807090303050c0a02041a01020c0303070b07210c021b0612150127030b0a09030c020d080408010e06040515010b 65
    0x25250340c0140c41c1c0c284001e040b240d5001d0701c240c00c4221100080040034a45042600500300910104107001483c3c5900686a550352511001480c0201c0160700101c603162140016910004d035280000c2805000307281902d980741d900c500380300c907010703410119800039034280505400740100713080107d21414401e0008085404901c4042e04204001c031b00d9000750713003060100820154000b0018000880900100d1024110040449004d07105582c01c02019040100507135400c40c0d08040701c130160f50b07141c01094507100d001c0b01c0007a40306905850041c850030700b1481602c00e5150300394010500c40b01c41c00e0542d541a6500f6040340d01c0f0301014890f216002028240440d8820f80010084084400050040e50780b014140070448a043d00443c2012103140b03070a009408803405a90320255a86035203d410f0f040712001000a070000d803554203c00c001d800c2610a0f41206889045003914150341c0320503160071200b40c03c000a0464108a0070310003800804c01085041d210342c4c541d02c0c11035524061030001c8502c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 681097751 1250 681096501 681096509
    0x3051308070215191d010c030c0f1a0403080a060509010f03150f020a1112030f0114031213030c081203160e06040e0a0e121804271205090a 61
    0x22421040d030021003002d442522035010412903440c4c044680640050401e0a80149001c3c0c0c02e8410030445d24207600c5020811211398050716500b60420703498680c008804812001a1500c0e41960794010300f060418040c2c2c2c0c0320301c0c000d61301d02c0001e0900202c842c040c0e17081640001c0c4215000310041c0203201c80141c802c421242c0c400e00110b410300010002030081c2c002e0415100b04d01e4404110b45001540242d090380c100b00d00c0070180c1d40c603e403104c0d9415055000036035140c1260280400103021408c1c42c200a8040c01c0c90040455110100b440780d985125801052154641c4003084ea041003044056118000641100c1c009040e2105020303120101c140070040017800c01d40c0102c40c404ca032641c01500542d141240140402d56507644400c07110a40420548000c11100c2c5409285680704201050342641c85480320702007454000c112800c80c0d41514001041584959130341c001c200075804200e48540d4400550f110380404a040f402c0107520001d18800784404d000041044074101e560700c05281040d5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 681099001 1250 681097751 681097759
    0x50607020c1c030306031703040b0705031006050d29100219240906020a0906020a03021b01111b040b12151b0a0c14010207020603060d02030307080415030513080702 72
    0x80c042e800d044014040c5680081c2102c50110300c99450320720030b90021031056000310b00011a60722070040440b01448200c03049004900101000d002c89803040380100842c811070040801d451071211b01c1801403000164000541c1d00d600d61041c0b00c0ea0070090b205610806c12800a80010f020f40c00000c03076500e142a8000300400c0110f90b00749406010f58650941c085400081040300641502e803080083d480b004e1210301003000324400180c401d00c0020301c034060907419030180001d6120028034032094081d603440b480c144400a26030102d4860100513000c0744140c911001c3c012a00304070709202c111444000c0c40c60003058132030007509020600280c1080304040e0480e107002140d40b568508000b0070704065a0160513400040d0015a070f13980070081e1800350b8040c3c6200030060044010f500e080b48650318000f500842c3c1403000900e240340c58488102440d0002d0103892524843d40e58010441d8840e4004141c0525481c0c0d09000302a0f140c07060300e0f07100e856460011070801c0d40d901e0b14000c50059100080c45 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 681100251 1250 681099001 681099049
    0x302040c050c0d020f010b0a0501020a0b0703021c02030a151a0a21050f011712074103090603061c0c0605070b0c0f0f0a02030f1204050607020c 63
    0x80c4920300702c0c2d2032500400300f0b80d054000300090003510f0346002d201c05101756085c8031301c1e01d076145001956103040b500141c008100100c40c82c0e0300c211071150000d007648149035007809268003c500502c10420060140304005070b4038900600244c0480c0d40584c21a90300146100040c0841c420740956103402072a00704100ba00c0311502182100c414420718603146a440086a054140d80c5280d00454062000700702568001d0ba200c1d161880b410341d4904441059502840c0c2094041110301c00a14000c5c1c0681420041c883c000c100a64084c81c2c0146071416458400f8603525049904101e0b4100c0300d2003440207107180029041c006281400003402d594450384178500003a8241d80503040c0f4400540e4800c200d000790554401c00034001da04150300c1903c0c000c1c1c44c180024003252240d001c807010703003452411040c1444560f04101080c0d40100f5008002e40c0701c100506600094160b01900030200e0a40d01010145020710307100d4104140a000c4006541c44103015002955801090728844108040d0f02e4076 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 681101501 1250 681100251 681100271
    0xc080a08070b090102041802191103040501030e0a0606080706080a06050604050906010302070b0403030f0c0c022407080c0a020f030f060109020306030c0904050c180906010e07111b0f0103090c030204 87
    0x100902c59a80130100503498030080951f000348a8000d000c610f800c81c05e01d40d0920703c5048003a0740160304c80340c25902603002008240a158001d40c00005512940000ca0f4082244c55455504440e0329400014460344030b8074007004010781c400c800c1a8050800101441030b14503002c04218640624060f685c07103448030303000150301c0e81d00c80c1d41541c40d400d4010b842031106041c00d0401500802d0305076440b040c243d0800d101590300e9130080d039140a440394040c02505c5081c1c0441c902c040540c89803900610710384002c020740f4010690307940251881600c0c4c4006032030344140380e10400032a588000c1006000e80c002c841000c413884808a40c407811651348940169895982c4d500080c2000c0440c1d244540c044130210604c028001c0000d20a41940e1080e21210030303500b00e60350a03201151041b618120264002001408000c0700403a803140c104440341481c401190700b10040d54203080414a0707980c0d1070b595240466100d481c141c1c284c4001e000c401e0a040008400c1c0d6100e485100c00580406805103840d148061 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 681102751 1250 681101501 681101503
    0x3121303050d0b120d0c03080106170411031f06050306010609060e0f0319050304051c0b0403050c07170c010306060315140d06180614010b03060915060c0a0c080a08070b09 75
    0x840e284c02c02006440c611152918090003214448000380d000510781e00000c50590b0103202c801240c01c0321040d8000443c0d03659620111804d00715000650940144031024940f242c18980418a2402e5801c0c0803039094200005d00d0300d844016404882000b44000041183c1c82d000855811041c0d4103032403a402e900b05501c0840d2810341c00d80c8044608044403003d0784140880131000e0001c0c1e81d800c860000102100c04460a2070b00030300300001c4c00620000000c100060b00030300082c1154040542980c0060759241d0203018440c8110400301001d4101c03451010156905200e800007422440c00c003000540c140d10341c02071401d44c070360054410603095000c11190603500c01d140502030b01d43c00a030031705c00340325620f5440c0d00c442c440303036401c544240c20444003100c40384007011000e0594607151401402d560300c0e802009041384010b07040e01034a201170b9000e400c0756100c14004040c1ca1103a100145545d0385146401d02c61400607070301130803907500100f04540000760380170b0840d0105e07a0002404201a11990065 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 681104001 1250 681102751 681102769
    0x21031704050703021e0f060f04122103020d0506030a1709010522180902011205220819030905030703030e07080f010c08061e040e01021b03121303050d0b 67
    0x3a50012044103601490040c189038501c03100c800baa40982168220306c203200080c0500d80320300e0030f01c4005101c18080080c01380b14041c4c0d010301450418070129021103107116060459004500003e400180f5941c9801090241542001c01078004003203000240c0c484d2180c1c416170aa0700e82401c0c10006001e40b043c1e1040c001d5994892051981400c0074201090600c004090f62194100c55800540703c1e4808592510a40101540603180c00000840c001c408000600000b8035000728540000314082c00b80a143d100311a07281e100b01103a96650094940403450709031083c50820426007011035071400104084180c44000ea0305040c0401c200c05580380301ca040020340d8000034918446c0410441880e081500244c500d410310b03484403036a5032184001d2007100c603411014000d01841a03041252203051a601418503103449600041c00c1180d00206542d115081e566802850340c40483d1604030307a0010300b10140c0150b1390305044420000030780e80240950017140e81d0306001641c2c0300705002003510b4440310 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 681105251 1250 681104001 681104003
    0x903020a060e3610061806080f13050f012913020a03020405190317030105060a0e0307150e0f0406120b0403140a050a09140a0b0d0b060c0721031704050703 68
    0x15001c491070903241313003940310070349100d0075002a031140300455032850030180a4003510440d03510342e1040d40d41c40101060034080940201002001094400080350041c09040020706656001042030f00c1044013a40d0391041b827101030102414241050701542d0340d40307584441c1c0c84441210144c0c40d00c42d0300e40241c4c002d010743d40c0800d400483d01008580310488280c11042070f41c0c031030b08006c1807088210039014254002400788070b40040e410400200c0c4940283e0380300da01d92354010103d5101540702c07802ca841c0d801c07001c42000d02040041d0856500c42c5810541101034400c2079408001143c40c2c6103103406c000c021641c010300441e101102190900d4403603144ca10550b0110050183c0e52804614001c2c483c5c3d100584c6000040c1501c0d030041003031100e420b5051007400300149214035941c10320f10071212139070100c546400500d0b80d5543d0b4011a03110100170707100751802c48020301545443e004400303000f0142600103100c41d1960550050010390070880c26540b028240c00c0e1403042d0381d510300d081c07450106aa00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 681106501 1250 681105251 681105349
    0x30c081e0d0c0c021827011a0301050402030706050c0c150c0d090302030601051002100c030b03100501210201031409010509160b03010e070c060204060903020a060e 72
    0x1100814030340c8010244002680070800255090b0341c41103d500d0f200420095100d26100d245600141d005004260450010440d034105c0d0b100c80741ca00d000d400144c01640c103140e5110f030703503251001c0208106864031510a5001344042d00d420342c0000c1c4c03180403a00600040c0540850f1140d12640100600c106100010307100c8100000b601c02c0d00740154100c2c400b1020584214204110068454042d200489034080c004241e640d0803d0208500310340c6401081302140714080b080c401d1a501401414401e81c0c441d14001400c00c01d03403003490700704100489219034050818004104c41d100312075404400803901d0003244100d0841e4030048000d0b0280e081c004a62850401c14001c1101065003d17500030024281140d000414007010100f04c43d090b4494940c144006000400440d0042200b9541c082900e00d08803842e20b0352503543d00d0403604540c0000000544a0784240f0843c1045807000001ccc01071420300054640003100040c1804400d040030301c4101c04100500241d10203450844418192480 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 681107751 1250 681106501 681106537
    0x1006140f040320040e0606130b15130b1c0f021c060f080703021302030703090f120210060b0a0309060204090603050c090c030c0a0806130c0e01080a0e0a030c08 70
    0x704000c1d510100114040200e4480c4403e152098640342c81400c0740d18490354003405942ea40c44041004102d503800040310030300d8a829a00740c0c1c0b42d031196a9003500074580e0440c07940301d03031030649204400302042d00300e40940c1108001c0d281d222407084103120b0380c03145030300000305050303143c0d03038204029000d85045c8500d2001c2d00602010000d11f0f0742c00c0740060f20007800440d4210380e40c7c2c074200c969400c00382c80041e4002c0380f1340104c0d902d200c0560b0010360b4000d01a04011600f0101ea9071603998001c0c04410030703030b480c040d4036200541031641440910340401028409111030303400c2403e10b8459101e10348040701816929026038081069940560f001858003000402c511030b40c0e82045030302d95503170160881c829085000000c0c88070f1681c2c0b0540707008490007500e29082081110040e58051009400c0700d90081040b03010f582480d007a4020060b0f0501c0a5592080d0b143c91000094250200900785030305260520b1102c0c01c070400300103000582d0681503d0f1000034100581001c2e405880b5446080c600308060b0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 681109001 1250 681107751 681107753
    0x30c0b010803030414060723090306010b0a021b061209010b03060a0603020406090c050304121101021b19020102100f1b0509031203090a020f030f0610060f02061006140f0403 76
    0x200140d4481ea0240302c03005c00520342071000325180c3c84116a4040420940c0800c038000149140c01140807800c5401420300d8203410324002450a1400d074007a4064407000a0004401c1e54144056200d40c0302c803a020b445000c0020002514a002e440211342d081c581c0e10f800209904c00c25004032815001c040c0c01c0d078005050a19a04000d8100c03404181d0003181410030008104c5140d124014658800f50364040c2986c03525550b030011240c41d01100410400c0c0705d02e03508030810082c0f00400410901154035070140110642c2907051020307519825940da88566070401c0542d0f00441c00d50790810004400041d080e0300303440346c84010b05135544080c02d41a6030314089040c054101005060794102141180c0c0c03909840d507040704241c401152540042d820100903140141000f0540c0b202028000b410f803148000d04000c0c880c580902140c204809607a849400c124031900007404504c0c04100b84003030150f40c0b4055006400164052140e8020481200c1d1149460318000c0152101540e00310f2002d55120ba60b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 681110251 1250 681109001 681109003
    0x103080301090e06010506090d080708040f032f0f03160f081501141c0209040c1a070308011203110607050409052d0a060807030501140c070201080c0304030c0b0108 72
    0x424082c004080d460824040407442d0006200ca04894000341030a02e800c14603c10301007454018801100d0003c07042c0811000901450040d01c06407015181207803416203103090140b00641c034880c05050003060390582d184201d0301200c0a03c01c8544c103413410b01d0080750b0100880d1600d039822a2495440118500200d090038100e40c04104452002045035036015074000c5681074400e0a200e00000122089091451800d2a00903d00644d1054016801200755900840e4000b0740840b8215400c94460400740020400e0349030900046086640080c02d01c000d039035000e840c4050600804250300c1d4020101c5e01010303c107034055006802c07030300d0568135203003000c0d480a80907400c640200040c55080c00009000d005150000c0c1d01c808500340d8241c41c021039801c0640c070089001911074410552a103c0216034207c041003000010341c4201c00000d0302210310f0400392091400640300c40c410150410582025070b03440403e894001070b16403c010394a0701c0f10300c3c05a907a03100c0404014440203d8500010b00101c0c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 681111501 1250 681110251 681110257
    0x40c020f0c03160e100e2503020a090e04060908070b0702010c0f050a08070e03010e0a0b131a0a09050105040308070e0a1a0904060f0f030212030301060203040501081905010308 77
    0xc00840e038040752180c0805480300c0994160724411203540d4002c0142c000f110102079003081600100c69206a141c1142120520040340c0790700d109225582d11101c0d0f80340300012011640258601107007801545840203100015500c20303600c048002802180c14454143e0182030701c241d000e2505980d80300380b03207081440d245080311600e0141d4600101100000c0c014504e0071807180040d500c0c1480d007904102d080c4c0e110080a4040720802a4034507583c881618244510000180658003c01c810f00007031400b030842e100014840d01c5000ea0404400380014842c0c001ca178180707060316841c900c1c95500d001425004001203100540158200380c1230005040d00708031100c0c0a4003980ea0303854052128907040c0f051001407481040040342080d1042410741c400d44c409440500c500400201d040d07a0395021200c1014407a8201c6544015900d408008520f4042a1185800d84910180d811581b403c10301a45901807441520b045c030a1000011340b0400c18071647da071030348465400c104001d5850b0b04103c003040d0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 681112751 1250 681111501 681111523
    0x1206121103070f0e0c030a0b0d0804080d05070c0605071b1509050907081b09060f0301090c091224050a05070e191707030b0703090201020712051e0705040c02 69
    0xc0950a0007091a0380760752401004d840e641000316001e512070440304038155000070301c04008641d03109200708103079803141307130485009014201840d121070a04040d1824482140a00b10a02408006c48000a104541004120303079842c00c00c151100210b0503e208031502c400750301317086128005400309807401591030781c0f0000740071380c1e403103d086584440034411000420b42d107002c04905540000f5060351031841d03510022a4003400c40505000b81c03000892401d411115130441426804001172280c49128819010300149501d003e070011b500d40072640040780903a0502401d80d14618070f001c0d000c031503c2207140b806c03020504004c20aa140140d841002001d007564028000390078405060b07040d140403072803404c2e21b100e102240744d03202d4900b140d01c0e10001c0c110204103686005030741000011440f6406041d10034092918082800b00d03980c030009040000340d4101003041301e03168868801140e80010661081488040c502c00c1c0013500148291521443e54011980182443d041000d41035012171100807003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 681114001 1250 681112751 681112753
    0xb0303041815031e031e021b2218080406030c080c18120109140703050c1e040b0f040507030f050615070b040813030c1d0709061206121103 61
    0x340d040e050b44440310303040c503110241840120141d20f4001c54805035048800d18424207244948148580c00400034444c031a8521000d60000710119a541c001c0079440c001c2d106c0200c0d080f074042c0d0ba0700d24a07003030303015000b6a4451001e40d0310400190044000390707001c1c039980d03008200c441d251035031810000c1c0501804800000018012000701d1410785d601c400b03888008030121401139024082c2d00c280100d401e840c500031002592100503a00100e81039980a0f202c02082d20080d048031400d600300320307180900d4920b010f4003034000c4410440803c180c075040c600c103035902107a0100749010f0039000140039414407500240d00910304010b00869540592007000c28030030088007445151382d200104001d0f440c0034035004440d08410441d1000149240744034583c402c0c4548085420640802848003c0b00350b260000c40c2c60580c0f2410601c0945841001c0107a105180030001080e4601a08001c02907100e504c00d00e004d104400700028404602ea4211001420b644100e4100490f554100200e1440e03112030100c0c02 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 681115107 1106 681114001 681114011
    0x100507020109090e0a0201021b0303030a050702030c070603050627010302090403050d051509180d21051303140309070608040204111602090112020a03080a030b03030418 74
    0x100c00302140003030170300808070310001e4a0501c0c00d40414542c1020007a21a0840c1d400004607681704aa0a03000f01d01601c44034010f9195000d074481550040c020464041000303507140d4007040c4940780c1107440d900e510241d041101c100b042d50b42031400c1040c0000e0014400b50600c0c206039504103100b8a40585007040a5500b0380442d1030176a080c420850020301500b80a01e003241180b900300e0344031004100410038007121241e40b0a1b102849009019110858040341aa603a4a010018800303541c2405180b0380b0400341030171296124030031008550b0b03c0810171350104048007502d226140d508000c0812905010b0140c0b046140113200720703030181d110600380401c0c20082c4094580d988207a03034504040b0a542c4104601d40074140c00014003d040000001c0143c1d0301c0110b40021a6004400b0076034070080d401e8114050882000003076017511002400043e85c1c900242c1c0039035900840c00041203 = true := by decide +kernel

theorem cover : BRFrame.Cov 680935251 681115107 := by
  have h0 := BRFrame.cov_init 680935251
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680935251 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 680935251 ≤ n) (h2 : n < 681115107) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
