-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3835
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:49:05.615107+00:00
-- url     : https://prove2.me/submissions/5528f224-5a24-473a-a34b-b5202a13f1f0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 689568345 ≤ n < 689748201 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 689569595 1250 689568345 689568353
    0x1502060108070317180a03051b031b010c02060705120a1d03061512010908030f060d05030304030507081615050106171807051026040803042a09020304170304 69
    0x4400b04014613619070b403005001003d5905200396180c05421140d010804002c0010203d01c4054a01803205608004d0030707480205036a4100d82002042e88000110000242e03500c186103120341c1c280041c01003450101159250b51902140400c036440c4035001041404010745c0c450705803640c403458115585074101c80680080e440c0c0e2005401c0b9403002403010710021a03500d400d889000c00d04403003002000f03903100c03500340040d0035881140c1c0c81c072103941d9550014455150600c1d86014142d08100250300f16a0359540907140c60f1700c40401074030164000c0c0702819801403c1c02c0740d5001c0300e2003074401c0f5120b0032400c40c25100b41d4406800100034051441070301c0c41614043e1703000a5119555010709000c5211440401e41412030540145800085400455000a402804003207242074000040b2600b40e150f04026480c0000076100205010000c1021502150080300200d54411140e103418150176600c6982c4400d201c020740c00b4850b031035008020403043c08100041c9145110191001070324610302551 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 689570845 1250 689569595 689569613
    0x91203050a0f0f0218040603080f0c070e010b0918010501050702060708192d0c080a111c110c060726070f05010c4515020601080703 58
    0x14140805a544001586002003030300402d980c0031034900708000c0904031210010107940400000741500b441109680b03218140703071145108030783c0c12440c2c4a060400322140404554011004024075201d08074012036a40460752040340200900d040d42551106110244454190003541030b1807a4280000100102c1c3d81040031078146950403556280d9444035440c002e20030340649a641c08144500313102c610251761b0401c480b44a10360b0f8010a854158021103410118414482d80c1c070760002d4040303103c9200090b1010050021084c550901c80c10b0321b540b00401a14011581d114610840c81040440c0500d9030401e680108120022000c2d00c040c288901c00324115100f0560f00903d83c084481c0405031803042c85100840500c898140943d58005c2c0e030400d840300b00048071042c4c9555190580400900b070042c0e603441e1001e03840030455284802c1e00c0820400640c81280101940d102c104d045203003640341c0d0600d10b000307082c032028207003a85c018801000740b80c010305070081d0010741e12840f0b007480461100c2d2 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 689572095 1250 689570845 689570873
    0xa0909060b040902150a0c120e150a020d080910050a0c0f1d1012050c090f031b0402090a1701050901150803030115050403060c02060f0c181c080c0601060806010309 72
    0x800c5d0070f652005000f000b160030405118000c2c03c034440500c08000032990104030790100100c1290558865284c05c154481144510204078000d640101c034990050383c0203c52196000b00000d00b5981034514031140d100550707038112024140241d41382c0040700e81c585c1100c0b0110694403d850309031b220322103400384685510608030f4000d100e0b20344215860300c0c40b4031a0900c3d0001e400403400a0025040880080d213590700b00f0652148a040006040a040d080000320307c5210004a0340c0360314036441a10030b0000952044051756081a80c9035008620308800c4040e40c0311060310036000160b60310748090301500710eca0b00401c1050911506008200b0000d002068a0644045a1000c500b86581c8007082e10648074036400141082d080030003880343d4540104900d0310407d0128218540d0356110b40032141c00d4400e1844100c5c54a40c192865081410910440724000f1518509001e0b20401ca07102e18a090f0011b00345800103900c600014444560702943e015006032081c2420f0200d40d500d5941c4050200d61a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 689573345 1250 689572095 689572129
    0x90c031506061b0c1e030203010f05090c040b13090c0e0714030a0f0902120a1202160909020a270e060f040b090c190f21200a0909060b040902 62
    0xd4803c12007400b0020000c00018684803040c0d0004c07900d200240300c1021040c0c441644a03510b4a0418480703d102400b60911400003c406000000701d92010000141442c000481d0010040303090802c2802451051560841c040d00d0451901490b01c0003807007020100400c150108107001039a000001442d40030f40380c000f10380c400081041d24510070140000c08120001960142402000d188000e0700813480c1d036055030040c514030a031031410500a980c1d80350303e4485d1005600c3c625108100b0340340b40341d00c454605440201807500440d03885c0c1d42003600d10880c04601c102d442400000c4c50700c00c00030b4401e0004805200000e407295150040c481c02c104040104007401c110841c200144585a09100e40054848001c0c0514120036a5401d04610b24450740541070103142811804501e142c1402003145101204001004600c07085a54510402540b120b007030000c9012102c40c100c4030342d54140c001c0013511003850b000484561070f0070520241ca011304d1030079010f985400d5056025840d4a0f240c070301c480c189 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 689574595 1250 689573345 689573387
    0x90f020f040b1c02040902070501050a14180111040b04060f26061309080405041112041106070503070534060503130b09010e0f0601060e10050904090c03150606 70
    0xb0f04128156407840840078031001480014041004411980500001402a0000c200316500c01c08298200c4418010301c03044000d400b4001000c21148000c0041c2c400383c80f10011410400100b00c50b80d00360400e80000451403030100381400801c0d4800000c074480402c0780b0f0711004c00411031444c21980c401440840040b0160f01000503580d444070a59119914010981003100c00100d0604100d10340041c02014422424490300180410b44401a51454094892005044e4540340d456020409105c031020b60040010300020021400600103030907424050700240034100807510010080c04900c0e4840c259007034104d400e604081e5100c60f00481950054100980d60303455203c0c1c00603181c10200e03c01405080c46400300b00c0f80c090107400680c09000d044044481c2c4a42c090405034441e142409001c0010703004200a010b140382a400440d036909040c04c01d82d10303100c035800209080d42d80846060301c4070f0401040c20410028800983c1d12450490071302002417074102017000300b05281705590580d540d80 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 689575845 1250 689574595 689574607
    0x190c1716060513030b130b07110c040b010c15020301140406060e0910180b040b01080403022e0608030a02070b16080d0b0d0b090606010513030305032509090f020f040b 73
    0x40203054403c065500690300603058034242c6044650101d8040f422120030f01d500010607400c5028030007810040811201404442d0b600c1c00c188001001c15200282c1007100601c00c1c4400701c2c1400300004160b440c01440540d686d810800011945040c5c4480070f400f9520b005410817803039901c004d24400b43c140499a919094481d09400d10304a40280c11050b5070711490071a001c103000c00c0b940103482d45441035405000c00e804106c0103640c00c203001c440117005070700509401c3d88900000443d000680840c050000081d28074500d0107011a03000303400c8460a40d00c0091100c03c403680401284004044000c0f5283c5851005148501c1140f10781e00001d0100e0008207140000004540000c1202000032309108500c4600c0d042840d00c40505440700c60079406410082a01765101c3c0e0200d80c0d100da44020800034141c91075404844c0e40d48020461803a0b045007910070854001004501c2c900146180e4400354100d05090701d440032203090513840040c00e0b10400c180300c40c00c1c5071081650101c0300c00d040c0c10394a80c2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 689577095 1250 689575845 689575867
    0x120f02130b040606020a020a090b01051c1112180f1002090604081c12050f07050f0d1b17150d030207030609030503010e1503120c190c17160605 63
    0x750741104640c03060800c040815025400200a05014000ca030031640700d55540b8121801c94042d18003043c0058070070042c0100c2c4600390003003a04145900c01e000900c44896072030300700c4150030140100342d454803032809028001458a128982205481000e48440b44607460110f94408420050100007174020880ba02c10b695084140c1c1c000300355601c241c41c0380d44034108040761451419048070000c20020707285080030101510030540305d4000041c4513002c07030f2200381c0b0642e0035810a003c452600d003030412480083d400700740a800105200358100c0035220400c0035001d8941d0307010000c2d528010700c60004221440710424081114001e0550f5000c0d01030091f41412406c00c11a031700301800070b508242c1050200341c1d01400035412180450030f41201c545032600030305007101c0b500005592580c4100d100318606402680100000b0465004584000302d451103040c01810005e90705451003442d002041240c9400d0724540401070400f18081c0404100f15403203c4180f060602a2408201d8013040c01c003105 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 689578345 1250 689577095 689577101
    0xc0f030b0a08060c040e0906041a06040207061b02011b17090a080309150105040c020d0e01030e0d110d0912120306031a070906020712020904050a0b0403020a0606120f0213 75
    0x10740708060a83e00e00c1d10f0711300304824059000d889224000341c0c0d68400200185804103c060103140d21071082a40041054000c2c0c000c0c9002400c2e040d84541c2c00c0000b00002090f9106d54060041952880141688401000303400c41e68080c1d0584144043c10041c0300d01c05500c03800600804050441840302030b2070307840f040c503e0256100c00c01401c010000003031151004e00010f000c1441703140303000003890fa80c0c8c0745e10910099031801480361002d0b03441183e020343c00c5400362421910132841032500240448825103214901080c0b680d003a00481e1500809446808041c4508072600d00641060040c603850040360721406001c444010342081ca80c984650f07041482030b00900000d54021000510794070340e4140c0480100b006503103150100c1c4440300000b4541c0e002252440844400e100c4044000101ea028000d000710000c1080382e480c060000d4000c00149040c0d0400e004078060741c018001d165252030186c0c2211140e8002110710311022800c1c5000800700c140d1503c2880d41555000807401c0804050001b07 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 689579595 1250 689578345 689578349
    0x606230d1a2505040510053604050f091903030f020a0f0f020d0e04110f070b1b13060e040902180907090b090121080a05070b09010c0f030b0a 62
    0x5100741d1882402032403007203001c0e04a00d032503051409141849040105454522440c0710703041d00105a905c140c2100340c080d81c050301c030b001c44102c00b50380b46141745601410341510f800b07040b00032004000200d950b10b062501c28294004108403444183d070510724401541d8180d0103420002ca414404028010940f00340c00c000110840f0304025521803003c0880507010344501480c090010b440706c040d00204501c001030300c48480d200d5880d4139400740e4800f0b05010151039014a031102191007000280202c0110500401040b401041030240034140004d4001503041810000c0444440900074030b00704130304020703400040740c0160601040014849005c00c000d0b0481d108081e51003002155600b0102c40d100801500c1a556401981d28080e1a00119000c031111601c1e42c03070704421032000521920300817070300c80c041c40c0c003080004441601a40d503581c002c0b0b81c4001c0c18200080e101045800800c03041364811504031000c0402400002c9515800404000302c101c08007040544822001e01203480741004440 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 689580845 1250 689579595 689579633
    0x1d03070302091b03251b1106040515180d03080606130b030f01090c020109051e0708251211040b04060b04080105040b10051f021f090606230d 62
    0x144900e00507401d0115520403003124180681c50600c1c0410f6031344034001032840030340020301c04a0104c9940c7c0314003841c07020354120309030048000c02021503a640c6a4500c161711a5180322003a54600c50444e1182001e400c5454003030240c440a098440040c1d00025800e51044050300c02586800d210091401481300f15480101c2100c800014024140e180108243c161013003007006010315080325004030300300c42148074040c00d2500310300840504d855030308641003040f40131002111013041d12103081703a04000b41180c0c5000120f0040c40340b00c001c0d07522460448002d02c03507040401007008081d1101b40d4000c04191a0394422907446003c003210381e03a00c0d4400000340464094140d20b5680741c40100f8000c040684095a46116480001d01ea1903011011403047c0c44019000b03801c0d40c40304010341300e000707041000d0440c1580682800c10803401079024081480c40030b96000440d0b28009401c00300c04403007154100745034101d1030321040700c0b85035078a1b002d00790716040a4640109610941c00e01e03202003041d006a201c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 689582095 1250 689580845 689580847
    0xf0a020109022e0305040227040308060307061704060915020d060506040f1a0d2a0e0a0b0702030f0709061a0a0e040c02190b071d03070302091b 63
    0x4511950551096800034403e541e00d2500110034920500200341c080305142000c4046440c4a4000d84280c00c620f80061020309030b580341403140300b01c243c031100c00901c0e4800403c0d0024108020b0503840f50f01d080e001201039010b80170440c10048018406140001505080802c21010500304103181e840401e071181c001c420804034090f28200361000c0d50000e240f00f1030003818000d0221703451030250116004c84801224403802c1610b0000c1011031440d0003001144004814405a4104107207402103c1003107124114130034080040a103034040340c0e800000d100d02004801c0098280b191103050110099580a00400b602d81d0312502c0000d02d05032071020b4480341c6005a41002500351401e80222013501c1d60310501ca03030350190060f4282410700455400b40001079402240d803510b424103910101500041c5c2c8192280d6100c0b130345120f1300d050140d170400c9856400040c200002c45a0041701108201a50310f00300c00001200340000b035444200f40030191050042e0f1001c5074241e801c003031030284041e80000c946 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 689583345 1250 689582095 689582107
    0x1d01030f021804120f03060f03030807050c0105070905152703010905070801271101080411100e01020115030302071707050307120512250501021b24070804060f020f 72
    0x2103e881c280e9071344408080b0392202e510700102c4c5d001e4040d420a98910081d50308205203152401c40f140d6a01412160034041c040001b643e400402b030003400d02c00c00d29074940401c800d282c135081c00301c503d001421441c95000c0c1400b150354806440d146202100c1c0103a007400300b64610610004e1300510105e00e0007050fa104e0020001100c40c419040718001c8600084134010b100111100340b610010340c2c00740140460301e80440c0814035802490303100d801901034030701440d400c1c0741d440102c0c0032880300c945604003185070402202c901f076074240903804c10340c2c40d40c8100d240d68a1556401a54410035401510041562500701c0c0802d40d03010402c02c40180700050889076895581c08981d0040f45d01100151418060a0400107080008408503207030801c1000300c0c3d0f0401920300d01001d254211540049903955020428481421a5042e1044820150380c000d40102202c0c520143d0b4039984c81421600b269000c0c0c0c1c100403038517130001000d41d481500010042129040326850b03200030711a039050031048074408249 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 689584595 1250 689583345 689583353
    0x3071409040c020f101b0507061413021f02031c0f050c0d0f0b0a1e03060c0905030f0a080a05030702010905030706020301170c13020c1516091d01030f021804 69
    0xa020300160ba1441617501200e1406504020303208125002d61100d03040da03c810010a100300002c2c020680500ba0001e2010214500c40d081c0740ca0503a00968071012030f152900c19881c200b11810030702013450300f035914102c0401d80d0203901d07801030f580807503000b40c1200c0f003010041801d42c01256940b0780224003089a440e00c00940291a0041e00b03064010074545213901500f283c140c4164001100000c07c19003440d440c1034002030450488100e1181d41c1941c5000020000d01640600c0c0542841f03500c3e4024020708000a06207440700303038524040c02e94011109034001ca00c295084584011040c540180d03603603a8006e0507809000f551000503c140300002e4050f0500c081680550b0603a903c2c5604103031006080d114a43d507a04503009110781c0003040742403000c0c0800403607008110342d00301c040a8407807070b0842403241a4103d06c01c0301c1140100e004000c41c81e10503a40031070708101030b005005005170b4220706100728281a00c0305000040c002c03030100a0200540d0b4851030f1350310108940e507003171846502e01498 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 689585845 1250 689584595 689584603
    0x60e09070501140d09020619110a0c171c020c0102011416030e280b0603060f060103200d09060c0c082b02070c031230020c070902070209010e060603071409040c02 71
    0x8181c0c0c001403103401c0aa01503009c0440d00c5400355400003031048129003000c0c80e028842c07407022040e504e1441110300014990107000d17002c81910690741c00ac0c0075001030701c0c40064255519041e46100e0030030f050f820800303d0000d41d0006112085e0501d00002c00d00a9604100e1620000c140b400e807007000307008001c402e462540b070709007560b151103001103074500d80300c80050542d598400d82d0b150400282d00c20014040c1e502c654000c0c039994070b501407008040400c0c0c04003082c2d96840500440300350713a104d58550b001c1c0001c03809a800c45a10030b18191481641e1911008001e0107500c147d44ca084220001c02c101803816421ba05516841c0c4040855a401a030310f090b01c96004907110881d40f8200709004018480d0044842d0751984c04200400140c3e54501c5101d06805038454680d0010715600780210f2540040801501010b000381c0c080041e03644040d03004201312490142d002c0424210341108000040e1a20010707a50460320a09001322840140c1d100044103020300c04110f60010f10b400302c5000c182d54009 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 689587095 1250 689585845 689585887
    0x2040e06091006050904020f0d0201090932010e010b0f0906030a0207051002040620070f0f0f14010f03200d06051c0507031b0e0703060e09070501140d090206 69
    0x84100030742c3d84c0c3c9205100c5a12021140a5800320480d9411070090502c000e42c0c0e18418030501d041c0c0701036501d8a650104a481344107a00302d4001c008880811031540e840c95130300e0360740c034050a503004c158076081042244050500500000e81d10108180748182480c2090703560000c130040000b602c1c2e14001e01c81d00c1c000d4110505c02e1311280300784a0244080c4403180708440c1a51384070f95840b0318102d00c54000445500801500355160320450034005000c5282245481c0681512070340d80c0c01c01403812545417007d00140d08541340d010b0404c040f040d50380c0c0e08980ca41c0c9030000765007401b140d050894174440d287c005041c400909c01910000313070128124119400302c01500c000b12171281c100d0115600072290440401c00080155201403002d00c040340504030706040001c12200360026560300d84410581d01c0e003085d5240808244c4800f400d1124107240895154001c080c1001420000c0c0f0f010002401003000ca030040e840000c000905000000d42500720858064014080c1039a8040d14060300403107018034 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 689588345 1250 689587095 689587123
    0xb061504091a1009141504050405010603021c051e0702010b041a012c09061210020a0f0e0123090604030b0a11040e22061a09011a04090902040e0609 65
    0x3c0001410720900486201d425181260880b1445260860500982040314540d550709190207201c0042c450752907015050181a20303940241c4c580007840182070a0000031066602d005041004124518404074130035141c54900300c840320358139290a90180e00400310000000d800c0b508143d6422a09035410114032a000d1081c3d031040344c04c00d01056940c100e1020740d10074124240720f2020501140c03401c8401c0e580c100342c005003d0140c030a1940300c0304c1c4c03425030302d03868503010241c003c290301d60310030740200501001700ca050800580710300c2c0020000f04504606805009480c1480d1500a0030f2005d00b0155044006d0103860107a0721070301c0b810074612100086078030022082c104450000420b14040c01c0e03a0031501480038000c00394030b036001c408000c0d0014603c403450300000011083c01040050050140d09001500150301081c03042040c01100c8805030000d0200c3d020400000d42c1042804080341c0494110050001b0100742030b10000b80034180343d0800381c003a0b100705402d015001c400810501d640e0451 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 689589595 1250 689588345 689588359
    0x90b0403020601081b0d06110d2304020616141015050303070c030609050c0904060507080901020a0207091802150c01050105031501030201030b0111061005120a0b061504091a 76
    0xe144c0800d42c0c0c0720208007a030f20054a03035241e1003500d03040c8174220010440c802c034008140c0385240e0004000c50b41204001d010780b15100c40f1117410030030540078101d115110f803c001405030b00d42030300822480d00c2a061042003100002440001384412040101003850801040d61020f5100094242c09004c1c4c2c182c604c2120106030350005814580081103030303440b980c0082a00511403942e00e42c4802400d0380c4005444a0185100004207a610a009030b44071314031800002901b401d0000f0000d100c004018820109a071041080c0140340da00011404200e504501e804202e08001c0d12003054003008100c002034025040d00960400011064043c140050a000003004641eaa50082503916980c081d00c01003083c0545005001552003034000100908040c140035a111102520703180c50306000f1140102c3c9408080014405031a00300d031003041500b00b09004003981da45075214208100303800f0304000c4c0700c1d400d80134910b0821001c602c261b600078180300c8010810002c0c81c5000606140b01480381031300c0303424 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 689590845 1250 689589595 689589599
    0x106050f0702041d0114010e0f0115050903070b040305010506090609012c0a0603030216030807300e0109090b1e18010e0f070503040b0f1806040f03030b03030c0c011d04090b0403020601 81
    0x601c0c803a48d030302c034001012160800307920f00082075501041c603c24101c200101081f8820301601c080103150010304e40c0840442e5100c2c5581805421a5000f130420751103526120140005540c2d0b03e42c0242c1507a4861042d04010681c0000a1603025103c0002c43d4031040080c080100021065100c241120700a03020764101007008585010b0001d640d0000600c40c032401e10a00022400703c502c880440803110850a03403100764040d0710a080d071502c040e2000015040b42800c111755a00151440080001100a01071005543c00060b910701c4100d17450074540c90226a00b03401c0755920303484802049000b80b001d00035543c43d061030380c8140600703c4079141000355400c04140e1441c480c4085902c1603812080401c56903c60340b0b90418500c201038070071861002a00101d0620003800c0c42303070900451164808600d903401c180742c080c2c180c41c094000c0e01d1203600203200e001b40c481800305000700d0b409001d10f0894810042c5880074000c008540e29203d80043ca00040c440800442c1c01e0000e0045001b9001c90b0b8241c3e03 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 689592095 1250 689590845 689590859
    0x90b01030203190807060f2c120a02120304081201150801060e0105120411131a1005040b03042f04360501140c0d0b010203030106050f0702041d011401 66
    0x18001e00310013014400d04100e641c011500585c010444800700400104181e1035544000b800f507844c0900000f452035050242c00140d21042001d01c2c03581013251203d40c204410000080c2d01e8046400c544502c60400000040800040d481180e01c0d08100001c280704c5561680c40030b9107441c80d00c000030740202d00c400e80045030f56806201c0344000910140e40340c51500780007049164400201800446640030b0580e407400c000c1d0365001c5562b101d208048800a0079040d5140d0600011050a001501500304608890300e0680c1c008129800e955001c0e803810b41da9103d614001c00300b44c906006100584107128038450540c084c080700a601c00c0300859050241850b14403001c4c246044901401d0010351101c40c00c01e910100784441504000e00032000003c0301400240802d8005004941c50202c02800103040581464584a2581031110070700c0114115070401d8405000707441494403045400c003000c6110000c41d6541d401994490605003a5180c4070003800811038003800022104880080c00d40700081001 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 689593345 1250 689592095 689592133
    0x160c0f0905060a030f140d0201020c0c0604060807080c0708040b0414040605090601030903050c0a0302060103150203041505190c030225050d03020913050112021005121504020c01090b01030203 84
    0x24070006040c00f0080e8555528909010940002200d101030171031101d04d04040244803140701c5034100e4002581d00d2100e82c4800f410700306040300f10391003018280020311a0b40e5101807840d0303001810b0f041c802103549400311601c4c210b003d9490000c000d82c5000030003280b1078906070003034012250702d0200300c2c81040700a020441500c2c0240030b203582121f007150010301107601c02d41150350124000c1c20034a00c2d0500301c04180e03080c050003070f0b019070143e403021004100300904252628262280302c0c60031800e40c18160340d440441600c5010010b0340e29200c07400b02d54004103a054050310310300411410030210b909094081c3c06900302002c01200ea9201180d20341c024241d502c0c125a40c0707503021000d000d92010380c0070203400130b401c80c10111b50880d406400090021701e040c41018041e20341c0140c00404c0307030340610400c41c00c91703a55030b0414204941803021004e0390240c0003049402503621a040b0040f540500c0100c0d0080c01084001c010642c00c01d03080a0a2254201125045e01c0c029400ea03034500000301010307500 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 689594595 1250 689593345 689593351
    0x11406120703170a0e37350f030a0c080405040f050708070f090e070c0b0403031b0912030e01300605060a1d030115080c030c04051e0903160c0f0905 65
    0x506c00b0400700c112980500070840c42a4002d40c020422602c640701e644030aa40c01c07545002043d05a981f1041c5520321101460b1580d11100344001003907041c040e60b1030b10740c90f030042c0c040707203010b1118004000041116800aa038007801d0054801c002540f8469800805800103944000100300c008001c2040305100e245109404540d0b612603000f400c1c41c000642c002d82200811403c1005001320401c0000788841c1e500900075070107550b0100341c2000d81001d005089083c3d003285014001840300400142141c201081d01d16509418211030700300520006a9501ca205141c0400d407801c40480c2c1080c0000a5a03040001401c80c14100413164449003404400e1158100c10800301d00541620240e00d08840c1410025000c050004290b0206660076620b00c200d00d508481410340100811700c1d280e040400108090380800c5a041c451401c2110581098001c40c4243d40b8450801e07400013041c0940c2041226540c40301e6110700ca08a11980c140b100c07003001c55006140b00c07841d0841f000504460075003d01c0d80 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 689595845 1250 689594595 689594629
    0x6120304121103013305240c010b04021308070512190f08030403030c120c080105101107170607030c02030d0c12061404060602011406120703170a0e 65
    0x81c80078894036080d10001c00301820b00c0d807541d00c401420a0800c29907510180344000d80242582d425101c072030030241c840f0250001130003640c4100390320307000d0360085404120920f000c0500540e201d0b4089450f502410f141c00c0d4494100d0300028032005840101100c0204907400c80081d60170654440c0c04104610f0304c0442019450361280c484801d01e000d000c00c0c1c0211840c0b03c0d816007000a942503480103400e4000700c50980100303541c0d5181c580b0f4507401040000042c03a4140007003000071030309040a0006a0107008060240381c01e41041c10125004050010418113440200d0f0302e03e0396110385a440e480040d9100c03107101e00921012070081d81c02030050001e4031803260007440c2007940e030914101c0107001c2c00180a04100300000148500c08142c851807014080100d1803181e11212030092109403030061780040216890304104084684208070741c5074011000712a459944081d90002601d42042500b018100030842884c1040b041d800c17000030840c4412540b60703c2004c80255040004603500010540 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 689597095 1250 689595845 689595869
    0x9080307080601050705010f0518031e0a14040306020405010e030f07050108070c0b0906180a0809090a15080d080a090f170d060305010608060606030720010f0e0606120304 75
    0xc15440c040c0d50042d60004040c905035041100da03850b901e0941e208240c1d90281d42c0d98500910191101c102c10318245445103100551904d820039001c1c8008071505c80440c0c449031004544816243e10070a10700d0f01c86d28020703258940703480c0c40c2d0400900962091250b1408034100e04900811800e010544045c2e0328480c0016001d068580070064440441c010080c1081040108400000034110481503000f00c41c5070000f0021440c0080320b514050a00d182e0001d1b0035400b48000000241c11070b811036158020030754074003045403148200c9174040c0080c10003807010264800c0c404603140d0300c00510820072035182d0f6190455511541804ca04a8149076405807200b094952a0703000f00e40031882c14941c0c0d921500f4580d140030880d9100341d040761500d800840b69a5100d40c020012000100049904458101c48084c950f050807403003e00000c04c441e00d201c3d9501c0700c1c4c1019803c065801e62003000524103c5006004203101024090b0700d50b402110760701d101e18100114980419000825502030351034020400d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 689598345 1250 689597095 689597101
    0x1509040c12080d05162c0105130b041d1e0705070c09060b0705071509050d050a020d15050a1a010c0c0f0305011d06160806040b0d0c0513090803 63
    0x80c407a0000c04200695106200b0403622440d0b40c0381e03110741ca20990320740341c0340081c0e10303540b08000b80981c0c10003c1600810140c0c0c5071030020f48003005003031100540d003420f2580c0d4031044410316000550711a48401107103900410001024207410950182d4010103072845845641c51900c3c0045400c0c01c111000c2204d90130000160b41180104010314103a8020b41e10030384040e9503840b00205482254000a00361140451840708202080108801400116020500902c41e102e80201868440c3c03103164407072907150f807001007444024083c4145064000d03003849442c02a505006401c1c1e2204408854190b14100000d5074003025031060b0702c58001c400c54500000b250309801164a6031007a0741c03e840d640030030800018214910340d1001c000318803480000c5860208a0510182426420390b400e825400c90003c0050080f928810350200c0d80190400284070384642e0041070003040f1000c0401d4000034141051014812040b8005007200c41c01c80c0c1201205103150f5000b000d560480000800c082814004 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 689599595 1250 689598345 689598359
    0x40b03060d231c0e0d032d031509090b040b09121b0c122a030a051c0504060806130905190506060d0b1605090402121509040c 55
    0x40a20a00407200800380a040100d600d6107080841110002688040e001036002c1400800e070b00244012411300c40c3c2641d218030302281c00704014210041c200441c882800c00c000c0034691142d0050407507088000c00d60a01c3e20006001002c4035031850004012402c00041d80803024024421440e50001da14400c60700d03155240c100100016020b07400e5801004014440c03919024050070300481c0e585c8060340c0b40d52041d95920b0500c464102028007032105411240c03410680003071100150503011403802c07030040e0340034020100c006010707a0090703243c014816004103000000401c081c100d5405508221180a00303a0281e810b0305c564818100829202400140b0900c1e06603500043c2c201c0e010740c00b10f003c6c000e940c1c5050401303804510514020000303401c020700f802820003e00d54400c40c10788030301d130a00c103075919171400d2960000d000d600d46800c000c4940385c45510403c2680c616030750241041d51591038107a00d002c680c15044660342c80e41086500041c0103460450b2516001e2a0400c02884c895800e0180d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 689600845 1250 689599595 689599609
    0x9062e02032709060306090618070f0b0a080109050105010c0201030b0f06041206052a0c0a1205220605091212040e06090703050405060a18020409051c05040b0306 71
    0x128095000511038111003844000c10081980e00c001401d062008079001001049074003e40716a020f640310400f00000f210000035582d80004100d45c030412225030080f8034a00d001aa50010746000c0b0910600041c4a1440005895940764507121140e05030b8a40d1801001ca0723809100b0f450014030081841c0f030155009a20851300200060302020044031100041205548194414a2441c0144070040e06014130391007900c0d0408070080040e01d900c2d000410002107a14101003102c4a2800080c600c00e886104209014000b584250030480700199030602410582000031018525411282c103002c0390b0550510440a032505500c070b241c00e08954406005404c1c005081c44860b03442281c0301080800d02010141009081052115101d032406100340130000034050012000d060420f0148030001b03202291075903122002d00c0001800d082c000a025902d284c110701c02030341103032030300201105002010404270b0b0040000c042c0100000c8288800b291544600c3c03050b042d803840f09102142107071800807 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 689602095 1250 689600845 689600929
    0xf06060d08071a18060103050d03050a091a06010306050d17070c120501150503010b0d12050702270106050703090e100306020c15060f0a03060c020313090b0906 70
    0xd4010341002e15980e9540e80003103862100041c882d0041c000c0009860043d84551602188500a800c89501d0359a80a030750304801170549090586a00015502c200541e000084058000c0d0803190300d2009540c002c8041041510703190b001904200c4045910b080c00d0826a01c5154064060000200000c114554640082d8011500300c210602e0001c0c03400342818071a00c0d014020800020188411816540c9031001503028074000d9040c035051040b00d1f0f0b5074540c0d09082c603030000d4031140c90703041c0001c0446980c030503540d0080d030110701500c020b00004a24400c2c11003201d002002d0344c0f010398036440140c400c0c0c0a00d40005001070b4811100380006840b52204e02e410032007440d04510710310345943d5410b0583c0c2003001008442d0f404060340070340407005c002d01c1d80d4204100740c0e15803594540000101e1208000c0703000c00760055440d0b03a240c103200c6100308103c1d0a00140982d024444540b501840409000c009a031f141c41002c2a00c00b084213403501d68001c04a042e10303034003011307100fa02044801c92060a06 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 689603345 1250 689602095 689602103
    0xa020906011707091d070c03030e250510030e1b01020111040b1207030507020c010e03030405090f1905070f03091403131a040602190c082b020f06060d 66
    0x800440c4240500760651400b42d80316031183c00c426818221449661201c041d417103402d0070913450174000700030f0304014220780c060341620f00450200790a4006c1032034001c10000b90150480c5c0300d0702651181804044000943d00708890b11041c80301070354000ca0503180b08070b0701050310750080d811905444031000c983c000c031f0841c10700012a40000007104544a41c0047d442031286400002d903402c0d14110007101c40350301c035602e42410070003800d00b024000c1d0384104401c031941c14800ca0010885880e85d080090340d00400b03004241040d1841d08443c4160450342c240e4890a044c010400c8030b1140032200c1c05023901c0348646594290103501c1c2d550b400c074058042e601003510425184944492404820701c0180240c282581920b8003451401c21508402040210074a09140051000307101c2d02e9804034204c1504030040c80318413402620b50502908004069110942e28401d01205014484d405500300f50451039420480c101d500c0a00000d90304c81080f50040d0301e042e00800006005460450840308543d401 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 689604595 1250 689603345 689603357
    0xb0a0311062d070b060102010e100905031207020a150513081606090b01050315010510030507020f0318100e0907031107290903070c0e06010c0204180615080a02090601 73
    0x45181c2c0039030204031034141c0031002500081c508280700310542490b400110070700c002c00110080064640c3c6422410200343c940d43c2c1c4600440090003000c00990b410a41038440ea40c28500b45203201a6844003d0340302100c000d2600c488210811141d0300c9083c0c400c4003200310705030500c81266101d41d1140e02c0f030310414501504c030310310342c101081c0709100f05040b0610403000b5660550410b810186448085070002424420000050180713480d009800c803080d003154200030941d611140e400742c0c1403000145402d40c0c18440410740d4140c590041a05502c8100103840a022003802d80e8812605c42c0c500d210907a41003400300000c20001886a840842c86850641e245402c101855946000c1d0081d41036031000802d000951800160301411041a046050b10380103500c0e080c080c0d1781c0c082da00c01c030522a50420a80e0f607000100d00b030b4020942c13401341c83d0703004004000c50591800c0d031040200c0c180c01d040c0e9000f03240c054030101001c0000c050300151510f000041082c0c2c0696400c0002c0b503d0f008100c40d0400035 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 689605845 1250 689604595 689604637
    0x50904061d09070f030201050906031315051009020a0e01110115141005270303040522060501030b0a26070b0a030507030501060c0326090a03030b0a031106 68
    0x40c0c1d900140304548800c0700544400e00380078450601d0044243c00c8007026450444007040141c1e007000032560200c809480850b100c0e56010003420301410804809454900144076078030f40c58142e030380507500c28030f044000c0c0014640c0760011030b0100e0140300001808500c85201c801550b40c040c036242d0411036200400803460102400c64541020380340d6001c0c03d609443d54018106603d00081c60340e031000c016103045401c1a618111100c0c400c0340800304540021944d00d403210003914140b00700d90113001c000d040b0740020000f0390007040e40c1c107100084641c401c40c0b400354017040c55803190082c201c90040c01408404c4843c00c102c2e50341e002c0400c02040ea00f14022055148681d0081400309a00510103581401d40703c0700c640ca0301038183c031001400300301050700d018014031110350065480d08407150140b40141c0c51408101c4048079a560b00904860002e40035010440e10308800106491321600c039075002c2c81140340100c244a801101ea000090a200c03004c070179104c4600740040641154042800c0c5540018 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 689607095 1250 689605845 689605859
    0x6230402030a061a07050c0402070f020904141608010e0601081b03010603061515050f030103060506010c050a0b19052401050f07030c2001081f08060c031608090d05090406 75
    0x2c0b04020f44042c0c0c07040219400f0103100d000e200341c1b68503090239502035103003800568818607501542d41c40244070f071000b44041014042d17044e085e55007101c40501210010801c0a6140d01c25543d240f2502c4407075030800804440410b4045000e50407209010000d20700c0c25074045142110040311402d0941540d038484001021030080d020308140c00c103200c2e00c100949410603031045e81d0f5040c5114200103000082040b41029003182c0d04036811280c02400000c3c1c603440300c50048a486016100140152052207198410301c02103581c82c0d07018184202d400d41e0051142d80d50802a04e00032140d03c04100c80d0354002c8117001c9070781d90200580c003005142642c60080d0340c0303c032604660045030003640041d0740b1041040c1080100d0b040c1c0710030100851680c042d440c3c00312000134003801000304248030b2280314008440112403400407841c00340c400382c41601e0b807918146a109800e43c00880b02160340c811901540c82685000d24003d030302480c5118041c001c1c1403015041541d240c4d104541d059000ba03074581c1c00142c0c0c9 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 689608345 1250 689607095 689607119
    0x902030109180b07080a0b15030117060411090a0204030f050f0714010c0b10030b15041118010e0a15030e060609100e041b18110a090603050a090605090a050106230402030a06 76
    0x10f4809030041d0300c03541020bd66040c20741c0301c0103000450317600443c240004640215000303860214225441040ca58540800c50041e0240d640020880006d13810030301304100022901c4080341d007200d0216518503640300ca1405c032101100c8226030120758501380c4040411450281290302c0070400542c002001d50742c1c0d403070b100111310446485070009008024021307685030074000c900d50b5281c4c0440c01c41c2070105400c451380301e444007040341134103000c81100c040c0d2080e2a10100381000700510000c070340c603560341444054041c09004138004001d0144c8400244207142201049004a46d000310402840d4207240c00c14401607005801a580c07210040700c10000300b55411013180c080c24203000c24550010f00d00000c070b01650006210316010754001d2141b54071156000040703404803921841e010400b034540887d4080103010041014001d24105810420181c07000943d071a01d5521030402003014658826010517543c0c2a03c0c0d401142e00307031182c0e42c00e03260310701074028640050b40b100d40041c919545070055094 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 689609595 1250 689608345 689608369
    0xc0f05092b051501120b010b03091c0507150513080304060f050a0605030c011409011b0f05070501080c0a02060c1803060924010b09010c080708040902030109180b07080a0b 75
    0x1640d014a100089040850f0310007401030a46110b1960401c85c107581e45003450a050180761000300c0040300144100c041003111510002d1032840062019002d0a001011548048400d494410720451280300d100d070a4030955110301d0300805007000c8001140d440aa05a201078425910240c662401c0020744105100b039074029004254002a014038107014182068198081d5a05200c0031001804005c0301c240200d4421a10034078100564000c0000304005140d02c0f200040c041c0415a0307008030401c000003803150203448098030f81442c42d6a07451480e000078441c4150040040e000071020a003020084005400c81a180a1941c1c25140c090b4003c2454003c0490f040b070b50307641c020200030291921400440e04688406036a07896698140b4070403c41c98845c0d51503117810403030b281420000344562601940c82042c0d0200550355215034401c1d4000294100380184002c2624042010524510f444582d5101a5221700b0218107079031110b405a400c0f00000f0403110380651280350401941d652a010900c0b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 689610845 1250 689609595 689609603
    0xf0e010f0506091926060601080610090f03060507080105030d1205180a03090e06030a031d0a0b030c0306030d050903060a1d0f0a0c090b030348010c0f05092b 69
    0x2e03622201c0074900e0010707400300885d102c2d9900128140b0103103982c01508940d1100c0700340c80c441c41055150000712003008684d80400d00380d5507021b6012041010a4000c0d602401140c0d07101c0115076200c10400da10740030f2001182c1c0100342c2d0210380003142c200c2a00020762054000000100c2c03c290b10040358100b0341940411000120850401c1c020405001c3c071641d0480000c2d4020800030351180d6015162045001000c40c104064442c403a00c20358401c02108040d2915035245500c1e0708200b4803075890f54000b940c1c458440d005400654450750b1044050300c03138075500100101382e16103c03140032100901a64450310000d01075000000d0440404015031450081040020210803540342403500c52171105402040055081601e5200f0030340c1c00105841007101000040054140c031480360200704003041e18074400e80c8005200a00d40b0b11140354140b0807440e0a50001d004a40d155681103458002c00b50454020400c00c1c4200d00040c282481903100d48a5036180750980d0310208800c0c40f032156140700c0101c0d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 689612095 1250 689610845 689610869
    0x712180b131707030323070309060807020a0809120a02031204140306060306180c0d030c033f0609240e040f0209071b03090f0e010f05060919 62
    0x900c064200300701c8004003041d0491400c221400c0460944a030410311028040190850000b042642c0b40c031304a00303070b04403c0d08001355540d015144c040c2598146201d0180401c0c7d01c0340005440500128061009940c040d941c2031801d0f03500703010455884012030f2008124481c1e8441c0e48011b89003000406140b80c198a4001c0d207551030f2000000345000d029800a000303801810510803503803800905550440e4440c101000c0700003605d4412031034101c01140071540b1403011100001410b400024080030365010740d0745d1001032801003d654280d400c06034501c51150000402260408042500007145071000304000f140899445030458141c0702c0110200b050804110a00071800e058060090010310030100890f1240c982030b250068075030003140010780541c3d03070080002c0d0401c0c454005010300705c048115511014019090003480b03842c450165544e4922214070206048001219443c1214100301c003004a082c20241441540e80001e103d05810142c40130354081082e246e040d11202030424049a4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 689613345 1250 689612095 689612107
    0x2030c070504110301060c0f0f03030c080702010203041a06131a0a05031212040c030b0a0e0f070506161106030727060519022404060b030f030712180b 66
    0x9040c580141e000302e2140e85041180015602500c0a4a044600c5810007110580c20303801e0404016140201c010207800380c0d0314100c030400d50560b01074040e80d48143d0f103c0e0010740e29400160b01f00d01c001e480c0038010380344c83d03000042d1585982c1d51081d807201006d4049096102a50400f07400e0380c0c030004140c658014151464200350402d07405000050004800030101301c8a88000f0703030345c1740c403a49401710790070b81401c2e00090a0000303001c1210000c650102d855140c81c0384c100d040c10000e011514003400d850040c40380d090300795040040c01206484005010910b41114205a0402400d02d0042164115880e45005007195513083c051840303400540c44444001d0170140341d210700f01403160110091288052000d20a146c4d01070b081e10103502031400e03c024103082101081c1e150a450f1181d2400180d6031844820162180303890090140c0d03c200700c01e0105c00fa03060100340d1105810080001a54420b22542c400701d101a1080f10028195040680c1c401f030000c07246d41c4035602540c10400581600081c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 689614595 1250 689613345 689613367
    0x313020d080f0a090512070e011514030109020d110f040611100e030304141b0d032c1906050a080a061a0403030e040605033c0c0a080c060a110a060c0203 67
    0xb007900700301081014007e901d0500c54506100d003018080d000355640800c1e103000b1864002c1848103204c034440180035440c0e69592130404040d42c0200e031026603050800c0c030012407880d100401c0e5640070342c8240501c2c4c01e05050450484184000c4007a00b078552040e0341d00030a44071002e01c03404140f0b40d0f105011b95605d00c0d2509040303100c01e0103210805040d500c603011032102c0640c9420700e240c040e5401c07160754202c0e41407410308803071558032400c02180c1407200300c07506240b680c108901d94032400c00c156905c003002c01f010740c10646040340078419040419000c101d0321402d54820281c582e8000d071810000150749494540c400c1c481c40098403000e040d040c0c0041d0034000d1507040f155012803910b00f1541031000a003440007098440514081ca2042240c00c0c9181d115075082d03280f6a441c3c0341c100c40000140c82c502000751f0b150b4401c1c0c095a070078085d00202c480401c48400c08510076050b0400681003510741107030080c1c103c1d0161441c001812150003680c0c8054006202030003102003880690b4002d540303e2021002e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 689615845 1250 689614595 689614609
    0x90406090609140711070b1b150901110c030d1509020a020109110316061d03010e0d090e07050708030a2702090106111e0a150203090607050313020d080f0a0905 70
    0x582050012a03460b1406504d00001d44209a0340c0c500c0310b642c2c9459240404107503403030f4440c011488502817a001ca0709c000509824039482403441000922442c840310308822580c1c41900300d0b1001c81d4208010300d6004c4c01c1d150304501980010100d90103900c43d5903004000c200e0f040f031001c2d000141d4580c00d6840901c00c0c41d0500c00340a00d0202e0241007890941c01c01c4003460f265512610080c08881520054207590842d2032009480c00a8000d1000c100d003001d00d16240e0015000080200790303c40320205520f414a0102ea02c01c0388180c6425250006580391560309810080c0740c242616113a4a940b04801009034603200c080030f1032208094420079a02c100070811805801000822030790740943c1d42850300000311903060348180f251500080402c1a0301038103140850740050b013680c80c0d03440902070007a540d500452044050500362801519600c10850700d03444155042404200c03000d50a00151038018440d2071198410b40b403092600d200300002c60825001100c1076001300b00c041c1010080c0d820003075 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 689617095 1250 689615845 689615851
    0x50d0e09060f09060301230609070e061c150303110d14071b0509090607020d0807123303060f0228050408071716060e0609040609060914 60
    0x3214004a0319025000c00c0d059250030000c540300728190703008100180c40c207502c44100140d44010032451040f018070707882c8407071a055803c00c0c062a17039180080c06851141030008505980200b006241116a211321400d80700a2800003036625a0b404801c840b1244014603500294481d460382041c0322aa0200a030420542c0b49003c0c0034001101c94210f41505510111160710343c0c0201c0a040305002d4840904803c1c81c640c011a401142500070701c5038141d03000840612885a903400c031005a0b450040c1125001425105600800c010143c00741103241190011500502d100400702140031b606104521480c1a60515030307540d190311801401403040c640945c410000d40c8007419454900500e5111610550000d14106080140220b0746003844c8036208072002404a442101e004503200c2080600c281508103c540701c511900005c44101049685818210b6005440d41c080b00781440c0d091040b01e40c030807001c2c164440d07640d403408110101c41d031143d9009402141ca0000b0780610700410a04100302c01303 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 689618345 1250 689617095 689617099
    0xf060309051504150213120303090b01060e030a0201051b12040f0f0b0909040203030f0f03010905011d220f060203090c0117040204022104050d32030c0c0307050d0e 72
    0x1d08100804512244007014607407205001c0160b91b050541d10820143d5840e4015441c24000501c62500b8194182c008484803800750005110031b980c0d0340015203442110b0340c086501a000090401c002d58020340207007070b681200f8100d81c0f091030080d040d21420114014003524181c2d60208050020b28441400c400c050092100c0d941c1ca05030030141d11403241d018600300a44a003602030300103000c540302401910541d0100c031103419241d0380090b04140140d0400d00840d419186080d000141d85014034601d0007030040d01c1341c3c030380d00c0381d446071100100c2c81400a48485840c4c2c500503580000a00036007d150200c900032180142c89080aaa1040c1000952005a81080648508245c00d40a595003480e0040c1e411100166158401841441f01c1602004001d9030988480104410f00001050003100d0702d085560f9001c0300003900d004802416000b007080f000e1642004880f443c01e8091100468014000d010790368140201e901c1c40da441c40e44241c60403140c079001131105400c1141c1202644500000c1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 689619595 1250 689618345 689618383
    0x7030b1f0201060f0e060607050c0901091b091220101e030501080d03051b070807020f0312090f1507050d091512230a0b13020915130f06030905 63
    0x9002c178030480880003c0d0130a44209800206031003000001c1000b11030000d00980b0541003980e42d04aa403008201d6014159543e1490300c0c048031070305100340c1049050341d42000c1000c10780b0080d42c64900d5041280d80d2141000c8030881016071480e51140b4120140b00c0450740c441840040c1361011203540f90805062a05040c1450018030903840b011480c0545910300b07141c0060250303142c11840c00e034091940a00140404006040c005100380c0000401c074460081e5411007a81c924038003410b41e2410219003050b540c801c18402a012403a00c18212013491074018010b059003110006000044e52050104549660240107500724050300400c0310310060403d003d02200d15050000003403d000c40d0080c0c26040e140d44c4841c05206403040c2c2c1c0c40343d05154404160882245880005100200231900a0b0343c842c101284004c40303400b150340200e03900080094044880c0742c102910030b0001c0d40141c07a0f4480002124240452000e040c0c000100091220b40e03408600e490a90900314105480d860014002c549 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 689620845 1250 689619595 689619599
    0x30b1206071215060c110a030c0b070206070812101403030304030302030a2901022512020d060e010506100534020a0801240e0a020307030b1f0201060f 66
    0x6404103109600140300c0c1804541e0640601811008003086001403812110030440030034000e501092100305144907809500340c46409100b040840202480300800e408415103050040003e50405049030a202030303d09803c0910958425449400030f28182c0703140c0e1080001c00c54544070b0003c01d20010024105088035485001010070b440744002000503090640000104010041395400b403244003030340317000700ca00b19010000401d07030310320345001d10b28018880c1032811901d17901c51400100c0c18045038280300c1401450080f620350032580b420390a0340c0c440070103030b10310f80411101c0c0541c03800c0c84040343c000241c03440e140b0104040142816807241c200b00c0140485c20602455180044400b080b04000d00589000d010341da90408071240c0d8000c1d00607801500c005240101504190744040800d4000c0741c98144802a0001400c0c80e4400d50000600075070100b54005034a070700964025580d8600842c0c200c1007400440d19401220038a4113100e0b04903104003080c69428070032000503180301005650054 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 689622095 1250 689620845 689620879
    0x110418180809060702151209061807050d0c0b040b0301440f010608012a050304030f03090812040201110f07030b090307050106180b0a031e0f140d030b 66
    0x20042c81007280c05070900044000541d0b81e101030400610002030b1800b90303298030800101d603910800f034614142c1c0784240d00110300f120360203107c0000c001076444001d00a15284ca010440894217182c0244e50740c42c656000844e2891072400200050103500c1007559503545403c800780c4149890400212024601040c1860446030103044444103031030003064a02890546080310b41000c01606603150607618101c0c00240410741904861070421690320351150891800b65240e428003142080c25001410410003d40001c2c00b0700e1080f000c2400c98540041c00d0a2143e8a41d41c140d0f10401480800e86000c03400c102c215a400100082100020005404000c2441e03944030358078549800014030580600c0009104100c0c20000c0e100082e400c00003d00c00103954142071046000d030040184003441c00d1581c00d03d04c509112258500b10b80d488400e98524000036002c03154032042c2c0c00c000316001c0f0654072250020507007003403454001500003006031408100301c0d030b0f000d42201c640401241c0502540700c44103a02c1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 689623345 1250 689622095 689622097
    0x1e031d0609060301091d06090706081b0a080a02071a0a05100b1902030c1014071d10170f010f080109020a120206070b04080a0909050f0103080903011104181808 70
    0x4500718500032406506c042c1c0c10200200040c440215103204000801c403110800107047c6088541c0ba4030b503a90241c5680b0010395891004404d1441c2c007000c02c1089103512407240c0e48081e030000f803200006041c0040c035a0380006c0c203480313452034840d140c03180030034843c0d861000d214468100d406100d0b07600f800761414580070344600651300e0450b4050b4054640e9030201e070092084624210944080c0d5008030760304010b0f00010038901510340320208441c800103003102e0060603c5841095007030902000c00060f1020016180d8408064408000e00b0451080700300801091860041d010303c00904155814000d403559415034170741c0100b40307a0303050140040c0580c5a6091860564581e01a09402da10342c1d4004540c140c8216200280204280401c102c140300803100500074003d0940e0342d6004496a81070980142c3d0700999120740c00051100041000811400003004425006400031502c41c06042c4014843d42080c2d204160001c40758101245c50a1540318540c0f42e810301c69103e0004d950365484000301 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 689624595 1250 689623345 689623349
    0xb01031814030904020301180528050606040e0717130f021504180204030b0f06100806042d0f090b04150f020c1c020d020c04091e031d0609060301 64
    0x411000680e24080c0345003841201c2030408090005d641d2940d46100e00d040d40e100e480c1c2d107001c00616180c0403c6078074042d00e5120788d84011083c40142020001d0065034010040a010654420000c0000007040b84140e10190300c17441c6542c80382d80a010004440e002c50800080000300d1401c550048040041d10101c40101c00c180c051b19114a102c40001d9402082d02c21030b00700d0044200903a40700201d80b4803a400420550340705140e6045241c0b82c1a0859103507081c103a8802d82d0025403819400009803254500c1a44018010800b180702c03084140010b240c1c2c95021061039071b070300c4e0608050350300000d40d02a41080080d42442085104001c0d1a01c101e4800050401003d0300310102c0900c40050302d640200c0c41c15004510110b644400d08103010740d6884a002d0590800c0c00c012070703207120450000c281c5a01e581c003660041d05280c60004d08220041c94240c104072080c0ca0740c00c1c926814221010803c1703000d540700392a0546140d0380244104803a41d494030306a0300c0340070200700b2020b00da1140020380781 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 689625845 1250 689624595 689624603
    0xc0602061b13031a04030207120b0a09060b0a120b0c0a090b03040515011203081005030d031e0501063b040c27150503010b07030c140a03050703030b010318 68
    0x510b401d58241c92a0112006620140c114070f01490400001d540284400d801148030f902282c481998800c40756050340c080003009840200480c0c0007514900041d009508003c1c401c040c000f800c13119030000900e26404070340294828641c0d0181c40360801c58255950703a00031868150040c00e09040c1400100000130a00483d1141c00b07020000ca020840b0030481d11034020703070000c03030004d280d0f031201c141000626010300180c00051844010407904042c1c2c420f48816138002030081d224010318102c01390040e140418100340c0c461400d00d407441303076407606226060282c0680c0d80d032100906002801c09805013210f0742c00104c8051103601c8000821586600d000c1c920b04107030390200c2d4500300d0f18400e0341c5144020b107040101c43c036803112005013030708030000342d000b079441c44041d0380702c00040700004980c81d00090040303131340c1303440200000c0c0c02090003400c0500c100351040000e10410040405814100030744190118082400400e800003059054054606020020f04c1c04200030400100604400001c00501070 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 689627095 1250 689625845 689625847
    0xa02100525090306050123010c020312180a0b090301140f130804091a19030f082a010510330e120f0106080c1509012003070c0602061b 59
    0x281c0c26005810708001190890300401c001d6a40e9034118100410075149042d40c41d0301c4104c0b41c40d2070743c040c45021051580227070041502404800903204181c2c4656100039280d9070007807500405580e6252040044c080d06801252101c0c4030105243c20348000300341b801c0280e0300160070442c1c1c01035130800742d41c1c0c00f0140c40b0342c80605100900389426144516003210605c2c5041c00000181c108072101400e0000e801500c00e02d82100c0e01280e290420411408002d00e2109480300c03000104c0e0796a000b40c00f0740745204070782802c2e1910500f01d01d11400381500200d142651074204000700c424405407020001d00701199410480c0844c03104061584100226030100315079018800c110035849480d5918010501401c0048071101009170103940d44c200c2c002002996080440103d604640480c3d100ea2002000e0449440d1007018554103400f80c0020210b24100013085240900c00f1000054403200c0c1c4000d003000e5a5100143e003440c541142c940e40250040d50310020521003011441c2c10350482c1055451121 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 689628345 1250 689627095 689627161
    0x303050402010e120d140307051617070c030b0105030c01050912070e090a051b10050c030702180103120f020d0302070606030230060c0a0e010c0b0a020a021005 70
    0x142d50409140c3c180d150402c3d00398169501d40790000507a25140300040c2c444080c5c0720000b02112074184800c80300c2c0000508184519904400080c001c3c0900b02e12507141400c158080055840c4941c00a160640380100b011508100b803003001c2c258a03002d0b28055000d42403c100702c00000e0264800c41805a0050b11084200424600c050020301d02408520700e01000c203003000105256501c103d10001d4440b4003a003101c90b03c504555250403222001c02402000300540c4845058403141c00031605010b041c081003042070300503560401c81d0401e0301d44400b200081941181492807400035003a10200c14013451007107421090750009111007400900d480c001da6110f9141c580b00024040c160300003504140103000300400502460400c884001c0f0600306d50110303480c0c0241c220780d150030649003100f00040c100000030410b4031a4941070700710035040c1081c0c681d501f100c0c0c0d01c00820303807012107162020640c081030b205451a8140140e106030b40161000748143d0510311003103100e83c00b080f034045040240580b10 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 689629595 1250 689628345 689628347
    0x709050f0f040b03060114030c0a21080705060a15050609030c061b011802041b171e090106090b06040608060904030212180102070b041511030c0f0a020405130f030305040201 76
    0x3c1041c2602020b0151581e82d65900e40b0348920b803126100c4240310b0f000c3c2e002020007508000f03007500c003102c000d01529801c41c0320910700c2c1010b6820854007601c0ea40c00401078080031480802034140111a401400107161510620030b01100702c4980240c0d201c1e00741009890340c16900015001c50200040b41c2d21a520319400049650124801031211041e50078661184d4010741c00700c035581d000c5e500985050001e081d40652940313140303c2e075003000d0340030808100390400c1d8010700408030341d0722140c00459446104240520f101c001e00d0101c503507501a81d100c500c280039003041805800100d40c0140c07010f03400c05017003040252210ba801408140160880b90015041c14800c001c21402c0c88000c1e0b03030f4560391301e070150034560f0640142c1e84824054461110000740401085084604641c0c6040380c09018807002e40c0e080700c140074545d44495251000780f10005070070800b4440100d0070180d1800408455030540f052009441d0003c013030100a12100c4105130114209500c0010010343c9442d000031159110300c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 689630845 1250 689629595 689629601
    0x150307050301060e060f09070207031101090306060b0304030201060f1511070e04030504030c2102040e0f120403060b0306060a05061309060e0a183203030405150709050f0f04 76
    0x22029500d90f003040c500051400101402c5400340b54162102d80303a0741070f0320301840a2801d0945076000181c0c40100c0400100b022086040c1c01d0403014075100504a83e2900d4071800c3d607a25400c8a10070100000a1100309602445080c000344802044c0d542c146260581188015401c0c08100003400744542d000c8d031900f40203222102c003030011107a002c1454203090030020503941003408101c3d9a040c2c5500045000a1712903101e0070322810a01705440c00c20095424440500b40303511824010380b090210f040403d9000703114082c07108011f449140c4c2c4903883c500f400c00c21340345000c1d05e40f0301a8116809006942d02c2da2550b030410341e5819120140d0b11140d003c41c941441a59601130040303a450050049207903410404541d0003400c510105002e84035007030010f0003205c08000001040c10340480620030141c08032042e1a06107c0c01c1c907050818110244008a0645c1e00464044583d600310409440740c001c41d0b60b0845421541c01e20304803005500741004078040c039880082c514802c411405091140f0b0396190 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 689632095 1250 689630845 689630849
    0x5070306020408031306020718240801050712140a0207080d0e03071202030a0c1220030307110601060c060b0a030609030e0406140f1017070f0210050c03150307 70
    0xa00031955980d40c0c400083c0c4035001022007044d05c0c9811400010614400a980004d54440400d1941c010481002c0032004069091314029240b079250200050a844004010010900607002040c2440c10343e40040620581c0503d9807c80341c601100c0101604a82c1c0f1100e0380500e03a1500169035050768180345805014056110b44071500304a4288a00304c404006060124411030105e011240c603550305a8070380c007400c010710001980e43c100000104820605030081d0390414200004030418144802f000c040782e469034540c07190310010034007000c00d41c800b10340281040420043c01d45941403000041868000140240015894841c60000c95403940f03021303401150305c00c070b0400141d1210714018020340b00c80300016106516110001034a01040c10300c04001000083c0702c64085005402005100354422014400700280065001070a0801d41080342c000d141580300c108040342210b1009281100d003080a1080714107003001d11800c60800d40c10703a03411250a802e102031001400e00441d280070350035 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 689633345 1250 689632095 689632103
    0x1a040204090b090313060302040b0d1e06090b0f010807050d0c0e0901060305040b0f100b25080309070501050f09040c020f2a0d0f021302120a0b031504120507050703 72
    0x11062103d4814000002e020b44034a044100c0b030400da60300019422401603100302c003400c0c1c6007040301780b4080009906c01041070111a050414442801c00e0b06012035820780c001680076943c901142040d4034010300c060ba420107092030f040000d4076041800401c60301a60b0300311405117840326030741100d00d40038603010000401c0142c41d80c0600e6035607900c02005000706640549202c0051404600841080c1180034850880100406815032400302c0401c1d80c5c0d0f000200203d20007200100b84074842082d10f0f19145103d001f4002951641860f01c4581d08100c0c195001c0e5041c094101b14100318181030b1000e03907100c168101d40004001c21030b0202070341818958000c0e11000e01400039000c136240c01103008100d8840e08095171108005104041c040d404048080240050050380d950000626110486a074141c0b1062005401c0940d013020210090304140c4001601d19190004044241000c100c1c003001c444410725400030306d040336146c001c04100c4690b4a0300820800046a000348101085a800110b903c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 689634595 1250 689633345 689633363
    0x325060c0f051c12270c0503031b120a0804080d021902060709270507110a08031b09090f0606090a08011b021f0b01030b04050a271a04020409 62
    0x41144032225000c0c40010303550201d040001460700c0007040e4030803a403952244600104600d011996024101701c15400d040f58000851400464562401c0c07000e00b8003494202d109031086018101500d0410501a0002c0800c150501003501d43c0c80c0e000e0181d5420a070049030041d5a2084040002d0180c41050404940c1484902141c000c16500250503849190700395914240c69848840c5015503103c4501c03074014070607149046180c120300b158060b035006056420702c90f100c64010f2511900307000c2c04100c2030359002c02c00b1081002200240b0001ca8007119604c00261900b01e00e0700006003c2107000d0304100303101e111000011590380f03c58040b10a0003034010b015591a83da984007440c060301c019404c40801c08440704d48075281d140001205d504450382c80d00280048940418000001d100c003480c8541015100c802c080d10b2615244940380c0940e03485c80d4007045804001240c40d6010341c20013100c0740d556410740d8620000c2504181c540c009110000b40c8144140c40ba0300000c2c019002c0d60401814a1072 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 689635845 1250 689634595 689634613
    0x7210c031407091715150307030507030c0807060f051219141801020a2a02040e0d090605040803122505030f06010e0f091009060902090325060c0f05 65
    0x50809101c004442c11303252025200700c2ca02548507200d0440200650a15040300003183e402260030504c000980c101030105c9a1b9031303982c0d403646c510300382d80c0f5401901c0030040b15405010844007400300c000a09020304140b000b03201d280c03100520910484d0f4100c41842c001c40c1c003103102c02035001d60301010440d001c0d00070700440b5a10310850b1113001c01603c40410180945503440c808100600030b85130840616110308201c00a80c00c100e0001c4504003405054101010b1040c030016070701d9104a80c1122030190041c03001010035032010703004504a42161090007014001081110b1002040700c03110411408003050f02c3c3c0701ea940d542c0107204507140902034544007122880b020380e44400070398802e411303034400765030071780c4804005480e000345d050a810f8002c4c0c204510341d800c82c1010007589030410325080d00a1140c07907036600403404441d001e03000755483c6500003440b00110b2a04006240c041c0e4072142c0b05020307181c0000c040e80c0000c00740703118030b0b030a0000ca0417a203400e21880c5803841da002070b04841958103c00c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 689637095 1250 689635845 689635847
    0x3040807050111031801050604050f0f0a0209040f02040501030b01020a0507090e0a020d0602130f0b03010308030c1c1b02281a040c05010305092406040e0a0c03050607210c031407 78
    0x3904144171914035603e000c00150603407a00e4002d5501130988900d2066140d2902548405401401840e0088158003004030801d903885034450700b0f1444107401070040e00c3c0c80c100000141078a001140b228115804139004001040c40030071790f1402c0781d51854000410400b01c0488130300300606004065803110503591130f441401750031740080200c50608201b0303410301520341245225200d0280105a400c91040c4018400076006400840e003000c2000d0002d070030411500c070304203400c3d03e00301d41c450505600d80d15440656405001409481d5041d030000d0003d81c5061429109001c5410303c510880194040c400e10a00600c40520800005448540c035a0351500381407202c050007181c49002d0001e4900000036515410102d50030103000e0b584403414400030003043c90321203400b50140089901c1955200050000c900802118424520414080241c0341c69030601c0d9060801c014401410700030245010307942030080303100400c10300b500c1c1d90000668051030714080f4002d11580300e500801c1c0c61280103100e426 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 689638345 1250 689637095 689637121
    0x150303030f100b0703020c0d03030f020d060e0108121614070803190e0d0f02120109150b06090a0611010f05010602030c0706020304060e0409020d0206040b071b0501050304080705011103 81
    0x9070310440e800a001d2652038107000e00f00e10072800c001c2c005030442601e9800301d1906141c03001c84e0a010389008102c203052a03489408903803100c4580c1c200700b50348003420888400a09101030050440300040c1c10003028550f031782c0800303114030701401c940d19200c2d500d40700c00c002c481d02211017010103000451382c00d5902c40384920395a42c0b0038150712140400f403040c09032280d07100340d00881114030040d2003411158040c0e6039412101c2e84010040380c0c0078031481d00088806009110f040b40803070041e07220071185a003010000c01100c80c5058030718060b2004200c58442511600c1400003107421a280c14540d880b8010301c07450060255140120515050400004400c1c3d4004041c2a0b548009800d0311503003903880a00b40e0f505c5c8510300c24600400c49444100c1e40a151691003089000c0c0060010b440f800001e5001440a40c090b0300480b0101c440480d62505111109000c0455030b03000c45e690803040342c200f1001034854040200024500a03001a20b401040340a4000907182c4182c030302019224149078403400c4036 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 689639595 1250 689638345 689638351
    0x51e1207020604050c030d0c060b010e10050a090905061f030915090506060a030b070c02061207170901060b03130609170a030f02161e0b0f100602010c1403150303030f 73
    0x1282c81781044180c0f092a0104405101140c99180c5003520252596110054150010294180501d5801e035051680311050740891500684d0b0b16140c0ea40b10b6048042c00b5010280c2065400c0f078600000c010303075601d46100301c4162340c2107120102040014600c2c201d02400030020001c0020300005180034602209401211548c0c1c8150b098405941c1d602042c04110349940c40090402040000403541c028020100124481c0c0058038640c03411000f80241c042c003410a9504000040c40e009401c403442c4065200303190040e6002000303001652415001d80443e000190400503401e9113100794404100c27669000340c44c3c513680100703100c0316601c0340c1e44a02e4250f000b48010b90042030802d2940840c0d00518402c85402e1210038401e40e04408068a0b542d480c2d14100c502c08035080c5082c205071002c1011042035511810001e01400328030702d42403030900520016580b219007568107040c5841e00305034102c0200309a4403440305042e07850313a940002400940c85041605500f600000050000d0a95600ca280b84 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 689640845 1250 689639595 689639603
    0x50c1606050403170f06040c05071b0e130c05040c0e040c17060a05150a211e05090a0318051003050a05010e06010c06020f04150c02150a051e1207020604 67
    0x1120b13007940700c6600703d0b4050444102c10403c0714000081e00b50f01e4140d000107400e12a80c544035050003015564102c0f803900c07940004400b8103030b0300010010302c0318134085594081c1c19141c0e400101412580c0d0302e031680700c50b401804e03c501c0c0c6034980d0404451042e40f0b100a051402001130204501207074001d03101c080000c4604007442c4d5600001001820a4210201103420207001c0080401d11110900302075000150104c1c1041901d03100c5890b62821514110054000a100081c0452a4079840e40640b80411a1030390390303500b4101040300c101030104204220a805091444060b040c042c4503000605c2c082d040b81ea400b103902d44c00d03903d40c0f41c0d00d50702c00d40c031624288108200b644d0f201c400c0600c0d0480100c90b5140062119040c42c0c0005005801034480840b280c85c1c100d003400c0c0c440303806a0304900d0080564001503151a203642c15890309001c800b601010b1012403e1422021010050a0713115207030a121450003102c90580f00b21450200321132a04565542c501a40d09204d07500035110113041d40c09031 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 689642095 1250 689640845 689640857
    0xb0c030d02070f020907110c0d060f060305070e010e0114010c060f0614040501170c120109060c17070815190b030703060f0801020f03190b0307080709060603020715050c1606050403 79
    0x18103400c1c00788444017030007c5140010521802c0c1030040007a2400c041380304550751078076440b002c1c0c00d000c4903001e190051031191002d0710003a8281003020341d580905a009000000000700108039418801d06418003c00c400c1c60900002c1e0444e04104000c0c5c9212841c4a140910300f440000f00c2070300c41086c004583c0340c03c507424001640d035810002c10a110340c80704c10350075400181c800c030300e02c1c50114160203003e500c0034004180c1c0300c01c0c3d0700c50404a40c801081c64010840c50b07240c1e0140c40c005a440c542c0c0c80070940c01c00100d03908042041c11204501d480a150040b440c1031015030404000c1c2ca400001004c000c1511540c80c41e16180082c003030449031151000800b0380d140c0c0070a081c8010300980e8143d043c00304040d402c44d03550000be0703002580560110f207502541c0721076159068034144001c00140c05030100070201585003c02c44c41c21108142c1c00102094410b02c80b58001558000c80142200d52400f00401c440c0c440800007517440c4190360705005100c42d06d00f000c0c420848140c000e944114000e40b910 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 689643345 1250 689642095 689642101
    0x10e0303070b181b060f071406090c01080601170106110111040f1d13080304020d140c01120c02061303020c130903030c0813170d020c0127030503010b0c030d02070f0209 74
    0x1140c02044e0100c229503200c08103000d001c4450301210081e0010600071141c44642d02d40105070542001c005844142c10364200d251401d02d107580207012950049000e280c2103105c0d00d508036000800c401d06001d401d0800010700c0d8900ca9181c401d402000000125202c056680c0c1c0d5180c1c03141000071280d00c1001e144040c103401403454230f6500e00b0070502c1807544840d2101c0c0c82c48c060742c5903880e9600c0107100300c2c1c0c03015100b01041c01040880000c4110b05125100030b04840c10301c10700151816440556040405003000800404c280d8041042900002c076100340312100300c2c036440c0981c02e015008403001e030070142150b800c1034400c1032a0480c00019010b5102000203051300c02e4100c40b170500c1280c03002c0b41100c100204030005480b104061a16a03100d42c0d10504000d19aa41101640e0020b40c0020381c0d82e441e0300f642d0b40302c98041d08022480044000700001900f20316038014000d800140320703601d261940803800d11102d80c4180300f1201e40c600c003600215981c40f018a0401c7c0e01d010820800e0303020355100000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 689644595 1250 689643345 689643373
    0x70509101e020f030a12062714070c1b15020d080f10030f060b03030a17010f03050a020909160303270f0b091c06060608070507030e010e0303070b18 65
    0x20f40340c88070102c00301840c80d01444c0c001c1030325098444046202ca4550300c8100140414841484160003003803503600308005000017000b141513550300c00102c60300d55000d50500c0700d080d400c081c50412859000c1c81014207509000d6020580c8051503020b01602105040d00100e0700d9400b103014540b0080d072303854640c0d01d500c0d0340401e10441c0303004840c40d6404540c407142c00e20101c1c0086140d601c1d654802c4c000803030011150008681160008035202002c508089004000704684100550150058401c030074103042c40c44c0c1f10156140142c8402034007451216001c207010700000d1040701039202040c2215900342d942ca01e4000c001c81146007481c9001a100c0c5a05c90000c0201d203105130071107404200701c0852504019090035250700c520502c80e07100074a14000122240c40b6405142c0290007145c00140e06443c2c028050030446006082408202c0200710704030010b5004124500d0040c000e2034a25410274100b03000c02c1c03031403003558000780018440d04100710b41e40f542e1b6140c601c0380d8007400041d0303070f903003111491 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 689645845 1250 689644595 689644603
    0x90c01020709150902040b1e0c120903030c01060816050d0b010501050f25060b10090b0f090310061706010308031f0801290303131505090a15090b03091005070509101e02 74
    0x72780106d41107442c0710704812015801920308500c004007aa0301c0c111420000f1800c5411980c012841e40e0040d8416801c0415001043c000811095030906108101a903503160b8183e03050103000d042c0200852070f8181e414401d0142d940c00710800242c90848500d081c80c0d02c01c0b618000204a6035941022582282d60620b0100d039501c2c0c034807680324502a2400c21032408890b03044001c5818620f0414003100b042d0b44c0c0c08008071452040b030b588001a079981429a080c504050125005130241c2c0035000420000d452142200d920074208100b1400c0d21080c0003204d8501c80481d48a000c0c5582010640c47d034988080462010706280d8044481600d181001890344a01524000c000680d448010402000060a164903460490b80c54890316020342c0f171001070700c2241c0d143c00490840d08013589030a4441d4001e9903100180010500040c21440c010480e00d907200610700108002d140c171070000c02d160700d018105450190350300808180b201d04056a0041512510380c2128002c04c124160114255002003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 689647095 1250 689645845 689645857
    0x30d0815150307031d0114180c06160201030605040f1514030d030b0312071a0105090412030b300105060603101e0e010b090108090c01020709150902040b1e 68
    0x4803942160f64254040d4001d11680004003414805200150004907007841010078281c151200a5142d041040317071700d019404108400d00c1e03c0c0c3e210030901403999a03844151403020f403024805250394101880100c0c0605050350026400c00d08006003000b004440b038004205684034071186000e210b41d200040f01030214601c03145034060700510041260944070323400c00261400058122102c0c140e1004e817005040d0301c000000da0301c4418040343c5c10350110716665124018441280e2400450600b901c40015040d203000c0c400c42810794415592041d9100c000c0880d45181003031a00c0c0d85003103140c405103580c0c074400c454401c0d40c81d4a13110001d03c061902c90203507805416089441035016050080b070201086000d004901d03a03189030720300081c503c7e00f00441d20380600000740d000fa4550030040000b500901015252070840c0d0088200300140c0c2c0d038002a9101250800d40000c140d03400c0c2d21581084600d0356800807006d80c1c1c00040c011984041704801400c04022080000c03072000b41800c1008170350301601e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 689648345 1250 689647095 689647129
    0x50f040902010e0d111e01020f01050f2e0803180303040f050411042c061c12030e030d090507060503010305100507050c030307020106140109180203040f02030d0815 72
    0x440548542041c03000900c04c0741c85612108510422000090840036071159064400301a060b00341200307590500100410309103500080c0001d0601d0a5150100c0d0001001008070342000c4007410040c42d95015213486002e0040b440d182c5c05038540181d40e4495000d05040c4604a048217624100c50400008450484d034039201a200803608040402001c2c100a400c00c002022040c4800b089156805034170402107120720741c1402c0076250700100700001c40d0303004040d00d114039020440e00745079600300d200402c1c0f001d074000c01400180f40b003080140c000b0f01c0c410003074080c3e500c030201c1c11182003107640d8009525180070308e04403a4039542e140780c03c640724882400001c0041c1c1100b5145104170013650000d030f400595600f0f00354180700040004518507002229400d00603912404200110345682d00003401240080c40c00522079070a1035400100300c681c40514000056000000030203004c81c80d500f5140322503006040c3d074112180030200a001101c00c3c0d442c000c642c2414003a24007180740404c0d420b103e400030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 689649595 1250 689648345 689648357
    0x1a010206011208120c030f060a230a0807061d040e030d090f060e010b1014090f0d0506070807090801090c030308070e060408010c0813020d080d020706060e01050f04090201 75
    0xc00e41420301c0b502644204035a002010301c4035140030300001240e03d10501c3c40d12044d41d200e01c1d0881603a20b120030080c0c4150b0081d40b14450500104400c4030078081403840c4108079108071890324012490f40c500c0350340084500c0c0198803002c101c0c281d2007091340c400c1c49100e51945a60fa0703010400c00044802c1d0142d442c402c3d500070003080c040443c0781d40003070001034014507a2454200c015181c0c1802d0f01c0300240c034404665540e90112610f0301d01001c800a402d08a840c0840b00134066400304d0303015114032154688140342c0d131105c020459564401918526a1140c261612824030b090301614030a001e8581c43c000c900342c02400700d4801e0b8140301b443d0300590820880720680d0f1840c0c406540f100c10141900e0100803030101d4000068841c030303000382300914841000180e4601c003480c00a12080700505140303401c4550100006c096030720392180880540d04203100a0751082c10380140c1000344142d5000400f0103040500c00100511890740700c0d0304a030000c0e02e00d9035951500070200700440c0d4042c1002804600 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 689650845 1250 689649595 689649599
    0x8010f050127050d1103010f0b09011202040b0301090308010f0e090307140c0a06051e0903120c03130905040312020703081b04050a1806081c030b131503061a01020601 73
    0x629607495040001500d420161059200e0f0302007030302c654800605a807a2040c402c00b40340c0500f42442506113a4043c1041040640c0302800040d0b007116040c802c400d40700d007200c506c210566a5541c881000e520000303008010105880c64042c1031b440c001d1007500201c2d40c601c04c002503004281c0018a02c55208a40594903084580e504c2201d01c994600d03040926101d20210200c950325041359010182c080e540b0340f6501c40d0001c0748a4a03900351541c61101c0214018456070803d030302c0c0020000440c0004010150f291216844030b189540940001c1d91210101c0d050000b801f2890365201d1030149009a83c1d040548481d844002c080e0b100c0c01c038004000a107000006512441b8491000e20500c80154616182580c1d8034005420003c4a030040d80c0e011980181034011400c05201d040d0003801c542c1c0140c165406e0f2019080d0300e103142d03403e08000b8140c0b00c0e590804140e486844100303000a0052013002070351111481d4900b82c0034140011100c09103400c141c02980708000e07a102000c048164004c200581c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 689652095 1250 689650845 689650877
    0x200a060c0b0414160f050d11040e121201091d0c01080408090621070e010203030103350a112a0a030b090604031407120302130b0a0f08010f0501 63
    0x18426070b284102c440c2003d0309080144000e903880c8010f1182d00380324a041c001100c180b880c940c2e202911902104401400055807106102c02462040b80c0020700920f0300240e5605020040c54112441c5c0c800007002c5d02c011103c40c00041c1603031400740c0200300902c0c80d403080c140d1009001d191040c1961008103400c8866126282c81d9501c14401c807801c0b42000b81076008a02ca80d081954500d85110150355103480b0301c540041407603400344451610b201d40c0e5840e00c0c00070b5164032041c04080c2036a0340c9503810201b0000c1a0f80300c10740002170000184003c00720510f000786290890951180098210013074203481d034400040c0e6a01e00035203101c1040300003d0558001410151802100382c00409000c40000420b2118140a2061840c4400303480e1610b01482c000f81102e0fa1039442080c850700900a20000c140c00250514030341c40e05040051366a500050345404003001c40e0b00401c420f42001900c2003007940d103c10000011301494031480c0c550390321242c01d181c01d50000e00481d4001443c1890300c08502d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 689653345 1250 689652095 689652113
    0xd02011104181d060702030703110a021008090304120303141522180f1406010e13051501062106080c010302090d0507080c1345200a060c 60
    0x10802c203607400d00b141201c0fa081c60300b0b1110883d0401c02580000c29034400707068008241a844120311400352600600542c001003401c0e12104902040202d11000110082000c1084801405428070807094140780c914000303016103c40240240414203541c080b69a82000e5200140c421400070724454551074a01c85030340800f43d10781d281900194882c0304a5042d12104203026007200e00501d00b00d03401e03100504241d400416003024450301c550042004101c0104030b40059900417802c41225010740c00e15080c42454003101010707030884070000d60000582e4a4119110800c0343d0030511412000c40014560320301203901c00c1c4114941500b00ca590183c40e58402d900600403188000e1040c0114089503e444ac58111280c010b04141e9201c062803580342d2401d00c168003401003220b901480914041c1002030910380c3c8801d1a49000031035402c200019125080d00c24100460609280081002c2820031074030410042180070908041560504402d003410014107090b102d1a0300c83c10700c80705e20f03503a8401803 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 689654595 1250 689653345 689653361
    0x9030a0b15040603060b040506100f081806070905040f020901020a080703180b090310090f02130608030f07021509101d0a0b1803210d0605120d0201110418 68
    0x8184452084400c19603a83c0310b410f01840c0102000904078002c001030208607200507000318410350503200060700f40b60344001919014582c6150200507034445c24000000200106203544640c000d000402c039545922201410131070304100c1e4140b003101d0014100034201d00c00d00404500503003001507010040346070040100411480b0f0b18111110080000f01e0b44051045a00403180c0d0341d40005006c8121310b41008800c9000461440c100040c1c80c169403000b2a02c4200c59009028402e10700006011200780d07070106000740b2415068966071409014641e03115445004101e10481d282004280c6414003030040d2030351054043d046458030420174400f95112052140f00fa480038494401102c900d071910b0040000920184149035180c00c2c201940300d070703050401103155009500c00c84040d200340300581d180d11a09881c1030071450343c4020101000d80079080740d80207141c101c1c0482100611105001420030420803166000300285000300e08074810a2040d445200e2040c16001191a0404000e6104140c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 689655845 1250 689654595 689654611
    0x6090e130203070e091501120f030c020319140304030302071a0705120d1a010503070e030f01050c041a0406020304050f030f0d1d01020a050307120c050322050609030a0b 74
    0x14000c610780e000a1509032182c010601d8007481d03006011807100104220042034100d401c3c412502e40c107024211700c3c40c10350b402d8041c19500040007240b003814010042c44844a402170152071400082e2041800d0400b4491412243e042c460038030304040e60004130680b000c0d03907032640c040c102c50f0b850a0500c0e030016601613503c07420400d0401a80300080d1080040804c001c9000388500e40fa682d06132030882c2100e158105081d1000d400e0500040b6980c1c0c044212941300c00c490501c0400035003d54042840d2424030700c80e241042d8030300340a2000100120000e4412520210081e84051b110004c445001e8002d900c24580541d00620060050b441c3c40d10011801290140c202c500c0846860107252504906e00c140707802184150042201004070894030381a480d9080c001410f04100c290385e07007075492251700c10207000c4411500c84004100d00c1401c40068039a0844112030301c43e0003a5290040544c4ca0500a419103030302c2c5c9500160b43c1c2098420b071962004020301520591001f41c8510298040c001c00c440 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 689657095 1250 689655845 689655871
    0x7060e0f011a1c050604020405180613061d071206020f030a05070210090203151003171c090206070b0702160303030204081002041224020c03120c0406090e 68
    0x3012030000d2082e0020540895642c203a9100e10758280454110305840c2d5803883c900701c103002c001244002409031b40081e41a1070004480e40d50751015240080c19400b511018054032040c0210b0681024815100781e0103144e04100300d050349031490444003501c407000c4d007980d00211820041c03429840c0c1d61341410782c0583c0c0f01629103907610100e00001e038030481d180c00d6243e6941c424081c08503410000442e103003940d030300100704c01d907404d40001c2d41c0c07065410f65041c14502c2c00c10000300d40c011850030010046a0014040140c00c0d020241d9420a07002110194000f0a6400701e20b01c4070511400b030940d02d1034000c0c040b14580103550300c1d820840d0304010b050708294031441d0030780e503174007008020482c0086000b590016284d90408401d0360401c2c000d03448850b4840d00502046c0520820f5084840308e00340e1040aa10040d50740440b000c02c9050340c0418035504c1072010646405070403001c002403103000108a1a4640c603a102c14410b040d40c015030040500044d5001c10610402e04112507841e000300402d80c801d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 689658345 1250 689657095 689657113
    0x922030e0616050c06040b0f070c1203170603010c0c030305040309080f16090209010207153f060b0a030e0f0d020d090819122d02070e0c07060e 63
    0x3141c4558040241c0c0008111441242010310001348400607244504641c0301d450f25290241012246c05603036486c01d060b0340b0020b800010801c1c0149164010205000e100e0403089481c240501541401441d070b14884c000140041c02074034040c8103503101c08400f52504409200c098600701c0c001c1000030020ac051050316107000c030340c121080108072a4288040020040b0070090b0248460b00103059001440c282d00501c04690540e8001c101041510401442c4500c00e001226080790726040107204185074010480d10f04c0e203c070b0003010710454103d21125004140c0c01c1e140340003078121403a5104000400302c042c45143c0003d8440d4018009842806007100c03800180400c54500304116580d80d40c0c0542d11566882080c50f40004c0c0e11002009884090242014101c1241504294504000340348094403488103600a0059866205035a15240c40d121388045079940d02c5103103100303000400090700c0354120019080b03104043e86841001d902e00f5040c1090420756944d0050303c5810080d8859008604807 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 689659595 1250 689658345 689658349
    0x70f050d060b03011d06090f04021809010902040c1701030b0604060801110a020706090f0b0714061801050a02090d060e210307030b09040210110c1008010f050922030e 73
    0x41d84041e204110388203589515200306014015001c2d540120311210303190070400780340d40d44001d01e58814510043c00c1c140e642c82d880000d4140216142e1904540103802c10310410320415801011054425a0704001c0d41c0c010360703016510480e40900e00714500b110240140005441400c44036000140a4001f040c15500c0308202400c0d140d011500d0b10b150783c004142c1da10059030420207a001440d076401c01c101d0711070410584511040440c043c00c8095600002e60781d08110040440401c007480400c19907103d81080d0104980c3c0751080f100c0c442840d0b0a0001040c0240e845100303c030f80e800c1c0000c6c42c0d00041c4e86d1542d01c0902420020540c1b890700d005014010720f6400c107081d001892003000c68500d9580f0315100001500710b40040b82041e0050302c5000400c4016180c40180b01c0d1544031a0800703100c0f0100c110b0803030b890625000340040d04a074900c4204a04140c0003c0c900d4140d8804800605403d0b445106201e80050121003290380100d60107403900202c810b0340820203d4902030702c0c002040c0d42601d00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 689660845 1250 689659595 689659601
    0x32a062412030915030f0f0103030f18030f0b07090603150501180e0c0705150f0703021813090c09090309381c0507120c050c0f0f060717070f050d 64
    0x4d903080c4107480000400140c1103521081a501240e92000040315504580b0700a290242801e199000d101c1c1c503154060550340303240e00c004000d640c4910410101c000300c4c600140500d030240c0340c00010884030302e00420380038003038080d0381002d03a101c0010701c410510b4200115660600d07012031644842034000e012031643c0050782024420809c0d811040e507a40400c0c80c2c40c900c0c11560921462041c1509024040d4192406c0242504200c15190160b262650f403a0100e00580e59040040c1c0e000b40d81d801030f040340038031a4102200f054040c0003200d060700d42d1094410183d0b01c450400400061051900b0300000302e00210072641c0703005107141c0952205d00041208086000344204800d002c002040d08607806101034100340460040a6040c070072800c0020019000c444904102044251200c1d411020180714105403032580f4061021511444402c50341c0c40d4a90f1a2040300303230110702a080c002040319000703c0c5200c13045074208400c0810f595460304100c5059410ba00d0200820000300216500340799140 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 689662095 1250 689660845 689660869
    0x120303010b03040510020705030406080c120406050603010c09080303040206130816030b0c13090507030216121e0c0305091203071a1008030702090405032a0624120309 73
    0x440c880395030f0704107410118038212a5114100d0403a004201910010354040142d9085845a00b0720740aa07843d98001c514041c000c00040881d079400300020031007840440d411031070086100394001c00926281e414115055450b82c05104c0381903008001141c0181020700c014a880e02420309d91541e40c07500c48812034180000d450b09801c9a40040205000740440a05000d4102180401d102d181003215400c07442d410f03044d48503c01e25181c1c0d460020300c0b818000c0c1c048900c45000010521346034151132a003100100724001a040005910702030591202c6443c082124040c007041d1038510030141d05070380485450b88810030301c2d90403040c0605858410740041024050442c4681e80905082d40804589010120010403c80c10b07002c812074200b08110003c01143c02854050720714207869030719810800e01d98403641510025404010683e440c2110840c83c5220046002105607049502c0c0e48844044d80c5a00c03800c0c1608100c00343c50307100101c0c0350042c24102c0741a003c000b03690a0801c000c0004a8402c400c0d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 689663345 1250 689662095 689662109
    0x32f09040803040204060902030106020616020c040c0503221e03090e070f0e0102030f18041107050d090504050709060f12110d0b0a150c0305070209040818030604030206130212030301 80
    0x2000f030008616182c0031b014058500c1d55411411913140c040b00030355480020b48610b020401d22401048054401e00c46101c0c64107019106110fa4402e1080050160384122400f08503140c0d0340e00341a0310b8210900c1520f00707940d0400c0c103214400d004c4013480b040c4104103400840c20f002030200f0000705468a29103072449901c0d65110421a202ca040b030140180025000c1541150400c21075101440c58001c16942026101200c2d20f9001400d50041802000e69201030200820040b0b0305604001c0005070180c03082030795582b800403c1e60b07204141303c00d540003900c912021904a60041c0702d21841030800a80c198102e14240b485002411200c50455080007540e02e064040017800c65000c1c9034500900396515019181014218600305c0301180d03080d001d45030a030070011a20450428548a102512244d0341c004005102c2414107181450030342d804aa0201d024080c0000040c10034030340828081d11464041d0081c000c80ea0741d8140000700e042e2020012603100047c50180c0800c0c0e03034100003950107030040c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 689664595 1250 689663345 689663347
    0xf060f160f050c01020f1c1202180a08060105010806090702100f0b180f011707090e03040e0718061b061a36220501090309050307032f090408 62
    0x224209141083c84422002d4199406001c100d403580000088207001c850b0380103c500141020702c0b038200c9200ba04030104020450010490f4598403421100a5140c8002110340b103800f44c0da079030b03c015100d040034403805020503001c0000035480e060a9070f400e580300e2403903c1543d03d80c09205000c2021900d68050444100741d603901540320504002c900313001a68201c4400301c1c10b925190485c091414014042c9184030140f09000c0d44034080204a130a002d051482c40c00e101c0c022002e03618035034a03042403050b20324468251f0301090f00c02d4081c005038960122100e0115192504003c2c00303840b10f5210721b05510200209500341000308025104441d5043c05462106032040c440d070080106010310504c0140b18041b440e800034120114000c0080302d6003c0440b03914003503a94508080c180307c04100b544820510300a4194820002c0c1035001c2c003032152181d12101070590310f071018969100203900000384200521007400803004881120341034240f20100303c078808075021001280758210140c03021605024 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 689665845 1250 689664595 689664623
    0x230a030906151a070506041101020717010911100e0103110d290328030207050619230f2a0a031b0b19110412060b0406050f060f16 57
    0x208092215040f0007050040030f05104490311281d03110080030300001d2201c2442951403580ba4024040340e4010800c0034111001102501c0580d40a050882800c999980300303002d0100c0c051038401c114100c00000c5903102c41120300480300650082064442140c500300c02401410100c00d000d000e05a8464581c820341001c2c200b1440c0d6003150b140441015900c030790801c2c00d511004511840602d510340b4009451005440381030b00b804d030308201d0944c20840d04141c00085405102c56203002140910006135641c1c481120f0b030440010000f44000700c612901002000302d0304041e40201c0142031455608800903400300b00328041c1b10251a80060114500c0d04128022000d01d41c0040c15110407540c019803c0078001c0d03156540c0358403c10014444c0c400d5003c01389220420109a0384029510340b44000c00668442c0c445c250f03820000000d400443c0c00500303200110000341050f0040d8400c40d00041e04091000c6c1c1000304010058100c6003080c01e00641c00d1041507a100d01a984084140d4015030248818034 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 689667095 1250 689665845 689665859
    0xc140309030c1006031713211a0910020d150806160302040e010b0c0a05010903080613091e1425090b0907030c12090c15230a03090615 59
    0x100200340d0094216260010400c0400d19003081406c46000700e0f0766542e40c1c0c4200c108069400506508240340c071403201c1c0c021000002403411105000d9000384010180800340044c08039031081e0407160300b40d081d0400300c5681c420f90340c1a00640031142c000840441c0d4440a180c112036003030079580c4030000e1544140180900001404502103400020b45425480c2030308102c1200340c3c43c2410310482032020030000b070508007803409200c1d2030303016036100c40240401c0826050023020344c0c0c01500c9281c4140010701c10b01440705500e1255400c2076900c0044c1080400c2900d0b4824400c0f61810002d03034900c02c0d030a1400350b50410602003809550310f90460810000380551006482c80d20315002151402d151084030f0025036100351b4560780c050b040e07103130200720b072841a9001c480d0800508071070f54040e4100701100081044a0007010301303490700101e500c400791002d0b0030102c48000010740d01d03071141d040030100c032400d022401c0d000780341100c0f090801043c00030081c2e94081c21512500003902e00c0781e0482d08148011 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 689668345 1250 689667095 689667103
    0xa09030306081b130209040f0905010c17042006070302030d0b0d020f0f0604050a03061e060617060118060c05010b03030c100504020f04090822180c140309030c 70
    0x68104000180402c0e4440e19030b03401d06424021010b880b03140c0c125592008288184c044030910300d07010300280082064000012302400c0f071210308450b1755003030a9180344260b200d40000205056011210082c40d140c0d500c0300e0b03403000c0e030320100113544412000307418031651602c9000b0400d66100f1750080d50303102d01c60050310f000c4910b0b244841d4030941c203000d01c5034056910b01f25a0701c11440c0c100caa60018072984400200607110700d03800709030844100f07071000017880150350200c0d10912034010214100b40820403c40100d4425000c0d90300402c131015004e41d280c0024074103403584490107043c0b64000a0343d9072a000020b1200b640040d00041c07242036130b141002401e004004088000b58019410070400e00412a1030f0341c202c1c0425941980c0c0c0e4070024041d0f641d4055085200f2002410802c880c00c09410303c005240e20041c0c0d500d0103100c25080c006410400401043c080781c0c1d14240f181120082c00e003c29018020f4034444034100400054100700700503160b001180500c1001009564400b8020856410 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 689669595 1250 689668345 689668349
    0x1a0c06040510050702150a1815140c090607150207051615020d020c1207031218080304030c050904020d12091a0f03130c03080d060906090509120315090a09030306 71
    0x4642203041080c0a4102841c000c1350011601c803000320301121400c1d190f0140d000200805001c082e00751032000540704272940910a420010100c04819503240980034000c4d10072044400d40210040100b000442d038030b2420940d50140c5d10a015140260a496840ca4005090038840c0c0350450500100140311004000700002d40d400d001414402e00403200294036001c1881401e8000c9680300d5401000e07900601614001e19440a80c00d0103aa01100c801007090798250380700403540b8039100d0049602c400000985003145c3c0d2102003a5040d40c00d102c180b1200c200042c00403030300407840e40c001c20000f40c1500d0006c0600364407503441020240c980020000c01e44c2d10b2041c100c0f000c441c20004164005140ba0450340d20040c2c0d002511660342c46132a08451a20a550025080c2c0401107482090941d240d0850012101420414800070b0746a82095007202d2050781d0302001030340948580e90760105164040e55102d004448039002200f07204010481c407001c00c4804564440c0d5809a00e401c040d01480381c040 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 689670845 1250 689669595 689669597
    0x1e0509060f0306041103030417060906060307083031081b210606040609050c07150b04061205010606020a0b0a110f07060f1b091a0c060405100507 64
    0x41407020075070210b034451034081c102405600050f848444c0c0340d24204129801000208000300070100910010380c0ca806d4165070300d518600920010039041e1800203113107019141e081000c2c0201c41540d42580c5488811004020107196880f4401c01e9040d016a019004034070b40303a4a04484500c005040800503a5240342c085402c2d080c0074010700691000055411208980300d80701d40c41c0510f8600010302c0425080c0d900c10600e242c000c0d00f02d02181002c5800b80c050001603070240071003602c840c034802c15124103c480c040111000d100c52004900e8050102c1c203034003090940028003814240100701911000c1d080178a6241c48000b1050030840240301e00d00091000780b011f0400c080301e590310315481020251024440c0c0c0d4441121618000d228004c0f224071541841d1103a560750030700c0c0b411402505103440b08100941c9840124203060f2400ea06450541413143e55204115043c0000c4400d99407401c00e10811713048080c00051407600003001000d025502800c0203004440d5040301100c1a43d100900c068 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 689672095 1250 689670845 689670859
    0x601020a0c1e061e05030a090519110102120a1206051f0e03071d04080c070f03030215010506030112060e01020a0305040210092301020a02150a1205010f0e040503041e050906 76
    0x82030422400004000c00070152600c1c1c0d9403611551034140223400200d201504c0390054043c4400310429101d126204103114000305a18400303890b0059031155000d0f6542040081c0421010180d24841e003e5140e1411403060001210340d182d002207941484803406181080c0843d21000480c290000c95249140c1c00480041006505001c00b48000100345c0106c00a091000c10219041103020340540340d81d0480c040c100c50300d190340c581c8484a45082c510080d400f60040d04041d90964100d4000207050b208007500003461070746001a101d042900f42d14040c2c407080d90701e41088034101c1007030000b418000e026660100b1142440e00402090141c0f0702c40c400c2c140240c1c4001085884001c3c0e8119812018411042080008000041c0d041c1103400d20025032005102c00f240d8002100503014001c011000d0b0f17034201803c42454100c03421120207004845090680030b01c00c1092030743c00d001e21030344184181e0680c1d052903a42c50f03442000c8048e80441003405544483c040c446030070a124141d80c4400105e401c1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 689673345 1250 689672095 689672117
    0x1f050601051308060603010b2e0c060903211a06030a060803040f060e01050406210906020c061501261b0a03090b1311040e030405030f0a020f010906170601020a0c1e06 73
    0x5640c1c481c0c0440c271148280584402003004444c0911101514140c00c050301303210300d00c05498000d005202140e900346a040e00c81c03607a1205240140700e05090038107500c007001d07603041d40e100420100d504010040302e03070035840f264042407502051001c0e02c01400f4016a840c0c0f078500701b880c09001000e0803552181004400d001c1003048560050784031900180b16030780035180040300b200f010301401a100c000b800c00c0d40009504101c00f040000c032688a0140144024268609031004440003019a5130306544146180c40e01a02a00c0078101e01da00429514030b8140003a041c0001e52545e600a2074038440460ba83e40c0800c420301504011030759004070300c0e07000900341c180c2540d0b41d540d000d11182d5244c0d008980d1035145180d01d880c1041110b0180400604a483c0e402c0d4056449a891a0f400002c0303010355030311010441c040d40148011015242036403947c081d10640b035000d43c02040c10042600b411071088071250b502291007a00420050039a00c1c0c054200c44032108000c107203014a51f030014042001400d08 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 689674595 1250 689673345 689673379
    0x303040b010b0c030702041103190204050109062d0225230102010e030d0209210604020d170a081f030507051012020f030601111f050601051308060603010b 68
    0xc0c050544031510422915000300400700d0340746004001009401a01d0160540003074010880a58400d00c9004542507030b1490b044d0304042607008510445010511119003404050b004049a44080503001da503400e03940c1c2072111b4002402842a00000035030010306035041c42e83c03096800035500212019404900c01e140407206010041c10310400091044400c03a600c41340c4c2e100f1b400200641001508907612000c540c01d07250000e501c010406886418101750440d0a16141c000443c83c4078008400383c0300070f9459400307100034259165411204038120003e641181703a40b400c05448880000d0395909424a0b150a041000012099032449480c05071501000041c070300041090569005031a414618002c2c0203007551341c001c50382050800c203800400c03820001c4910002031841402c1c00d98445804204461030350ba15040e2540040e95900043d1041404c10349094100c590000010701d46a898054903001d00c0c03403840030a802c00d54240d00007005002c014035003402003c0140c1d0045601a60307200750011 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 689675845 1250 689674595 689674613
    0x50a0903080f070b0a051603150603110d0513110d0c0303032f0904060501081302300105010609050f0a03060b040e0a05070905010605030f040215090d110909030304 72
    0x40010410400056076000b60528030040d0342c0c019502500440c09420548200009070a00f295400104141d0740c0000e40d41c54030070b014407a200c0e810707219080c400504080c0100d015010100c48090701c20010400441e846050348202c2c0e10500c401c03041050b1029582c40d02a0307080b03850b803400c180704504900c01c00c0007080c4298031040880b41d040c14005a00c1510030b502c48031031707131808940615400006c406002001c03404002041090390848081101c26100c400650300103805564190011039085441401828014550035640400c08a802126405a6840030050000840300500780c0d4460004200e0a5000543e0307001902c82264816100450900442c12440680c0300180c60680c0300c041e180300720340f69503000390801131034502a41c20a03001424510b80e51840e034070031450384e03518040001660a00c65001d0740d020340030607569000ca42d110350b02088848248041d503000426020400550b0a646020f6400010780c4104070000a03204800e04201c4400c800411f104020b400800c2000b001130300140d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 689677095 1250 689675845 689675849
    0x20d1403071712060409060605280b0c1e0102090402210912070201030504060b06040e011406070f0303090c0905090a0b0618060d0809090c040510090b090d02010c0204060f080d050a09 80
    0x45e400190103449820914060085940b0241e00100c6074440c0c0c10003c0703010030580d0302c0500c9100081800039130b41c0004182900c00d00328006015000760101203204091030610741c501286401c00541403c09050001c0d080381d01c031880a003002c81c0007180382407041c0b00b403407841540403000344003619003c2c80c501000d8000b44038115000381010f907250001410410180e0258081e00d01c05007200c1d44840c1c803411081017944080c001d26003001d045420004440ca450011601e1071540103507050a000c849580550140035002000c40300a124001e0102d0940882d01c00c140c8151078181c0148481540d80c01c01c403da000018123441e00a0700c0d00340502d11500300048603103400130026602d2004503001ca003062610703800b401500b41e0303200030208148024800300201610585400305c0b0b040003c1341802400341e44143c01d91207039011314582849002020310344415020465401030408007400c00150340000c080b1000d5401c281c5003842180303010700902d58108500e00da17100c0141046458071010b0790b0b000d0a01c1c540c44c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 689678345 1250 689677095 689677099
    0x906090b01021903200a0f11090f040c03030c210f0f022a01050c03030703020304140a051002130306020d0608010b060c100b04090f030806130204060e0d020d140307171206 75
    0x71740c0070320122610410103400000c0d00f02e074101400c03251900e0141d002542c80d008c0144070b5902c41c00401d8103102c0d03000000740a1070307211100585044c999a003d07904072801f0781050300c1441d00d94070320040a002d140502c1000341c84d02d07070b14000c80c2000d81002401c24612740300d402c821907100c07d101140103d00b203000000c03080ca00350921440300304d072803004031000c2c81481e201d040305010100c1405400c6400d600594080d5200c1d50042103005d4003084c00954a041c054006406603125050322060390b202e9038014241412420030f0a29140e4580d21800e060764007400c501c03404641ea5420402001c1020300c178510011108a40d07051070603044012140c0d81d054075045000201c2d540b026418403d54495000d041c10560004203503c2142d070328240034100d890210740080c040c1e645800100e90040d038074400c44003070760699240c14110350005005c0c00b030303010101c541c2284c003d1032180319030000c03654503007044107120841c0c0f000350740d200303507a1910210448280350200d1051105101d50f07541d41c94003005c0140e00ca001 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 689679595 1250 689678345 689678387
    0x150506030c09032d1c02031204050f0d02070305010b09061003020306010e1305040309270e030d06032a1d07030b120c011b0b01030f0305040906090b01021903 69
    0x301c000000e040c100c442022070b00350b0700100040d5000102180488074401384c46800e40e03040c801c0342c58250240b0810060f051005800030048043c503840c2c42c0d0f601c103400038050021560041c0984003018a802e001640c4000564400442041000400d000358103016105907140c003e0307070a000c8045103031848010071300c0c0c00b8581c002c80080c145174800c000022503203500420940040010200365001030038252002da0020b02c01e40004640c02c814080003181e03900000b45003900c01a408a92180182210745602e00349020402c45418000511b00600c0095402030b40d58480d4401184080041e0b120340005111201e00c4100e000c03c41ea902144d80d140e00e020001810340f0190355100002c80040c552412800c1d131140c41020151008500099500e40c005020380703c4d40c440c00c5d0840c017181c264682d00b404c02015081e50100600004070f1359481040e0303041c4242822800c0035100d000c80781c20742e00e0f00d0304840105642c844410806603410000d65226210082003a10300d00324076100104014400301d0b05010b0049 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 689680845 1250 689679595 689679607
    0xc090608091002030103110f0a0e0a0213080a030e18040206190e120d0e010e0603060103182117040b011403070e0a0906110c0705130e0a0c0801150506030c 68
    0x6420301c15000b02980e0b989046503039607102c1c03405d4400c441540303002502809981c0e020861506006038240281d45a81c11041103070741d511400b241c046d41c04000603003102400b9100004a900c020004855203a04c25100d00001101120920201c80c03400300780f200103940d0200a000c00b40e1502c804446803c516409400d606083c0040181c44024207182c160b90000c0c82e00c038419143c0d0303002152061064403543d0340d40002508101c01125550500034940d94400e5040000c40c20640c00795010702560700c41a510007011030310b00e44034142c3c0b50f4049030f40b41e66002c44401d2203e1005901284501200b8100c10140c152814907817120a1900414042c40c04c1e01c200c4100420b405c0d035010400c03880107202242802d5442d1a1078900d0358007610480d0300481e0180e04250b51070311580c1c800001e403169445000d00401256140c1070030012452000810304011a0380c0c4e55540c2035020003440207400084c001c004030007105182ca000d0a0854852002d4455484070000092140742d80305003c480c1c02110b403120640e01e501c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 689682095 1250 689680845 689680861
    0x304140d060e030a091404020705190309031a0a1103070219111905030705060901020d05030c1b010507020606040b0a031103071d1b0405010e061305040f140108010c090608 75
    0x312040d03014501c140f101066056000d0740c06880c1d44281c640704400c0490b00204d420501c800c2e40244030000300b650708254007046604180300b07264110503000c3c0c90a80e284941d039460b0381c080c01520080f0105ca954000c4204800d50529000d600900b2401083c91032451030031400094503040d00d9055030304c6804e50f0b01015410311023202c60301c1440ca1300042c0310400c10011103601074000d01003882450701900030b500c4001405e20740f044c15035503c0c0106030041c222050001000300c546500040c84640007040a01c80d4100e03600d1042005816106030200004103814a41d002a2411800500e2244500d040051011040d200c60700010203c03a4480d180340b140500010019081040d030303400c0102000446081c0342141680701040a004550f0090400810a454088900c0d544564000c44c4c0c04245941d0700300b61641001c0d0001d0012102c004402c00815464800240503602020009080c10b0388170301c40d071612204010a0107006020383c4008100c03100d0f072102d0140c00714141d481544107006880c2c002400c88 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 689683345 1250 689682095 689682101
    0x20a0f140a0501110a1106010803030c03190f02070303240b250b1006030e0c0d02030a0203100b01090f030510090309090c05120c0a0903080c2104030203010b030304140d06 75
    0xc03950090091080c4d00c0352800b500c1c4a40c000c5010400054080b0b00190310002e00856400c1c180e071040000340d4955518945074424a03440680840040310300e00c40c08952200c075620603401c030684142805a82d841e15801c00406071500c034404035900c3d0340c01c0180300c1c1100d210114107204a0b901c01150039190540000d62240381c183c000c240601c04140c0443e414100044001151b00c100448492188140c0d111202241111000101080780754020b44018001d803030035208084540e40700604039140e070310300d96000c41c0c2000c060300024440192507000c85001580c008014001624407282e103402401d20316152280c1c1c60458900f02e481c01c5a80c1d4209000b45841100358001a004204060020203043c010051503680490041075844440c1004281d00610000480d503107804255110740c240c60a42e1500e034415806159000301c00d10641c18201c207400001400c06009440980c2c00b5070f01e85203140141401c1d190311210640c40703a0002c001c184911180e24500804103802078031805184c0741c00789402001 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 689684595 1250 689683345 689683363
    0x1091503020411040e0901150608090d0c0213140702010606030b030a0b06010e1021020406020d0809010e0706020604110f030a140c0604030b070e040b1018050603011d0106020a0f14 79
    0x4903040d68030030046c2c0f4082c15042500b61283d814041c94186e90369800807628614259a04005a0060201612007034494590015000e000810300c00c0d800d80c14050010440d8610543d03221340d842e1440411a620b074082c440c2e880184404c2c01c042c0807540d15600066140d8a018900901c51340c0c42c5400301d5040e91040460b1041c2000282668000c1c90b4080005425035450a0540c14011400b4503841c40c1204280242c4040700c40980003070290341d0112005440a04008142807100c0d03507900e202a0b104102006050003d007550313000380c41c0c1801d041c1802400640d160301c10b140030740c400448140d1251000202c5481440d0020501140410038006c040d0510014002441d40307c0c0011402000388006800c680d401042d0644540314200b080c203042c80300355120400501c0c1d000a001e038243c0d080074041d46072801c007a5540307005050f80300d03100c00005066801c2a003086100c182640d4000315a039440030049405050a400101903100a6640d08006074a03440c100406451030103a071114030280410074241 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 689685845 1250 689684595 689684609
    0x3091516120c05060c190c02030c060d090b09030403030203040509220b1905040b0a0b0301090c0e16320d0c0e03151905041a070503010e0109150302041104 68
    0x404240d00380c00410040e0b44820585481c042c0b4030118034100d6940d01207405030f40340182540080a003070001503880c080da05030700380c0e014061000036001d1642c90742c00a08032502d080f07000150002c4141480d9081010083c0151080e520401080c070110f07800006071411554100c50085155580c40030400c2042e203080142900d03000d45e080f4040c20040c8944a007440f031071742c40100b00f240d8503401c2c5142050716130907a40a4200201034010070118040e0303800030340b4507400c080d00124401001e580d464181640642c400b40c40305940c0710520400344882103040180002078984068002c9003204900401418201304010005410312a02d503d103111030144c80743c642980e4030800c2a00103904010705a00520703da00c40c428020380c0043c0012188995045c1d02400c0b070b0082e07107208011908004401810050300641e0301d1105a11918401d504000c3c40031f10543c0c0e02d0f070741d09859500d000340c400700615043e004414060304060414001206001c58901125011070780841d82281500050402e8032031500100 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 689687095 1250 689685845 689685863
    0x90304090c12020c100b060a09060f14030f2e21051b01090b1e0c0a080409090201030c0309030f080709090f020418020a1b021314041403091516 63
    0x500e13031000400c4581d500b60301c002c801d000303400314a004c00581e0b02c9050f500d800418410384090207140c0c4240c800401c4600c0320b007041000030400035102d50b61508200c41d440c07010000700f405c1107081120504074001000d007400701c4411490303940140c4440c25109004101e50754803c0141c84812102e1007452600311604102611000035008001941404a4014032408503680f04000101402054200c03040c840540038071450310000b0070008004c1c0da0209400c02c400c3d1250701d81c4100440d003014001c0000701581d42d00020003450620001d0292801702502d0420706107091103100c082034014030781140e028142c0c0b801c45684c0c1d4039150300344c5501919030040c1700305500e006003000b007050466008000b554072800c4040308075400c3c2d01188050b44110304030040000c41c00201c91005241880644130b81920041405c21140c0c4080406070480720300b1880c40e0030081d0000705200034005074040b800008040800507524003415407001c40c4004203020b143c1e10700ca000024410014442c1403080c40540d540c041056 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 689688345 1250 689687095 689687107
    0x1509080a080f2106030d0915030509010f020408031e0a0c080a031407021e010204050d15060806070801031a06011b030309122006091002030a0b0904060c090509090304090c1202 77
    0x409a95101255460f004e441b54102074003825000340042d00450b000103245440840703111204070064000078110106035902e841034213a496206001500241062200454072050803048c1e100b81960700380300002c40c042d8204140368106a0051000380a41e8008010720b0f40c92a0303800080f0001c014501e0303010010b103042d0f020b00410550105464075501408110351610b40000c1c20814200d20503841219409503500d44c1701c20008a04403919000701c205500000761003503a8070350860400004840c1840003540c40c10050080190544844800241010414159140400028002e90b0300030a01c3d4030a070b16030b203012008041c030981005030307240c0c0d12140100d8110f500c000c010303100000010041c04140001c120b01044c103100003621034480c18849004224030000c09002000960002c1e080c4d0104940340c1c1039003aa41d8a90b00401c50003035115800000d42000c44507070080280b503550304010b109800d060b05001c40c580c8000180c07400c0d6010404005081c0c04805400c0c0d41c080400c00d0012039040c00842c0d4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 689689595 1250 689688345 689688397
    0x1704050105011a1306110a0b161b0c03170d02211807030318090c1101111303060e191b05010c21271509080a080f 50
    0x56030403961a100030141405510050183c180030f0f04c4282c840c803c24000b01004101d1207a080585d0082a10040d85c039900100d44036a40740071001c0f030300c5400707040008801c035001d60303032210b01c29103840d040baa0303149050205555034000b0070800744005800d00300000e0740c0503042c252076012038034400713a554821951007c4205a000002c214484044107504011000810ba1b8503002411b00002c112000600003203810356805a0300d0018401e21180070303145040c0301151100c80303032040e00d20017038544c4c490040c650307040141242915070246041c600302e0f9060081818030a0107800c40800c0e00e511060106501c240100700300d19004446143d10711030150004a40103200401c1e900340740c0d102c070394038800500d16211001076405400030b02d030051451055440e030f40c06010f00e403400c5405003801c0d883c1802c9483d02c0801c20324004100001c0c234280d40b13440350004000940302c248031200c408035a8249172a0701441d0801c1e05480702903a19001e045c1d01c5000482d0072486800030200c0c0c80c10110040c22490701204001 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 689690845 1250 689689595 689689601
    0x1030f0204030c03110904020918071a1b071404090602070f0305070c0902030402060706050603070506030a2901020a081e120106020105071d1e04020a0513060903050c010f17040501 79
    0x2c020b8489081181c00502c586c14a0843e4610442d0082c2c061490382e100e00d141c44042080341c2008516600039003101058490b01c500420090a0666401c1601c4034254405020844a00b039003207000382e4030100d41040349020320307206800805012078000400c500c03981040e00291240c50700080c282805290304c0c0040503044405016034030300604140c0010340e1110000c104a01c016280654884004d01c00b050000e100d80d00000e0784164050160740c006542e9001090081c2c10541e400c0404a072548100300f04081c4403200218003041840100e10702c0300c2d003500043e444003d16070300602000c000040b03481503a00001c8210f81401c99800100c1d036281480310315540009000e0003000015400c003c0480e070364521404400252030505001c03403860a04400801100c1c191203203120901006001079804c0d0780d920351020b8100c281c901d0300c1d000d070350381c00d0640080301d4400c45800401c10310108031000c0c40494000101051907040030b00702500c002c3c10422090f11002c5820b00032242c001c011608100070090190 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 689692095 1250 689690845 689690849
    0x507060f0204030c0807080c15070c03030201020d0c03051b0c150423030702011e0908120307030b0d08030f07050403050a060c0e010306050603062710081011090f01030f0204030c 78
    0x4c4400700d860761180d084035101c001c14480c0d404540d0042102d041c091400d00ca080c0b031501003d0242900d043c87d00d680e0a0700b1896142c3c4180e0150b58040f4121581441c02c0c0201496003085240030021407401d0030035469000c2100440e4000240f0110300c0440c0d40b42d08211326410f0801c2403029405e20301d000e1030003210712040040030300c00280b020003080302903540000c180c92480fa416100c6491029000a5070401c0c496013a02c2d640400c100b12a0001d02000e0a12185000d01e044524032580e91038070520180c1550249004140140500100d090208564400396604269400e40b400c1294481d15821281d5004940000d000d5020b1021501c007005640d502048112100f91241240c0c040004015400c03224a44a100d4000c83c040000400528007404121044142400c0e440c80f050464540079400c40710842d4550080100c2070814042241d0030000802c0619201d4828800304030041500482c5000301800316020f41500e12016440d680607400500cc00401c8407000c41d03d46030340f070828500c3c1c52014 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 689693345 1250 689692095 689692103
    0x109030b190f0203061f02030d0f0e060903030103050a030e2e090503030315010c1b0b042d050904050705150901080a090b0708040c05150c0d020a021509010507060f020403 75
    0x1240b4184006620760090783e104d12001401d60307224068005000400c83c0a4016003c04c40c002000900080f22a0384905d03441d42000d0280061201213403003900d85401e9024050900300c1d4410b000410005a0010341c01228941c50701d000c00c1e4034000000811640e43c644101c10308032405055854216050301c41c214042c45201d50f4900482c00d90310000e042d1a4401520300b44464040001080c0165001e198980c4940388180e5160341003044100061f04401019000003031036882c0058100011040d1107603c01030b10403590b240440c04000c1499a620422280c070a80780128110350000c0d003404000e1007214001c08020300305850700b81c0c03103102440b896800001058040385040c00407807040362039441041221640910f8418260311100320a40c2c0e40c81000b0000c80d009400c01e840400c2c991140c05442c2c8030306000801445d125000340e000719060801d00c00300e000455001414400160f91160396248403560109002540c0b4145940100e50320f1281000180030281050703c1400480300380d0f801130088a0203 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 689694595 1250 689693345 689693351
    0x50a0f03050c010f1e021c050a06061202040506180f090c04080118020607061104080f150703050f0f06060705032a160608060a361116020109030b19 65
    0x1d0f030303100400c648000410031040a4221621140c02117203500a2044045254592580d142d901242c4c2055410403502007a00a454440801466400c8010070450f0f8102900540c2098202004500c150050795680142d0078000800c9003e2034076020f001000c50b50300076203806940e20340343c015007007079610034403c40070650310308100005444134807401405801e84c0103000c41c2c07516215458001c0070f400d98a4006007110002c21000a0320f400401100200306a644003402d02030034a180c0900e4080d0004100358281410442004500380c1201c0758181d00440300112800552034030008603405001e0030070010309600c00001e401c1c4c112101c15844a100707a500e014000c0c0701d80042d00707150b40c5401e0084100a100d041d90038007072100c01e0054030351380c2c0e01040107400199407547d9000c0302001c2d084448080d6a441440450b50350461890340c0c1c0c400d1300003014480c00c0c85030722042e00c44810244610b16140b80e0300245510304c4030841e031042012500550f0003290b140498180503460505100012492118680c0303 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 689695845 1250 689694595 689694611
    0xa090b06040c2007080a0c180b010c0215130308040806010b07030c0b0603030d020415030e0f0a02010503060a091d012301050609010903060501060f0207050d1e050a0f03050c01 77
    0x307007901607102040c51680e142c80d280c22076881074042e40ca0300c0e80c4000580e8001c0003004900e0b84401c02c0312210b854012040c4862031132400080c90040007000c0c00e24141c3d01e040000e00099642c116804210381541601ca41400c140c0783c0303a25400502900d01003a0150b00d040600009120342c0a0261080c1c032260030a032851070340c0c3c404d0800d810b4031409000901113808210f034400400e804000300d40d8406000b500307072383c9024400f20600049034880e030000300c20408200c1c0f503540c070301c0c1d80340c454918200d1b40603009206160001030000d540c1c9a00b884024104080007000076040e031200c0d4900d500074211600140907101008081031036480401110612561922000d41c04400c025288481906282030400041d6402d21090110645c0f20040c4581440f0340004000000385113841454000c0c1215501c281e1480f0071068000e08203107030f03a40200d00c10700c1854100f03004900c08020080300b01c80304da160981448480d2410301e0030188004000b0300f80b81c404100c0c00050640060061020294110080203440 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 689697095 1250 689695845 689695849
    0x8070609090507200a060f020d0b030609030d0f0b060406170f011a0d0e0d0f26010618080f070f380d05040c0614040e07051e030a090b06 60
    0x1082142c3c181c0024854481c04000d2030614079207088603284030419180c0086640e1503402c1502e1070202c02c541d8a541c00220144050031901c10010503110445c0505100d080a00390035560740a41089500059603908004402031000e50041c0f20110010300324076142d03592210003074400c44203d00e601000700b0f0500002506907a500c212a4182c40c003004031244c00301c80000500850707070014070810b50469600c2882c14140070f010044020080d4039555044071002801c07000030190849070044c040760000040b900c00340c1121126400741920401d140034500c0a44104007413407080d075598451482400f0300441e07124a98008104502681d81c10000803820030341e120804210441d8021a4901c05035450051903580880200400201380d003d4850300d040c042a146602c081300c405070b60403a8842c0b0301040401126070440390703800b00e00580c00f5040c0d0805140c031400485040380101958100540090f843c07582c26109501c90441e0109250101e0310303441c015440d540201005001030750b005050500288440c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 689698345 1250 689697095 689697101
    0x1b06010b180a0305070b16020913050c0d020d0611041701020405040b060a02030313150213030b0702030910081003060513020a09060b0901050d06051f11010c05030c0304060b0303040807060909 84
    0x483c1c0c007400a05010380740c41032a000c2c6d80c202004001d40403620311002c001507031b9854001da018501c2025040030070003151901c20f1910078100f540a01651280418070301503510b03100c044403e41d802201c00704603085d480c95140d41c1c62003117400c2040300380140c2818198007001540648180c440944082100201000421500e801244608030040c0d0080002685030204120300002c1e581c480e0b4030803980d0200c102001c1090b80c00110713081c4202d416400e400c00a00021013a02900008140083c614104041005c81c005120410000c81030200b2003011401d40ca0301ca1050000450304104c01304840e00709008803001260744910143d110380a00c200c0414aa4038500ca890115440000d10902d0300003030b00c00550792900070140c012643c070303680e090003c2d0544806c1c3c05c0c50034a1382d4540412400e51045080a881ca104000180300b036603242400c0c0c1d08240d50000c040300d1f0000c0114090a8496445180a80c0901a40c5d080a03815010228000074141400600e4205480782c1d6141c1d0103080d500d501c291012 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 689699595 1250 689698345 689698349
    0xe090706031119110c060c0a1b05030607050a020a050d0305061906091502070b030c0702090a021207030e01091b1d0f01030206160602040b0310060e01080a021b06010b180a 75
    0x80d43c1c0c070841c004029000b40c0b0500310354000745050b607211060310b00000785c940c1c011003004480e0f50030004180e002c05c01c0240903078040740aa490300280c260704040c0402c0d52008020443c2060250001d402503590780200848030081d075000d02121140c1048120003005410306a400d54020040c82c200b501207543c4c0d0700c001100340d51041e03551641c0c0604d0a014170340d4000a4003240707400d41c000c00e0404100c1c0e0030000021446621070518180da0b6401c1d40c030501001c0740000300300b400e40fa03105025814a40149441c02da030401c05500e0b010a0408007010407600403c000d1600078003100007040c40d40300c02000c4541e103d04139010781c0400111001101e02b40740d000c3c4803c582d0041c0040303103800184014a011000340002c0480403a2210340c0041d04d079102c1040340c0c0039400c00501180040104070341182e9840001c00509680e00e80940fa0f0b08401c0c1c000b030300c2c054000d1f01c40c0c10703400d8021969260a001c18001c00b08880051001c544083d40e490280900a50000142984000e0030a000305502c2c10801113009c2 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 689700845 1250 689699595 689699617
    0x1091401081b0903160f06020a0c120819080a0b010e180702151807052205040602130914060d0b13080d0903050c2e020c070e0907060311 60
    0x68141d80e0403192030b40540341da00580710121028490801e05440420090707640c01d0a07a100010254240030800003c1a016400b8804560100c0102c800003008500d01108807880701e1080181c0041d03d1030030120b20f00400c0907615440d5000080340d0381c01039210301154002d00c007047e030408c40d90070003c00440b1810340c4c010201d50032500d00e8580e401040c9514183e607a01860501c190303520a5a4a540c41d1f605000036110717501c2842d940c803d2100984000d101070301c0200400c03036071024045a07542010810030302004940307410355510000a814490380d81c04441c102800000c503154070586a4001c4401030030300c6081140d4145d162400034080c2c4c03d0808503c00c809802060710b0851369240322036814003600003035003140d8200040c041c1c42003c4240d4050102e0b010f00c01d88580c1d0b11100742000003417810b200b00d00c20480d482c485482c640380010315800107483c45000d0110241e84d41000c60105403802d08590b00500840b85101c0c10400c0c81c81c000300780700003030710081c3d581408200180d000d9829036005000441c4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 689702095 1250 689700845 689700857
    0x2070f0308010e24130504030f090501021f18050d0f1103042603070609151b050d09110a120b0c030114090601021f02180307140f1302040b04030201091401 68
    0xc0c1615551250120088001085c0b04050030481003080191170f42694210080f0f00500080c00086d41c2103000040135003800e20081803590350a000c800102d00d110041c180c2201c3da6580c0610a071220024100d01864100003141c400e0100b40c02c004051000c0da00d1020001061002d103241c4c550380c0801220704590603401c840b02c3c0c0c0c04518006034600003070308210b0160781c8402c000e00000117559000300c0702220300508100c5030300c07070306940c2c40d109540e54550141e5452042c035440c89200d613080010349940c81a060300c0060f500215146c210505400705006641c03003d5070308400a80b00e080d0f041022402441024044c22544840e403182460b03000a0041c1858003009840c2d880d16414414211580080140704542002030b1408a000d0051a10304480c079035147c0020350342d00c440b000d06a00201c410380581c0102045881d04c0c846009240c00203044600c20070b8070b00e94032200b9076a04c1405003003c14403a2001c641d6145c1e240d864003595401880204d01044000c00001000c00e1007130402e2141c004184c45035 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 689703345 1250 689702095 689702131
    0x3040305061506041701020304031d01170907031a0405010c0c150213031e030807020a0b04080307020705190f211103100f02040e0c030103050d11070902070f0308010e 73
    0x50044101000b0190340c000300c042c40700042c001080742e40c0d801024111400180e807424982001880c40c01c9581e64001000925480c550890b644a0004da61903d0501810304442d181e603d03481d418500203a1010f0444100d10824001c85040440c0c1d03240101e00c40c1c4006c018204040300195407011040b48003a0030340150080341c10000803684c0003044940500310350002c43c0794990b1b0720140c00c0c500380c0d580100800c4c0703640c0303456040507000120642c1080300c0d40001c09502d00c482c0d407506d2605800410040c0815008000f003001e0724020040580640f0000344000503100c0554515801c8680c0c0d481860a26102c0d10070000b90644c400c2a090380030107824ac04000b0850061301c40b00e400044010805401d031140d960108070000062196001351080c6010140e03443d440c18488a1507140050540c0e00400390400040000520014450016103c01d051a41048030b070200c0d0f89040c41391580c4032240040c000a1030108000a001c00044040d02c2511060340360307626030803444021842110341d0403986000c058070b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 689704595 1250 689703345 689703361
    0xd0c021c0c08030a0f020717070606050603010b07030c1a01181b0e060a2c030c0312270303040605190819020d1d1f0506010c060b0d0507031506080304030506 69
    0x458140c984245e42c015103400442c0e07807004074211015065801400e0003251040c03c000e0b650040d1402400d0450f0b036241103505080200f07400f07108040300181030081d950f94610130040b201c101103804881c450340240407580d40e8411401e110503840c205518092608084420703507000c0e0a605d034458445550343c4074050750000c0900601d507120a00b001c003801500c1c444c800b0745c400400a406e04100c105030600200902c2c1c0001d25140c080c1d00e40300548250812241221000103100c10360750b03603402001081020710440003002c0d4080e210140d2494049c0800070780818100d821600900c9140380850103426802c01d000d0084400300000c0d1034112410010b003c02d02c50440746034010f4800040d4140300028402000d1201da144000c1e0381703610981c550495485480c0a44190006445500c84003000741704a00e000c3c00002c2070b010380050010251a0740c0d08840d0300c0341d2034208000c01d12a600c10212400703161a8104600c0f0020000d017510716040c1481008104040c0210944017180d6000006005d02d45480300 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 689705845 1250 689704595 689704601
    0x3070b0f1e1603060602150a1805030c0d0906110c01030c020705030106031a010602030f2b050406150503070b04231005040f1202030d03110d0c021c0c08030a 69
    0x101d145048008815201802500d40000078000e054802502403405501c00300034050301c00c2940441e065410281c00c60750701c1125180c0c455441205c2d480001058140b01b001c4d003200310b10480010300148000b049a244d6450000391081d9034040503100c0640380356840320101c0c0c60407400b9201b644690807601c1104c0386540250840c64405440f801669900e60701d80c00031900b103034a0355100351600d0b0584903d142c0416110b03030125000d81000c1c0702a62401d41c40c86a003100b0762151402c9800300008801c2ca1140c10401c2580c030f24102400900d06000b941058103022003e0071503481d9150020a600c3d05c0000e044c980000c4140854103000626410310b03251100351402d00d1080d0000d0306021044034540384031956040840d448130007180c4c456a440704e00b42450b015000040d81c0014644c008841c84250141c0d50001e00070700e0b142c0c2c06140116455001d00020810b81c000c003103003042500d0400040302642500890241c060700c1800c01a07841a05020900b103c0304140a44040d00c17400c410004200e000420b50 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 689707095 1250 689705845 689705851
    0x30b0103111602190515130611070b0918041401050a02040812030a2c06070c0f02041e020315030c030c010f1115041103011a0a05040b040b0603040c05011103070b0f 72
    0x242d13101a566500c60100e003041e91000c1514501040014030068803000341141c11000d000d440c039002801304400946180e80d07480c130f03000e0700312040c402180484e02d0795140b0b21604903201002c08100b00d50300740b0b4a046480190500748800b1035508260002d01004018400e5804803031240005107416002d017075071380c1810350024000004640d102c0100c108088042c01004114030800c01d2603501c20b003003908840c1e003459005404c150400c800a26502d010403c4c4401ea0a040f03601140c0c0022240e21b0044074807400310f001c0c2c20300c000e00c500200030000c101e044000703880400c42041d0141c848040b0f241c42059198032240d00100d008ca1410b0a04045c040e01c5050441c203440208c00031690500d0b0400703a0341c59610421101281c1c00d81580e40b614200781002e0280141071240c0c3c0000c0200954a000083c2c21091980101401265145001c0c6444d644640120002d402d0280429599003068204203041c0c0c9403a001e96400b040c00a103100d6101e0301d0020803902030782e030403042c00503c030386606030310047c040c4001d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 689708345 1250 689707095 689707129
    0x51c09170105060f0f0307080d0f0207080a050c01050f0d0606050409060902030f010e130f0c170303042004020d021308060c070812061203030a09030e01020a0c0504020a0c08040303030b0103111602 86
    0x9517902180c23084c030030060f400c0c007204991604544502d5030322000745881c0540d003000c1219005000f42c80c1c00180c0015984140d0703482400d00d6030301d62841c900c05800d0b81c0942c00012003000e00340300c400a01c40381c2100c01001621ba01400500180d0f40b50301c024030507132105985242d031808450004001d8a00110010b0b44c00c40c030252000001c1d01d016480d02c0b4401c440281040e5800087c10300b0802c01152020000740481240c8005141946401d8683e0054080464841c042c420044240400d03560b8440d03040720102c40c0e44920840d2100da401180300c0196450340541c000030320076140840d242d60108803da4152982c0301c18070034901440007040c200d10032005007503240c004440a240803246c48050028610510444034009888400d9060042c041070398a00c105066400c40e07601440032803090940d4400340d45058a02683d245042007040f02c0715034040001a000c4103000c1008403c040d0300da0400b400e5110309070390034415480301081d410501d00c141c99108162101c1045c0c00d0005007410000b01d0303040000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 689709595 1250 689708345 689708353
    0xe01090902030a0b010b190c030f0c1e0b0901050f0105060d020a0e0d050d0906030515190801050106020f06060103020a0e090406090b09030904140f01030f051c09170105060f0f03 78
    0x450390b0303829680c1400780c1042d170386030300041f0340801100072a43e1095403103090352070720403040c140b6520301801405401d1189810011042180d105002c43c04032400d01141c4180842009140e0606184582d082c007038810b03034441d500b01804030b443c40c3c54144126040e5803004009034a480c9007810040000c2d40003038040002c0c400c44d110b84280a0340c81b2280a1102800b400c054001452410340c010720700202a0002c1c0c00b1706103098140201120100a44810090141c48403545044a54010021040c169124850fa036082c0000414000e0780802c401d01000c404004480301a180c41c001036081c1d02804c1110400508859014141c40c6841d801d00c1d504103003d1326000070791080c03e855600070243c5c100c40007140c540c0005045803603820715104000d080b02011600c0c640f5400c0035984007911f0b12040c0700241030b110051842100307001c5e003405403d120a2600898002d00013660401a020040e00d120f0002046085901c002154406015403442000c2c020301c401d000c00160400c01a00c00402c110365905442 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 689710845 1250 689709595 689709613
    0x1806021c02150103120315060e150d020a05090901170a060b0d05070b030702150402090a020c1903211a130e01050408030103111203040e0a180b041b0e0109090203 71
    0x2d10191031038041d6015401040c490400c00c503010701510202059840c90002041080241c55484100b0300210322003160024640c044051780c50b0090300554141803846803000030300700700940d0000020004000291101c2c1000eaa85d001d11720540003c007910341110303070005020080041d4040d84040f01a01c0c008200030340c47c1540d07803116850b00900ea0841010544c001090015151701000581407804940c030204c8858982580800d900f0400a421404143e8002c1031640c404d103000d020084480c440c455005104c0d8809080040c9480500410a40502c4028400c0c1d8460342d003502640e4106820b01580b0403000c02c0700d0050080d007218905411000c00d40d210a181400f00e0280100741c0210b02034078445c0d80f00c3d4114141401c0300d8000300c0c0c607030344140070304d000c409540314000c000d0314101d5a0504000e01b0795600c900a00c070160851840c04082e2040400001e020456030911a6004a00903010380c140004101583c5008149a024201c0140d100074010005800c4c41d411120240f4070103001c0d40d290300703 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 689712095 1250 689710845 689710873
    0x70e0d120306090b030102070507140102070512010501180e0309010e030316140d1106010315020403020901030b041a220c0e0708090d0503060a050d051f0c1806021c02 73
    0x11449980800081c2d00d421041041001c1c1d406030240c214400c400071840c0c542e00741d5820b82e54400e180315040c860000302c11b500c0c0c5968000d0010200610380030700f1403c0703407400c1c1802c038500030b2103340106050200000612848080e1500c02c80e50903240400c019440e20001c1c40c01910394109008a1a6242c03108028000c5e0580440c07004848a5100e0ba008071132603000741034503174202101c2448041c100038603c20002d14100d000070ba607a0450f40c10219405600030140c2c0f81002030310480e080a5048a02400000100a088280f00d48a9801000b40200c0c100034101c0004901c0b00030b0700e82010740100119050500031000c01f0307651602d441800c1d100c5c802e590755103005e41e42c3d08084600c1c8001c0780c00002003040300001030040c00940043ca2400920754900040050303100e00c03190086501411000d0000c908010040200600f40140340c10789020744142081d60350701400d0800c00780300c0015039501030b002c0d40c000340c0200b650030f460554001d050b11a54004040f840034a0301c01c4040d045201e4100a0f40c461 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 689713345 1250 689712095 689712113
    0x90f0d060f0e0105010b0f03010303180f0b210c03220c031410050f012d1401120204031101050c0319020a02100e030607030c090302220e0a030503070e0d 67
    0x10461514002c41e400500c007030841c0c02c40f08140c3c01010708460401c010f640060541c0704a9041d45d2385030400c61110102550001e421600e250810b2070009030400e40810300340f207030314050403210300311421200020407250165074600100b610030054004041c4049810303500d11141018003158203104540b965203503501d400340d10020b141c1c82501d0710003407101100c0d030b0450240941151092125002c1c81103090048444203600d0052207220b0310034007140904810b000c0000850307182120303100002c0d44255101c40300e0044e000880e840b2103002c41e458a03015000090140223507000c603a009461148100641c60055641b5405241c4084031400304100314050342046034200440b0113001d034018811094039105008800800c019140d0600841020a1030365070790010f0308aa001c501450b010407024505074059640d48800c0d080254055498545080c150581407a0344206051183c07040c8036184441c2c2565888021400015000410410019400c51300804544e40d03a00d001800700c1514096170b8440c5510 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 689714595 1250 689713345 689713361
    0x10120603060e0607050a020a0b1b070c050a08010c120b0f06070804090b04020424050c010612020f10170606090a08100c210f0204080319080714090f0d06 67
    0x440d55100000b40002004000042d4020142e04060786860b40114001c0e40c0c4286803070009001a50320f0002a805101007a114110000000503072500c440b61440c5c8500c0041d09801554041c24070607000191a1005004042002d0b800741c444c50045801100c80304050469003a15580001c08444010026280d4400510015024840b140e440324107105561040d00e00088205100b1401440144451003043c5040300c00c601400041711003410f0521001d45450080f90030b13546182d40382c40000646030070321050160b0040e201f2038414039043d00f00d104100707003101c4006610f000244107514031810041c0042001d0703003041c8010f10850800841a0004800c5811500070001d103800500b00c030004d445003400b17030010070880f9040202c1043d210000c1c5091496810401c10805074944001000c00440d6504031000782010344192076449040c01c0d042d0301d40429948000001a00c0400001e8815100d0010040180300514a13245040048001c0040d600d1000e000d0302d0b84442603840c4540002c2580c811800 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 689715845 1250 689714595 689714603
    0x12020708071b050915010e040b030303101a120105240304080d050f1605091801030f02150a05030c0d1b030f0c050306030a08070314070309090f0905070510120603 71
    0x50682000a40c50800482650200c2d01540c1c070007061140d0201c001c0d11120442070286400d0700d80b11f040304002809081190342c140d40500000042c070840c03080914030340c070580d601e0f000441200841c20010846500c03c0c2c48800e081070b640200184900e00d0080102c0b1400c1500300c000c061034600920b2014071992007510106c4104600046d144600031440c010b8540c001d02410700080350345048a20003402501e684142c200700000041c0c1c0c076003a0303600d14114411b040071281c0c12654540e16807404c0010110800d03002e921030740e11114a10812a030b00011241801d90583d00e250450711103008044081d000041c24803805900e0302d407060703e04646940c0c070807041101d0350360108421a1740c0c610201203c10b580020410044200100940c41d2800541c0391141a40081c84070368540050034122481d4100000c0110b040c080081d20405141e400000d51080d602d00030302c10001101085841412221842402400c80d0040c107000c00051401040811140b5041e0610701c80807415800c102d01181d01d9a0000ca13 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 689717095 1250 689715845 689715863
    0x30708010611010e0703020114040b07060b0f060720131e0e1b09130b0a0c0207120515040819050c0c091905040f0f120206070801151202070807 63
    0x4540c0c044072800b0200d4070030008102d00711032200903a4691145010181c180b10307140c05000050348030311b41120020140c810080752104164545200030f030003070404480c410f0340d2514120f1f000346401421904400e90003107030120302c00c401c8480800f28a81400c00d01d03500017508071600080750a10f00403c034541d0028420705105007050710f2028216a00507043d04556809a0820403000c03070540c0c0c82c43c4688504a41503c015918140610351881c01032100418101c221002c2c030086406a070009d44611b2500d400343c85001d52200da01c0d0403110710001c8094002d900c9844844070720442c0c0510560840c2c0210308052400e03441240c080d0080c3c18010450740000c00c00620070603040c1003800311030000c10382225240b07100e003001030310001e29038425a140d845441d82c50010034100b064504101c1d0140c1ea00001e10101c84240703080048508002002800240c040c410000303c00610841e4960b042e42c8140b6528105410300395403c0750403004544240d41d03955820845400441c694201419803184500c201c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 689718345 1250 689717095 689717099
    0x1140f091e12030402060f0f13081c0c1511040504061a07031b150209030d140313020102070e0a050115030603021806040f11030709080a0b01050103180803070801 71
    0x1080c508545a1082803080360020807030880100c021a1010900341d49208881d01c1c1d440740d000050140c41040b01610101400281607807041114030060a000920b407020241c68568480d81951120560f59000d0420810f4807200e030541c40c0113501c5100b1a034002c00d03001c40240401c00e007140c1211242e0081c00c0c480d6501060400142c41d150251801505407071380705081e020b4441c03074134a400e405842002028801240c2079003d007208070280310940c09810040b64414003e610800308029405401d030320340240500000c0001550241c8010721050504048503480c1d5a40d4070b0807a041000132401c00c90450244160001c1e00303111482a80e40690210304000070654034142503051550351525071541071600780801040960340d4862003c03640c0d124111801070f2940c030200000c008050200d40345034890704d01846245007080b83c030040c40c42298503407240702105803540c00c00ca984031415000240300070b030078a00600a40d442038103c3d90701540080260030071101e846e610540765401c11903040700000c07000001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 689719595 1250 689718345 689718361
    0x20f014d01060e04030c15060b0a03060b0c070501030f06090e01020a0905120c04091a070c020f04200a020f03031e072d0e0d031107050906130e01140f 66
    0x580510321100400030450b4620740450007002c5a002000a01807004c044c03503400600110070200401004454001c0102e00d03242c624001940e0400b000c0c02c40020700d00407011403400c441c0c00c03c80e0401000d4800500516207404011009402c505428014513500c4020001c1d00030f04d9801008041c12280380056188c1d8181d080080009100e41d110a10504207802ca00e04840b00c041030070f850030f103400e4902080e50012420605c4000c2040344070b8004000c094402c01c01915401241e040d5103901c00c07500350852405520422099660420081c04034130001c241144121690000a1a90701c42a00544a0100f080c00c0424255041107520141004102d100b0025a000e81900070394080098106400440710b00b0041405c8000e03407054148158401d241c42c0a0323080d004200000f00c80b170b8010080c0040e5092860010f0042600d080506464070815501281601e00083c00522402c00076002c480c1c0008629203c0d0094102131400c02c01a5590320350201c400580d0454580c8031300740302216000300c0d01f02444 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 689720845 1250 689719595 689719727
    0xf0405041b08040b0a140403052703030901050d0905070b070b070306151b080a021f0603021f090b0d0b01120921050408060117070b0403020f01 63
    0x110100c05500c05072039082075107030041505904190481c90a90599441d40800c1006150381419405d00d2042002004205030340034000306a182080031001036400801e005140c5110420b40b5102da243d042030103a203629520400c080d01580290100115030904c0544031542010840d400c0644803070400107121081c0071104211a811041616080140d0307482c000d00b0070140710b0180c058404122a4802181450001c00d00b405409a081065a541e03000c0b03024000c0c0d66600070918100060050070702411501d6118400c4034201d9030060440d0020000f84000f0100842e40c4040c55400c1c040d03103000128516180c0c2d0040c290407000040f0019907140301000241c03c1d80308400143d030100e42002c0c6003000080c074418004140c81e15600048000403219071003500c0d60700440c4c010031810304c9107000000300102007210b62070491080d20309680e401c0f600c0d00d00c03000040c4242d01000e500441c8421103040345511400880c0510785410109410502c10117400340485101ca14802015010804010f803482c2c602003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 689722095 1250 689720845 689720861
    0xf040f0f06170403020d050904140a0c17160807090e04030507020a080303100b0f0702030a060b0f060f0a0503180d0e03010b2d030f0f0f0d08010621020904020f040504 73
    0x116100c80ba40b50507034000f5618402200c4e00340c2048030108001c0c0d0151125040640c151450f800d61118038644440410300401500c951030b400640881050100407800124060088440e0000c800c4a2556001c0658070300070050140410010030240014a45d118050510b0055100f640d41d599649002c1c010801004032070b40180905400030010721030040f42d0405c03030f10110f82c1050000c2c0e4a403aa2038800c1245409a03d10207900b60294042d24410081c96074010f50900008403052030040c0c05100038851a8007464070031300d02c070351410000c038503440340500c5c051580326601100c24482c1aa841e1105424402203484d81d002040e0007540001481c0303001c0c01464084901034030303071906045040c0c010440100c150403050310780c2c80100c500300f04252003c0c0b2103030f40001c42a6013158041d03441841220340d24800b203010b441c5a03005560501440318426400039040354050b5891318a0603010308501c048c4c101603c00d030715081d15800c100c0c07400755032150700140046213107503018203840e41c0c0780c203085c0001d40b5201c2c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 689723345 1250 689722095 689722127
    0x312060f0b090d080c0304030b010305010f05010503030703050327030334030902041508030a09060e0603041407181e360b0408040302030d030e060c0f040f0f06 70
    0x221009000940d50441940c0700c040c2c08880303018840c50541001206880340710002c07900c5004c001004010f004003441c00a040303902c5000204107698a41640808495080c041c0a034141c0040002c000802d00c9400655002242280501d100e203059400150900020000b980d005400100801480240e080b100c0850f07041403210b07034100c1c180c0c0c01c9400311020001402c40018036540e1031420b019920740f07610042054445010016040c0e0f103400d0300300e13a20780201c281c1c40001856240c012a216100b9503a5006910000e000c44d410b5494130b0350b8a2914000c895211241c6210724140056200202e034020200e15441d0b410011f0395410520000c0c000602e100b603580350607410900c90102c08040c50100b19448aa100050942c0c000d00f510b10004903401d426000d0310090005040c4001d101481c4001c02c01ca92003103003100c0c56110f8a075410780558001d518034003400e401602c001002d401004c401880740d425613031601740c07401c2d4950100b200b0701c00050b0051300d410601810309200b0f8a03040f1040410305184 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 689724595 1250 689723345 689723369
    0xc0e100f02060c0c15040302070e010803091e04020c15070e0307050d030e061903050f0f090a110303070206071415040809061303020414060103050a0c09031101090e0103031206 77
    0x11080001c0d5071898054000351110200142c00b048212050061181020714241000c1c95400c0c2814000d41c0c5a005000b400ca681c00354900024940e82c00004030340203130101511081241d1681d800861302254012a0355401a80810560112038810f11610b285d00140780d41001c3d482c200004003c2082c49404800e9000360301601c0c0922165a400840b100503590528250481402800c00b2480500034140300f0340030f062003107541c101d000b605908694402c00c40425200883e940c1c0320442c60380880309a486481c81c1d001b100181000c00ca05800c803014070007026041301d00d001320541c040b84031a80704607400e441114a0744540e1882e04000c0c8140034044640c4106980c141c00d0940380d42409104d0092203070703c0740d20000b91a12000c003a00580314025500100204103202254030903180c1524125141e5000a1528000660164003403107410300b000144d9841000b43d9003150383d02c4d45034030a200c06041c1072020003040000d155103040c420b103010b5440307603032401241503030b01c42100141c40542c1c00500c03e03000c0c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 689725845 1250 689724595 689724617
    0x2070615060f0c0807110904060f18030e0904030513090605040c0507150506031e010b0301050c2b090209131110140306040e032205040e03120c0c010c0e10 68
    0x291004a4601480d088404141d88440c98985600a1015030f0010794101f505c0710100014441181e203c48030481c1c0403403046c840d81290300728800002c1048180140400d90400c201030352810711202c01644680b0074242a460110310200c01902d07076542c0c0c0d20000d002500c034502031205044c0750003244212203103400c080741002050b03a03507001c12018600b0940507440d615400a117983e81c0411142da8001c9220454516041c0801f030324034080c1c800c11800c1c43c025801c050220300454864030407689210041461000080000034000403000c00740c8074010821502d444050026a54803501b0b1030052454148003400180207281050390311400c0c2c115140300382001c401c2000d0040e0021a1100c0300f5030b024000b00e036070340d42d1b040024009140d100480b0005109c0410f03100b80d0705003210303661901002035007000041070303588801300070a4072050206074885420500c03401b4616010f81d501e0603006481440c0c0c42c4c0c14030940000c2582181c2c64007a422000625181454000d81003183d003554440102e0f14084a940e9 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 689727095 1250 689725845 689725847
    0x705070e10031223070615030b0a11040305030c1621060c020102220611031804092415090510031403071a010611031201060507020a0902070615060f 65
    0x64603100c050540060510b0300f110301440703502d10400a641029005040e4200c800e000780c1c8680098104480305840c241300441084540c0910304e084030750040c0d2401c3c496440080f60070152220507003564040109010200025405201402036100b02100500716a44054041e00c510b1100790302a4011110178248000111f1668500d41000c9400c07010115a50903458001c900910074a034030b500c0e2000d000715402c041c0c0060240714404940d00740c0d45814948010420141e00c2e485202d1749401e040841c0c80c4204072a003040d400c1130b4440c2d802001005400600c05500e800e07000391950064240640d81c1e600084902c0300040c624014209aa00c01c119030300d44a1001050f00300b6501000d064aa040103140b800f000c0c0800c2203401c11603009021440d801c100f003403c1c04000c942030150300049018195034a403070180010a40706201705d0440a15881d0740380078001d40d135036803052809036006171054202050740750340c6000030200140300d10700000319483d2010b0724481550307940c0c0000c01000012890307071240d2 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 689728345 1250 689727095 689727121
    0x515011407080a12050a0b132309070b04030606090c0f020c01200a03030504020f04180b1e01080606040c0e01171306060e0702150c03040f060e030f0705070e 69
    0xc56000030015510500f03000c3c1503e90140381a4000c858a06040401c0b101c03142d140c1104807446410b803003c40610801d12602d1068440380344040714a00c01710413400c0145074813911342c01d03000a062019180350079201c81c02040a03074450b401c141c030041d84541342002414400d2151414a040b6442c00070100000e85100035190783c2c421840504200340d0b000c40107048900764035002020f4015808440c45d8282510700900035000455040c3c0c803602c502000d00c21241458001d8001c440704000144010400698850300498000780444048d42c00300c041d203000c144101c03404a4085c00d040c1e0010801840e0501c10881a2020500c1800400c40b0019403102c180e40c102c00ca102e8030300294a00c2c00115941c0500030080a201c107040070384510300708a03001940a5840d03044901440c516030071344008000d540c406480214040d216124000f0013040014046a02c055441c03003664415200030603202c1c0c406101d5440c603000301007504e190784400111b101c20880208101001440b43d01d80d02d41142ca040020380400e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 689729595 1250 689728345 689728357
    0x3050706090f0308090a090218031e030a0c03180608041101020a0305030705090d050312060910150c05031b0708012702101806050306043b07080f0105150114 69
    0x2060b0801700350074040c1c1d83c0d0001400040c1c15003903011511803201d81c1512500c0c09030380009502a01070920f80f070301e0b18034480c901e03841c21020f15001141340554282040790304500d00c243c01c0d000c00503d203108039404001c4021200c001e02e40c1355202c24150502d0b040600481d00e2054005056500ca81038010000360480140c075070100850610303e80b1600c2d1500400c5c002e0029490007407142c040001d860768026044031803240200c50a036a4941c035a623801c1140c420a0740e071401040d041d910700e02c0844203028802d00328a806648202e09581c100114826045140818201102000e4101502c1880403000074841e040040311035405149041d000310b0202c1080d200c540e400640030301c8112f04080c5119004200c5c2300b0960800c4030190b1405a982c54000704950019580310f4815030034244404145071402e80d1907822140b450b202d060511003044580d030680000014010300360300508c0b00009031648180f18041e00c11482030b0004c1400d14008038221102c5507443d10050601120312041c0c000120924241d0391 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 689730845 1250 689729595 689729603
    0x40e0c09010f1b2406121e02040219021015061e05071b030201090e0402090f04140f100b030109030807030207080d020c0a0c3002040906020a080103050706090f03 71
    0x440445415a1500f5800c0380405080001018400c1d4200b0b60705001028295400319400c200054031284039000840c0900b2016243c0d0710400740300300d044d01d0064109011140700400052901d403000e03100c148600301c20410740026030040b00c2c06103201c507950f009854124442410008001d4208800600040143c090102051071004c00030300c0301900500c11180c04a40000f140762a8203079106241783c0000303581c0030490000d440d40c0d83c0018116030a40e4140d00642d401003000001755900e909903110441c00a206455a4400c0d4114a00c040c0c007c1c41407241144156026029003052000e162058500003e40c8034040d82c034001400e0042503002c40312540242e070618025035208940e00742a016400344200b50700e415440064243c4546400165503218180b05045c0400c038180d41e0304c842060142d11014000c20026098250003442d1f505c1b903001c4990500c02800014603c0342500c0700380898000c02c043e00003144044006006000c0100048001003480c0c0c500b01000d0f5050200340949680103100041c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 689732095 1250 689730845 689730857
    0x1d0610050a12150216050609070605040e0705090316062003070521040918051e07050121060b03040c12080d091a07091a03090a080a02071802040e0c09010f 68
    0x800c55500f180c04a0740003001d144504a5030201c10304000d82c49140654507158280704040c40011070724080d000f074030f04880c02410795040e107603241c2d5019989984403408456150084100c07004002e404800e15102501642c0c0e120b0940b0700c06a80103c0541540c034440560580c800c0c42114000b9a00241011041d94400501a41000100c06044141c0515001810101c1c188020310000001c202c1110700303994014001c4882011100740b000f400046841205400b58022907401d2125500902c0e298562026101c0d840754076601e80003a410468080b0341003108400c10000510052000b850004d0340680180380f03e038124022503a980304103500c6070030481e0411a13102e00329001802084500020304c465a05241c20040c92b151000030184d2450f0300445840600c0304050140407420241600e1040c1500e900810302c0c150140c8482089400c006250740c00c6225400c00403480030401c010b0f404e94803000c02d0f070261302c5500740501d43d01c5041000700303501c040e01014030500000780e9020781010721036a19401c0c41 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 689733345 1250 689732095 689732123
    0x180b040b1e01170f070f0309020d11030a050304080703110604080601060c02040e03030a14091203040209220f0204050a052503021905090f0105070203150a1d0610050a12 74
    0x40e54126a01992003555042c00f00030415008105007074144140150356802846460704401541250441480a0b400c00700d08208000003810035000811001d40c011708840c1c3c44ac0d0b890f61101d05e154031580208003203411004040081141e161700d810410102102e4641c03c0600f01404503035200341c14459241040070221582044d501d559104030025a4600140c9a503481c0600c401c2010302103510703e41c0d0006281800140680c5400b040500041d80a03550b42451901d50f40c0801c601c852026000c2c000d14070800040410340fa11030f02d0b50001941c481c04550202400d07500400c4200c90f00100303502c42803030070320081060103007282d525141002d401d252a01c0e03001e25580e07002c90090040805444012903441c0c0d0a802d101c0e08507000e03007050141107803258400c1030700100441d001e020b0900029003550201980d040c414502c1010f05a101140610001340b000b540071101038180b200d480d5407080768000d0824442101c01011144000c0c0c5010780782c000c1460320707140c1d05c004019540300024001ca0514500 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 689734595 1250 689733345 689733347
    0x305120712020703051c050601090302060d060801050f071101110d02130f14031c05090112140c04061205040201050d0b06070204050f070f030c09050d150501180b040b1e01 75
    0x3035030720a05400000c540360080703450041d0541d444081d400100c0d10b485640c1c95841e00d840d00440c0c6c4a05011781d25807940601d50382c24405180c114161520100f41c44090200780b028091003070390311a103482c10542541d03040074007010b050482041c241ea03034103034104a074080f01d488280040314101e142d907020041c1d454004c0c2107411000c95058014084990402000080070315168001e11107904085090f0b401c41e21421080c0e0001200405043c4c02145d4103100d024295806400c1030950036005044c0401c0242c1c0200600140741006c8500c090744d040046001c0c000035500c0000c078801c04000950070001401c198002900a01624807685655512000340d030029880e0002910b65065010300140f2041c10401d01e58191000c0407151703880003501c5800d090701118401d004a00c0040600d40b01c4130019424003040c82210207a0610689100015580c80e5032880c2c0244a210b00030640c2c0780712180d11b5070a6800031002d8410800c2024802c604220060950381d46101c010f81f10345028411006000d110340740 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 689735845 1250 689734595 689734607
    0x105090a0f0f06051305010f29120414010905100218091008061003080403060902061b0a020102070611033405010603020a06081512162c010303051207 66
    0xa14829510b0510307000c09510400c40c0c000d80203842c4111040c0144000c04036261044074024803e241008980c60002c0100d0044000801181040c50815003800c00303a0034039149180e4031031a0f41c590300030784e01e03001c0000340556884142059041d080081c4603102c07468686607a1380f100a80034100c03847d400180c1c44100342c07500b070100d601d40b140070341900a036142403000714900c10060321807a4041c1c002c1800096110070395540503070640768054441400d00d810b41d190b540c000c11000b03104070380041040085401070381c01080c030701c000c080110f0000c01050382c06100081c1481a1980b000f0288040070407d40022031000c8145d5884031100014011140c1091044009090703104402854840600b25a08c0030b1000c190071800035a4000c3d030f00d103502d4903950700e421a44588121100d100e44103c02042104901d04002801030200184048909440600c0348118032001541d00c01c2d8011950758040580c40c148403608405a503403500c00c0d04c603096140da00c02074214451001180c00f00d81c81400080e051601500d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 689737095 1250 689735845 689735861
    0x6011202131e2f1c020406050307261812090618180903040e011e060305100e01080d090e0606121e010914100803090607021804050703031808060105090a 67
    0x500c0040c0c00c850f04038041c0940c3d1011200b01440c1042c600500c1c4418018001c64040360b0340b55480e0b03861036a0303e01003118644c0302101644604249241901d13031314040c0d040003d010300b4100320f54400150440c10b00b540b03060350446c0b254002c80e000707115285047d510b6009642c64000c0710054406120f002c000040c110451070b190450030b401e102024095008030010245c81a07510302058102d82c0e9072141d000b1310080d1510446044980b800720000d0040c42d1103a041190840b0118049850030794032051400d0f10300c50241c100341170903800f01501030722165005a080780105000483d0100d00d08100d80401e801340715070034107400c2f50040c20012884503100070709464540e60070140d6002071075071500403c0c40075280101c00580208241e00114800420140241e01280d111100035443c1103910014403c041e00524020b0340d0007a80b44071410400c0c406010a54801c62168024004513400c514016000704c0c3e4150003020a845001c40a10484800040707482c1034800441340b0a080341d4030454030380c1c040c14a030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 689738345 1250 689737095 689737151
    0x15030b06040f091413020603011a09040615091d18280c2c0c040305030d02030601030c050408070501051c0e06060306061002190204060806011202131e 66
    0x1030480081c0c0f9000a40c80b0f800340c151001d10644054031079000d290003407410325802039440b840030001002a1000c9034841240c02045a800c5800d000900000a040380c107280d01103101f094100013000012a03101030000c01900000f1100070f9101c06400c5007808604008000000512001d0000645c41c030003006842d0041e48007031b0f0400085085040000869241d0240895800b170043d00045030f54000d0003564080f45408145003003542415040c00844000042e200665030001004040003140043c0004c1000386c00c1c1250141c1d0300d00305000018119075680f91408104a0700348002c0c00142408203007034040310702c2440d0032500d5204501092a140c0c000e80000c030f4000d03161820015958101150041c41018200c0507500255200d10a11845900c200081c01c01608800060050f14084895410071140041d10004066443c0d40c04140b8018081c1c020545440c16041c80f0300440c942510b003189908161b0809103c000f110100108480c0301c00d40802e42d00c180c0301c4101c0401034400c81d00c500400491 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 689739595 1250 689738345 689738369
    0xe0102040e040627021e0103150f03050c0d020d0f08042112030507050d05250908010c0e0a0306180b010b040314010c021f0e15090c03060115030b0604 66
    0x4a49401c1005062240d40a0f0400084a1040882c18500074074444605d402400007841c200b15000255000b4070f450001034107041e0341e10743c080359041c16010b07490040c21900503030070360345419410010b141c0f01e10910007605c41c0d601036400700c0041c0c580301001c0d5902603214100550820b6070b447d00095500503900188490f038540300901885007950010f0f030800600403c0362301e640d00c0b0407071000c90540c0c104403159808a0010440d104045440740d003c1c59004480449800080d200e070f4818070601c0c0160015540020743c249410f20044200384512070617100542000e81c600305407800031a240c0400c610010b003540b0743c0c0d01002c0c40344542e8180b5140c031082d800003040ca00c03981c66131100c0303009070841d000503500340680618041075154144654059811582c00400500b000d22070408440810141001d1040e0b48800312102c03855000c0001c03002910680036103404078904003803004d18003c02c4510040c460f500c03c400400000c3c03c010684940c0e608285004265016420041102480f4641c080c07803d50f0381c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 689740845 1250 689739595 689739601
    0xe041e08040b1305091302010503060d060207060c1701173c071d010803040e0619080a02010e010206071d0418050a0209010e0c0a0e040906050f0f1609090e0102040e 72
    0x4000b100c0f0b41c00b5240304507203054240e11b030010311110916102c0030003030101e8400c10106009241c6003c041c0c03000c91044c1001f6142c81e85d035988007015624058144400710f02c06205d10408e00b603000071840d0140c80d1140c02101070300d5120600b141c2d078440a001050001c0341400c01121f404042038188510400603004650007149507901c0581d0b40c024500c21588a0400310076508024480d4800540c12900440c000750b0620381001c06c480001c1d03101521140e0f1000c400d00500042d500d1420300c05006100c46405010864400e0002421051424001e00d0454012004101c0b1443d008030403203100441d8510305040849000020030001c0106a8100304a01d050a500908015001500315a6140b0a0702e242402e66680c0807803684500d4285d0740d80c0d91892080c0b1010900b10311601d215401000010004074440030316440f800c1c01c0391020f0f03039103210f036085140400803c20008000c1e01c1d00034641c100c0101988403821401005203000b4080c0c00011034503001444030201d02501500c024040b040000350041c1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 689742095 1250 689740845 689740867
    0x80a09031b080f0d02030913061215060509040206030714160b06120106151803060e060f06060406140d1d031b030f0a0804140609030903070e041e08040b 67
    0x7a400748201003043c45500b02c01d0007840d501265030f1501c6203454004509004183c010803605084403490405181e55603003000681c81808000704a10310b0003840005084502c44202c0801d0369603541140b03029440b14028040140c84032400c8947c080014540011418154181c180051080c9020204144c13111407040062000d4811500d001d064201d80380d91130303070b0214100c01d82a121039104410003030300d4aa90300d20b030803070007010003c2c01c1138001882c60b1243c54580e07803a0003c031031050b150f40c6405c1e84400104446130340c2c00b45d4003075041942224894101031900c80000e1000300c150310422400c40000c40e001000307030200c4d009510201c100e441050040c000744c2d890340760b50b90003426080b580020300d0550054495030120440f94800b00c09141301c0d01d0820914401e480117a00030b0800c449007401d050f40d49114103000d00446000d030f00360300091a911200b880401d864803a403500000b9203454964140300004403140890049540f1008a0b4401a007541c00c0054550180e03600812000e000001c1d040c50b24 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 689743345 1250 689742095 689742143
    0x2e1427010905100f0522031107090c0309030f0e030601060c0f0209072616080702031303030e04110408030442030e030910050c0a0204060e09070b070f080a0903 70
    0x6410300310b20800050b0740e840713070007282402c5c6006c500000810402c12603012a1003104000c05484410048a1000e6501c43c2103004680140c0c22220011755510000800c040d848003883d61882500d00c0c3c1000010710a0001a03201c0ca010301c112418040004c401e00c0801900000744440907070000d0030341e2042d10304010090088588444900b0729a2440544201c000d00c40c0c02006002c0c809020b8841c103025101349082da00008090b003c0c609611040c080e40b201c0b890080070700d0024520980e902e1034514104001e01c0195010040359400d81c150038042448481e1002003910115101000750309280c0d040d4031803541c0740040024003a02c2156240d00309d22089899180300c50003200140c0e4080150043c40060b01d41c8031300403504c0855100d400d00f0144c00320644110043c100510900303050310300a0750160b00050071185c06902c00e0b40100f21a004001c4504420302018008020a03545246411301071f948504040081282c01000c001d40481d138202c1807032140c402c40011f036600a2154041c48400c840340507203 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 689744595 1250 689743345 689743361
    0x103201210080307053007050d120902090606070f0b010e041208060d0b191406100503010806040305070501060302040e0115060e0a03030305092e142701090510 70
    0x1c0400d210310028045400204584540b604030018186043c80720400e80d0f41003100c0d03002284840c0480e00c1c010301400c1c55400801d5071510850041c21110303c8a903024004000c0e0f51b00c1010720900d01810440540c403500078003584504116020303682d4219134903104400155050340134040105040001c90070f40004040c490185000d08410070022107066801c5440300300844006400c48428a0300c203000484c5041020b03008010045c41e44a54a00d0140407000c0700c00e02c41160780044000ca040c401e20b410a04c5603810350751414035043d0b00c0d40d0704040c40159a104060001020484009000d0003032140a6001e80040c5074010070074041400424440e9010388840d5211140280b0001400130b4014000c09003600759040190041503002e2640c2c50650050074000c141c00050301400381c02c0114a0078405c001d0101c6002c0921964402c031201102d802141c844003000f20f4001023443c01d00008095208501c0203404c1c00d050119a031000364200d0b0741c003500038914003c3c0148140c1e049100f41d200c4a0b000955 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 689745845 1250 689744595 689744611
    0x190804030305011410081306020c0a0b09010c140f0c0312012607061103070b16090b03070903020d1113020309160e0429010303031a01030e0c01032012 66
    0x4100d0340c07561480066020f1440c2030b00d034441c982e03a0500c14179500034002d1644c40b070940e1840d414414040d03142c0c3d001780c0c3c1c44611000055044407050f80304025042d041c0b150480640300c001c0000c803007028005482e110a840800c0001c1c10003041c85e0080c0c1d00004111882d6a600000707994442c1d11244542026803400c0c0600408041c40c910100c80200d90104152468080d140c02001c2061404109460718903000d000c00445020030007540012502240d88140150580d44c844501c11300210310061020700c05400c0311a0021081080c0010654480d050000b940e4049413840440000307032803c10080c0c1010440756410500501d40d0036584500d56010318130404c08001030f41c1e004194a01500548801c501034251102e01c0b100c045404207405981c0013107103100d0204150241e002140315800c1c0d2134000d0f442280017a480b400c5441c0c49000b050821226102e00f805c00b40400010701303c24940324240510180d0406903034403841000c211840090f8100d40380100100c5a8642c492600c2d48400401200c00310 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 689747095 1250 689745845 689745851
    0x30307030c02031204060801051002030a09051905090411090609041110090e090d090b0c0709090f02030a05100f090317070203250b071404140612190e030a020d050903031908040303 79
    0x1a0ac02c0c00403003216640d20807990749403032050810041046110303600c004981d00c50501003000c0703216250340c03000c68000c070301548030580490001c03c1002516400106002d00a044403428000000c02c00820400c00c1c0d2012038510b4000d0003440ba0417511850340d07600c174000749580007060143c01240450225401c85071692125035880d192813044085204420004000f40e010102c10801a0211f510100a051089080988080554000911788004004151882e410211690028602c03900c03441c4198140500280b06110141d240034000f0a0400c4148580d242a0400614024800e0048458003840704a9402c0040c03000b0f1011114004410021a0903190328004036411074083c1c80709a1071641410405031926061820541c14104088241a0000014441108000d085601d030714400c50710841e00c1d40d0314124220f6032105135405030042e888190801c020725200c3c9075011480c041c9800316401e03c61b03a207840a0010a2071482003200e0201c841d0b204c080d007650456400401140144c2c0655024 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 689748201 1106 689747095 689747119
    0x102030c03010f0f03030507080d5c0a03020702181609080c190308130602060a0b0f01030f09021329030307030c0203120406080105 58
    0x4008a0400031006105422243d01000024198010003a215070302d103450260003846080e6000c0c00002e40010000c011030041d4001180000c10f00c150760b501030a1003488104410302001c001300b00c0e107100054210380b82210a02c40140340400a10402040c590b02c0907114040d80082900720074960280803600143c0d581000007090441e2050701c8810520b098904511020b200c6003252081c042c596900340058034000660b0400150203489130008890050b0360204800099840123101d001c00007842c0c0346801640140d142290703101d408440d8140c58407c0040c0968580e101229044000b10781540c0171584603030821810f03002d030501d00190106090b00410221102407800ac0e0f03080f511140d4100b003145030b8003045001d501040040c0700b094450840025100d00c100300d0080c04202d444078510095646c14401c0b0b80d080c65003020b00e1a60303144d07544005054004240f00c0c4074441c1c9040150 = true := by decide +kernel

theorem cover : BRFrame.Cov 689568345 689748201 := by
  have h0 := BRFrame.cov_init 689568345
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689568345 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 689568345 ≤ n) (h2 : n < 689748201) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
