-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4250
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:00:36.248796+00:00
-- url     : https://prove2.me/submissions/7281d146-f584-440c-a116-b509b5c5905a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 764208633 ≤ n < 764388489 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 764209883 1250 764208633 764208677
    0xa150e010911060c0f03070807060c1805060304030e1009051207030b0a051f0f140105070f020909030c0a060504120206011a0306040b0a060c031409062203060e060106020706 76
    0x3140c0030b0f100c00700d10043c072008184958544600703030100340c071780d07490341c0349404c0c502c0381c0c4031004c120f5906107402c0380303165110710510f40b0601c4c550528061640860411040007007640009104904105040800010580324000701c1c170380b20001c0d0344804030b005081008008180c4480c3c040100c1d00e502c007039002c001043c03040801e0b07030700002c0c800400240b030740318403121140b128400340810006042079040081d10b00210711200003120302a03051351000114080c0115580d10070060080e09603201d0155900140c5420140940c001418104480c40c20464a20381070a1002000d404c0d074400b95210100b0091041400860800c40c126101500355036043c00004540c0b80b0280c4841c3c41c0040300032000039025202c82e4080050190000c01a400395540d4000c020301c59214200d00310300041588140d042c070302d00618240d07202c904d801000c6a00300244101812524080f90060440c0d804605070000013050144c8289048425440c010781025810003402030302d8162141c3c070000820201541200110980241d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 764211133 1250 764209883 764209913
    0x191d1509010305040c0506070506010e0109050105060711130509030406261b1612020c241c020301030c172a0301090b070e120105060306061c050a150e0109 68
    0x900003404d03242c80c10f14050031001e030b0b0042a00300c0c10000703410303040c02400038006040350410404101240e80b180041c0c000d6503028032600f90807110500ca050b0000d0646500e810044001501a100d848981240101516401e643c1c0010640001406124869100c01080200d40d41003d081c2c1c13078105440803144880303030000c1c411001c20245402c40000300b20044102c0342030114544180c3d0411140d0705145800386d56410010b009481104c0c030b52034060070181c190400400bc81417000205511009503444a035004030091100740c1c1c0051802c40002d28244080e6000c0c0d8056004c10b0134031414251040c0094100741c0385038940360301c5002c0300808520f0005044400c0d10030000300c0b01c00b000308900402d0160a01351030061030307001c101d03040010444c2d122401c10042e210403510511a4408829128200d5800f03440140d0190020b0001034500d0401d1090b60310813410040c4698029076103a101c16003000b101000803a0411a203224a481e1001c0a0003180135440d501d400070482191665200070598000c0e417 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 764212383 1250 764211133 764211137
    0xa15121e0203061c0606061704020d03110703200301050705040806010b0a03021917010f21020102120a030209010306140603040f0206131205100e030406050f191d150901 74
    0x104070703440c2c138404441034920703100c2807046000c194606000500380c4c50043c6400a031038032030161b0400080c03036000c5002d0f03500074224040750f12250320100d0b001241c80204103c1c5219400b00000054031032505031142800c010180c140c0362084400309030039680c000d800314041100901c001e0041c94000304840d0704485d000c1000740d640b2040c21030709030007900420800341031050702140c41411594101a4070101c0c1c00d004c405056490381c032404515100d260901800c080c0c1c00d42070310981c051102d02002c0050190050040b164600d241004040301607121900c2e59001940200312a189560940100001342903203c0d8488070340040000490307018040148090b0080e869080150300b5919504206c4078001403a0290551030340e102c50030b0411120a00d101261a44640d03038442c40c03203000f14807a261310242810f014524141c5843c500700c0d402e40003d45100748010b02040716101d5024407240300c10307408502da19901d21414003041c1c0c1c0b5010240140c4d015015546600103190108690000c03100814824 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 764213633 1250 764212383 764212387
    0x50304080a0507060603020a0b190815090c0f1c0b030a0b2409010b09132f19030603021804230705041112070e0303070602180a15121e02 60
    0x1810044e0207803d19130303c080c0d0003d09014010446814150041c5542c2900d40344003503401d0100c060443e0030610031541403151445155076140d036850031904080d0040550b184a604100700850840d03880d502540d1115a080c3c00942010204842c80c060307103c081c8002c1b006069084c40d00d850391441c01c0f40040130a501d840303a001c0d21003104240c1c030729841001d0601411101556840d094021400e074080898948101c3c070203040030b208200740380140c0c0e007900005603200000420414070120b20304041d48030000d0785c0f10107004800d41280001c0f80c0c1d40314010316a0f00411101d00e10b005101c0f4800750300b8000c8819158000c20040492064141d441c80405000100140e0a030749005050074282d030340e0049648070781480c40b00c035842d0204c0c90141c42d144a5a5140401d103403210902925040e044541044e0190814010040420069806032100300d12890f0f00c1441c1400750000588040f502d0740107000300440c0301e0b0080c01d51944c0003a0502540d04240703401c0024119032196149220100c0c0c010070702c040c0d00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 764214883 1250 764213633 764213647
    0x1406071202060105280e130f050304050a050a0503030d050402060c24070206102d091d0303011508131e03271205010e06010b04180501151206080312090d050304080a05 73
    0x420311f111905541103414540d9650310b924010b81c4035441841000d1088114003000704a900c2d08035440c104550006004600e4903400184420141100a00690b0f005c02c080c041d51809030b5040c010b50780c0e203446100801d170302d40d900c4c280c04030106040034124804562220082118141e9418000ca003a241d000d00540d00c04181c940d5845124400079900c640484011040010b00780026000a0081381d008102c4040f07124130714551555901091140c409070501c00301c000c1a0306801801e50b141c02403450070450f0032030000c0c0e407100080100301042800410a05042c01014103601145124904001c24030140302e003040840c080c101c081d02802041015088042181d040040940c01a45182450700c1903640e25a91640407030384541262117048034040b1005041c69080c0c0c247c0c8501416159941a564040d1150402c1200c100031018141440c096640c0c0021501031030400260652105c110313500c500750710300a0390043c240b100410301c0c0030a008080c414800083c8082040e105040a2450841e03210301c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 764216133 1250 764214883 764214901
    0x2010f030203160809070b0f03010806010b0a05070620040803030f1014090c0c0106060c060b06040e010905130506151e0108010302060c011b0e04050f07091406071202060105280e 78
    0x305545c041c500c510310000e16400423000403000745048403a400262419683c4c0c1e103210114612901ca62140010420440140081c0c03081d481041d20418880c0390003255201001c00400c03030343c001c1d00855450743c008010441c0901958031400e6020780000548614549445e10b1007165120213000c180c41500e56000080c5448001c8082e500b5001c0c41400030310240f40d60344801b03070040f50005801e035100340c1030807601101030802c074080781d0072a844800c1560142e031800e0320003402401c000c0d029441c00c600c2401d05001159013000020700810303415160440b980d035500c0c00c01640b82080c005502c814819000030741d400d40e810a48060440c0d405860035070741e6446c89040301d4010114525082464141010050150756010742000c1c10347c18161010001e0303842c1e00c2c01e44464407000f1129140050707401c607014004614105141d200c81003000d007019040801c1c07981c0702c40768151040388820050384018010807552400302c1c600344131441c0c44001000c8240c085d05007641000d8003070060750000c0c07010b0004074004507 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 764217383 1250 764216133 764216143
    0xa0201021303030801050a0909030206240a0306020331060b010207092c0c090c0d1e0218061606092409050c01020706200a020d0501060302010f030203160809 69
    0x40407081044000e5100e280143c1640000c1c0151402640d031040003041f00125446450076068254008009640e900341d00c3c45071401105102c0d00d4100d0383d0200c01103c41d02c0e440c0150028510a010160700c07482c00b0400d0f54a2409079121044100c1d044000d2050b41c019130301644a00260051404603c14084c00c00603840c0100903400102118541491007181340d0704410040c4074255000441c4d03c031420348850041d0f9410380d130304041d5400007a0501044240e142500108252070045402180c4608d0041010f8000c414040b42c4040c3e032a00024408078000b1555407105210004880e03a5082c40f0024824800c0c3c00311500c0001c0400da40d0320810300902c10b220b40c0c2d15251030490109158060825441b9401900035040101c0f010300c00c0550f004029800802c1050956400381d4aa1030300c80042c46514107031941ea10b203418038a0003202d046101580790b0130010542e072401000040b64a030b18502c00103102c2c1d070701c0d1031621007014818010702c041034482c03a03962030301c00c14985404000e82c0c0310b0300481418a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 764218633 1250 764217383 764217397
    0x10031104021308070e2202010f39050c01090b030712110f090406060801050609040906241701020f1603020c09100311030724050705011503120e03120a020102 69
    0x520544c03100240384480c02d280144110502c1c0b03001c03a800044600e182881c02003499000780466043c0d885185000d1140100302c600c020400c039070b0824040903408194030403c03a024080510340000c080f8400384002003100d022052030038a088403030117161150f6828980805840c20040141c0c44052031010702a07a0844540e40101c1240380d075448407846401401e580c40250801d00a90400a002580398058540075040700d40c00381070b4519040740241004007d02e0340010484546588008030b01450360000818122000415000c0e4040c60815507030341d1035002024080b01d0160f0040081c0d5040c5022401500c058108210300314203007003814038050f4204507004101c02d802c0b100004c20441486296125001207038006e00d500c0d919100184189a00d600d290301400803020307102030002c00300021070844442d030441706207410750500e801541d0341400e50b030b1900100307807801582c0030040c014070011616403003c54649050184605418101007a2118884c3e05c41005140011031000c0c41c0324001e40440300d02c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 764219883 1250 764218633 764218649
    0x1051c05120409050a1505041e060f03210207030303021b100203060a091406060901090f08160902090d032a06271109040201090512010e0105100311040213 68
    0x74074005000a8550b4100e445500c5682c3d0a29000c036074405090700c9040d403035110580e030301c000b02e908000c184009000003810302c030800072544000d205410018071920003d4000c87c10245120703031a605002d800d800403181001142c04540008000003600002d401044951604015807148a0010603429a02c1640801402401060501e00b0550380a80c001d40c07003840c045034401181520f40b100e030710803150041041c034007440402010405600d41500540341c54072052400b450b00703d4454040c08003460071544029188c0d80101e40606260342e00000e040040e01204070110304202130341740040d00c00640c101014050100000507408034004280d822458088003d00107889542c030703494403e0081c0024101d00703541011042100b500c04807201c00e401102500411401c64002401c1c041040f48840584101d05010ba60480054151107400320030030046500ca0000800d540c42c00450740c00d40f48014104035418001c01801e1000900c803110380402c840090320016103400d180d20700084106029085065 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 764221133 1250 764219883 764219893
    0x1080601170a060911040612020306040905030c0105070e220507030e0703030c1205090a09020f04050409050133090b030f0a120201060504090c0512101802030606031501051c05 77
    0x2070602c120350000011920b002604000b00d0711995007007a40d90283d40501000906420329142d00b0f00e005030051500321400a01c001650b650307a07900e0b0391031580140c0205500343d44403c2008207491300401039211447c800ea07a00c0705000e60008076601010690042000c0d0180c0d240702050b2140c1c480d41c00b1a50703845a1740c04860420707032242000752444c0710310302e4121444101c8000b1001814403940076038007247e01c098000b044440c1890f4111002e904064207040a048041c8000242561039025100c440d0f8011000084c100d04c00590044921490010952201c4200c40140b0030100c0c5030701010782110130690001901d0200d00000904104203907690400502ca00072154042c060315911030105003441c3e8008201c0a036940007840242c50381240007405150800000f0040e904000c0198039070307602c01c1d00c01d9070f400560a8075070804403422200704058407185048da4030f0840c10100502c5400c010100d000b0701041c0c8920f5840c3c04e2850701401054041c40c81400104c5c100c02443e0307136050342d8940c03050982d5 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 764222383 1250 764221133 764221141
    0x10905061b04140d21111b0f0d21030e0f370c0605120a0b010e0405040602070b160905010201020c0d0c0311060c030f070c0b04111c0b060f1e0108060117 67
    0x145890315030000e1460a01904840ca0b0702201e250787e03c180c0751080600340c24145041a410407801c280c90550645907040f1070485001c1c2042c10862042c1d0008054400048000307280c0d882a180100c3c6800c1c0c6450740d40f00c407114600550009550014400b144103101c081148034500c3c1c04a18111002c0051150910100100e081034020002d02021071110741c40c06d943d0b030baa1500c00710a0312107000c245404181d0450350341501d410250032040c0d000d07004600141c9030110a98030000b01c560b04503038040030025842c14a84903540c0c800c0c00803004100920081d4288013071507840f41c0c0c80301421504071080c03000c60311000e41018010b04000a50f1b02c9580240e070400c0c684409482c010703500803100c0720140303a02903000444035401460a0480c0c3c0750000e1000c8440c0e42c0303e564080a015040100642c00344880008007481c071240244401d0443c4200d801401c141420720a01071100d0b50303464802c0c8608000140c0140030401600e258900100034640b500e80c580344c8100680d0a1050302c0c4407404c3d840700d004100 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 764223633 1250 764222383 764222387
    0x615090d02030717010e060705030c0307110a2004090c1e0e07051324030b01031506020c0a090e10020711040e0616110c0904080c010905061b04140d21 66
    0x1440130301d240000e001c44005101125182d08003150840c000c034906101003654041c00c0350203503921174840d080070740c041c078090705160780340c1103018100b280c59107a180c525210140d002030400028900542d000e000905455a401034550f240d4021a00805048001c0382000c0040c2e642010003400304080303044a5041c00305004040d98022600350710b02404660000580b1940c0706104480c603e550302c0c10044040400004030040c1481c038880e1760425481f112004944020303600404000c000340d0b00100065002a02402203004166208141c0e0a01e008000c0e40c030301c20041850031f40da40e0500e50041c0e88002c0c51510102c80008400882d411a15044412001c40342c0003c086000316030002c6802c0035440300090840328100d4080c1f55006030b40054103d03400f41d082c0000c800ba0024415000713a8200100b0108041c00c6a01c82e03075003584c5552100050003408003605070000f245410500c0340d00d02e080e040017000c0303e0750803061002901035440c02189405100688030850b190303220300001c40103030020362840 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 764224883 1250 764223633 764223659
    0x1020409140108150f0a0c0e060c010c0e091b0304030c1a060103140c0a031a0306040b07090b07020d0b1905090319111e100609060612050615090d020307 67
    0x212603e5101e0401541d010f0350901101d10f20a504c1c640007511070b982c0c0c0d1251800030f41540e1081d88180314030203402c2d00442d90f41502400c2010b0301080001110424001d008001d503c61031101d5003da0790000c1848180b001200e400907103001b10001d003a507a074580d490708603030046151402820f13050840c00c2c2c592846500750400d41c003c00342640d041c01520f000c100c100e0710900c01510800b8801008101d041f0b583ca0003900804550b220b4110112103d0101002003420180c0468048034246641c008005146810010400203840910041c50424407aa03000c00c485004900026203160b920a0000b070404400e00c640503c902c43c600c60a00c070a081503010340d9942e4100101911040c58040307032090103648200101000c07148100700030054410301210003d0381040c0e84010040a018840c040180c255090054074000c11600000041d110700d000e2004180811921405108031f080c5018000300d0359501101d02c0c01421305420032a6940a501d000401a00050b076000390580510030b0009a11079015070 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 764226133 1250 764224883 764224889
    0x50c0f0f07090c080609010513180b04030f051e0310031401060f0518190e030309060105100c080d11090a0f1a070b0711070e010b071208010f0302040e010204091401 72
    0x5010f0000c840d10243c190380c5420300301e88444e000359980780100440d2810400f007101c00d85d5004070000b0340980340360072240c0014245070207940046c0700718184010541e1080300303000a200c2524140d810860100c1000d094030068581c200044400031022600a049121041c4011a8016022109480c910b00b02c507000c1c11131032042d140d504003403080c0096a4201109100c0d07100c01c50030040040d640c0c0e401c6000382d0714410b203403070505031170760300d00c400003482c5400c000450003400311200400c1c0561500c5e00700038841c004409440304000360b01c1c0e074480010300712005540100e510310f07030003007a03954425400050034000c50301804d600120410001502d119610f401c20103035101300322050080005a451040144035000c0d0041a82c1135120015101314881c60740805102d18100a541c901d0b41e0b02d4031903a4041d030080c1c120a490040028101c2c0421020302100342260249082201c030a44c5440140030041c4001c0c40007a008980304c500c0161940c80a504413800f03005141c03010400071540004070305110100340 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 764227383 1250 764226133 764226149
    0x602060f0f060a0306020d150e09060a09030c1e12030c1803053d05010e060f030c060903030c0f1e160603090f050604030e13050408030403050c0f0f07 66
    0x201d8000406858624480c0360054010b211003851940c840000b5401414036488403507440c01c1c1202804035010f9020020850000c8851660814011890800030040c02e035410041c5000d183c0710020350022903c0390310a0b04500c0181c0e010505038065410050300a400403c0c20404d440a4000c60b41c055014400184d9266900d0a28445407051040003031114040030300640d01502e142d00c000280300710302410002c01041350880f000600c1155804404041e1004028280c440d0010b00000c1c1c0c90200301948000c04503034803002031420502003921044000c80300e501408000558000b0b41d10704208940a11110004803814803500000594690210710001482c0304089111444400070009061480e000100c0c0c441d00722901d4840258002d0149581c115540c182c0c1c80300010129009001161147c0e00a449100c4035800c1e18040100403440007004c81c0c00c82d031520040c8008078030150181d9600652500b410341c0e54a21150985140000c0170080700c03000d205050600384009030108800c411105a0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 764228633 1250 764227383 764227411
    0x7030c020106050303040b041a070807060b010f0302090a03060c140d3c09020d08160209010801091109070302160809040606090501022508100504020906030705011b1b060206 76
    0xf5038101360b02ca225074454000004c0003408184032901000c0080c24800c159005502d141005a590f0202d150b00440401c1ea21150b070791031001d01650300004c03035190015840c5011480c080701117002131110072141c00040c0006a03107080003074016020760f00f01d8181d40b901d9101151910030302a0814007400794452a220300f88a00d0314010010103152860b1aa0705041d45c050203000c0c0c070b2800c05000200200300c416a442b2112000c6c2101081c1c1da50700030b00e050080c45100b01c2c5d111065005020340c2030b0f01a400303108141e00d08040100403500c3c01c2601d0840d8001269502c005460b1290224041d0040c0d83c842d4600004411210b000c008000303004100c00d5909840a001d401c1d40d810045c0c0f6102128031501d400358000b100044021002241d682102c3c8402000c452160350f00c070804145486c03202c120582a4503a1102480251b14220f0010340d8000380440c000e1200c60708000000b1700c5241b17804600344400840400c3e802c1000b0300c9074031140040419050320192660b84880c025030303400050b6007044920700c1d2 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 764229883 1250 764228633 764228639
    0x81b04090c030308041106071208011703090603040c1502100b0103060501082a0a030903030e030a0f050309120304080909130302031c0b062d1e070204020c0607030c020106 75
    0x140101000c554000d034a0803011440c0d80c6040d41c0800004004591000701020f00840c150349040240000c40c1c001d224034200801d1361000603100800c103030042d100c0400400850800c1c0ba40000454000200a9a41540702e40303407407900d81e50700c0030641c2210104844800342c5034802540014401800d170141c00e4240300b8900044015002c40741c90380138440c00641e41d43c1c005024a0101101d0402e005990030110000d808000c480007140d4000759000e500080e15001800c00b072551601a5485140202014614100c14a03002800c1c0003001a584e000b031200c04000030300d00035000c1c49000c2c8503d540000725650303481c00f40b07080074065100700f60152003000c808011a0030442245075a00701c0c41d5045e0003d42c944a0395015403403003400c02541c1c1c15040c54480700c41c8a4580c0b07999028000f825018000d048090702c003510910b0704512454540c84400d1000e0204a00c01680b005228515050b0341e40c40715960202c50001c81c2c017902c00c01e181d400d10791081400303214030940d050340501c00030002030303008003c0c00761 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 764231133 1250 764229883 764229889
    0x609090203070b070c0b2a0606030f060c1204030210090b012c01090e07030f05060601030c1404060c2901050f030d0e04020c0a050601030c0806071b12030b0604081b 72
    0x5444000341031140d403071409210328608140100303664407ca80030b035202200841d1200c1c04c444509030103d64980c02c1070090100724181045165086900302000e000b03507103010098200c0310b008040c240900c5514640103e02814028081c0044030b010501d02401101e69a06011103413038020b00c110000c40d01e2000302c410748844081c24001c0c50004c019001030a503481c00c006174001e002c441c02d03150390a009441000000405505598145500ca08043d050034544200003401300c030382d05922070050080360356030790503032110300c038115802e40e03a1390b0030014985015801c11512009005400044c81c031200e030003d6105080c12402c0b24100d1384201c90070603604040c4018140c0300e6000294100100f07038540c00018046c50315401030240e00101d0006c880000000d07071242803600600307a1095841c240920001d008800c030500000b98042154203015501441d04084c1071601c609103040600070f14100b507032229038039209420038008480c004080c41c3c0c840d61034071041a19100c540c1e80c01c002500415003a005141 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 764232383 1250 764231133 764231137
    0x306061a030a38012c040b01110d020a0510020a09120302030f030903030610031112040503131805010e0f2d01061709060f16050c0a030c03110703020a1e090609090203070b 75
    0x110f820120544030300c0101c800d1001400c03070000c802d0305000c003102720009560810018507140c1c00c9981d006003103619150800e103050021000b01c3c00d1220b0b0040049900c8103400c14808070803604d240c4036902140f600c6060403400c50060440f02010a038002062001d04034002002d94081d150407265031260706024101581110880c14a03803a122405000702400b008241200d140e109014806603072800400711548800da404035000a1840c81a0508500ca030303c020344107a84c0074010700110300203281040015201110001020303100203240c0c14001d07656281405401083d203400b13112070050a961515005441e11140410705407403201c0480000d081080002074a0b40614501c01004071152100d582e01e10301c5840e03c1911800740002000406200c0c0801c018010004d0b00903512843c000900c0c0c81c00902d49079074582c1a140942c000d51003440945d031880b68020450350020400c07010703e541e02580b841c5465240d48004211031400b030000524a00790f80129400720701c00c90648140d01d40741d2240030454 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 764233633 1250 764232383 764232437
    0x1090b190f090b040f0c020102031e0c030a0203060303130e0a110310050f0d1505161d060a0306180c110715121103100306061a030a3801 60
    0x208903440c004002e4402c250744000c124250140c00070a007500000d03a01c0701520804c0c032202006139400400c0000c41e0303000e80780e5401245900c0381220654240007841160b18003002c1d103c000c80340d900201249140d68204200c981e000d83c6404104002a910014404104011658580034609099689200c01b16000032613205507030484a02c90907509100c188254113621710034158010a465101c030020412800d207900351b1500b800340c0403415190001c400c0908011035030b901130a0000031039010028940141c02e092019400307944207900c980001b00110040c1c21198006111101c4007001c040c03035409560020003000902d03484880000003c151555900c03005031080107180a01c01450307034070040c41854541c40e40070411034081241789d00180305490035803054802c8a542d0710010382c00c2080040740d020710710083c240c20108051454840c01040d90074031000b005110031517030b2441c100c00340720044801c4a8464a040e02c800c02c0c0601ca20b10442d512414807400240416540540d843c80300c00400750360400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 764234883 1250 764233633 764233649
    0xd09261b010201020c15160f021f18030c060e0606091b1e0a020f061003020409020d0b1e060604050d1103012901090b1207050c0307080301090b19 64
    0x80401155492004040000301260455408010f40729840b0020080840700b840c8180c41001daa040882c006100c9294000503c401c1c0040c40041d140350f29004502ca0850464145140488100c00a1140014980104171030241e110800e410300a0641c800340600d10301d4440c1d0020001c0302c18103a10302d660b07a00103d0300680d0100a01c0c001440c1d0340505820042d100c00300c0c600d000d0404041d204000418070031001e41c89007401005c215403009580c1000090510f911042c06000141002000510700741141e02000c2c0c00f407600d50703110200310340381c0c8807109c44403030b4103d000503241d420700c0c0004c00b00d0382d40c00c560003985c0600d002011a40515100c0c0c02c41e01101c0004024204410007036460030000900c1c20340a6134955030b104401280e085444903042000900c03d101070407003148110000d0140708441d0020011100240810b01c030740314800032601d401a02c1424125210034109604a20b1407042d070710024021440400005201d17001900102581074045a880400314081030003e480c1c2d00145c482c03002 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 764236133 1250 764234883 764234893
    0x5090a020315060c0123061806031009050f030d020c1c0c20031203010f0e09070605071e050102090108061c03140c030c0c0901050102030c031207110d0926 68
    0x2582c2d1a0080080101c140c000001040c0d10300e03000c4080b0001d4070607014a0b03c46008280c00c01801d481d01c2c807480c45580c1d01a00607403840b81081000310b41d941d0108400c0c449410b985455403420300501b0001800c1040e025400c40e5540c00481500c030020350085030400c440c0303104040c01302c2d0f00d0007a020040548a089541d8102d5000410740710502034a0041e003120311582e07150000c40c0c15544060140242140300312560540e039500d0000804404011641b004090018242c01d1295140c40410b004049503aa0b02d0a29151520303418005c81c0c0c1d450800101e104803042c4803035007082213019006803009800036201c01c0c816583d02028841032440304c24030850502d1030401c41f04d00107400784150504411803094102c0c14036500d124500e01d15807201601103426401248407404901c0c0c684002b80c090b09080c80518204071001c11681d03901d00a00392100300640145000505043c860a01c0b44007110500781200c0421041c00e10207031280303032980a03028110342c01084003003000c1d541c1c1b080e40c002c9080c4040185 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 764237383 1250 764236133 764236171
    0xb010c0b0703050a0f09030f111209090408040b07051f0506010c02090a0e1506040c090e15010e1003020705010515031f09050303090f0f071503021c0c0905090a0203 72
    0x82c003d0600030600420b0300da403410a101c000941c0c3c412412014801c0d25031000c45541420090806481c85a4075007441e44150780706030342604600d00399104508181c0d504065500c85141545880c090b85c1c1104108450109242050100009803540d65042d180d00c049081d03249481440c1c15110104e888502103580140c1540040c10008644c0e58132001e8100009480f00700e44903564209000100c12118a000420522031513180c24801d0b041d0300e14075410300380403041c0f804d100e03c101003500408001180c01800440364142e40128903800d09414010f188031040c500340c00e800ba009400c004030940d201c0d071070800001d092414071a1052030040d0028001d04a0881101049040410800d8111200c03925203003c00c00199040000d103004441950152502985851545140004d2032108c604540e02c03000b000c00c20880c40b080d11001c01d00e00d81c84c02680e03c18103c0315103600c0c1d200070301000304607601d40041d0304001355100c010f4000361041101c20303070246d40b02d84080c40103a02081c3d4401d41c01849004050b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 764238633 1250 764237383 764237387
    0xb1605030c0d14010605090405090d0f0f0e0a1d0612100902131a150a08070e010e0a03080d06050415090507090e0106020a140102030f071413090e010b010c0b07 70
    0x5400c08581c80400460194542c1d5079083c02a41d080e400140402e8000c00d45590034a058001c030340d849214400100405408560b0007051103440120b10401c0c403100c070301a107058910800104200a2010303109a180765500c4003501d52545100c0428181200748c18007280162420895050018500000400d1587d0029000b2401040004001c903444034840b09080319a1841c1d000300c01d04402200c0c00c0141c0c3c40060b10501802c01d031a00705a030540002041100c8095820020b00354000d201843c0c6520075007a02401a03a4009030318034810b40c800a4503400108005403170300141980d200802040c80803a0382d0f46d00b440142c03094004400075030002000140140c5955a0010754010721614200948590340c0c1e8904140340000e03044180103800a48107041404801c0c2c13042c0d80380c0907602c40218554074003030380034120055014040d8003c02102c0722000101c400010143c0b40149400e2241d44d0006585003112001050707007006500c1554200080110198041e910350304515822900c3d40c20660f90301101 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 764239883 1250 764238633 764238637
    0x203070509150d110901080613150908070f140f07031707123b241602090906042021030a11010203070c1b210b1605030c 53
    0x4242c0c0510a0300c10a5011983c41c000c150105038040d01c10350030711041c1c00c4240b1403020416007003002240d0121052014243e175140d40b600760990061150301003400343d1100301010b0f005030000903114071404504981131013815074101d80514441e8071000180340b9100e420680b0b0710b0004990750300d00c0c0c00c25038013040400c071400c088485c01860350180c0c6150004960300c0b50300300c2d04410061030024048585000744001e04180c481004c0010420900409000c0e5280e8101120b040c1c9456000305500c408a00c901703900c107180034800391840003465440703155411a101c2e08841c5d44034146d104e03500d4000402d4422030003142c001e000707913002004900013180691664050403d04000e80e500304050980f0340180300944058078401c10b000e003004d50340d03a282d40ca4005000e44c41c1203c0803521648100140b00020303800c6091880720300c2d0300020140c1154004c0d400c3d010f42401e150321074903a100080504950024280400d401413a1043c41014001e40320039400c00c01c0f542d10200200d000c42ca007040030941c20511100 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 764241133 1250 764239883 764239891
    0xb040509013303080307020307060c090b0d18140c01171509150901060809160503030a1d09070306060f030b0306060f0310110a02210d0b060c1b04060905040203070509 73
    0x1003100032981d83d942d10000698030440d4100d00680012405800b0040240198680410940303451308005013001091011403040a094920711030f940c10b02501200f540210343c041d070540140280606155802c1c001e0741350140d503594140003030780c03540b030022010038404201c600600400000340c0503140c400303013800795200b4058071105400700307000406841695030902c4507010305600e03503441005080040c41585005001c100d212000200c00800b88443d0314000305544081110b03103010440c40c05620050312201808a0406400001002c10006401e0b055007011084074903a039a104540078410604030102d038030a03d01e599040d0401000b00720f480c54046210074444000800740d40720521400f090000b00d4030766038001c00c00b02c00c002c81c1868405405100042500c803d101d803150605800041e0407144d84909017502184a40c0c0b80d55110312501c1d201d0550b1241d130380180403103c0701036900e01c50b0980d4031140d01c0322a22860a1175404140e4500714040e00303002d542c1c054010485903060208000200030010 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 764242383 1250 764241133 764241221
    0x10170a020c1e010603020f0108071d060f130e0f010f03230a03020705010f050703080f04031e020a0c0f140919061202040f0c02100b220b04050901 64
    0x1e01d82d10000e0148042900040400b40000345851640c03040c44480080480e2140c14090403000b080b8046420080490312890b48100c05028a0764500000b1224000c02801d507600300b002083c680010544407010400f5644203045c2034040e559a61b0340d241082c6000d003d1180a000c0c00d44040002682200302540c030f00c0817005600b1581030040a02610708104480181c0059112100c00c11031544c00c100c000c11241c003581381c194940740c000d840240030302c04003030426074042d160b110014040c0b503ca00d00c603011090710305124130350184640000039034820000e101a14414580c00002030070040d0304030f150341115042c00c41b1141c0c1c0b09440080000281d00101812120f151031881d0441800079441640040c260702521000c1c0101d441c01400101c1d13100c1c1218690080c0761200728100e0940000389000b071401000d0380030800010640c04114a200400003503400445281c0c0300c07220340c7c60b50743c20140e11000250784c00c0042d913a840b62054282c42c0e03850741c48409109404c0381030481c40350313401112007142484 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 764243633 1250 764242383 764242393
    0x130c090b030c090a05010f200a0209070203270904150b090108150a05070219081317100903120b030118111009030804060c1109040302030910170a020c 66
    0x40c2410024991085070590305035000040c040030035280100c100c2000c3c08080c41d2a0829402d90780d009442101483c10004601b030080034440c0c0b0b1180100046e490030740d4048d00c0405a4207001d00080c1d905d27002100100c2e032030004200300c803913040c03990017452201c02001007501405454540780c0001c800d148c40040b07100c164842d1518005911000703001402001210000c2481c45841541c0506942020304078140060806089c420800d40c0090014101c07020440b904010b82518a4a07040c0c0d07100d44100d4590b060305100e0005400f255005010013641842c40c243c6461070040389610088404030303100100810700307040049100200740d601210903048041d0000400e0915074101c04400200b940e0121184c140c114008006810309180000480f02d443c148809464219074aa0406000d540074100c01c0180c3c11148206002413668440f03603400c0050f11031505420a800d00a4503a40002184c80c02455412000c42d1450710070102e071000c050460894100070b440342c0b20264060b40c00106840300d14818 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 764244883 1250 764243633 764243639
    0xc030706060f0b1c1d1509010b06040806060f0303130f210b0703020c07080601090606090f060f030203040c1d09071505030411060f1b0132090f0304230609130c09 71
    0x10400e2540d500c42800b150b90301031805001c0c2a082d2000300702707647d014001c20302c41041203007000070301990804000c85900c2210020400880e14501841540e6416602070040001e0b500280e501450b0560b5111103202c5070000510018801e11005c4410040c220f01602002552641c440d038050500c400d068001d541001c0d41c1c070715070189005000e13000035010307994583c420005950440040401005101c101060b0140341580242840d20910210001d1507000000a0708001104183d20050820350700c081100c0d1003075801d02030641600320b807101114440c0f070101260030144200000b540d02175079038440c0e15580d01c4d03650700401418031441301504940248845045810400041c21440e00000038030202d10103007190507429070f80c0740c001d00c0061404107445500507000b03040f62384450a0411012070a103031a4600c03c81d01d01080c403081c900c45400041808100010b03d410210382d046916207d032003c1c4031040e8100245c40c0700f80750034983c1c40040c401075070030040c0c0b00d07030017000b044245814000d1340699 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 764246133 1250 764244883 764244941
    0xb1506031807150e040518030a1b0807030f0f020c0f06130b1606060e060604031b08100b011713020d03050d09240c1b06020c030706060f0b1c 62
    0x124040740e0002c2003113088012002e003010712400358000104200b80000c4000d8134005516445141607860420480140c0912880102c4890000e41c0c0c0d408131640740e0f101e549007002071009011503c481700164480388001812440000e4010b074152000300610f4001a4083c100505039106500100314810070b400f0000340405560081e010b40340454040f010907619600c0c1120486141d5002405425500800d1080a0319000f081e6016250711502100e18401c0100801010b40325580c000040ea10072100b00b001d03108041c0d0880350394081c00781c85802c20000401d410100280c000c50703402a00903415280d03070016107810f804400f42b41d4042d040403480c04013050440d400340c41c850041034840c000b044044070440c13540c1344a05d80b001d20b2840c004101e98000014001c1101051900d0041c002c810841c540040c001d00380e04807200c055181c42129a214242e14001001e4400e82c401d0184070894503400090981c501c0d0102c030901e0250100030a05180788241400c0240400004034119420800030307c44160 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 764247383 1250 764246133 764246159
    0x9120909050f0633180111060f0604110d05090102040504110c0d050a050c0601080a03140a0e0f06040b070f0209070c11040c170f0406180c03020d0302280b1506031807 73
    0x3503ca0348540240d141580005087c9a406808000d000d074080310030480d02d00c94848200d50403140031600410320700034101c900807081c0103203070410a05924001c18003100b0740e0f05500070710031210305036401c0c000c20b035440003c0400c0c4d00030701100590b16004640d000d0402ca210f24020414130400d400d10701c5c02c164103401ca003407400c4001d800548860f4007a007402c2c402e042d0803107160601420001d141501e8503540e054000c011040040b00d0311b0080740ca62007541010b42c1c0f40c00c1a9800342068001e032a8403400d45040682150602d81001e034000c08817880480c0085100318013040c5d20540190940c5241506d00003803000400506200404001203090355039855100e494140d03006600b80c401240b2075003002d00701603084a10140e8070710f1403558160905000136a5000344034007100c3d0100c4a1031f070b0080450605034103107480340c2c1218012001c07604000084603952040424040c2c01282e0020a030381c2c070380d03081008102d015480c0d9035000805000203000c0da030084d240d481520094501740c841c01c80da25019800306c4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 764248633 1250 764247383 764247397
    0x90303060f0906080610081b060d0f09020f09090d1803140307031206080a03200a08040609060c0c0302040b01030b030d0201060e060a03121209120909050f0633 70
    0xc0c0d0f181d250802c241ca004010710b64102544502d0070188034500030890365a0f00c0d4000c031030040490f0890340180280d441c07a080d9201c3c82a009000d00a92078015a030800801c28504100c2c86086110203100e05824410301d200c4c42242c07901d00410281e1b00c00a000c0d24618001d50240e80e9120302502c010000400b040540301c45000603900442c0c40342018036009e0003240180e10341112940c40d142c000c0181d00c0c0b0015925480d10b40604050720310081650400b81e00715400105c81c41d05100e0444108200105200144115010b90ba1682600794030b403003080b50042d642d00c0c00a012407505007000c0c40540f62990103c2c02c2c03440e05040019022080c1404242403005005407100903075075500040066610340a200c50740900c1c11109a42d8040c08d650310710306541d8150500208010440b60002200612540300c0001503070400c465071000d000300c1c0f500400042483c0a0500c0180c01c04010410400b1034003001401000001d03c0c038025104004060308540d001e55440007001e041c1040c140401e119082c0c0100303a0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 764249883 1250 764248633 764248649
    0x3090319021e06091302090d0507080d05090904030f0e09010621050c0a0806010c08040905070f1d06030901060e010306090b130f3201050613020f0904090303060f 71
    0x6422003900400c60724401c4601004005000e510480080e03079503007011070346913800072500c0440b601c0c3c1500c5a00020b00a03980300542000564940c0701c2400070014501003211549011100e030101400000c95690144c0d0072150742140503030303001c600000c0c0526400f514507201881d00b048584188000110240420392040020500f4524030031a4a4001009252003a01032031051010b81000c0c03030001800c4c851a42403108115908011489581c480d01c540c0452940201506480355110515400141003c0d5140c0021409030295403803414018990744441c50102030029680714021818090a075000a05c0ca1115540c0d591011070900d140b00342043c041d6000c3c410000315001280f03090850f4000140c203000d22042400480400501c048200030700655220f200e0b1a17001020700c0440c80321014a4040c000c40f003130b800e100003d03013540562203244151800c9450040605645881c40100e1141411003241010100940501b900301504128a40c070b1003407600040c400e561b02c0c26212001c030f542c0c214042d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 764251133 1250 764249883 764249923
    0x1140d1506050f041e1d09060109060305060f0a0204080304081c020102091f032d11030106140306280f0b04140f0d060c020109140109081b030903 64
    0x18004030a001820041e04141c105180b41c000c1c000c240740b806000d540300e4100c000018541849101605841380d400030310700c0c502c10750543c40b5803600c2c46400030030031103135180b080c4110400000c00c1411401010700b142e40040241000b0340392803a59607080b00008203480d5000e5001c10000030300880c204018802403c103079018180024420040361070320403015110908580c01070008084c10703695210b03d010641d81d202e2440c0894410b1000a80142200e041103510341264003201480c400c415000d10340c1204101c4608000100c1c0c00403002230580001e00a0ba40040c01641c02c426840121000540d00884011300742c0000504080320950803c04c00c40c07119458030500c207002c2010322004070348a8054149011618102400c1c0f440300300841c0301500741248211300540c0140004d403100003440300c445030080350a0110541480340030703019260050044448001e2910044055001031041c00f01d80c030f60001e200c0d842d10620b11060903e0152150580426020070802d541c520381d004c208198443c0030300b403118a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 764252383 1250 764251133 764251151
    0x301090b0c0a1e09120303180b06030c01110c010507262206020c04020d2a0f0e0306070f17010f050f0111121303140f1e060c0901140d 59
    0x1043c50078103d0449900c0f07120a101c0e200502d03040701c0840152800c040c03945106a5071030a00b100030b0b00b048881c0007202c105601c03c810070311214100c0c3d80d106642c01d40c00c0390b40c503100c030000460320200004201961034200c5e80c0c58052542c4582d004204903805200c2c20040c80341c00020b4107041c9200c0c118a90000b10000a9a106117640c0000540300741001754100c500c0c05142090194a0f4012203004600c42c0358002100601c2c192264000b44048a03141400c90300c9401040d000014440c90140b9a00030405040010041500c074400c8840d0150340580642000d465010058440c2d050303407500801802503000e05807030b013045201c082a000b030030345660040c20b20707103803e09106da600c030503046072030400c80348030100b1420702130014110008003095000c01c2d40e100880780c0401c112050680008008200300800115542c42c0084d0b00d03228404040203541000710046c00407900440221742c1c42d074194005e48009051490440c011b0074016606052002141615611112007948148c42c01c400301a40c4802507 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 764253633 1250 764252383 764252387
    0x31b07080f0d030c03110a030e06060d0f021002011409010221010b0304110a080703050a0605010506090307061202090604031211160b0d020903030a020303011d040f0305090301090b0c0a 81
    0x49002444900050108a10004001601c810740c0c60140828191078910408421384203a001d140304813030034000c890b1104200c1000602906c0354004400f0148500e0001c50450301d0910744035001c15500c1400d544c00c1c0700a65007407108070140d1700c2ca110159503a90000d1000a031404031590304c01c20502e400181c1c3c03528541c002001e0445050f000340819041c440040c41210500d408482c0c016030071180125010f00c40b0360004000007007540003442c442c02000c8000080100008001100c2d078420f040c1403080c2da80718818481c10380248483c16a1590084004000c16801030000010346c083c2d142000d842c0ca0030507004a05241e00940c82210709036084d1040c0300340301e84d001040707030040ba01c8080900341201e0074800e030342c0b8002603c1c01852010b00300002d020700721203201e0f411a5540007001d0700342c2e51528400f42c1b012c0d48a030024440d82480121850903c031703003501e024029a01c6140c0c07002204008454580701114182c0000030465050340d070b00c600190100b19041900d40c41445a104060fa444000140c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 764254883 1250 764253633 764253643
    0xe0a060f060503030a12060e0411011b14070801050921220b0702090f0403080121050706180f060503070305040614040c050f01020105010305060f0415050906250903150905031b 77
    0xc050541050310003400001a82b0101d100602002441d000c02ca83c51030074110b40d00c40c002544001c01c510b00440503c00846d170b02260403c00c03501c1c030344020051035490031501d646900e4042c100103026a0200c1d15150b10004210103080c1d0b040b0f402000100c030812180003802442030039000054000030108580c0308518241e1807031944004110500303071050a15a4019081000c18041e2130130821000e5030882c1c42d20301407078000316101c0d0000c080310003980d60b4070000b1349203c00d0320381da001c0c902c05040c40100e072240d540c00300c2c401103c17900d0380d4603071842e91400400c4006110181040303e4040d20fa200a03644041400803050186004d401c1e10200246400c007040f4180200c042411f0659061000400c040b0390041256584000961034041c02135840e85015a40010300c107450200a500e07100c01c1c001e604ac400102281324803401180581d5016010b603d52030b028030224600340010341d450f1424400940300c003500c0d82590b60a50000704425840d039959a00b990402010907a1007a40d0340d0201d5010541008 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 764256133 1250 764254883 764254889
    0x3020f06070504240e150c060408030417040303050315010e12010608060a090b04020f031c0305150d1e080d14040c090204050303030a020f0409110712030e0a060f060503030a1206 78
    0x1000740803098403400180c0501130717031140540b0075600321224110b10200c0d41c044030030b46410403081d910300b86080e02c1d03c0105500305480a41b810307210b076081e420b00d124540b4115010381360591541811595143c0c58822003082d4241040d04222844050100c15200e2200c8a48203d00350400801d0f40c7d41006003141c500040101070849090821020300701260050010680068050321081c144803d0600468035101040c001030615107c40c00c403104c3c801da410382c4203030300130381a4403507800c0d089107110100b100030420aa00503090980040d5981c00e59544580c442d034196210304c0140d0304000030511184203e0b5080c841d21014010300c14100020041e1380150000a04030200046090604010100395240002012886980c1c2d00181c1c0b00d469a0a40040e28003d01c52a1003d00549011840c0d000c05030300a268103c58aa0013030241c094841c2c024001c0360401118080242000c13107050302c8101c0a000410843d12195a84000105032614140b008080314512900d8044080c10703202080310844180e54 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 764257383 1250 764256133 764256179
    0x6070e03061915030c08100e012c07080105070525170a030b03030301030321270c03051e25030b06120a030e01030f1b0c03020f06070504 60
    0x8000e1948440240801c902e9101200056107160000b4407034058078658002510070001c0301c80000c1c070303900d0002d00101301ca4100d003002d2002e10b0407880d0b51400c3c0c07002c2407140b2007811000d92800402c0d080a00140314414080c00c21030b10700135920982e903803c5502c103860308000510b00013981084224080c406480d2070340665200c8c2c9412185031291403940601031030300407100c8800160f640d07040c1e120b50403d041c40b0800900740ca03076a503034a00d03025103014600b400d1096a561150440001500319125015080308601c0c02650300300322600b5110781003001c0c40f8040355620240080400450b10030015030310645c0400300e46c50031440c84407402074640610098080d0400c0b1040f20010010301441e501c1030200c03079203d8903541340c6880d031000142d00100d1040c100303035003803080080394814035911801c2c40d09104020b03201006242410217480c0d040e0b84500d440f00c1e024480d40c441c8544030602c03506e61039000324001d1054403074100b03400204d58244a01030340c0d040001070000c20103000383c0c04503095814075680a8 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 764258633 1250 764257383 764257393
    0x510020c09070305070c05070602010f0b180a02030a090c08010c110d090506090d1e032019020d0f05030a1d30032a03090612040c030c0806070e03 64
    0x20002a0344020010070710ba04254a903004290154001d0417a5441694006d007607800b4903490b640b00a00801d00d0b15007070181c481c10702c41c0d0810f80d4105000b200c00c800c0c4080600c0d0846036500030040010754009400d8107452503441c4200703c00300c2c5042211102034982200007052400303100070014000d100d280860f4200e40c000340d00e844407090300560242c0455805840e41c50300c44208900045032100c0b03440e4003610050303080c01c2d4454035803241d9005020a52007a03d41c5031080400c890804542002c42d940d10546611a0044135081c41c804019404098030041640480304425942d082221403004007c0707586600114880e40c0c180c0e00310901d03400b010b11000c0c40d145a944500c0015582800e1846100c2442d07202c0740c66804e11001000000d000480400210703030b0360f039070f107114480740c1880d4402043c0c0f40220311003d0903409007004402ca44100200420407800d016100c801c0f50000034001d40112810b0000b041c001001428141504d4018200704010748940c3c5003810024000c03003c00002c0b90312030303084 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 764259883 1250 764258633 764258653
    0x201031e060e060f030d02032d0408010c0201060b0a1b02040f02070b150301020307080c070c08030a0f110a0f30030519090c0b13091109010909060321120e010204051002 74
    0x100005558160381d1000124040f140a0b509c0401c9809a210080b864400700142c003041c0044150403407288000d0a40c020894140d80b5081103409024090b1194001200074034400d41130070f1494000300b4580c1c001003001851a20703505544080b60310598044408464840800c80b09400d00210840403d03002e0b0700035891480d02420042030194000c10f201150308010902c2824001081303200005070400000b100da41301148000175015400c6141003030001b40c0c1d8091a100d4880c0003191524059501ca0394a00b05a4010b560710740581862041e4600e5503912910100c4103401c001c04c0c501a49555500c002800e41000443c0303140780c85036040c1c1183c3c0d0714140788040000070b000000d84421224080c030b00540302d00342c86200000364082c0c0c2d408481040d0429a0034a0b05100d0b000082403098026202d80d803159030b035040301308152030051101800000c0100107202112403108540142c1701c44605d070000e0000044000d1208a40301000c04401c075a40c0402c0900083c20300410702e82c14584075000074121352038 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 764261133 1250 764259883 764259887
    0x309270a0e0a020603040807140c1011071401021005070306170a111002031b071d0108060703200a11070605040e1303031d0a060b15070201031e060e060f030d 69
    0x9030b500002d0190f0b00000004041c0710f0795009072451190b04c82e984914020100703082668a000c41024a4410390424075441c501d140202e03094840d140d0302d2000341c15000d14107180506211107820000d815400742560895401c3d1b0b2500c1603e10450458800081041c1013124908642c02c1228014640d54041300d030882c00728804580c0a412040100d0702c1c21112200740504a00b035008a034411140c00d0f524101340481100d000c00c4180c184c59a91402ca100056061000c208215080c4210541a0000e8000c00c82082c4a9041130103850141e21141d07442254210140410764849a030440000c3e910300025500100c0511040e4001d00c860f00d0a00e08080c00e00203a0a04203070003508580100d5540140002050700036002040b07032200c04201e03100f41101e0592022303225003007454111800f6290640c50001c915280341c00d100c106000941490030032407039070b0065000700440c0001c464107854905003000080030901400c0094100030f84580282d04084040c050450703081991309100c0e810010120341001d0b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 764262383 1250 764261133 764261143
    0x5030d1505060904110d06030302010212070903020a14030115080f070b030c25060c27060516140607020d090f030b0402221109100f0206180309270a0e 66
    0xf03082101c0002c4c10150080280a07030b4851010b84a00312414210b0020515806602607c0d201002e400362865a5540000444402c0e485000003988000c2980c0c3c140700b413000c0d5585000010300d014000090240000002440c20b03805648000c0c525880310489024074030080c03003500014420319a0755811803c0c100d44880c82401151150580c80300c031800e40a4000c00094505900550050380030005800881401441c010f919107111042a0542c03900581c0d2481c0c0302c0d142402c075642d5036125410041c10b4540e100e400c440e00001550150582c0e460114801014882c890148115800038600c2c9590360102521048445c1d0082400c00c00c52402000860300c0d43c0711490340a036048401107101344001c0800c01c0c020448400301081300d458140d02d05044c40e038402c000d10042404640343c0c40200b20880c03080302c9190481c00b001c401a0458408100b04244200300940d0880340d40b0305407410091102c0100389a0748000070000b000c4000890005025054948034541002e110704c000c3c0500e48000d1841540e503 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 764263633 1250 764262383 764262397
    0xc0304170d0c0c0b090a05060d0207140a030507060e0309090f100e06131e050109020711030a20040608030c0703031704120f0504030b1302090702031314030a020d05030d150506 77
    0x100001780d070403059520013000320060300340200016156801d0240082c0290441e10007202c1d02d00318026078061a890009007055499490350f103c81c03900c00281d407a440030b0700b1004084440c520003403002d400182e581c42c82140c130801046411008038030300342a08103c940c5103035000e189110010418820b09490321b4100c3c6400d1009124003007140180301d240b003030300e41c40040c8020020510b8003002003501e092a400a2100c18014210b00782c80c5450403007050307200c408980005002e41003140c241345560380e00030004014894002c0001402ca40e80d5000c003819a480b244541d14a80c11902c402d008040e00070b006142d040007219003a103e145082e95410850000840c0da030014000d8030700c25860f1aa110b40d086402540d4011592030306420610b03104c080d03519400c20100c1c4208003000000315124400826180380500c900d0b00d0344d03180c514200440d40b44d0314021001c690540254885400543c484a24103c0c4903849440119604c148000310781c02110420642d451004030158010085039685405a64032 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 764264883 1250 764263633 764263649
    0x90106122a030b0a091b14100212131802040b0a030902040f0204080a0b09120d020705010209040c02010f0e031305090915040305040f0f12060507120606020a0c090501120b07050c0304170d0c0c 84
    0x306042808c00e81c03400703044049045000100203141040a80352240c4803040343c6407595520010043c503514101a0301540c0075083e83c001051000b00c00551280e00310501c9240060400190302e034103c000041070340c1c4550002015903109609032001c00c11188a0310342e010030003601074141c800802150f002c461183e200c0c1444916008503d040a204081d81190b41c1c20900500030400d400d004d42c0b000e8007900c00c80004503880e03894081c02e0b80789800003100f00c8003200404c0d81d84105140c103080403c80b004001822808a51107072401e14a8030b21000340c8494007a03400394590a1704e1354a400016044e08000340c2184015152010003040b1808892240b20005540316801084603920030340c044500d240308501100e00b47d42001000500281c0100d00500600d004a031081c0d10162030301e40f80c5007510001e01c00e580108845545020100b02c020804a4010308103241081c98040700301201c85ca507400c56084000017000e45280628010010041d0b11050422400c0440036040d039900d070810840c15038418061 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 764266133 1250 764264883 764264899
    0x512010207030c200d0c06200304210c0f030b10030b0f040609021801090b010801030c09090302071707170c0f011803020a03050105090106122a030b0a091b14 69
    0x20305400d0111100c2c0701000050442c03d2a642c1c61b052050041003144501808122000b403115198400c2d01000e401404010008514043c82d1004036401c0100320784840711200c0b51000203600061141030018020841c10000c0030303c0f9400c0d418540300000b0040c00300400c20300d00c4501000080c0d0b00c214400d030320035401c6861420740e40c0c460500b00041c00061900075408401c15210705819103100180c181a114241020441207200c44019100c3c14000e00024144420700035080000e0300651700418110b0f4401e1069850103076030303202d140000300c42c40c04c80d000d2990410b0a0922550502d03007410300200300d001000b082e1040500c00801c0c114400c0b030022a0402501d219402102a07038200300720019075015042c0014651340c1d0400030b00074a002e48540481c7d500301140040e11100a03503003c0003194220b0700000d54101080c6010041320f0b14030101510840005900101240f520000b244c8900f42c1800042408100361400001ca003050b822485012952850207008164107501c801404030300560780c0c4c01c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 764267383 1250 764266133 764266163
    0x708060612070305220b0109020c030c07030627030509040f2c1507080703180204021602150f09060702030325050c090106080a05150a09060512010207030c 68
    0x365851154100703402040e85000107002c010742e031681c0050f1149101018480810a0a0051000ca190352500260500c1d203c1c000500c81c003d01035000744881000d0341300702d0b0310300b80310710041d117081403415070050703824036034030070400002074030511100d803003d01c04211800d440c0d445030341d016045001e21520300703000c0c50fa20b808947c1242100e41c0040400c2c1d5044002c1450f045142c1881c11008140368032100003809002c1030009940e980f5900c10b4020b00803612075008503600c2010813001001e982c0180e2a420180d01001130158075684002c00846118802c00c294586090042c03200030a03451301003990445080100d03000b40011001610404803048a070507640d0540360000a145000b444003c6800304074003581d03070803891b640811541c920f80c070880644100a0696040041200c0240300d101c022411140000e90800b078603600075076201c80c000700300d91000d04071500483c03410700041d0410304c0c035260b54501c01c1c17141d440d020038003050750032048000754031380640745c2c0d030092031892446402800350307005100741 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 764268633 1250 764267383 764267389
    0x1514160602090d0221120703050a0f03060510121415060c010f050a020910050c0d0c02120106171e070312050c1014060105130302061605061602070e070206070806 71
    0x20a01244d0010000c00100c078803400c544036100c1c084100d80a0500c0382e481501481804031064555154160300ca0310708041d14510140d401d80042c501071001c00d0790b118004039840d541d20200707180150059403003803031401d020741d0604e00b06c4000c42c017220820041c4100704a112440d0000e0815020408e070784440e16010800d0507940942000e0084842c150b040c24100200000950b01600c65400111082081541c03260b03c10340c2d42e8411001881840c0d0071000301e820041c0d01070060b42d20907503c082c01c0420b669501c04100390849100d03420000070030301d000c0503182d1400400c00101c02c16a2084083e508010780c400385e440ea4812003403000400c0b0710061102041440d0081c010784d810201c0000c103807040f8459045001008101036600e0001c200d4440c000300e2040c0d42300e030741506d01c1003001d0500c441002d41140c08200250f00944144400f18032261800c60006105202080c020b02c041411600c04101c004000707420588030b50009da41c9002032400b00012260b00007202504a4103a06042170151100f03004 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 764269883 1250 764268633 764268649
    0x9080c0607110604031e292e030609021c0305070f081207020a0201180b0318032110060801030f020103050406021b010b180903250c0311130216030e0a0f151416060209 73
    0x44450200e07081000040c0210bd81282c45124070071580008040c264850500220301d5420000e0005582402920000368515041c5807809002e9000d041c103216202540e8007030b0003000c50f69440160031810419086581240d4603584442c644072039031010300c0c102800c1c00c03858000180b004808405815040c1d04049041c0200c030382802d440d0084401b5007500740840c060004060301c0c000140c1154110005020388114141c60580e90301c08204141c0502580045006d000d01400554160790b08015604603890b40030380300d01111070010000b003142c09150040001080c618640c003131600c0e2210041011980300401180c1100507851034824082c24810940901c0070340f0000e0007800314903450004014000d0040c0d49210071341040700c041e05007002c4014900164010707500010b01d0010031840e040c000a0042c08421035144002c3d0152240940d56400d40c6404501d41d408640c0003119040c8804003140e0121140416551204d40545015441d10003041d15003804e24029200310360100c0c2a495030307a140c1c15 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 764271133 1250 764269883 764269951
    0x7030e1f0512010603050c04060309170c10110f16051006090522020109090b0111060a02091009060f0e12070605090109080c0607110604031e29 63
    0x16201009038030001401c0c5601070469201403860000000880034468001e061007580030f8513607941071516000e4268003070402e00303104681c0d564a05203a18400140744001d08801d80c1150010a010108002050200d414950895007090310801003030891040d80d2088400182d461002c440000640c0d09015082407203403c030700c4184500b03014000488070041c0e00454002c0f02c44042d0003003900081c103410011510300910082c08110000402c01100006034000001490b043c1089074401c2c4154002500b02001140d40302c90300d582c0880d0561040c144685001c19015150409607601401c04030301405071088803001c8802c100d02c41682e00aa6103a030421001a810040304030b8900c5601d07608060155048481ea45001a01c0306100013000f50f000a890225034030081c061030325040c955259409000404100c2e1900071104010010004803076116000d8014240d40d002625010700d07203481b142d00312003034510070a000c0301440100d110b00a0556425001552518030440c2c1901d0300d0655092000411 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 764272383 1250 764271133 764271169
    0x608040c0e0613050a09061407080a0f06030f080304060b0108011a070f060e060601021207080f0f0405030304080309090105040507021b041b110f01020a08070f020a060207061a041107030e 82
    0x140910012005c10f81040c403460340705601c10302a61411080d08114010100d03100c8c400074059901065402c4d66651010711140c0c1c4400000c03552548a460380030f0782760000c480440318250008100424011148201e02115000741380c2803465514102c8088040c6020184009101c17800140c0b040402c001501855980c1e0388c030001c18402c115041d00f070385440d000700711042405030040112400c2e5248040c0304132001103a00c10000c5091030005c0301401d4075604842d9076070707040d84c508000101d107030750b8200013a10092607000002c41e81c40c01100107001458006038401c43c0a44e04200034041e00c40c3e00802c40d0710910380c00700100c1d90a0804600080d010740106542d105550641c0e0702400a459444550b481184000302c0c02c8072403500064461500300d00c43c501441d03000032051004034134085d00c105401402c03150140b048629050464030741d40104c1c0d00c1240c0444159076100811043c0b09910100050300400440d070401071141181241290792280b030a00504014128042c030040b503403800c02044004e0144 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 764273633 1250 764272383 764272391
    0x40605031e01121727100201021603140405220b0a06210605060a020a03110d300c0801031a060a09020f07050102030f0405250320040c020706090608040c0e0613 70
    0x6058819981505c603124010a1007150003408a8014000c0340c0380d01005100c0048400b842d51000c560741c0f401c000007420016002c0100041035520105c0542203404460170001d40d02140310342000c00c507644d01c006140901e604001c1080030a410400400741c52650071020900c0340c0700a07005500801075900204d5000d980856201c001640c00208100310342d200380c60700107192000300c014550319920066007038006107000007040b102c0121240c2c04a0f02ca40070030544e0301560701c0100c4100c1034405030a68007000621001c01081031286900100713040d0080506005064280380e40400c501d06400e000750550740350001896285d80085800311210a03030000002c54036400c000b000f21200001c02d440a40c0c081c894044104a03070400100c03a2002c5c030f40c440141003080c0340385682d07901203501030740f10200e100b03000c004041c070301764440d4003c903000c145042c2d01500c000c900f01007018101c40307400d40080003003005074030812002905030714030304080d07542c2b4a003010482d64980b00010b8039000400c0c0002411428 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 764274883 1250 764273633 764273677
    0x109152006010f0603020304050c01051b0a0f020906010513140a0302120615090c072004180203060c0c0c06130f0603060509010e040f0f02011103040605031e011217 72
    0xc08142181611080c840351242699250300c02c9090340403e07240608580c121801300e004949c0540014540e40d0b0301da001c0350086c1d0907518112801c210700030b107003a2105066030b0b00c0d0504601d0100c1100d5403014090030110b041a09201480d0241401400785500440440407008034660b1524079070001036030700410444c80c1081001a9640300d8034203584109018a000d6501070070741c6001d00c5031501c40e10640d000d02c0d0500c4506d48071032400c001c0224036460320101359000d00b54681c840f0301607905071030800403100c04000250f1060501d0000018440c0480003810700c1000f8440c000403c4d4040703a9801100d1031615000922100011441d03140d00442c039103c0c24890000d2405d806400c518100e5100b100c01407111307a80c0308800043c840c01180e00030250818000950700140943e8010004140180342011504800341c1100d4555481900f01001148001c4200314800754125070f41c409681842c0d5481810b9490102044881c040d03020005107084049000950780400e02d00540d00d003039110504c0c1140d4512 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 764276133 1250 764274883 764274947
    0xe0f010908030d06090516080f0402010903060504080705161a0d1104080718050f0601080901060e07210908161511091201060e0115090b0310080714010915 68
    0x134181c03040100f95410070000822a103a614400d4400321416211640240e413004c11001503420000c1040381800100800800804e01c035201d154400e508c02d41e0450b03034410080c03c0c42450f041002074a1120f501026034144042d0601b1401c6501009002c1e440075154218030507071401610b0082034503482c4c3c400100d030005000c24005100e80c2180c000410028401c500d8401940584404580002c030303190102d004503242c0d5115181e0305601c04045400042c41c030742c542c004030350740c4801943d00c40002450300300d10290ba9150060080c001041110040000708159920403800d4050f0b4021004025014070400c8280146c88400000140424408026400390130302e01190300c0e00064030080c040c880c070f14502034014205108840656407100010031403a80b0b05203152401286426800c0301b081a4040001030103070100024500a522803421a180e490030b2203145407403c000e5503c000c081c0c00d4807540e40189640c03c0a0b41c031081d140e244249208000c06941d00795280b503d01544e007a40005464000c040c020 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 764277383 1250 764276133 764276141
    0x2906091314100f0312050304050a062f03090703020603040503041a07060c020c01020709020c070e0a0506120a1101050d110c0109030f2a02180f09010b060a0e0f010908030d 75
    0x8510b5948500d640380c40f041c062402c4038440c0401480d1107050700e03150700c03120700400240d43c0c064400c104030707a5041d209503a103c040e01e0100c450442d029030300201c00740c01e006100c000d0218000110a0711815864080c1e00c0b40d503104007910019005500c000007040501000340704850141080c00202903100200c00305100d484c1c0d202c99029281246056030a003038440c400704114074610380c141d00420401e03080c10360000007503002068407c014890484001b032080c00150b0b1140c4100302c0120001698a0202d0520940d5080060069003a4200100071000900403c1150491410a2034030701e0301d422108103090b000b4400c0a04014503108041103031f5481c100150401d1700d05520903503400d20904500724054030b803900e5030140c5d00c0d814800340081244c40c40d95006420031950004080c2c48101c26000055500f003001621005034070f100000401c8a03800c42401020381042c02911001d10704004180002d12031000080494030945451040c41143d81c0315000c900c02030314000c010780b076561407000381900c020 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 764278633 1250 764277383 764277391
    0xe091f020901050f1c0c050702100e12010e0c0a0e040803180106031e050d0306060516060b060403050703050721110d1212061e06050307021c0903062906091314 70
    0x11504200002e81c02a00c14019623035410f501400950031420210b100b507520f11010a088c6421807030b000181d2000080034043e07400146016801b800c807004200050001c030040e1901f0800c5020300e00d81c1031000203460641140c2d4056899403800c049520082000c1e405090290f00c0036140c0119628400d810101c1c2844d41a101c9100388100d50000200d11800c1d816101148180004030740c0500c1030104e003501030178580000a02c1038000003000300142001814a8201d60004d0704c42e50b202003014000c2240400c0408050070314000c0103410044602c180c0d108010705980300604481d99840c400a0680362031b002c03000643c1d0301600c3d66881e0b44181030018204400c00b030100c880c45c2d040c8440000c030020245078030010301920104101c0c102c0d050203015070b400c0d440901402d085114050f2402d103041c2031603070264040340352581c80c0801c0310714508018003510000c440050840d1400142c901320ba103404c0d21000380650090301c0e510784803d14000028807001452942210860030302c22010700c1d080c4140300031489 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 764279883 1250 764278633 764278687
    0x10c08060f040b0f1306030501090c080d081003030f110d03020c010b01030b130b010908030c0a0c090b0f24040806010303080f070e012f01060e091f020901050f 70
    0x38540000030031003070f6000000320f140c00c40c40105249034542806480c0c0103160301c40e91000304802d42d481e80c032242118070183c004d48046141e001c0903c80e0b0803040c000c0e0590758640b0720f40300c0307002d04018146541c84145840014181305182020040302e41c010254016454503200581d04003ca032810094003035805082c0040d11946800b4040340c0700c1d8060321521400c0304000d411200e078001780c3c0545034000c01c41718818505010481400156600e4104024641030781c0e01d40c06450031042d0ba10300302c41e03040f4a03074200c0501c0900b0043c01012a4803034043d0942c2d10718046803034810725201404001e080105d500309046a107040010082903415002030014101c910a5492480c1a55143d5030068228000c0e0b5424002480b0300b00c140b01c0310761040e48403201e40d03941c6c20200300c1c0d0445c1a812681046d00182085583c42c2d4481d0020402003214072240780c0d00103030220141102c92001d0a036150684d10f640c0000051940c04501595546d109009464001150718025591000c10b9001e00300c50700d8070040c0c0088 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 764281133 1250 764279883 764279899
    0x51309020307121d0a080d021b0102070b0a0501060c03120204090204060e030c040203010e0112020a180c031113030311030403120504090c0e0d030503060d061a09010504050405030a080c0408010c0806 87
    0x90600581c000004e5859800d000b0301101040c59852014a0b403081c40001000b507020b0015413180104208016502088400010fa83e11003c0ca003882c0b01500042420801d80c1ca08001048003907000808030340e10640c0f40c0303451500c1208280192009006075009440320b1440490040380c3c080d0052000c0c507129030114201c440c00051181004181d2009024a810001c2c20074010001011034003229680d082c4010504101d06850701c0c40140401c520f440040c9115481c2c044009003150544596503000c64110481032500000340c210910000302440003c00304100b921140c110a407041c01624091640110075022881a5150042203608940a00a4980d140003402d80a20b03020300c0130344d0030ba402c0107000601c900c1d0322510182c6054000030700158002d4502141040050154400c40115503000b90a0408200c1108140810511f0580043d4044c80c130b890305100100b04000192100e00c04949003000c03559650114103a101e0280fa484103100d5070a1480244207140c11031801fa10030241611045 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 764282383 1250 764281133 764281151
    0x180a2109080105250908030d02070b0a050f060112061205010606080a05090a030804030512011e050405100e1e0a0b010806010215010303050f120a020307020d09060e0105130902030712 80
    0x1400c980c1c09a6900400603110500004c1034180022424221111030611904650382c0b200b000d4150381c4807120414041d0781c0069010100803c0d411000d800400d003900030005464090b00c40b00e82c80300b022b49041d041c0908000e0726000184281c1000c40903103030020020290101500d48107000e41014003503400810001400950400003a00c0b440344100030640041000d54010744041d64003c102500035020440204002ca040210584c10140204000c669200d12405000003840b00711110382c10440c8101e00741014000c040c481c110382107081c0c03020480902c5082d2900d00120840718006100c2c4070010b8501030800142440c0f07035004003696402030301c1e0703000030340c0d0362000498a075002007054003c40c401010050000c02d1250011700400b51000901a00d01055802407501041d021540440059000020041c149505102c2842500b10314104007080504180025010500f240880e07410030002040352440c0089400d004002003510200855503404c0042d8020b03c450483d100343c3d00e0213801c0c44505 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 764283633 1250 764282383 764282399
    0x6060d11090a230d030314190501050d020603041415040302030909011403032a070803030402040b01080408070b0a0b04020307080907060203131e0b0c031b0a020108180a2109 76
    0x280100f0036284001e010b04030341e9004c02c141c00c0782901c410f80c20956030300e07448440c281840740714a000d80c0f0120b00c0101c036a50015140302c00c3c2d42050b00181c2c018020301b0160001615000c054a801a600103154800f80301300c401200d00d03140180c0b2181420f40710304010301c81416008001415502425608400036a0320340707035241c0140d003054000a815074000c101c81e0402d1440d41ea140390020010303450401511442c40307207091400322560000703000e5400010511045282520039041712400030b08082ca00d40ca001e8403400d4541c0030308100503225440100002c1c40da862030f40d01a03600d00070010002c40d124148584d00404100c1c04030794507103503446544c4000c43d50303900000c1610b00a0510041c04800e590900101c10f4550000d01c40c4e82002946014011407060401c3c00541010707802d076401541c0b45c961040c04202103045081403060305400c2007a2140250b40c0c400d40413980450306100e2401107400c007110312460000a180e014201c4503d580c0c0e4482c02449106c1c102e01604603e983d07200b0710b81d03114030407 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 764284883 1250 764283633 764283659
    0x1020705012c010203150402030717090706020c030a11090403030b09040c0611060402090610020319030b01020d050414040c0c060507020d0314061c0c03080a081b070b0c0306060d11090a 81
    0x30751706606500603102c203441d192523001107500440390701d011103400c01c50b84048542004240ea2a19141d042280240070047c1d040007110030403d4100d00600d510030b03841d15000c4c182107035254154011031b81880020141030103900301e0348000300e000e0112145031801e418449200c2c055401141d0014422000c820b0b0504000140e20b8020fa400400701049501c8038010002800c080720002025404180070f07142d000412540d40414030016500c020401d5550200021305146800d5005d500307100c0184014481480d405030303c0111b1131010f541c00a81d113688900300b130328104286040107005504080410a0080d030214002c454084140c8043c40181c040303206401012404036011500035000809400d0303e054040048206240241c25904c2c4564072a10788076040c0c3e2140e03400201040604052000807000c1d41c0d2941d0b50b500302d843c0d103581040392503540e5030742550014094554031007001c4081a03040d9101c1c03044450076241c00400f00492103403440581000d422041509215144011000074041c1000c2a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 764286133 1250 764284883 764284891
    0x50f0105070201121e020c010911030304030f1502070204150915031505071106040b0411011d0915030f07030b01080f0a03052808090d020d0203070f0501020705012c010203 75
    0x15444074002c0303076034a003100034045482e00d4079082d0024105d0584800c00c520041590240180010503c0c03942c42c1803401440742d039041d40502a41c0108420008100703016a45000ca1b6030098018a002109080e18006402240c1010750b00503c0d094a0144840c6610f060324119540500700717100700d4454610880c0d1a08052002070b000c600501050154101d050784150b03070240107130522401d0320709184402444c20000701d6049030020800c4090000788010f4003008003241100740383c0075040c81424075449160309403039424240200062004100160000c0d00b041b03040c401c01030229200c0c02d0034001940d5450308644030035980018030800106000f000460f4440329a00301300018032000345c05a800b00d03582d50200780b00301600d503a2840d441910380f1034030146410a0505903200c00150618002e906d05007641d90424405640c010b2502c5284075401009840700144c000005415640c03040c20604e01a1084890090465181031641000c180f8030400030105000c0c1001042c501402c000306003804c070b20090ba = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 764287383 1250 764286133 764286137
    0x705060a0e030a1107031a07110a031d1201020a05040f05060903060f10030c06050a0807031506050d110c0a150204030c0b0306120a080901030b0306010b030a110c030301030c050f0105070201 83
    0x1c00b044102e03024441c44c041c9020498119140903030740c0d80300c042e004864503a64044032000b450a001300d00b5400b102c450122a000c03c041c0030030080980e00980b03a405020044251221202040d10741c999480c4c10100d0341d00401802990b4402468200420300d611900032240700700034100c0085100c1c10b04800746c90300142d01800070455a10340614030070345103c005040f01010419144084001030f0841d100c1c10041038907440381c0d5101c244009014003030020040a2400309131401442880c0c46d00a0703050402203d0041c01c190b0350360b904201c142809400f0000c05500d0560001034900300c110030015004000c0ba00540e20b6040001c0c0b076001d14806d81c07040b0721001d422286445014009101e107600110307000768006006543c1004d540d8801030500c52406001d841200c4003080004880d60903020340d41e5560303800c0340507100301c2d810000403401c5800050940c910040c2e0300d103c20f242500904040300d0714014a0011a0b4903036a4a01d000c56681d10b181c014140a00e0420302840419401141682c031995416 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 764288633 1250 764287383 764287387
    0x303090307080f0d060b040e180715050d020c07060915080a0c120c02060703050a09150b0d050f2d0604060b031606050405181b030402031c03020705060a0e03 69
    0xd03071220a0b994000c8104041800340800807042e4034082880f9280c01032100c040850749843c0340441c0b006c00103030004d1003105032450310700451026000108042003511960190700c031140c9907460701241c0c54000d02042000840c400141d1143c90000010030408844d0207030b0b501e450540e180c0440c0104103455001c40804a075505010403030900a0742c1100ba10681103250020780b5003520007444095410040074080560806001e21290039494098a5406006664180720741003c55035000c01d001c8403c10450341040d500d8107001c50a546428540d80b0344c0360030008448800f00c01c0000c45440c0c0742003001302e0320854120039004a4100354600c0c40d20009040e2000703003159139030310744440010307044801c070840d40750058001d07068101800c0b84085000d4041c40e035649488a0402d020712030340070002501c0c0180c4200300e01c10003921700d922705c109071180071a0070303403540d00d07500d4510100f03252410080d000343e094071304240c001524039410340c0a020921301410855400d81c5460790070710b08071032105600061503041 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 764289883 1250 764288633 764288647
    0x3010c080703090f0803191104060f1440051c05100e2a2d061b190506010b0703090909050109021e0612091f05061203030903 55
    0x764004510f0034001c079055400ca42c80b50350f90b580f55074002c403000054041c845660780c5003c8910b1040001100c1c24003034840c034080c18260040c182d0100700b0300d10020040c0080861b1000340c2c0c150191808040008003c0000d0310480c1c0101a04846011800040043c0d003110541c13071026404655045a00281c01322002c0f05900780c40701620341d8125000e45151280c040e030881e01c81c215101c1c80100710000405810209c2615071401890800a00c1200c016010f2042c0c000c0595110f2903400110900e041010300c004030440003464803003100340c601b10350010011136440540b020840f040c10001020809840700b843c07001c01100142c1c0c400200140180e0701ca50700501c2601c0c0c003a0014001e0764041d05042c000303580c0c0c40c2050030940e00140400c44299455451341f404504160b00f07091280a84140c0041c4502d84442c00f05015000d21580030043c0c4855901003140300c0c8c02800410740c0d081640412042c0d9811050070030014100030f9907054040d941100d1034864110001c0b050b01d001c0c10910703014524201e8 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 764291133 1250 764289883 764289887
    0x10020c060c2706090d05010501050f011d1903050102040603050402120a050d08090a0b0c04082a0d240e060112020904020d0303180b07180308160c0504090602041403010c0807 76
    0x10b54456003a4002d4810481460a6aa24400188054070400001c2007542c181800e1084064682c0c02c000e06005119069404140c81c0c600d00b9075103e0001c2c0d0314035001940440c060405000c99078805401c5520014012400c9a03041d04914070480c02070702d19180041115041c640d4940213214064641e03000851a03504180c230503c1025005018542103a0200c1910380b220907204605891070140910005010041200142700040c505200000d03c09000b105509060f081e440840000b14843c028014034481048016a00c6040130400301c40700c451203215100c600c1c001004410001c003034603c101800013803020411949403201035400b4080c0b01103912250b0a106896008034000c42c2859120445161843c000a200c1d20189010b4420380000d803d041320081d01c801c4091450045800d0440f100707201007030450b0f04564601100b44c000440d5402e9a041019184405801843c0d12609180300b400501441d60040c100340c03040c45003c0c0c83c900c0300440c10142220382c0c914200000c00c80310703000541898 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 764292383 1250 764291133 764291197
    0x103050d141c0b121e010c051213061b0309020a05061602010c050114091606020d08010b0c0c060a0908010b030318060f0706020d060603050f3610020c060c 68
    0xb10003408a2240d840f041c010681003030f08003c0045581281c03810601030b40d03031007402461b0850105007000d901d42722807488102c44024000301143c0240c100682140b080042c0d070f034007c14035804e140c0901503809119082c001c0c090500904268070444521501141c03034030b010300480740c0c40810b40c0e4003040141000e600540d182898071206031819581c7e5851481507008284a8174898a2b01002610f19507441c82080b000d8040d9540001d4110b50002c50851485a00210103905540130342c0079280c0c8550000550504d01030032170070690f07040f810100381c081130a60000411070a03100301100901043c2160400c1c141c0d64003850f40415161410302014202a051000040002c405c0680d20700340fa1851980340c40003681d00480415180540e5403d04000c16035043c8242c50700102750144030012070804c551800c10400c031004480005070550403003041e610703480d0700b90341c02d02c44451401e13240b0b10300703040c500200213401240d11010b040c06801c00040c560090b1030201c0310349102e03a0990f2103d003580402558005 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 764293633 1250 764292383 764292401
    0x106050d11040302120d1103030903090105071506080610080c0603060105130e0f0a0506030a170904150b0d0506060304050706080727080d030908090405070e090103050d141c 76
    0x701008110200150311a15030000525038032100030032952000a41c003c00244c0310354105491a0000c1c024400b01403404800c0320042c6109182158603500d44d030411052041343d5400c1007502c1e9140c0000041c1948000c26494480c0051440701021a580c982d0a2616084030802050b0b1165041000460b190b01400182c0100302507c001c0001c00c03921b1b00141d001c100401e81c1d8031a0f01c0d050100800c40742c20601c0c0a02680300070300341c02500c6005555591800c0300c6000352041d004050001c00d800e0074a4a030795100407014020340e280440310079610400303088680d1180170802400ca080800043c0281800411240150361100003007066600c3e126044682800c040c20b81002c000c00c0b10412103c903034800060304800341b03038195412406854589510724083d03c0e0400380080c941400c6c1e040000c101c54809580300c0c0b201c29100480c86aa45120464243c0511005207a0003904840044180403000683c082d07c0821070710f50351406950212510018024000b0361104513501c42402e07222080715070407030710030f03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 764294883 1250 764293633 764293661
    0x61017070c1203060519030308070c020f04090803040605010909170a030f0c020c030c010f05070b0406060504021215090c0d02090d0203030c03270603010501111204060309030f080106050d 82
    0x2460742255102c081c2d41080e10b880382d001036140d007010722440ca41030744020300700c0c000305c020024100e1950b640038040d00c4009000c01d041c030440b203a0900941d190000d400c031440074002c200f003199410702d04e4034003010342055030180c50303180ca0302c00007040402c96845180b512640003a611154070043c011790441d15030210305480c04141d254003224145501d58056403100c2e40e11a009081c1190b0042e003070502c0d02030f44800c3e850421810401c046d100e1900b000807642803540100708504e140e42c860804401500b020391116400c54400900043d0000703041104a020b42540f00c1800c8030203992a041106072082901c82040321001089584030411070340d4010031085030043c2c910891288141c0019080d5040341215203010f400005810001d40d9940a038043c2d00c05c4e09604101d003051001000c511980814080d007410b004c48050700040e0701d402000f11480b82800303030405543d00c54998030028080c112002080b008524520200100d007030044038914103803500f0f030341d80c3c5080400800140d80a860a60079101d8 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 764296133 1250 764294883 764294897
    0x90c0307090e250e0907050d180b040c0803090603060405131b0f09051b030907180b0a06020c240c011406030616051e0405040e0109050606101707 64
    0x3075401e41c0c2d8100b24410540c0009807440100003030361648140b0101c1d0240000c1104689a100580e5983d614158203c0720310320700561912081c1401100908001d43c410098201d8a0441c104000000d181c0600c128030030141118620750310800360303542e4040c004403568807600a200080d9039007020307409264003039001108008010f000d5220b03c0140c0d0300b003549005c15841d54045c03d20110400c9138400004046441e1f040018aca800b00740b00e110000c03200501c00d0f020f180000425a082c02c20006030026003030702ca88043d882d1072890349030001403103c00c1070540101d59030040000c90b1b5001150a503101c04015005500400b03601c0c5880c14484083c01c40803003042014440716102210034415881001060078654201d030400c2010140b0f0044000d010925050260113403c7e1200c1e803140c1580c450404500c4004100b440c0b19011002038090703600990380140c41c1c9440c80600c07440c150080a0018055000e42d4080c0d12203000f40002000c200d120400450000740d0900c3e0361944118940341c0c400c41d1440c00903 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 764297383 1250 764296133 764296139
    0x2011121102103020c0a030302030d0213150914040207110909030c12071109190b041815050f0c180d0212060702060c03010f0e0a1b020a0309050a05090c030709 70
    0x220750102003401c00d4400b522004544040580410128014620850341581903510310343c0c00035075902c141070845041c5500031901d01112600030840f003001d40400550a00b2001605000510590440c81031140e004901044603406080501c01c07903031556041031240d0050b440d11360a110120a0140c00f42005102c100800101000d003808104041c102207601030356074111074148002d000c0f0919070050300c945044018480c40041c03036070001c9030419a802001c6542c1011000090041c40c0c0d408051801e00c034200e00c8001004003468050316440b898a8042115031548140c0340100c08003220b0030b01811504001c5852000c80b20000c1488030f140003005040c1641190b40421048131f800c600e884890350041c402d00070203e40500556030701c00d02c0b440d0b0704d80c203540c0b40c82d40c019145600f9110741f81500700312101103041001c131a0845004441d00d200c0d001020300017044029a01e1403904800e82c001740c0364038000f003000e1401504090071128020f104800940310381002d510680d03c0a000d003818444020000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 764298633 1250 764297383 764297399
    0xb0405150c0727050a1406010f170f090d211a060c0607021b0a03060e0307050a0c150306050d0210110a050109021816050a03021c0b010201112110 64
    0x800c0343c4658048518000a2050440070648a002e403030740300103908100c000b103840910300d282c0c16803000003440c00c411448078540c0146d9030900001c4000510500907802c1000031030310310820500906810085802031034903110f00301c680141c1182c41d01d07032003000300038100c000120a810005c040011900078215030040c00c1e000450603800705000b041103810007400c0021003601403081010091207144031515070448200061141079045c0030080c44c4035980c441d944e1a55000308241d0380401d0380101102d802560300c0c00c107150310b80410312032400c0a5901c41c0c0795659043c0302e8001c1e00c080f1180a004030403584425070801c104010000d07107440c100075034103140309c10800041040f2100e160142000080800710b41c010b119a160b40004021092a0954180200041741580701c104880ca00e2505a4403241500400c03030103441009040151281040721040c8042c04581c0704496488090f002000702001644103c2c02a010394483c5076260749940c0703460051007416002c200d0340310300f01000200349103840d0252 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 764299883 1250 764298633 764298659
    0xd0f030f020f0a11040c0212121003080a03060e0c13090506010e1c02010e060f0d09031b140c0a23030312040b0a05010519140d0203060f070305010b0405150c07 70
    0xf0a582c3c0908411900645003001d00c200072182c0c04510160800407042481c3c0c940d10b00c10401c000c901107100b0400268010030841c4140051603101c1502076803900c030184000c000d403240c1d00440a10300142d80120340c07214652011544101c88800400507030038907020001f801070a00810207814007401180350203c80d503403055000c404514810540181c02c40328000189024056484580181010000164022014801d07192003800c04140414003507801d01c0c04941003601c18030040ca0642e9003001820400500b002146001e0f0500b4048446e032079848820828012410b218148040c01c4080d040f8480700c082010f8400c280c100507049074074040880300300100c503020480b02582d0340d80c2e041042c4000c005060040034010001200d44032a030440403901010700043c1445100f001c1c168951801296480e291a9844040e4000342038515500c2e1500703008880d01b00c100c6243c1e0020785807400225100d0745200a60b404d0340c50190000c0c807240340030056600d40380c0c058240500b49124941c0000345000740004 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 764301133 1250 764299883 764299903
    0x170406110d0c0f020607170309011e0504021f170f0a1b21060e07051210080c0904020102101104050f01110307020105070c09110a09050d0f030f020f 65
    0x15482100304501031a580c10088030a20302410007101d0001d540110f10303512804040d09804589180d580c0400d4642049443c204a020f03603414000401004501801035108200055100f500701038000e010510b0942102c0080305c1c02940404403804400711482c1c0d0031403030501c00017103003000103240d8038450405a080008039420040b4001260800903030130788070700403400d41000d0003001d80407608500b0f4000d030211400c988001c1d9400c80200035030400c0813003504550010b0400100d0742c4190700b061130700280f25905c000c102c502904036070030100d00903e284a0340c003411143d10802070f00c0700c00310030010045074410151060741144a0700c90741c55070071200c80c0306041c0d50904030343e4200da87d80d14050038000001c821445040c14005454054980308901004480150341e0900c0d00a503152068604502d0700240b81c0c100034003081c68229004110a26076000b4110500e031070300c03407282059445080080e0904d552000410300c02012a04a0010b070285000030500200c03401035070498401c801e645480e04002030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 764302383 1250 764301133 764301137
    0x7050d050f100e060d0803070203130311010219080904020f09190305100e03120a09150902150901020309090702031e070b18030a1116060e0f10020a020904170406 71
    0x71091110051840600c80020120031040d002c0fa8580540002c0310801903a0001d49040030020000713003900d20900c01c9a070110182508034407615200c1c1010304044001824450151041d0814040300401c001e444281301f80d44000721615180441c014403003c0c0d00614050002c2200500103100d45545078107001c2d05001ca41103a2212091560a155240a41c130030350742054141ba200b105040d0030404012074858500202174462151100c140020003030152103000380c0440c034454202000702c491a0807211800b40225101d402036006501400c200d07200d4050441e000d40c2c800c001510060800c100110b0303000c1c9080c011f41e801d203152400d0488250b114904540c2c01501d0005500081100d101c048507003106d500445d01c1e2580a69592084d43d9111f61205803041c4040000710241e0b003481004009103802180045060307c2e9a1141d0140040080c02407052007a131406915200342d0418008140200e84030b68010f0440c0e8050b9000d2211001d405070060b14054084e004040d200d241c00002040180525 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 764303633 1250 764302383 764302411
    0x402041502060609070f08100803070c1715040b060d150603060e0d091a130e040201110109020f0d022b020102100605030a02060307030f0e0d030e07051807050d05 71
    0x2040c402820200001c01d05807007400c4100174009610b91020340644d0309401c500740a80d1507250140781c10601d100d00d0307111490520000503003108202c200302c102000c48103403405080c00076810402c0325803540200204480642c24a0000401041c11040055007158001d018030804800544441c411412090764044d01a6154a410400c024a42c1b089401106182d8058140200102c0c1b004010620511507000528801d80004980c1402c901c1224049984100b00152030f80c0da174512905040b4040b00c06074082120ba15691140360818080c4806503a800dc0500d0b50152541c02002a10280c6001c266048244400030b22a114406200800c001f0103191090b00c2c91300c8030340300080c5402284103210f00b141d82802d0f420032190302d000510340135655048070801c0e100c0e83d8026045004140070780400203a14140030840070341c09000705003031030003684680d030a01c880141083c1141d034401c00e600c9282c2d00604032088210001d5548601c0fa50445620329181d40f82180301400030781071f15070540340107114801c4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 764304883 1250 764303633 764303669
    0x3010e0f070905060d060506030f07030b011a120f070c0602120f0615041a07051c02070f263a17150109080a0c0e0105030316060b030c040204 62
    0x30080300c0c00030822440b00340700ea468400d0206698509405c1c009180d40d80f6040030400c0c550b0144046000c8441c40380803100d80d95a282402c980c045028413401500c02c202001c0c001c0042240005c17260014003030006400c103610380711401c200304400248810200070004c680b440004582d400282900941d003140e03910141000f0043c0311400e00080c0980d4401e0014032409004a1082400c0d81c00712a0104400c0c6002540706196105034810085c004145010745042542c00a40d040003802195400d6070845421f9512070001c2034590b0f0b0a4010035060f07500729286001000010300030480541813000503280035003017180d086685d00c005040c00c000403100f400c11b0f800d000c3d42440714260380b50f8500e1800d5580c0300c2c0d8200c860426042c01404004c0095541c110444140c0d006191500c02010b080d000c48007100c0c0b070360511050040c0140030b0b0081194a4400004a5150001c10389050090061322380200060503982d07100184540c1e608250180101131a00c9550b60b01c5102410040000f54003d0b0f00d0603107 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 764306133 1250 764304883 764304913
    0x8040807141603230a02031f0b09040f030e0301061d04051e0a1b061205180609010e0c09060303030105130f050a06051009260709020c0d081e1603090203010e 69
    0x4d110030004407591280c00c480300035039800075078500c0840580700a0601100d01900c0a40038020901025030807901c1c190a001c1040503440d1a403400718003075900c00b800b00100c0c41c100b40c03d9850310711418000945040f48500001c48190300150058403650840311650108001da032440c0a41c00700e00001c940007030600800740070206040c9064015410344a811590503c403001d86429030381400d80141d90b544100041d0100c070b4002c0c101d10741d6120581216890b2614a0007240030300002100c0e0813507401481007041d0f13682420000340740100307001405903045a080c801488001709485141d9840d141d1120b0801300900399921805014807a100000f00705075051905204812450507400300810116030701c1000030440481130b1b107401d004074004208030381e03420201561608207950405c107180c81c0b00050b0300d1203082c0000340800308001203882c0c0740f030650349420400107880382c5855682c0c1294a2200050350026010007260000c1c80c1d14240011140e4194002c41d00715410094549043d0740540d48406010b0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 764307383 1250 764306133 764306183
    0x606090605040810020913060e07030f0204030803060409020310050f39090f03010513020312030702100c1b0f050c030c2d180708060108040807141603 66
    0x30400703007001c40ca007928142c5980c0d59008501d061000403070340480c2c01d100726910460a070721201c201c000c0c107010942d2583e0310010761080585120707011900e007070076007060300910f030003a01c0031a03030024031041c25175440105000250041810491b414002c1403201000101d0b5403040c2802303654116248242840c101d00d00110200b0f2980361441130583c04442e040840c0d0440c000c6100d1404400c0119842d140e622000c500124650104140e1550800c41000800d842c181950120180202c04039580a40d0034a2083d00601c0180c8905005030001401ca801e47c0c03082d03030821201d82040b4030300546610b401c03c2600304a010046012940c10901c140380500b8004108424144540100c003c0c00d030000009001500c00880c07045144440041d5602c0f582e200f01c3e4003e0380f41c85010000d0080e06c040880b42036403c82000c1c0071120030003c14000c0010a5055100b1581144510743c0720380c0d014070702250b507150900307402c0c03100303c0c040c80600c100d86184000309840d40342c40b001175100d508080d00d95190403662040351 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 764308633 1250 764307383 764307389
    0x6031506080c010c020120030c120304170c1c03020d0608010612260309030a0215010b090409020d0813140907172a04061205040231050a060609 63
    0x8a0610006111515010504610210007400e000c84407446034401a100f00c8510a0180d002024518640c4160000400103280b081c1501064880700318080710303441c55902050341c01600403084216207000c400d0405009000080600c2d040320720460f8043d0703250f40074031000001d00001039000700e030302c1d04001c00750f00840c4084c0c2404002440a0303802e03c0d00c0b01000f01480c4001519003065103a030000f8004001e030a80c02d031100c034481d00e5640e900c4d00140003036032070388102240030051040c107a886400010301c680840c16108654981854406110100800341c04180030590748958020714240c002518a4005d109440142005403012450242858640d80b4200c45903801207541c0820003000a034080c6064102e0000300510003d2070b219000c10007601d0b8030311442e142c0d14054003518918540502c1015004840361607030755512000c130740701100f010340c0e00036039000750400300203c0d5a4040002428800c29083c40013581022803402500400c416200159103030040c665642000748462170340131002c1000703 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 764309883 1250 764308633 764308673
    0xd0c0504180e030a14130b040609080f06040303020c01140114120601210f050d0206040b09010e0c0108070e0415030506130b071b021e12070614130f090603 68
    0x51070102020543c691042511101c10403502c480e880e1241007201d4255451003410b1404103120a4a030080c1c040950700131b01034403011404203040060401c800051100d5480050009411691175683d0b054004c0d4100c0d0a0700341e025500e80140c2c1c10701581200743c0c40d0003404e58a601454510040040c0000061401c2818121742c001c4801400621011720602ca007064001d20034020001e584d0500c2d4607444c401c210028400d008000060300440c0d40043c1d100e014501803210940d06860790302d00c1b01d0803240f650011850070b8001d4041c4050941c001c80c542a4810b02e141002c034900901e6a000504640d48a00018031844843c030091040c0b00080000d158000121003040300c0244980d01c4400004000030409410844a64a50a500c1402c401e0f80304c103203580a008616034404940359401d840320403000b4540101d66402511180d8000084c0385000c9801036103469240f0100c401300070005a00051201075800c000400000c0c9425044040b600200440c0c2000207181d821071408060b50b600c0030303e0441c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 764311133 1250 764309883 764309891
    0x81501090b0f01020307110a2412050f0a0c0e03030c030705010510050d110d021206060135060f100c03020c011412060d2001091203051e0d0c050418 65
    0x10140d13000001c640c1016000b840c061150f520080000380800c000d5000000101d542c9600880c10300d282602044031002e0340c0e00d640c40d801104030f10000841d80c040310028001036424012454288240d40600032565482c5000d0110041500104c1d15503030150b045284103034070003d032601c1400820b115007600000a0741224000720b00e020b00148001e0f00a40010300070303041c4555400070a544041102c10460783c007900800c10a24022070749511000c040b81c200c1c0c040b6186019098050000031401c00c00c140d00c10b4207107450079004d480c58440385800184181d8103d0100075840e449551628941d0204e84119a00c1c45008640c500d0000c1c203041c40c4442d071905000c00c00703844086042260099813600d8030707840d41a01c207079130314500001e4080301c40ca28040d00941603c6000ca403003250174814450022400e80301d054206a40381c8010000354040c41c0080c000aa05206218961007100c00e4803415110044c0d4041c144440401c1d65000c554440c0308840200700000780810000300410a5480c09217101e0310200 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 764312383 1250 764311133 764311159
    0x40b0420280203091002101802180108100f0e0a08031009020309030a030b13050f01150e0303090919020c060604050603030c070302060f0c0109230601060f1404081501090b 75
    0x60b54034080c400c041c078400c0803c580462445842044001c07010078551f02e003800298110001444032044084050703004000180c20b07409034411114501d41241c441c0d80040055440b00c041030402402d0017202d482c4210f4456140c40c01d071020800a5140080c020070902d60b8034200815401c0c012415a404500450b0041c001c001d00c005011054503201c80c2c141c24003280c240300800000d18042a10780f850f1329214904014031001c95144803540341610541c03e41d80303070400b030050700c142c4010300010104c07581603004221602007801c0035440942c002c1801c0710b0345101d03e480442c0d054143c2e0000103440280b40e010404120152809004254001c04290702541c54980100c008a0f107480c0c10f8040640a04800103013106011078560403611500d99140082000307480350301e40707214610238504e040702810711449590200780368007142d49812221141c458808118100c02d0541d0f04405900b01c0d0014518280800a5192018000c001c1c540c0f854804101096040c200d8840c100c1d003050b041d075802244803018035 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 764313633 1250 764312383 764312387
    0x4050703030302211302010306121709180c030f01060908101e060b09150f0a08190609140702030a0e0f030f010608070e150a05040b042028 61
    0x800940350103180150307948044003d40044e41d8203609481c5400d40c1c40e0010440011040558000c041e4400d990500010b0355800150b5000702e003c95016146c500c01042402184140c0802400b1010700030700185203911541c5443c8070b482c141180d42d00c000540020070000051406407143e40503010b81c6c24010701560602080d550381e0031040c129065819a00d80f03030090072051000300241d019800e03a009209041d1031700c0c01078080750040420f140c012a6810f42000b0220840c90650b0007500c920340c2c0040c1842c894030780880d0034541c00781c52200d0340303000c4010100d103d101c0ca000d64000303818036643c0451802c03040f0a955044501c014001c0c000c40d00140b241d443e0a9500c440020803c000c205c1d204d00e03035088c103440080c1c100f05a01403403000643c82c3c240001102e04002c04c07408100c41c0da98070741e011640d40b8000d802c40c492042e465800d600000412090280340780036800985029030290000852001c92144a0007640080048000381c0b10041121852030480c403500c2448420300d02c18103da001001c0c100 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 764314883 1250 764313633 764313643
    0xf1b0601030f15051e070314090d080c0405010f050d0603060213030b1b0301060e1f080709090207030c0f061409030415020f0606060705030705010f0c0e1002150a02130e0601030b03060405 82
    0x14045c044030094011400c924401d030800f01e0401c0f03040c525826641040c4410503a00e90721038003002c01040d4844002a200e1008800791400c903401078480e40b0340034041c0749080350182e000c03c04048101c0d0303484201002103441c9101521084041c14803440006065040c01c442c81341c1e005000c10019181654002c00144953301035904480071810301213a180403c4000404003000441701295820381c408600700c006610010f980d0150302d080e04c0303003412907413251091001c2e032150410141c0401d00401e0500d0000d02484072280e080d40c00703400300140c201d68044820000c0b01090711040000e603c045070034484900a02d600d08001c0b40c40740001e000421500c03a01d01c0c0c0762000202501e12809003c41c27440e0602c0003c1c02160509540a8005c000302c1d61469035900041500d072401c038001403246480c482c000c1c02c1561400c0080401034000b4038581c004c41c4c18007120710b2310042450510540a00c0748001500c081146840038024142c43c00009103048030004003200c00040484c2d229900c49410301c03002c2074010403 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 764316133 1250 764314883 764314921
    0x160f061106070e0f0f040905070302040c1403010e060109080d0f270504020705010e030a08090d1119020312070312050a0204030c0b130e07050d050f0c0f1b0601030f1505 74
    0x50ba104d820551100040c00144644400c1e5400c54200819a410441c020030100c094a100b114200184603040c6411035010480680d404401201080140050342101c140260b00410506d00303040180d44403400281404000445c2030045001c0c0d43d00090310b55080004107899901000c684400e1800c9144024002c0303c05220702c5008079400541d201c18400d00307401030b2481449000880380d58050140009000300c0c02241e1482e814000d0340c02c140302c03030307449134461040700355841000f00008204072000c50090840040c08907070600c184103a00011180940160495038065141c440406a08440e08815078000901b0110000d104200500000e82d25950080c2985c02d0390300c0d400c1d25a0500c0812640040c0c864212461a450308001c010070150710000802e108c0725900030078000364030b41190103000c840054944840c62201400008103d401d800c000e40101e0101403041c4004d6200d500c03085060590a070016036140e5036900000d02442065002184606079401e0200400d140441458a201c0303c080c03 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 764317383 1250 764316133 764316139
    0x20a09081c030509010204270c03180605100312030204080f03040305070b0a0e030a11122b05070803011202180402010801050108090102130605130e0c030117160f061106070e 76
    0x78040b4018040c2541074401520700c40e407602d44c45041c0f410301a0148c82e0b00e1389803021080d0904000040f001e20900444403506140301c0c01000c032080c80d544001c080c1c0001040d10f86070700b0b0212400004140e0107000f076421130f482514016a03c6007000b200ca824040840d040007201e5004000c10800101c0018044c3c0882e09092840c50b1949500c12084494507100f8000ae80d051040110302400d0102c44000c03400300100c100da452101c2484005c0107074490003600d002a056514080500000038600d144507400d0481b0341c41c01900d0641c155403564110341017030700044a4204540c20603001c5080c40b045018501060000d0034495280603400241961707014080d0a040280c40c0307011490151094054802038203819410380c031001e07240e5500034a20381029542940d003014810000411b48410306410f401410030b1080710349503a007030480c08203a8000100d941c070750070300c51103940203155201216000040c00f040c540c112078042c81d1400c01000390380480c024030700c01d030005014000040d4205c45080c000d00016 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 764318633 1250 764317383 764317391
    0xe300301050a380301212301090c1419181104050303031f0906030b0c0c03070c080a0c09110a0c020f03030d0b040509010b220b13020a09081c03 63
    0x52642c1c1c1d450743c0402403000719044000c100d00c80300c40380502c02a6058900e1042c1c0121242c00ca4582000c107004c08001c05004404e010194500f20012a1006900810104004140d402640c0d96840080301c455211002003681d408a110b4645095004070100a01889095224504100c807022003440401003481083d5650105051005400c2c0150b03402480e00509a03130712441d01c03e00c0d40d840302007004c1100d0759000240380702007050860303882410b051302c1c0c00050019055450305001140d03980480d00c603507500d03c410300a810004000c020401d02900180d80a4001d50b8428a00042d07003003032580110780668101300c00740c80300000340d90590300e0620940c501685000d03040e00106034909601e1356119018040001c0c800d078079100c00d40003108030074000e40f001c200d00d607602c6c80446c0c03c076000700d040b2941c001d03040f075101004045901000d540e00034004000141151000380010241d071200301204030344070b4011583d9522141c001c4c01c601c2c020111080174264050024103841806c4980701c01c05018540d403 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 764319883 1250 764318633 764318669
    0x405040c0e100f030b150a0b0f0d020d090302030c0c0607020d0308130816200d030c1a070e1306080c04091e081312240e300301050a 58
    0x2a8015007009141d01e901c9080f9954603405e08142c1124111601c4410204e0098004064103003442c140040710b407c0002c15040054541304c00c6540e500c035000c01003210303400b407014142046081c82022000c1d4444c3c0c000f140c3e2001c03084461400c0c511142c4859206042c03d00102d00540c580c2000340300c40c581c2c13500c0c0100310381d6580100101c40c0301040c00f020f08801c6010400404091541c1d480706281c50044e44c464404c00020f12009505054480d055500036001214a41c0000d00442c01405c441c0d00c00c00890509a0181d01e0001a8500031626100010704490020143d4100310b4404400f041d2400018041d07113003081084c2e0340d11445201d1203406980e840c17080f0020300c2941009502c0c07501c0501c1c44a8000809400d00301c1032504446a20642204038120029900304000341264403141e01c00014030000b07641011040218210303d030802543c94468078085501c1105001030310300100b02000f101812a880300d100000e51210061071001c2c444100f00511055841c00e8041e000c07209002006804210 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 764321133 1250 764319883 764319901
    0x806150d0605070c060f061d091209010203070b041109130507030209101d0708091c0f140706051b09180603190f03021615121d07140405040c0e 63
    0x30240240aa92400b00a407040d61100e400c46030403100c001c1121010800c00641d1081c14a00581e004212750b40b0030001c40340600f48420207480550380500640b42070140c1912030404402c8101d501f203484c9513812200103002d25049044d80c0d0000152141940b1084069585540cae820640c003001c2c0c42118298000383d100e100c0c450b4080c024100101340a803a110320407000030b208801c2500e00001180583d40064425040000d000c40560020110903030703240d6002c102500c0041c1540d00707070b600301f0104092000703501084200038680c041c403078400018103107440300400721038203402d198614600f0070400c03c881031503658406800c80c50345003800804007521104c000034546041580c41546810402d01c41d0400d01440006066415000760280ea05841845514280c181d2041c018044d40700744c2a200303180300c58410f1824030745448040e140003d013000100c2d46126061401143e40540743d0280d03000b884405c42c0d0306c44181300c1c501f080e9028400c40c10300d50344444201825000d41d1003d11a0a400101121 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 764322383 1250 764321133 764321147
    0x6051206040b0d0b0406050c0a0c0b0601090b04120302070b04081e0a1202030a030c210515030316111905120c19170703200406030203160806150d060507 67
    0x3034401007480300c40c00c90b0ba04d8285510802202c05440d05460302c0700007140081c0e030504032035010032240d84d82152122180da815441e0b91020303181504000369170501040d5401c800006002804a00d0f461034039120786407500901e001787c035410074422114180010040c6102c00195040001074030190f1b0341196661400c0f09241009584d0054150009518000c0b07000d0340100051210f440d869400784500c00184e082501c06030210b008914165281509111178030030380b54002e035084444e44400c43c5107200e091000034515040200448082d065042ca505d0402c03070240c1400300e04c15810f55032041c504040c0803208944c140c842c0325042c090750845072821040d42c5c017848010380d200f0008020010354101e084141c14064418012403141284407039003903082880c00212481240c0e41300481905900035008166a03055031186a507405c2500c0b441c001c40181d800703100300c090700002da2000c0f0f12941d140c41c2d0703654034000c4054100340000a59550742441c1d0340303403a42c0c00c0212980103680402d0700e80f42c10f00c00329011 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 764323633 1250 764322383 764322401
    0x402090d050a060b0a080a05060703020a1101112d03040807170301061d04090203300301030614061e0411091804060c0f390b010602060109060605120604 67
    0x1500860b10000c1c10010300f54003907101200c0940d1400c080c00e440b04850755458001d1007024210307030310503070001da41d180c0309800a01e41599070f8a005101c4000245c0003509454019481d01c0b407584020030808200030504900015144c24420340e581c0102c6001c600707010510001c1d00c040c1201800003140014422a480145c0b01e94204040392656903039140c0004203004400c88810350b4118207404501043c1c54140140e01189400038082c0150314413180903480107103038540c0800554010302d25000400d608030400345000390300a08004c24213250395046101c0c001801404d083c426212503420b68964034180c00d203c64009030580d00011103103850b02c00c1138000d0055407441e40d40001440490300d5041e003085811801075200d4030f004d0140100005003510600d08134601740d0700041c51401d0b1040841501040764804400c2411084807803000f4400c0a0000e80440400741c5060390102d0040029643c10000f10b40102456a001c020103414040000c1c490722841e4165201c00d06950085000b5581d654800011 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 764324883 1250 764323633 764323643
    0x100c020906060403050d020708010f02090f0f040b101707031506080c040b0316020c030c0112050402060403050a0b0411011407060519020a0e0301050f0603070e0703020d05011706240402090d 83
    0x81d01c0706d0f07504003d55600641c001c04485509000ca044411103240c001e581101400800c580641d40c0948248100c4261403c91250f00588812245401e915154003603c0c09442a60385d8040c3c5054100303414000b00d4000c0c014004142c43c1c8583c62070248003070f403000d00540d12181750010f21921901c0000b8007038003e0760803014040f01d002060094011003c0c2046e00080b48c5902600d828610f2241010345034031090210703601042c14114030210b1910950b024560003403004003004c0c00c260301c170b482e25850484000c10841e07400780d10340d040c88103010442280800d512000d191292840850b550300b0340c0c5c03034060300c0f50042c07490380c654000c40c3c0c000d5946070036005d810f100d401045454808900c002001d03544004a051b01035440d000100d4010f038250900184201c0b40034009001051500002c0c489040c002018002016030a00200441c0000c900034140280f494041e00307448003042d60076450501101420a10000070103a002001c14000c05600070040c00040305c00603103445001000c1a002c0fa42c002000341 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 764326133 1250 764324883 764324893
    0x7050f040302270708060a1e090c17090c300a08030115030504023304141318031b0204060801050f060109030302330a0504030e100c02090606040305 65
    0x118a12940d003401040301900d8076102d941340c5410b2000d80382c450055981a40180b40c07030005000d000d02d1019400700ca80f40c0c0000c02c5c81090b5603220104104c0e60745001c840c0c0051400c900031f580815101207035035004610b4501402040c00200002005218160344120603040218010300400e464143c44071220300d110019600100f0440c50030020b00d900c06d0242c80c04044541129800f84d41c4244035003032046074082c04101d4200401c0d174000d41c09840b02a44844d9009006c00c103c19a40788000240c0300034038004040542c0702d150740c030803c401c003a507541c00313004858034001030b940e2422943c1100c01da100f501810102c1d48100c400c038007078144030032012002c3d400c03d00f040c100184c5c40a0541c489440b4031011000315103180c035003200441d01341c0c00911001d4016440f00c0e1620003800c00951001030f0107200000d00509401143d004104145411180107010668580811060641109841c00e540c04104c0700010050b0388031340c0c050a032250707203071019004030390320b4000a000b600c4090440e4065604481182c1c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 764327383 1250 764326133 764326159
    0x4180204020d0e0f0c06070b04050f030406020109050601150507060e1014041707080304061a1002010504061d1e01020f030f01060f0f0e06090a0312053007050f040302 73
    0x100580b03405050f0744114800d020189038043c4002c5402030942000500070740c41c21105440700c030714209003d48142d03058020520320400741e150400c02400100080c1d0000301e081181414180c1c18108140d1000c1040d44804920007416a401012a080b413a40440006264113066000a1401c0d0000010f503241c40e240040c0401d0a1425500701c6108a11410381c0400342183c0c00d015108600031424020800b101c28004507000981c1030f088007803009410100c0c110b003a090703580050b824404800005005d03035540c90602040c881c4a000e203008611084620303045007007501b04107940d100704034544001090740e42a1031402201080d01101d0003803d07580d407070f00c0e120b0424085240c0034613400e11603840440e04505690303c019001d140c125600003c0c544034000030f10071540a0240c181d1201c10240c0d4810040000403000071036110840707403115481da0728241c517843c640e41d00744000c03400c1d40d5541c400300c90312213010034402c88080c0c05641c0c4002e5518007070362a214803003991030b202d000e01d030002907104045811344 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 764328633 1250 764327383 764327407
    0x60d0303150b0d09140309010503130512030a020c010c1419090504150510080f070e010e03150613091106090a030b070f0e0603060d021513090509011d0a020418020402 73
    0x1048014000c210785c0403407403010217009560303115400481e40415014400030b400061202905443c1601030f0003a122072070104880030b940c035030007150300d5103403643e010559a540d00000d05c6188000700c0a4149061140c030100c0c210801402813403050f0f034882826981c0c01d0f02c03092242120780010080940f041c0190105a00c0c1150084001d006660203040c50070b02800081c0d128100300350042d2121001e0340342c40e1303ca10a04407202d20315620340c1d50500111580c2c5000d5030708c0402c400d02d203441c5102c020300081d0514000b0418211070035002d41c540d0b0b90500070b00002040d01411314503100c1e5012501c00d50345000d0071000c2150106c1035440500216410000c008851b41c00c00a152240c5220707590344d217520112001000410f000c00d5611f15001110b03130003001c0040c240002c002c0c100e1071141d04120f0400301240c0d006103220307071a9003220031095265406d0041d2480309018030b282030f500075040d85d4191011403410941e0743c00000d1001e44201e80310142d01c400e400846003403218458002e4070a40d640c0c0441c4883d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 764329883 1250 764328633 764328641
    0x30a0209030124120f0206030405160f081c03060321140c061b0c19050706080c0a0f09030c03030c020901080f2a1215070206060d0303150b0d 62
    0x44038041d50030700d410000f50756440c0320303503c02c1044041d018002d000c0c10103032241002c0400040031104008a00030f00f60251341d4101c0518881c078450070081200c03440d2241d2102c0c510205501c105001601e407801403001e11404940c000400e441404401e4420402270b40441c0039048991001d40600070b01904003040e80700c1c041c05600d51003445c2c2c645071002c5032401e40c0c440462003140002c40d4580c10181c0458690003100c00c2d81d0f00440707443c1e0304060070810301028880c1040f10307403a203010300c00c4040d55a800c100101400080e00404160406c8103403850300c2d90f0003001500c00d400c0c03413008000182c010080007a0107081114040c3d0740000351100466100e240107041545607001c26442099607400003e221040003034107100340c04118015190055200c11688440980710462456550102c80401e6031754a441c10181241641a0f0081501064a043c10a03100101800e2002190480340030810307292185c041509690351301d8640060340e0034205680b514016066000302c500d0241c00640407018800c0b80d04 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 764331133 1250 764329883 764329897
    0xc160215030c0307030501140d3f02060c03060603010e070507050a0303020408010e0f0c010c0201051b060105010f0201060e0601080405031c05060f0a030c0303050f1b060411010806130e03040b030a02 87
    0x281004581d813164090340f00e031254080c08e950310811410003000025107043e66074081d8600c5150200e1149080c1042d8025090031011403040d40c4201039000910f5681044000c2c0c0050b2000340091071810180301040b150f1005000d00c0d0307050140c40740443d034420b200d5811105501c2c0c024084d940c0554403450b009000c0d41c45841840829030030000c070154859008509240c00d90103000041c841840b0102c01034034481032485050b81445400d024405080d115a00c0780110f0801c0100035041d50342c103020000d8204660309040204583c0740580502ca030f004110760240c0c01c00802d082440f110b40d12841d1840c5544a44551649625880d2240401e4800e65401250290004440200050040e18140f00741840c6612002c0e0210202010400101e4000d200a00160300c00903429850b000c81ea089030700d06a00b01e0310301080c035680290208010b11072601002983e421013481c1a00640c14480002404a84c5842c0c103012a82d5075040d44070318820b002c00482c0e00804034096110b44a25000d44010002c0d0404c903 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 764332383 1250 764331133 764331137
    0x714030a030b010f020604060b04060803040801051f0819022107030210031401050d03030e0307031d062b0b0a06020c0907020c10030209030102040308121e0c160215030c0307 76
    0xa8040301c00c3d802849000c0d00300903103070300a00c135580d07440d1600300207400c1009600d81c02a580f03d1002c02c40160520040000c0c000070340002c40c2038102281540380d0401c09880441e0521070965084c001c217100428034101d102c500c4030b100b0071621301c503000046c2190807c848902900202c00d448040964011400504407802256450b205070250b80042d4141c4903084044031a0349280801813041d840c1c0681044145400303403600041e990900c03512903103503500010068011a1900004410603100ea0012103070390303482a03c413181000e505410400d847c840c0d040040006a844240101040e6020750241c8084038004181d5148a580c45001a480f0501000014084d1451b41c0c005182c05000003119032000101a0800513000540d0000700c000703400400405505540810002010a1915001c2c00001404190311304060030007803003089140010084190442040d60200401c001540302030700d0381407048642c2e40d413a03d041c0d40700051104251800c01038a408001c0140040c1c00c100101440c8590065 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 764333633 1250 764332383 764332391
    0x3011e06030e030d110912030c060c180607060e0706050a080a05010305250f0b1818011e0302030109080304020a270e010f05070f14070f080c030714030a03 68
    0x1400d821002e403800c255890401ea0700411804464900c1540291421104100c005080c0103900c00014010800d030222030f500b540c8013182c0f24016006c01d000e12138000015440051509184504000040390a5141d0030b2165801240c1241485030076001110490482400e8458868554002500503046911120005540d180004010400c10310900741601d40080051550a03d98200710300300c00680c0090300081905600300003200265a94001c02401400d124603484030a0b040401840210304c0302040c0c4200307a003600009844c000c0814840c1520341c0d10201c9108030404141e05011080603500083d0190310708542441400102d10255006038400c85941d41c071195a4200307040442c02204a503980034000382d240400c459042c0d0711404820200d00c0c00854254a0008402c0448204484c0e02010900f0741290f04481c55008607551080440c414290b030508a403615a68480140810020035100c1c0c001032280042d40204150b0350302d0760344802201c9417403040c07500d40c640340d40010074040003007030070 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 764334883 1250 764333633 764333639
    0xc0c0a060801530d020105010e091f1d100204050a0b04031106180d030e0118141c020d0c1d010b0306040f061703180f060d0b01031103011e 61
    0xc080998500320001c20100300d07142c4220300031543c0d48480c0c8045191803146038440d40441500910078043d00e460390340c000044645c90141007008443c002030802000707400c1403017205032030708440c00074003144000c040d40007501c142110850301c910110640c924969100d0103003000b2140000e9001401030351415102c911045948090b03881440c092400300808255541c001c0c00320b03500340b880c09003c4949443e0031008034900c182d40801e484080708041038000540b9800d4003200b550300306c542c48000f100d80000f9a444640791083c652003e060f4500381c40c0c81b400304445041074a1035100d01280d4141d0300144040e040710940c0c60503240147c0144502980450002120410400b800c040340381243c601c0100c0c030b860b6a40c0d880030880180b001e0b1071104030803070b0354070300104001c0c6a800003014a101d00700001c550702c0b601d1482c20b50000f000c441040d4492a00e03001c000c0364039103440046e185980702090000c62039101000060b40036180b121015803c540c1e0200000420328030a18545100e8660845e2034811152 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 764336133 1250 764334883 764334929
    0x301080106050103111206010c150c0806010e030714060c010203160f09061b0240150605030a06082a04060b031602150915010e0402010f050c0c0a060801 67
    0x2402d804040741e810350910128241c405a850507c0d8000e10500d44160300c100c90765a40d0342c04480601c0c0000007103980d924042d0700d154020303441c9034010000342050107440b401d00f00003aa49500342e000d45022500c0d41c8200c4074180e22001d05590410070780307000a64592410501031044003030b441c4402400214086c500298103030149101d401501d001e0707031f1504000300542920a8405031001030490f0460f03420030700410050320422140c4104c1412000d0b29a4440d185481c03080d03800c3c01c4002c444890f9180c01403a00314020b203103009904590380e07030425544030755580304180c008008991245c0080c1c0030303c4010b841500c0c45c50b00050315440400b98145a898814810b0000312501409000c00c140000c02c08140010400c034040080c0440714412a041c41e6071003040661074501c15201c0c000181e1102221441c0816100728850160644110049841c6040c4c1c0000b04036282001d100014400d00060403180800e007401100003052001d0301c17a00c002540c1d6140100411403d100e081b1120300000460790f4540 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 764337383 1250 764336133 764336141
    0x3160f0b0a110307050901020f2e0e06040b0402061e03010e07051615060807030b01080d05070f08090a05090f09010b1905060d090f051006060c0b0f18070b0301080106050103 76
    0x141080b01c0e441c103503500c18105a071a503101500140c19803050304240381201800300002040c00605540243d807030748000040c0314501506001c0c00c603020341011824494864006841c1d6441600064002103980b9603002003031161142d41001003c64000c40c6103013503480c0d50b0a00660407941141e9007248259152041201c1c24001c4112042d550054a02504046080b001009485140c07a4400295555031030180c145003100300c2d4002c0f40c2c803251400c01000b02801c1804280c1007804142001454071203641d45a95136540c0901c0700400d0810f02150703244107626940080c00c050b001c0a07000303080c07d042c003003206c401d030440c2103036072403265800d000c1441441d0500038862054038020f00c98034074055040c00100a07841d0400302c0f01400d055564000e640100b8128050101d126005802425094a5001c1d00e00140c0c1e40d540c00c040d0a0101c80d4420b078000800c071140081d4801d2551412030f00b1a2960203120074400000d00940b0341e1485504000b00d82105003400030360490707600d00000c2101d65500c800650030f03030f = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 764338633 1250 764337383 764337401
    0xa0519210203061c060f151a04050a17010b04050a0506040c180612020f0f04080f070b0f031005030d030b030124170a0f06050411010311040603090503160f0b0a 70
    0x80b5a22400000307020b509814180368003880313040c5c007081c24001240e00d141258100303180c42414246d0f40204200060800010b05007400100c0070291910782840081103111807240708091080c22441100b861602080d4488080c1d100c0c000e00c280680e05203818120302804065900354405c51403c1003542d2800c2c015400f4000c4086001c456a00052801100b0b4a071503508400e0400640d03001c0014820b4810504000d0070411804c2e50042d494a00b0001503a19001c40d144546400f940020f90500808440e00d0070f491f03140c481c084142d0b60726591102114525825940619050311880e000102d411303405406c6841602c1c0140d0003000b0301c0303038040410300581c07650600190440018100500805403031442c48070a41c45031400710b0308628010355400b105060a00c0c02621029039910520040101c00380a0900c103190902e0f0034480100724248103c02071140303110700424103944c0c8007000c041101c11300c281c980012065001041070011810090900b0115000480301c1405500000340c00a259228811075 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 764339883 1250 764338633 764338639
    0x30b21060109090323030f09030a050f0c0109150605040b0f0f0d1b06050a0306080319030e070905090a03021905030406300b01020c060c0307080a051921020306 70
    0x25a4645030340a0010883c1032401d6040150300c021108403850404c1a103180351039155096992450a11111054030340d0203001031144e41c10070010300f09015070146c123032484040441704cc1695403a000840304d00501c1d43c030000520051403e800c1f2149055554811412034a064500340b10810120f020000c5008040000035800702c40b8100ba0300039800e203403881000301d13489180c48481042d500c03280c9941d0340030b05602200000c1c00000701214001d503d0b00459004240d0f0700300544c144002410100b065180c4151010700301551415900d140c54402c2117800010401c491042041d07040012089442d40c00020b829005403040c401c3e000221103000941000080c3c100d00034604007810300104a90148041c404814018015020401c0091115904512400d400710001810100ea880064101030710111854400c0105009240c0d100101004440013190311003122640c1d0501040d0a0310765004a06800509202d00c0c000f5170b1501303400c544220820f07940c00c024070855540901402d0140e110807150190 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 764341133 1250 764339883 764339893
    0x73528030902190e0a050901020702090a0504150e0d1404090204090207020f0307050d12030609020d20040506042d0f06080c070206040303080405011d1f0501061e031407030b21 77
    0x320a9401c0c2e0000da00204041f001524042c00781e00056000351085d10400000b5544d2400d210400c000b94400100c081a207090030301480c2c9031141c009451303240709080c003424007641180f180141441d94044030083d149000c0c04644a68943c0306841c029003054a00705d02441502d01c1407046842c000614000319000203049464003021030361058814044240d01c0ea041c0342d1111008a800da02c5070016021400c0d08010000d00e1ba00c241800c0c44405c01110070b440c03a106d808000c01e00c002e80740c1c401100c084c0c40c101c0528410fa24016000c440240c104400500c0500800c0700c0041107006808404100b190300c03a40e5100215200d20003c82c280d8458858002e6102904210400c00a0301591150307900c0350007140002104c00d1024160407112851400d040b00c203402c61846510b416079284c141d00704002c482c910401c501c5d0f0601c040075000d40c1503140d0180510301c00b6202403840520a41002c15070241941c4059540c3c1890823026002c1d00000319141d11a07861106284c0982c0040d07080f600c485112280200 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 764342383 1250 764341133 764341141
    0xd110f0a110a0f0b0411011d010318020a03030504150e0607060b03031e092b0609051e03040f091b05031317073528030902190e 56
    0x140e010050341d003620440e801401d180c01d020484541900c00e295001d0a1200a149028a4502041196294100c0c1803120003200c000441c0706081e80c0d0002c4020a0034005080080364280030035041038040300940c00141c000e8040201a03000300a0000c588015030f5040d00c03004040020744041c10b41d2003005410030030a000980200d941600000c80100010f0143e03480c1080389001c0d03c11241e4134514100350200c001592524504040d0795030405020303000001e007942030081d0030302c011041800030090f003c40e459480c1c01c03041c04000d100389101403820040031421941803412842c3c0700d400c1441140c6802120200001d0782d841c4c50b0007a140b0b0400c041c1104400e000c2c140340c00392050380001d0002c01185002e0b07512603000880d441440c005c40b0500d221081d890340f0080c9802e8040d84220040000200b281d515102d021781203c05c100b0340e07100c41d8412101d86442803c889403422181174050000c0d41c00c500c849a070815174055100c1054240203072150640000b0030441004540210706c0741c09803d442c070070001 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 764343633 1250 764342383 764342387
    0xf111005040309170d09051e192303010c09050127080f0109060b0a080715020c0a090e1e07050f12010203091005010e01150c05070503070b0d110f0a 65
    0x29520078401e060030f40660380c445006060030f0004e40e100b602c182e803040306141900790700850705000416045070304520313402e06548504e0400c005d007205a405220240d2115003001008810f02d0b015006040d10400c00204d600240e40c0d011203600c4040e0701a502e090420200240300724102d500b9a041a1202c02c1c03400c42c1481041c0c643e180c0303910305041c01c1ca0b1038280070030507620606c889503d80c89032400101d0381a00c00e00b428000c0f1600711807105d108070040740041144400111700e04d001c64083d40c0b105115148a810280d0520894100c140d5011480341001b0580300f1103688014170803080101111b120fa00582900c1194548820f00d40c40181c5c8032002c20011071501c0c10320a141a231024000e4458010580076681c03d80e003082c0c5000d80c4030740005200c481c8001c140d00c41e042c0144400412010320b545451020941080e000c040e01080026110910303041c03103400c0108034024071000e02101c0c13805a07103803103018594000c41d01c104002030030001a46840740e0107800381c0351644040d0300542d02e00704040f401 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 764344883 1250 764343633 764343641
    0x1403070f1202071e18050907050105030c0f070f0618080912120304030327020a1211090f01051914010513081f0c0f090e0901110403080a0f1110 63
    0x35500840c4501d00340800c10404014a4034008800c513000c1c07010300341c1030003110105520041010426946880c0c02c0140c82d01d000200c00d030272108203003029079807a25022001160340c4100071503d840d0980c001000000c108418030000d45160081504014450f07514441910a40ba0030030007415185040c05040441d290411000359040d0050085500040f000621507425410484055020a43e03078103910f40a0014108a5500c202c0302001090038500203500091460300c460244036085807a0303c82c42010000d100c0d200b500d00003002005520f1030f02c0c000100c0b218801d024003600740554200710b08808010100c1401c503090762085544070341c40b200d4042c011034260304100d00080301140c5000002900c0e03041400000c4554034006158030168403802911002c1e0740b40080710008001d4212060042154000b11070410346a64203c0083d0544425403210b014000070300780c10b07203c1070380083c1c00803c200300ca80c02492050300a4440f5411103507036030b00070b440d49900722074610701c56040a030000304103c80d2988 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 764346133 1250 764344883 764344913
    0xe0418150b09090c0907090b031b0c0307110f04020705150403170a140105101704030201020906130f0506090d030338041b0e0402090a0306020f071403070f 68
    0x1540524100020302074110039900100e0f940c0106800041d10700f00b21892a9201116040038000341d850a065400144030040c2203a41c0c6154a9841c0b80d02c41c0342030307402c440d80241004200c80e01c525890400c00401c040b05608a80300314500c402d030f0701260801c2d000341c680c1c141d0460090442e981d00e0050b1100c152400400031001c00c038280704a48100024510315030300070841c081001a614804441c004c42c8104c0c180c0046c0d1150012104192045078080c00d40c0550205003d0701a0150b1582c2c54141c1c064011000501e80c80040882c20018020000c061381e01140c5440690311030309039031041031081038455144882c0c1c00000c42010800400d000b50403002150304c07414001c1000c14031001e1a00c61a4803261400180c10801d007880b210071386824084c164181071110200f113042c0485510142045840741d054501594012495620548c0c0b050388010085420203002d40d0345002034210858a80d1010390704560346010a0786030742200c140001580d03000d6900c01c038206080200d03030310f5258004140d0b030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 764347383 1250 764346133 764346173
    0x30e0a090509163b1311011b060c1107080d0e0618010c030905040203010b0301050f09150d031115060a17060112062d0605031c08070228030e0418 64
    0x42284c0200710403030200c50320482c59907020200302c0c495031401c1c20070700c032410ba2802c1c10045405000f0b06112003001601e0300442d4000d80004106504c540250b0b010109200340d00160b024070070001490030404500c1d01c1ca4401981e0325841c40300c400008002da64041c0b5404000044e8a807804040eaa50086601c140824084e0030180c0200d5501c00000d8141d0b13000360005069000302200400650814018500d8101c00444440d141c0c2d14090091108807096140e0462251080040500074140941c0800d1065400310054812040100b918089080c0e4142c50481c00f400e03103002c00003403121590200403240d50035400a02400d03440d085550411a00110b020f480c9103a0f50044090242040145440400914000040215140c0c5e0041303048507410b6001034004d0b0000399201c0d8010b900c18440c07c0d02c50782541803000454031800001ca16081002107128640004040032101108100e01811a5036100303907a25050318016405010584100101288500c601102850001014222489821081c030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 764348633 1250 764347383 764347469
    0x302030c07050d020a02090a090b150d02030a050609060601020303090705090a0209060c0604060e01020901020319031b0215220609170403030c12030b01020a0609030e0a09050916 78
    0x6440d200c3c1001c0030000c0000150384201040021030070f0000282c0d83c4403c8404040104c007034261100c4000d1400288115801201010720b10556660708215201c1a40c0180031201401410f140c0140e039082b05550740401d521950000404641c07001046912031491000030b065050700d4030f400c0c02030781000a444104419024001c00086031642000340944003619001040e2030b080c1801c00604448a1804d20301843c0d00403c000e58840c1d0b0000202c4500a1110220b00d560b0b00761018100d0003004080008000203401406400d1402e5002495910210910001114a48070400301c8040f103850390000091806900e2100e10201e6101c0d4085500c0368002d0000031062200500542c041d0b60181e00128041815018000c060000c40b803800c490f20358650070100010040180080d40d5210041c40c01092191503240d03080070103200c1c4401840c0c0d60005003045805c16103504c0c1520240c04202d0f201300c0e0910640f10001c11079a002c0da01003048a800c584405d0903a41c1c40c034a0ba920960402c550030781c800c040d0f = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 764349883 1250 764348633 764348647
    0x9050f0a0c021e0a08070809282102061911060f01061b0822090b030601171f0e01051006050a0f020705090403020a05120403110f040b031006140910060302030c 70
    0x550001c00d403162059011503941caa814040151490301e012540040950300001127481548000205007a205498102c1100e0180184200d5515100c050029004200865802c0078101130f0241500107524507200c4490003a00700e00c186030742d81c008803240710030802c04800400025002c0d80e5544044640394448000501c00703900e039503091368844a00042c4a4000301000a80400624440c0b005000900300074807030b600001001a948040601070101c01e40444c403c10f401c021010885045551480010b140c290f49401442c1e100900710b0000c042055420302c0e0020700b0743d4030010702090a40b407554540704e0800303244120407036200740c40078031110035441100e0b001f140e00c0d681c2400c518425882179004003080e003600e10b00503080060305440300260b10400d000034400910f800085820292040d941200c032079401c000001c0190021115180e05401114202031040026401006c250783c4c00c9039030440720070a4081880150242180d45401d00c4030426003e010390303031090b0005d640008107001307902d0404039 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 764351133 1250 764349883 764349893
    0x1502031006270621050103050303161e0e01270902030c04030611030711030c03040b07170304110301060b0405060f0c16080a0314090607060c0306090609050f0a0c021e0a 74
    0x12140c0090000c240c0c40e00c0c860044042c4c0e40500c001610060f042405a03500d9a51002c0da0390101a0205640850111120200b14452240003174512618070980c115181c030301c480a00465540f29030103001030400304015038038004007485100c8582d0280711601d00302d49030850070002508007404a0b00b01090420002011410a003e2940e1051104021035540c0c10100000707411000d01450381d4400360010301598041c00b03c00b1041d1012280724080b4207a6610701464482c4994060040744d00d1162008001d120510004468070b440303096094000b0000940c0741e4040720b18600491140d10b40c45101041640c2d04298400c0c090900c907000728040b914910700790390309100d07480b8807138201030b15981c072002d640000d2540c04050002542283d0107424580810103021401c00c1c440c0c8400039045540720311001c882075219030b214000521881c4801c0140c3c0c4d84079884440500b9059520b0703014060100d020540c40c01c1c2612827903200d034800740c004110f0000401000c034101018403011803003a028103010b541c0420 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 764352383 1250 764351133 764351207
    0x303040602010501090506030d080c030901110d0c0e0114090402090a120510050f13030c1703010f050301050c0a0801260a2d050d120e07121502031006 66
    0x3154980010581d03606081c0031100300d4200a14451080c0d1004e0802c0f000183c1001c0c0403074002c42c00100d180d5407582c801d64140e0141c9801d0701ca1f1440000e0010320b20b5032150301a44081003011941c0e0303a48000b001080011110700041c0428900c04500030005d000c00d0b0300d4a071380140f0380b440d0090000c40080381c3d580c4903012a05035888098441e0780208051050349003541c86019881810614030080c5810061640c05047d01601401001e00c07103801c582800f80504000d42403018070100a4003552581c5421404030346403058803c241c000e6003403402040300c41601d0025500b0010352580c54108582c6455003c0c0c1902200c004d60480348002c00302c2c1c0c2e42410509000424410703020702d01341104c5030001d20540d403200750340304400d030b0300c240c82d460140002410101d00d00707210310035030300d07145401c12451440200209180d0807a45241e1081a20020f00980400a651006805200c0060502c01e421082c14203a1008403202551041155001c2c00500d00400307038129a001c90360040e503042d03407201500f00120 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 764353633 1250 764352383 764352389
    0x151101020406180801022d12100f0f180b0a08030f0712111b0f0603040c0f1211090403090519081c02070e0c0f0301030c090b010f0c020906040209030304 67
    0x8843c50515601c0c05803444a0100501414008518102c00d540c00c520061080240300b0100603451701500a610000c030042e6030380132a4000c0e1f010894105207a0701503028099104a41e04035100c100d00107003107071301800e160044808683d050700c3d90411203000c5800030002ca03407060764413170380000d004107000e40200082c1071040c20002e074859664401c0e04045003101041c0c0b04100130003024284062010102058402440d5144445115000240000280720100d07010200350009400310801081c042d580803c5411203d00e54240b800c0251280c00c11940000b00c4c075030190100719840304014460138050401540309000e440d001810507140c50009090b010903c0c9190750b080c2e40f2820900200d40e05126440c0d040c03030031a50011407942c0b200030294407455148a0902d5507141100080c0104004208850000c03e50b40c10302c955079a12841d10803820f81c1940605030819160080101c500e50080c43c4910b24001151038030f00300802d0560030043c00701c2c0300034440d58201e40c09200c0328402e0b0710204040d2000e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 764354883 1250 764353633 764353637
    0x903150703020d06120203030a120204170606091008070b13051e01031a2412180106060c08190c0c08033408030c0906030123120601151101020406 64
    0x41c0e070003c041044180c94080c0c01000207400c1d43c1d0b00000050f9400805c49070964218100103049100c1102024000d004a900c6281e8114542c08241c142000100d0854800d0303404036180350407500c0d044207105812543d030085d424250701c001c6c400d0050130550301c041c25403180229000c8107240d8030351000c40e40451a6080c0f80c02e00c1060001c1c00c3c0c3d01581c150151590311501c60380903420114003c00003034920383e888034400d410b954a12450101400d87c0000701d42208010b404d502c221402d041c45540b20450106114402d15440d000010821900c40c6400d0210710380c100300036a003403407208003841a06e402d11035034071005e11415406041c00600690b0504004004480c003450312486a1045100c0284014091000c00c8080c40a0b8800071042d040d400c2c100c541e0022265603d07540c0d1051100b40034401d40d000e00c0d0740070b500400002511002c1e040c0ba0110608180c10b05c4210f46015401d000042950a510208030f0300f003900148003948500010980c2034501741341c24440f2045104209003240c2c495080680 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 764356133 1250 764354883 764354887
    0x6050d080403031707120f0e0d0503040b15060d020306030109140607030e0f1005060a09090803160509090411060f040f0509011508010905071205090615030c0312090315070302 77
    0x1810707003140e0707621511010b62a84c54000d2401c424001c000f14441c1c007006450710b0f56204035012082c01a1f001c00100b0030224101c4640c140f031000082c1c8540c10440c0d04407540c0e0780700d0300040c3d90103800c0c481200282101820131820408040c803000080d4000900c002d0b0199641d2100c400032584100e040c0c0c020329924001f03071002d030902da1002800e4411014004c8003aa00443e011f105003440001c43c070501c0515103e000441b42c655800240c003070301381d950004031980d0400f422201400701800007075000d00c51901c0c55a14404018005403410302a2400a66000d90703164005030208010310940148031200400013442c4c4108500d60f03001e1030700581c00c1103e801040c000140014180002100d01604072408000f080c040c1c1401c0c002c0200303205000f40041c0c50b4070346010581c00360003040c0c1c0318000c0c00c62510510003850154000d55039284200d4a6440300c511000c0340c11070070300740802c2040d51000080c0183c02c205012a010b21281e602032040c15070584200074403c009201c1000b0f20070300500071359402603 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 764357383 1250 764356133 764356139
    0x303064507090506090d080408060903040612050c1e042606090a05070b0921010905011a0d110d0b07081b130618030611040e15031f06050d0804 63
    0x203400a80000e21881c180301c010507080c0425561a01602c165100485420f183d02d0f0307162030101c20a00032503001800a100d40340c2401685880403002e0800d98245546018140114003440d00541e00191004000340354100513508a80c22298040d1482c05154424186400d548040865030310a0b90310400040210507000b001b218007003805125005088040100034016180d22407580750413a0307104140c8200c1c000262404d0326101d10303c20f41405c00d41030002c40d41d8070305104a40ca01030303c51041c0440310340d4030b046ea00c5c104180f00200d000e96000e030007510100041443d07a81c0c5644508108000b01d502082d01c0c102400042c80403002e403031044080d9036400c2280d040140076500541403055090884420500c40c0203040070048070f148044400c0c500e080b800d0790610f0001c2c0b2500300c05e00d41028241c40c0c100001d00304990342d010024400c5410420810055594110302407044510035129031364150004803802040280b042540b84a521881400045c802e03074510005102d2018510103c9140380040703010 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 764358633 1250 764357383 764357509
    0x1806050403020319120c14150a0f09120507020a09051e0705030f062701032303160209100801020406091503020304020f010f02120408070512030c030306 67
    0x213203103440810324148602d101156614402c40039040740d0241003000070249142405412079001d8107404507201610a00b0b070940818801e03000341228081801c40c00d0042450603508907104032082c0540003c20031840d668804411136003a80600300503a84401e0b074800c04605011148135480c01061000c0d804181100382e10403100c1a1140106080c0034810240700700980391443c06401540218206c8407640340004592410f00b200200c24183e00400003a90004410802c600b40c004010801c0042451038080107a1180e559170302c203141c454403042441e00504c07801800c0500200760000405410150803585a4540d94220b030026882680010014a800c2000e402c070840708901c40c01c5185070075480c514107500400d03c15028001c0090400003140f5090201e94030074051211401c010303a1055980315602d03001142d0703401e500c5c0105881034030ba00c060565071100000c00c031340c100041080034604540c1e40204210070b4080c1101140354100c0c28035840240c040c800d490001a8041e00520549110402c1d010 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 764359883 1250 764358633 764358643
    0x1c0c06050f07060b0406080a050a140309031c140c0d17011d0a110406030617070303170606070b010803030714090a1211040504080a030c021204031218060504030203 72
    0x80001809020003540314616007074000c82d5070443d0441d0011a0050448000c50010601030348110824001e00d194401008404211811000c0c00795441000103940e04045075128400c1100d019490390050300a030001107085018011200c4039402c0050a44041507004d00c0d5551180d80b41c500306411040c290002d498104000301c038031842c09d0025906540c104421215040128101d10104030860000510441c48a4025042c0d41c00c542c108035448607075401000d80904840d0142000944c1c43c440060340341c1c1c800080a0701100c0c0c247c8c0d40e00308407a4901808100700403026045a4000904000301008941200841030007001440000c40d580e1400b5680105030a01c00b00e596032030018100480c1c0b180e665114a40e005541101d07a0100581c1c15520b480e43c05803183c2c0e0b01c01078100313007170508003c140000c41d000361608441c503450521403001d0392281262030310361611004201d0781d414481400440c0348116406101c080c14200404903d0030310000a100e12240c3d130001c00000c4000805100318202400 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 764361133 1250 764359883 764359889
    0x192604090f05060616150204090204090b03011517120a080f090703080406030f09050d1112030115120f0f0c020f0309060a030e19060b04060806070c150b1c0c 69
    0x1c2008a410b098001401622035611298641c3e00c5100d20042400317546900303102c1841c0001c40455540d0b988040c040081d41043c031540b18468030303003036801d0501e003018000c2200c0080740c1c103401d4002c035051480a1032149025050041c25205004446645181d1403004010680c040d807a03500c0035260414205640303240041c00d649050300030110400010341c2c140f090301d0665516041c00b0070b588008041210041240300c0d0003070724520a00c03a4602d40c41d90410401404107090a05460ba0036840019a010a1000780b18001909104080e03550074144501d95138584042c1c0c1c2caa0216000b6420001c070010744004090280751035075a90660b10302c240e0100883c122108c54103010f1424051f200e80000c2041c042e00c1c030980e0601d601c4880314941804140308600c10095030f1a035142c00280c01d0f0070410300616080c005540210714181001c15103400c0029801d01c21601a03032410103092055407025910000441541c50316034a8115070552960b81040600c4c00c6881d4850b41166a14541050401d51034154 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 764362383 1250 764361133 764361161
    0x25060501091a22090f0614070c15020d020d090501140109060305100209040905060c0409060e04211101060311090f0603070902070c03080a0804050c040e19260409 71
    0xd10075600342e0302c0391401078111408151034030040d620f02190749009000c54200060410001342c81c40780c1000301513480703040982c21607200028150365480013034030000d4000380040d2070b0b92480f03c44d010440792a6001403c40b200c94610144c2410b00c20481c1105645021804907040e0f5100d12501903041c81a118a0b8010300d01c00f9400e010f400e20b15200e140d1141071101041300c0c2c650700000c0c3c0046c03e0302ca81e00400422940601280e07100c0c60961400690b0390010f0080088450070048000742400b41c002116010304d80280034403005000340c80e0000205a50310398400c080c0100358115168500080c031501c801107005440d1000d041501d613003002541240101a030070310002e483c042c010b031034030002145000d50f40b44d0400146d03074108a0802d005240d1580c0d00052600500040301d401035a84a42e5050086210b0000c4440c6c010985040000782ea80320f0005000301da02c40d40300014000440c203002c0c07051500902071400c610500c5141e104a41201070601c80144800150410150f104c0303109110500c0f6480e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 764363633 1250 764362383 764362421
    0x1b0c0a030e030c0a0905040503090d0312050907030215030711011b03180507060c03140307030204050f0d08030a090c3b0403080a0c1b0524100b2506050109 68
    0xf40e00042c41008050107910840c507a1140058100301c0104200d40005500070040101c40c0c105160003000c01800e880b01140c91030030907003c10300101002552009a80c1c2c001d1030540c0040b06644203e0040c0c00c018115020000c1da0856100760f19020702c242c5000605c80f60b8501d80a4103031010180580e1603500403100c074000440100c8020a00200300340d4151181c914048d0391f011040d080840703044a0742140070603503aa001003440350094050f8002c000316501920508441c1001e0070030419402d00591014191080801c0020070b81480d990140041e0340c4903003c101d48031901c4040443e80c5030704030681c0c0f02c01a035202000011100084d80c039031418403540401e10034985850340d0000c0100e4005840e0302102a150040c55103a05c3c0521280f200d0020b078a1050055602c40381007288d07035401c0400c0c140b075103903010b16074403403c40001300c031000c1c402e60b160f08012500900d0181f001070b1a901540201d64078902e1510b520301c14500b814001a0010b00a58002c075883d4104040c14044402480b005040d407446 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 764364883 1250 764363633 764363653
    0x60f06091401052206170a0504150513050102070506041416050f01030b0910090c020f0a020f060c03030a05010302040b04290102010b27011e0e1b0c0a030e03 69
    0x24414641c07040a400303180c155180c0b1a0f014060700030b5003034440d140c94948881c00000c80c2041e0b1081031190800400c55503c106074940100d580101c03103094401804540038140c000442d181350350051038025000108000440301d050322000d08907003101d42c0490f000d401804c20300040c0051508400340e0b21000101030b107000c0381c501c603d40c14025120302c10310b400344001c0045092568040e9000080d50bc0707000d00002041d103007200891410150b40d004200301c240c5000311007000b0303610010b41c0030103030303203000000f0f002e2840f1b16000c1012425000800c81c0d03018900b00b010201c000d5040c4041c5020300c40c56280807904d0f504520420060385e10311040e150113079142c08020f030f10f08a040b801001026010030f4461024106c4000102c2c0900300c03591007160400740c0152890a80c0002c0e610003148040d03810201e540590700c452500e1005245041354170221640900184004013440c40e24039004800d462141a182135110030b8043c2a800c0311104800a80000d220383c400c0c0f40d001105240c0d4410128080e040000e0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 764366133 1250 764364883 764364899
    0x40f0506030c0f0a141f08040308070516150615020a050706031107030318080c1f1b080703060e01030305042108160201090b030a0b120607080a0203061c06060f0609 72
    0x600b840b032094800b505c0220401143c41da4540b5001c8180019200f59103030361440340c06440480d081e1380440020b20484000386046200d101510701064600c0c403031052442040e03d40c26121801442041240340d6141400251028091041011401d61390080c0c108806281041800c024840d44080c3c141410300c0301401c6040c200300f04440b459903050030009443c19020f04010f0007400d040310000d10109000401c3d000394900041e41d50307e074503000b84500c1c01d440c02080c40b05042c0d2b518519851a1512881141d50f045400750414550003400ea02e4000b0709603030382d0904040340c04000e138416408550001020b01048404400d54101d140f0101010b03900350b84180d441d0941d51140255a010701481403128600710ba10550070702006094550255440f030410301c0c0c01d48020842403441600c100800f0b005030b038034800301084540c42008941c5038241c0c9a904d00403a9006544000c00c40da42c00598030003a440c26051040403189598041c0d60000742150400d0b450108801030741d007090043c002400740401c4022 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 764367383 1250 764366133 764366149
    0x30d240b040e0109020c03070b01091a0409120305220305030a0615142101091a01020f0c0409240507142505030913020705060a11030610020c040f0506030c0f 69
    0x40d01c008401a0340d0f80c02c8920203410350250800003410041827600010b10030041d03800901e03100c60411a000c0f8000d5840c0104070803107d040c40e0040400320300d0081482c1090080d84078a52210648240d41401040302d1104400301101d078401f200428400310900860008a02c80c000182600c41d0003a81054808440580780a08041c0419840390000a0080496031042c0b421403203a80d8411800340a0f585515110015003042d0240100c02c9500304900091703903100199045003200700401401d4203111032410b2001401851200b520205108072500e00032003070180c880407079103c4802000807141407014000300503002182c8800c20800d003d01507061042c0c0c00b44803042884e4864614a901d082e4145041402c5000700d00c2d9040d4054610303000f650540e000c03a00100381580c401c0080d2541070340d800101e24200c031a25913406080030340038030002e102401d05062003144860a03004960700310b070511300087c040d10a4071400c40011a241c000780501c6050801040c0c40040f022120404c400825401182c102 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 764368633 1250 764367383 764367389
    0xb090a050129131b08090d140307034110080c010309150908070c09180f0203010b15130b0901021518011b1205101205030d240b040e01 59
    0x244101c140702c0360885039164808554640c1c000840c6610068525020b03050805c01c480c11680e500035214900607143c400c1c13a00b2034002d11364401c0c880c11070f2a00601100281220700701d0313090301104230080e0351500440c01d52074100c8030014150307822000050f4126240c0d04001502050f061200c001d030900100e0804507030410844030078a0001442181b600b055803810b944258040815841c0c28140401c2c42814001807c2c42c5009502c1d40e00401e40d00c2c00400111030540070317003510078040b044010001651f1401e100040c1f900080000c130f503030300c50300c0d00042c0c2c00300645805da0907840e0001040c1841d95040960040106010345c281030030030a030780c0000303515001c022403450280c200a20004400781075010b110048040c00300000c01c2502d11001c4040004460078560303902241500c5071900321420b01d8010944100c480f03502202c0311914016840042d94080c0c00c0423140ca00090003100504103c40c4520300a50032003120803174010034403035610114000d5680003080d01500801050001c0415208800c2c11 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 764369883 1250 764368633 764368639
    0xd02070b070f1e0201170603032506050f240303031614030f070806030a0c140105040b0f0d27020906060d02190207090e060c03060d0b090a050129 64
    0x1841c80c141c035102c0403000001200620242d00340c2e110001c0303503641102c8546018403c3e05d601c03400c80c0002183c01c91a5000f110f541d5810b0b4800c006401d03110b0550002c640000804815100035520709a464100740e9604950514405070128104041130241001c44001c040d051400300c82d10074404000320761248801070001400204c0c280c0080c1d100c92185071000721002840b2001c40d00d9050814030f45500c01800d80c2c42d5070005103060085001840c020072500307046644580c903104011318001c003220070708072220001414804180800030702c0080e14801424003c44211003503948103140603103102281d402400240e0030304040c0d000a4480c61803d4040303011b483d011034200b0060f6403280c00040c1c4500c14009000441c50002c83e0aa00b4144e000e0b400311090203264007a0381d45203440d101c00604584148004007101c0c3c1c49000402c0345640c90f00300640d00900080d040141046042e190048010030584441030580d100403802000d00c0820311455148409488c80a11402c10024401032185810550144 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 764371133 1250 764369883 764369887
    0x70b04110607050f0c03011505220b1201090b07020309061c1803030203060306071e0809010609060b04030501112802010f0507181a0f030c210411030d02070b 69
    0x100c541d50311400d0700d0106034040100c5a8002c60034200c0e5032074000034a1080c0c0a5828020b0020941135070000c400142d0303801a0554100079600c8443d900c96203084907225120940d12401400310341c4400245110744d045d41d400110741004940b40c4000c441f81c00400700c40442d002400b5911143c0c1d2080c0441d600026a442215000107603640303042e00915418000c62000b1512110080c00c064143e0050742c4104011000c0c0d030280c2d642e692042d0385a0303440a845220310340b401c00411000c64040c1e99141c1d0424000d6000240303003525a01c101c01119a181c210410403e0081070400030014240070307e4140328030189000c4c0c14404c090b60124010010210300c0009040d59491440c20f180c401d611900c07070300b05030030300c240703e1418600009000c181c10040c048408a07844c540100707100750700c001c102ca1540110391400e4500385072140c45c2921504050000c4002080411200fa00da00711a800c0c1d4040c044105503501841c00d191821911150340c2d158080c2c065005a4100d6602c103030041040c0e02155401d0407065 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 764372383 1250 764371133 764371163
    0x6060f0a020f1f05090601030b060630010315060812160b180c120607030506030708030f130611060406240f060201050606040e011406122a070b04 64
    0x41d0400b070080b41d45081501c01c02c03511025071240318003030744064660814100256220b040e6201d803142c400740400380038405c0041c08100380e0706080300240703915080907503101d2156500080e5501064011615a81d0008480d0010700074043c51041240340382003030310720410203189002150741c1c031040c0c0c1d440308858281001c9401d590848826009850300c0782d104001780c00fa494812a4540800d400328070308212803103201c41c400c5880c10100b460410894118008005136a9080c0c4120058240145500d405004110002803940c10400c094a000c01900b10840e85920502d0501811906540d00c4401000040d2012089909011541d07581003608034001040c640450081000310f9180d541c0d260004219a10002a4420f50b4411030030690300c40398002c0c8a15180c3d8020842c040c011401802c00300703202c5500401c10007040010041d80840094101402e00300e2010580c04101411181d020003c1c802e0141c0320a16207035022090361058071000d8541c02e042c855141c42000b80001440201032032102c02c111 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 764373633 1250 764372383 764372387
    0x32319020d0f060f0801140c03040f0f12171303030b060f0409021c092102150109091b1a030603010b0a0b250201120218031b090f06060f0a 61
    0x60354a4000d103501400b145074581c039014020700c000d1094080120f41d440000c20111410700072010241528003a0400302d0305c4110765142d03103500246c0b0446942c1d00300ba90810028038441e45201a0341c1c06000501100c07405890041c0003514402503211030380012604102070000d5500c0c414070800d41501e0700040000304940480c4076442100c44100f940e94020500180011b02038004085003008101c00d1004685540540c90a85002101c014000340a03c449441c4c5018900d014481d1082c071b500c1111040520111810304620080e0010002e0a4940e0407000c280714100444440100d6421590a03402d0b1030003542100000e0381da00b4a000d1490008080740752943c0940141c4803070b040060107564808d075940710306120759000c04510f40368090f0b204039000c00000c844182c00041501030b12684017580000d2a100b0081d030001141c4910241089400c6006450800400d48000b03030641c2c4c80e61100e0182401c11070b400f04000d01a1713502c103031030004201e4261505002e50b4103204024003c0d640381c502014013 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 764374883 1250 764373633 764373637
    0x15030f14010605030610080c060f07020105070c0306090f03113714010b10030b01020318010309230c0406031e0305040803180f0306070905060f0d02070f0303231902 72
    0x10f142d0500c507001c10300c40360165400c651012650014101d0f01800c2400c01403201e44c0c020b5106200d8400f1050042e4005540a64010541c02c0e1007007203904c05050712540c54504582c040304040d240d0b950809075140c00c158000101310015030403c001044164440d010300031503200038100080820882d0240880350b00c600081c0c4950556003c80050b03003040040c072a02d4024001c0c1d1203010b228840c0d9500025101d8003a12542c1514401079010f10301c1c001034083c100380500150001541050f503106503c00104150181a000328184109090152602c41100c40d00c0e20405224603031096140c101d080000500d0100480e240000180202c443c3e5500341c102500c1600481d0700c0341d4170900000038003281c9000c40014200301d0000465011507811501420b15654100490f00c03440482c20a860138005c1c0d26014010740f00b007040c40c2004501d40717100d07600c8950590304030301c0044030f4115140341c6010415405000c0d00206040544240208814840c01000c1820000d40840c4c400041501c1c41038400340a501 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 764376133 1250 764374883 764374889
    0xf1410090c05041701051e010e0f180a051006090b090604090f0506070804020316180f0209040e0304090b03030702030a120905040912030e0c0321090301140a15030f140106 75
    0x151855900d11103220b58086c000c03c840324982d0b091038252880c01411342c960303124180c4400c1ca0024849a598000c18581c1c0302c0d000d0451143d40d03007900081c101002c02004159201ca1042c0007400c80d07c0114041402559010340004107000e050400440650721a004d040364003050450740400e1440190820301201110440003030110b001d100e0800020a400000d5a40141d100381c04076450000c030302942270910411401000803c09021803c0c01412489030001a400d4020307030401440d10b0244800142190142d0010308416040450204004406440b4600c0020800c6d000345160419035800a902d92110b0300d0010143c0c00d00b0080310210038441e80d524030141601600800c1907003842c0c10703d1400d400100b040580001e0a154a240006034007060b40455000c0103402003201c0c1410403003540f039043c00b0343c02c00507801409100c5140d040c1d50034001e184078240d20107181d012070309000a0307074425241415040c20303083e154030380b0801c001410321114040d0250000055811a06a0b0110f1805404030354 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 764377383 1250 764376133 764376149
    0x21902091b032703090a0501031a06191e1715180405010e010c2a06020a08041203180303020c0a0f03020c24070b100b0a030f1410090c0504 61
    0x1104021205001d552842c20fa8403042c48401c450310307800d0b01d1180e501c1c400d071603009070030000059080003030354020b4100c220613010003200c4203c00340c2c000c001b05100e6007051220258a80c105d9090301d00c01500202c0c0c071907006581d03181d10103080540d4400a051101c0c5200421041662003000802c07800c3c5010702c04080c2080142400036442c03941107003031581141500c00303480079440d098255142850500c61400c41e90442d48403001d4007086504442d4680240356030141101c0c2c4800102c20001d04144018565010b89855178946c074107090a002015002c413642038402d062401080c0314010f14100c080007902a414603025030b80c0d90f40d082d5900e040001c2c03400014401c28000c0d5074401015004075504501b24026600c030012540c0070380d4107407140042194900d80e040030070040080414030056000350302c5010ba04000140c10b5541c5584600340e4840420070000039036803241c080c1d10102700c0c041c4481000c00010040c4940c03d0020805500340d2542c4142c440d9550b5078481c080c030381e40c0218160b034000e001e40303 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 764378633 1250 764377383 764377387
    0xe100f1d031e0f0a080a060e040c03030f1b0c03121701050f011106041101030b240304050109021c20010e120f030a0e03070b0a2118030f0906021902091b 67
    0x2c1000501064420b441b000380c11824140d000c107a0048440000f80b2403504030500c407501501d513403410b035000480e90071040108400541c00b0404107812070482d0b40e141d4030614a980801e850f42c02d003401c40100d0091003e00b049180d021100104019501141c156130088980144a03000328005980c03615298045201a003d9402004107001312040106041d01080e03e0074010b13801018100460003000301c1b125000002c50200e21094403005801441d40903202d640000f0360078a260300050919002001301d80d078949001e110380d80400c00e9412254080c2c0a1151102c0ca1801c3e60500190140540360320503401011040517141c1180410421403902100c46003e607550341c4a4244000e00400d50700000b98068801c503031000034420b118004480a0811554031400d00a541060740d46d076a90002141408079038407881c102407100600d02248000e1031007a00c4461000044c20030140032540c039588044195048078204807124036101010001181d8121502c1c6d000c0c0e40c621400e40c0007011003070143c072080b0b600 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 764379883 1250 764378633 764378647
    0x2090c030f0601030c0c06090c0902070b070212160f06150603021b060603151f0e060f0301050103030203030c0f160807030909061404020d0e100f1d031e0f 68
    0x1440003107000780710740c0000d80324a0360394030019001d0714800313404500000d003545a80400b24940b5401442a503100d82c0d81492450341d901143c2041e078000c400152200b4601c407003800141c540400040003000790f890401c90424600341046020851042e001030000700c1c950703031000200070150340710075003003110b0800820f469038940e40024001d400024540c030a61032029003040641c2c00014645100c0c0c6402001130601516000c400c5a45420160402d403244071071142c00f0605440c45e00707011000d020400c0400c022884c20724208800f0000074518039019914100051011070341c08011258054042c4034441e1313031040c0164100856200c0c40c408100c441e41c40c500d41d2010046000001d10b80035000755a14050705481c1d981c10b404940f81d034440c2c050509000507150300d00f42029000303800340f030145110014064140e140c0c1141081d108440714240969a00c50390f8121203200c2c4940301c0000000030029528060b2640c2d000d699205654a0004808010080c0340707080100c40c045480700b181c214005515040 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 764381133 1250 764379883 764379901
    0x3030c0114060109080a1e03020a0606080a02040b180f0903090411030115090f06031e050703090204050714090906190929010203091909112106090f06010c0209 70
    0x401501d0780b038005010140b0000e50100001080f100140e0080d0305030018443c0058421094410007604400b9809203d800380c009c500c281c4200c0c0020407180c0d018103c6024244100400c847c0aa40450312440c030002004651807403200400380c0c000d075110084583ea40b5100100c03850b500502a8540e8881e051561005480c001d080155049550505401461061106056400360b9680c0621043e01200d0001045810f200e5000031482e895055002c20400c1c00000b5001c003503600468074140400d44455214086003000e10805511421502c2c0c8020780000e000001941441032a0040340720f0710784034000c40c54541d100300c001d00b0b00f00d5041403015006a40c4050901c05045020300e20700b04000200600590304007441103174100c540c5c05a001d036203410120001c2004000919549081d9540a540c2c041041509442a0b25207110305da003e1a0300c5900c400b03540c1e0424140c000c4e401120007052414840551a29032a0079084486d0400341c1c074490351490300480341000741c2034000e540200a041480308000c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 764382383 1250 764381133 764381171
    0x1302090a08150604090b130201030204170303070f1d0d0212190309080a080d091a0c07020a0f27020f0a0305010603230a0c0e030a0b01051c11010503040203030c01 71
    0x106855402d00203a6110b40c20401244d00101015000c1011100010074059401d1030000d50030b40305040041c146511035001c2d008920a8140b20b251076070000042c8001103800c1713103096008008504d000d04c1e400440c407440c03805582e0300360350803805052440d440c0e01c1150b40380c001022141c0130420481c0c2d48031304084070344402d0441c12002a800310307801c1c2501240b196008034019017160f4121480714a48484009550000c2110400c243c0d403214501d82002d90140d46207035038600414208083d941c841e103190040180300d22882d406107400350040c00040201c01103040d000d8170405101c68100740480d44031115040684584c41c21800c1c2e0000c00605040400d070540d024a050303d16075542080020070001601003101000c1c041000d003049603100107864038502e030b001800380c0801842c1848010a800001c00d1501e0f806d450304558880044005003d0350610301042000201070841d0b0280032840e0740c44084040c298406c205041201c0040050f0035503c04100b00c500fa01180c074020004007042150b014010 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 764383633 1250 764382383 764382403
    0x1803170a0509210705070e06100302131202152101060305070c080a20010e010b03070f050d2406170318100c02060301080d0305180c1302090a08 63
    0x185005901040d2030a0441c441d0520407030281c0c004020103070400f86448020f044401c52104015404c2044000165003071000c00005c1c4203903e50890315080440422400825203075104040501c144900d0407141d6840030110704803102070101c4c4d8071000030f80c00440d03100c801c1615a5640c440c0c0000301d1030b448450900c2c503421040d83c4100030114a03600e0703420031025034009841c1c0e180000c0340003030400003140346c3c03000601807041542801c1c0f101c1c1050b0074000c0c0d4000c0400c0c1b402d03207890355954120b6902c001d080c002c03582c1c4a20220040c250803824a03038039400a04090041c940988508000c0c2d500300040b80182d41084a034051017015568240d201c05006030000303010710204030303006000a1403d960300000361102c8101c0401c041141c8400702c01842a49920180701c2c80130040700714960fa01684640c00194060001080a04080d804107030b405401c2d40d0028164514100b2070760b181104400c40450520361440b01203030100102025101c40c50301034061244865417006070400001a00c1c4c0780040e44201c5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 764384883 1250 764383633 764383667
    0xa08090a030b0c131502030a08090304050406031b0611070614131527030b130f0b0f010f061710080118050c09010f21080316020c0d12030f1803 63
    0x8641c070b45d91079050301000c2c80c08000242e403041c007d4080c1d05009050b9594404020401c42c0d0074995664009815180c40b03600540c0c03440d07003941d480d01c40508400e150101410040c240020f41040c051425680d6035400e01c654010442105e145c141070450040030cc03803081301c60280c803901003030321800000802d4160207a010040b8007440d158024007141c0302620312a865010200c200d14614685503030b8400342004100a51407940c0c00e4040740010b1046143e900e60f1401805040390710710701406c90707041e041e5040e003154801040404081109907444240c040f01d46401ca540b40b02603495000c1c081018032201e401c4000154205000c41d040b000c0340720a41988035010320100c40c1c80124a81c184680c0a00038007510b1004038031050b0510a4030359001603081e14001e090246546000302d922006415002960100001c80a40a0348040c19504004204001400329003417000c4086981d0354108242c00e0032550420715481d803401c040180416484019000100da121600c20a058640104990b803101c0520031 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 764386133 1250 764384883 764384917
    0x180312050d0f0606080a090203070f0902041a070b060f0d050d0f031a130905030f0706050105040c0201050910050714070809092802030402040e1c0813050a08090a030b0c 74
    0x510411500543c000c64001c0d454054260711803242c0d1101528003140180d0300b510588000190150820519400802c0c0784d190060300c03941048243d0281220b11f14413500c0c8240c05000710008552482203480e0000d5084038a02d0040714044080380d071480c9a600082d010340520f9614980301d64000c49400d0481030030b60b808010400d4115201940d54044281c441d401030614080b40b032403400c40c0d90001c6100c40c0034404503410001c0b17092880e031555000b01070843d1015103a10042020742014061000008400c0c00240098904400303107607a03a4080c0c4600490340fa441e00c0105103941d000300102040510362403500b0743c2e01e0555042c9550f1603484030340a1800390361590009001034150f0944103040e254288a4030008216819040001e50006030050340e009944407507242c14000100503800c400e01c01c8049020a108420300080d000c43c5004082c0d07014103480211881c001380012a65450381c0d60310841e52510380f007280c404210008410780005199481000900440d130500e503015052060405035084 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 764387383 1250 764386133 764386151
    0x60601090f0303020703060c020f061f060c08030406110409020a080f0f070504060e0a0510020609150c0a08040f060216050708030f1611030712210f180312050d 70
    0x100c0071029500c000703401600b0900c03050001412a8004820a1800707104448903004c4d019429810400213540056020000003c000d0305044003c407820020003190805035a01e60898641403011701c4020001820940e07204201c4511241120079540501880601191140a02c00018001410680c3c0c440e50303034613200303000842602080400503c608242d50300c0d64207240c80d04000f81e0384d090f0311410700b0354041005003000c40c994446220a81800c00c2d83e600170b10090400700301c0d0030b046c00f07058200c50320031880290400c896420040100c0307100404a241120a540e40d80c10191928a44228000c202c9800021188400404035003845c051a01900c296048180c1d10030141c2d0340c91290300c204d40003240003403011003804848243e6000b111801002c2500072001d2010010b42042c0b0030703403c500744281c00d170a40101405a88407501c0d00c3c0755003043d4280522042c2a00140c0410396905c0c02d80100108544021007030072010030000011580801000c003035140b2900064500e0700050a855140d41c58840c0130 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 764388489 1106 764387383 764387399
    0x1503070207080d0305180d0207121b0e0106080f0f010e060105070212010c0e240721050442180f081c120b2106060109 52
    0x51989848402d0040e00d800c003c0d816812035001c1c110800000c1c8c0c0018400d01900c004c8000103000d06018030302007025405800c014440700070070601c000342d481c064901070b5060340c060340c6410700c40e030b510a5240301329540100c070082c04600c03a00d00100a0406001102604268189000351030180f03941c01291000e02e95909051030383c3c0d0354001150b0310703030381c4441c4010800a0890f00fa1141da1038000760720340715060b000520700380c500d800100c0408000c048001940c214a98a00c01ca8000715803001c050b085070003500c1600040c0e4141c45070507001544501c005082130340080f600c00380500840c505510026402c138044414030a11080200c7d1103907242e0300001c000e0010400308501d8504054000741402600d01c040341080da10554040c1c04035130005600c516500000200203041e45c000c100203800e280d50380401204500c0031a044612a401c0414464880c10003a2030300d0f201e841d130742d55030 = true := by decide +kernel

theorem cover : BRFrame.Cov 764208633 764388489 := by
  have h0 := BRFrame.cov_init 764208633
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764208633 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 764208633 ≤ n) (h2 : n < 764388489) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
