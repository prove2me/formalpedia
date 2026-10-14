-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3694
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:24:16.414308+00:00
-- url     : https://prove2.me/submissions/4e5c3a32-92e7-471f-a51b-6ec981765072

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 664208633 ≤ n < 664388489 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 664209883 1250 664208633 664208647
    0x3080c10050c0901031b120902150703020a030305011a19050408030c01060608130506060f0f0a090e150103031706040207141609020306060418092108070302090604030f17 75
    0xb00380c000e403c0c0c102099a0a209000e400d4901c203c5d082d80150501d00001d03a4066400403220040d0490f20407244090201c4800c9100d805040c0e01070b4004410480042e084560b000c01459454017500b40981700d20041c02c408003005900416851080c810055500090000c401d04014085c81c1503130700904a080540f5540c00038005000c0c000e08407405910081500700e0003040040c104010840a4150f03c140200083d499400401c41e000ca00840c01030340c1300500301c240b0003494031843d035801d00130301e1030000105003130485027000da0915010300400ea200020a400410100c0c3e84020300398105800141024155210000850060321030300d40042c00b50850300c85c45c040038400001701e80009200840341c40710f4070354980c04640164401511003e0340201d040c0000d01042580c0003402d0003440110500140301c06980e0390b01d00f4641e00d03000e0011940181c0180b40d04069400008030b0344c1c040d049143c1149461f48090001d0864095804082d0030584183c82100c104140c1d814244183d03040580b000781c503059 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 664211133 1250 664209883 664209901
    0x608120418020306010906180b0c0714192603070b010501030c022a0a05030f060115020f0627100605011101051603090503070f0501051e1003080c1005 66
    0x20092194528402101c0d6080308000400e10a072801000141c2d11003158601c1c0580071161940c059100b00008803001c540014081c2400d002011903a4401d070140c00c07032625000400102c418142030490082104050948442d5a18274401060b10054194245c4000c0f41c20b844034000000102c0b501582d210005081080c40030844000781250801d03a8103000c01958042d04a860b40ca80720404501c0f40742c2801d20640304450840d407444000d402900510219980d500041d2901e1030403030546040380c00c064014441240c014032400d403020014002401c0d10342c04224800da8a43c0018201088a501411440c40414807542081005014207040701c5a4074603030440003000300342d1442064041500b815007450146c90600515224400021601ca22260b6246003035001d01000c0e801260030b07001c10403c5e50002000b048000300c02a000d52300004203803400e0800f007221800ca841c201e411443c02207042010040c1e018410000752a4000f99071030f10f07000d10b01318aa14108400ca00707208400c0c104010400d13411 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 664212383 1250 664211133 664211137
    0x91b0a02100608161a0702060d0c02010b011e0c170307080718030b0c0a020a0b0a0605090a0b030a110a05031e15010b040311010203041a03310f06060812 67
    0xd003034074020442155a00340aa42d214200c00340d550040c80d960b042040388416a0304050f100c24960b003016840c0075400d0b4005091548120b1100c0d4080b9030f543e01524805074244101c0451140a00b4032148031580e1100164640c0582c1081600b00421203195004220082c10701c1618070b040f8514141c0c0340d06251a000d031403010f00700c4903a40050700d003140c0b01703035001c00f0764510307808030307a080216040c60b03880d81c11004a00d80c1c031040720300b420345c890040c0200004080700e0320140f044403982000115141400e08000c580d01c800f0302100c50036414440031400607036000c1000042d850b0b100e039200000c101d0010100d0302c81c2119500c0340f80e0600400700c1004a02c2003d15a02c4081e403420360a44013004030020381c0003100c20003030180c4030040d601400240005041f44100070800c1c00305004480c106661031106011301e007041404103000b801c0110600422105100010303004000003070400803194840541e00000a40305103010b0308100303d044018081c081940d001e10302500746501600ca100025004028107a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 664213633 1250 664212383 664212403
    0x20702061801080c19203702090708040609060c0302090f0616080f0c07171c02061b040e090c030706030e0c090a0e06071809020f09091b0a02 62
    0x450343d10400980c10a00e02021100f0080d4182e07038042034070704070300411125600c2c080c50300e10502906407155103c00303400b00541c0c090040410b180c04000d0000d4600c0852000f2008989000070300c0c01c10b5100b005960301c01d20581e01030810301d090805c03603840c0d0034120091300d100540984860b15001030528a80d80c1500240301124041e290141403460500900c000c0f03100d18503012070350700d0b5031034190742c0010032510050009411746085c40c4d042c00d45080400e42411a252f1241c61140102800c1c204007200911205060941e0b0318001503800300112000785d03d402e802002c2c0d1481c800c0d03601e081e56500c5180016a07001e041c00314441e401a1401406544e91041551b92052107445000b20000e843c902c40d019a00006014101900c2c10900590a001d20f1110207003c2c1106141c651076141e2880004100e264890003883c1d5132017800c0c030360112800034450000c1c2c000c0110320b80100132507420480c000044a00d000380651702d100d03040d90340c10300c410980d003150300d4030703221104002511107042c5600140308803034 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 664214883 1250 664213633 664213637
    0xf0e1827060a1503020303030705070213021602100f1d150705010f05060607050a060b12011b0f02070f03081e03180118241506021501120f080d020702061801 69
    0x190f00030020307010a00400c54070000f98141e1080001401481c440c20144c8585880900017080c590111040075040c1e0b007189000381300c086c2c1c00d003c151003540340c043c001004942c010300b010f40c250b4002c000001d100090219070034510b102c1480c003034000350700c03514070703035004220f00e04a0951103001500d0010301901070014603280107420301001c6000d600c3c08000321041c00350f001004000c668269034a240291001c00c0711542e001950b54401910084203006046a0000f810412030b1061903000003d04200c410402c0c50086500c1442c007404260394852204068a80002d41c0645414001b03118944a46154120345140040402030040000614120001c2040858004d00101c0100b500c58440c00c403030310502806104a01166010304802c8211040307440304255000b01f400342915082e540e1405c401c3d4043d400681c03013498414100e03102502c0b4a40980f42c48807008081d41441d844803405a40c410f440607083c81c20000b503000d690391195046403941b0340e024105546810603800c104402d89040149140 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 664216133 1250 664214883 664214891
    0xa080108011505090718090504080309010c030218090402060c0304060503160f0905090a0f1802030606030a030c0213060806130605091524041107030f0e1827060a 71
    0x2d20b40110080019118003a181e04440e6460141c12180c454409458190040f914200401c484146014040c800c900032441c407513482c24032411007421104000301e64400c046c418402410310030180ba031780b02c9a241003200c2d107024030380b2140002007680c441c104105009100c0001c00140154003c00514030900a50449190503203c00c0419910040081008800034103422818042d51030b020503200d4002203c007100060094550003400111026044800444a00070903840d0451500308001a40101c0a90151042405c140c0d0041c0c102002074000030710074100c0a03005101d00740540d11003001002d841c4100c0e401c07400c158072244502600c03154140c8029007460009885060001000418500384400c80313921540c038050754900d900c9a0b0032018910180d5050010380c08e0390385008200c000c00804684a40d1901e0a00c2c0203404d00e843c8201740d005006408102c40b10607500c10100c1e82c00500c0340600c5038015070321448030803090380c00e03800300c5480f0b0500400b66107504000050181d1003041c401100704 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 664217383 1250 664216133 664216151
    0x4110a08010c080a0509030c0703150f11120408070c0e07081f0303031a151213030509040f1407081906050604090903090b030c18010e130b01050409020a08010801 71
    0x35080c2e810780400385020400c1000403a58000041d80056030102c034403020b0700d05001c1c5501c405400d014030369200b9940008007207068039403d0450310407a404038140007400c1204041241d0603042d18042d95223084e10502102c00090144200f0a0403540729a0348882c00901d1140c85001d0022807080c01d60351407001039403a40c0010140c8804c20b032942c0311a20180c402e42401341c5117542c21005007003049815052816110b1800c003d9803282c5400d80210000003880507165805030201002c002d00003004041d5808180c4d007034501107034000d4221020398001751000b003000807540b190003000c1d1046101350010000700004100c0704c954410181e0380600600e05500c4800f84003107000d40c0540c2c8442c094180d00200030041040304140030ba03c40d1444921074201740d000356999005070411a001242e200010752070024900c45100412402400c3c81c0d8000d00f8521012080300c0302145082c12240c044e885007650f0b443c040005c0fa805481540d005200c61902555a061918801072581600b880784041560a2074525 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 664218633 1250 664217383 664217399
    0x60b160b07110a1101020139020312041e0b0a0c030c030c0212180939070f0309090c09030c08030903030f0319060603020403021008010302240c030304110a 68
    0x44040c102d01000280711046054a81008400c0c070031480342d040d5036039869507425115076603903810074400500000c11048066203c2c0a0844001d445c40c1d541190001c0100148002041c408160816000103038602e40340c0d08510b0414454410503400341280d0b000078100801e05101d40c000503240300c0d65640510054190700c0741502501c010007481d0300560080d0905503d42101040a81130003d50310a08140207520800810019481030f0356410701382c1000c500305c0700404107245810800c1550368000e0488441c2c1190b01040d00c2c014108020203c00855000c1000c2c1032052110402034a8004000c01c04480540009481e45c0c0c0640300417582e85c09e094000040541020065401a01c03000d0042c42c0b402d0f000486452440e4001002084070321140c07003454019404034032840002d00403136103005917240e0450040260000306040d010b01000a804010f10040e10360004806803a03503020700c007000d450042001c1d60458050f40901c1103292001100700020720002540d004d44800064072511025a100e040e0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 664219883 1250 664218633 664218647
    0xc181e0423010906150e100503030a120b040501090b04140c12071106090601030c050916031107020d0b0a0b01110307020121020d0b010917060109020904060b160b07 72
    0x500340340c280e00c190101401c1480da401042012901c0005206111962503108036030440d03000c20345903481141c003441003112081001e900034200501c0d003c115803402c2c001941c0e0340b240e6070031013041116000d80c00a4036040ca42041d051044010014000c0750b845810440041c40982051071150f170400d00c3c0c2c40d80508411407041d004901114181e4a00001c0e0501c4e901d0340d003400b800050402130001c21006801105019190103401c421000e040d00e54034504002070308143c031760030507440b0b0b440728000c0c400c900300c4600054100c1d000900b0003041c081035001141c4001d004406001e5002075024211804102c0c000c45a1072168103800e1040042011210044030700c0c44c0190703201016a4010022240598050403940201030a204404801411010590016a01301d002c58041480e112a14511250782011a10000c0c0968031940e54001411100721980c61b1018418814650f40c000790b4280e0685464100001500400c451036542d8584ca80c2210000018084142e6982d81c1c0003010076031040c41444 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 664221133 1250 664219883 664219891
    0x1a090a11010c15091a041a220b1906080109060606030c120b030c12060402010f0e010c1b12050a0611090a060f02100c0c02030c0904080f0c0c181e 64
    0x50030401c0f800340c46800a0090030081010746242e05c4260b84c0101c0300956201c071134804d0340311300c101c41c80e0714501e45901c1040400c094001c4140c45130038001801000c07189401840d2450f045400350710b080c4c4603003034955402d070008600310041504150740403403483c105402030b07041c1c6403041c001008240e946043c1102100c108880200014003080410b801c900101e0b0000c110105000b0700b95801b405030a03002401040700d001d03c1800c144c02480400c400c1d5030700404000014841c40c10201107207968080000c003190301745540107110540c2008802c02c5614513510341c0003d86062203050004c5006414000d039510351089084884c50b0030500040408140c41094401d056405440c001c003480c05c2c29401e840e03407503004180c0380451090f0646009100c00a00642c03962900c1a2940d01c41100540180741c00c02108000705c40c000d82c00c501c28000061652011070354401000201541c0b02d050014420f81884841401d0b40d50007880b940c001183c07180c04408081c000c1c800a800c0400c451441d01400c4101e0a080f1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 664222383 1250 664221133 664221143
    0x4050112140402010c06020906030a0f0c030501032d05031308070b07050c060c0c131a09060603070f051b010507111908090a081e16211a090a11010c 65
    0xc0041001540100c5d407a0702298030400d40542170004901c081902070b001210340e80d40440d00c885401e0518059032007a03000d400480d00d400c6c04298110740b1800000c0180f010122544244810076441300340007050040e82e01c44d0300209803569030014582c0c3c9159060700c1d00980a50340111000021101c4001c012268015804005448802150401c00085400840400100d0b00a849004142d9910142150460b01800c200044d0f03400c0751000554511209980490049020780d052202e2076075010181c079848025494803040d180c2c2d0242e02203070b5030300509200340c41904000402d94034111043d00014802c400e2551203005621840421943c2e804c0c8200ad01c80314003100412040200d86140002d025440700a4805240a607448c2e0400e880c19401c0d010010040f5440c1d44030744000d4406002c0b01ca002003d90089811081c100704501c202a004c40b1800300301d40819000c40c2080103048494900b0185944200101500d480c01c2455110040450111344040141c595a00a0b60190000354005c039081 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 664223633 1250 664222383 664222421
    0x11b06050c0f03180607050a09050d050114040c0e100605190306120f290c1602090403020105190509070b0f04090504030512090a03050d02090a0801060b04050112 71
    0x58492800812029001044001003000800d100326100d0700254015401051100e0000700c06001d202d00740b101c0038003d0703801c100d41003160101c2168003202c4801035a000301c0305180002c0043ca0b1140c0101905907180c6010401081000305000e03584442c5000c40d0155120000c5569504001680c150250b00a210206800348240070000901b42d0a4101c222070908000415a8881c004000240c1c00c048003211508ca035601c81c07208000a501c180d24801c61402ea034500107002c0000000e8841d1030041000d040400085016213130343c080b00540c0440302da00a02400003901702401d009001e0041201c150820b80c80c1d1250b14028101c0d5441024800c0c2407080140407881c0c28050001c0c3c003540700b8400498001014440421441d009104d0540503500c80e807502c0b50380716400c0d0614a440c0100600c420800e400100000003c40d800070100c0307102100c201001691540d1803800560703001007039080308001790301c0c01c01c0c0880c00501103401081507a4098803580030401d400203d100c180d604d03401ca4142c8860507 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 664224883 1250 664223633 664223687
    0x102070315020315120f010b030601121e02090c030a0b0d1110021e03130605120a0207020111120c1605101b080d060501030c030c0f140f03010308071101 67
    0xc2d0301843c1c00024034200090328540350340c00548082041640c142d0315801070442daa0401c00244509611804158007800c1158900100d2507500c486d580340c064a041104214598003440c110b4640d0800b0303500409040b4070381003401003806150821107003000303840d103003940c1e824491825036000d0b0a100d51250181030500c04c0041400900203417211844254410000c55a517440342d1040f103101c4100c0903400a5445000b500c1210101702c5066101c041404400c0102c0c040204010301d000ba800b1b510341d030015a80d4031061004848141e03d4170503461141c0207880f0300c01e21720911800200a00d244820450b04207040c1c581280c140c0c002c5c07a1003481d9000d2800d510020003d4003400200c0c00361403100c2da40c0c820007051611030038082e900144440140300d40c0d40400384003541c1c062246420b421100d190030000360001c5d00d07001e4172080c21202c0040520a0303151048400d54854030440b00c064444599003a180c1d6503030328103203506400c26030048541d4820203d0008995126101682d940d04209820700d1945c40 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 664226133 1250 664224883 664224923
    0x71e150813170d020f030402040b061606020901140d0f0f020c0c0d06090506150a0603111204080903070906090f020903030d0903020a0b0f181605040e070302150c070501020703 77
    0x8200c1956030b4281000d00143d11031031290f1000d08610b418101d943c6559180c180b0410040b550312501c064840c01c8184110404d403984c9211801e2440d40c02000169294038450040c0c80c0c042c42e0062241c6076010000d00c0640f0b1140f2034010801c00c1c51030020a2010250640254040e4040c02c0c1c2d0909003684211451001480e1032031410700420b020740c0e000101a103030380e02c036141814800c9542c044070254065022080341007090110b001880756207001c1208650040c40300ca014032030b200054030418480c0020405008014003154030b1008001c040b1500e059649070040301501c80b1b0301c1260642460451078400942c5203008070340d0a504018007841c607001000148038010144e10405404511903c403c410008081208070340c040d140408104900745881441c20f0034400095801000d25040000740500c2076400c0791081c400e9503c122800701707040b111912150f16184050b40040e610021209a209034101c40000500c00540d8000940c2c00300c4c0c0d00d500040e680d80303146120003801c0510185202c42c081d4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 664227383 1250 664226133 664226153
    0x3030a02031c0f060e07020d021501140349050301030b0417070c05040f060501080c1b01060e0601110303070203070605220302011b020a23071e150813 66
    0x1407410ba40008070560780000d8001203603003581168103d07465000510031255010003a10108401c144010004103004003908112850103105610300006201000500c40d0340901c0050302c81581410024400220401e1220041300d183c08102240c00071403003c510007442021074119401050b440303003481d503442e550302c0350003c60000304140c80c1107a00701c0c80034a241171008014607a40d4040d1401c010b03154185020031041b0740002c161110410710b808030410944c1d0300b124016138010b510480c90b80c0c40e00c41d460300a403a00c0000300c104526652074400e0124a60350f0f1803c820780281000e0380c0d0f0021403000302100a0342ca10054900002603130051281384000781f07803504031a5202c1610441d040030322a5010542c44440b4201100318050b0351120f081001c030440305080000440120710003811400c449460711031a2042881c51000002c0340e545440c4403aa00400480700240515a40c07041156203c402503015030655004071445410400d840e040b0341481402c031700f03000d403049a074540c40019066541c00300f01 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 664228633 1250 664227383 664227427
    0xe010c051c0c060603060c142d160606030b06012604020d050d020a031d010503040204020a050403140303090607030203072c0d0f120516030810030b0702100b03030a0203 74
    0x464854200c000290f0280034043c0218031a46011031694404140903142200144481540410500c10600040f55941c02140d030511204818070200382c0103065485688038010550008020f601d10360f10402c07446910000031607000c1d002c400b00d90f44481c001154002000b40e809070307403400c03145200002280096242c64116200038903802201c06c4030394405041080048103a00982c020b1540007082c5900188940c01d9001d801c071400c5401203030030001038000c4c000580040e00860380031405864150140e011500030b180c001141d00031009015a82075038a41c421510703504240031711f0002c150514068029207001e10340130344441802103030b2110003c0840b1844e501550012409842404160312101c44a1500501680e82c0385050300c0c090a111124011200003002000810003407070401701010507200c260b007a45468030842540b27038411704a45003170b0170f42c1000e0a548544814410101c4e000900350025083c21441404208059010107889000c2e191a044c09030308104040b080d00803010041c6c2c014 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 664229883 1250 664228633 664228637
    0x30c030c03061b04050405190608010c0219020406030c0b0403210e0d050717010e120f0a12060315020903010b040b0630040c0509090111040e040501020c060411010e010c051c 76
    0x10203545d0800902a43c10503980755082128100c1458800300280c002c038000b500c002402402030444e100170013591283c02200c4510350344603011150046540b80d4201800454005a41d00ca405132180748010b01ba81c843e1004540014400e001003034094a086a02d1143d00e640340c44100d100344902040c040c801100c040120f031709014070344010441c0d02d14502055101503800c0000075104844070040341c07510690156201c022942440455600f503141da0844107113074180d00d0007000c14903181504402400060f04002c0c048107421002c10b90b01890f03a800360648082c100c2c020f003c0c4d01209000d20040301c1400c207146402200400c00c02220200f140c20a4204d0303c0c00d0890b11140c0c3d42c40000288134840251000c490054000f40b08000ba0b16054080c2a00a05d655008120000c0f88003000d1354103200318402e8030310490b44800060240003080d41521404407a01c2d080d61650f162500e010724030504034046241c08141c440907504c0c01944103400e030107821680301c00100700b6101e080c0b0341d8000610300680a601 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 664231133 1250 664229883 664229887
    0x60703120f0c0315051e040e0f03030703090317040203070608060a030b0129030f0a091437050c0d0f0c09050405010b0f01020a06090305040b0c070302030c030c03061b 73
    0x82050748500c940c800c11103541c2c1d00003408104042c400050b074070b46035112074400d1000e1000302060301824000200c140340c007194005180280d5628803414415a45106d20f41c1380800301c2049910703078064006030350192003696450641080041203500d03100c010395002c0d406902195080c01600e01401d4516000900140480041903a80d660b0b800c444100340c20000b01d90433000091070000c80343d440321034404504100070314154a001c5110000d1000000c2c2501c420f17945480541c4184a40c0e86031004580004205a0308600111650210f00700d0111924a006100702c14a400307044038015460002158400e0180c0740c01c5c28180100f18040035100070564004180203041c4c2c000542d03044040300100b6800102280d5880c180c00c216007111084c00c42540140e1031a0b500380096039010078440080ca038015400208084142400c6409000c1c81d00b094070090000100003094074800134a80302140c2c401c0341151102e0742400241a1102c4846000641552111010441c0040d165000c0011512103503000c80c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 664232383 1250 664231133 664231151
    0x120403030c14040303030e0d0302070512030a02120106030506010906020d02030a11010f0204121a100611010f0c09030605010b040302060913020d021804050f0903030705090a1701050916030206070312 87
    0x142c00e5074016031086010a9075801400c504c8502400f80410300c85840c2811401c112450305e0b4152034104060070b4650b8003100000094110780e25a050740c1d800c0414006007221582c488402030000c00b41501d0040c04140c9131003000900500c002032080340c90000340c0c05581440d181c440b068680c1c042009030540155218003442078101d81074400b500081c03c011b0b1000d501d2107200c5c1008248441d41410b00b00c801180c0c101040303c05541002c6810071940d4a04d4040044042041214014039441004090b00c3e030501d015003003015030240b414025079010b42820001d0742d0f6a4015040300d44038511000790015001e22034244240f414800c0300080d080383e004050b00e440842001c2c01c040764020500004960b410181a03c110b0030107210f0a070f801f074210b00c10341126007070440115950780401001c400c204440004d41001c0f640301c0041ea50000d042200036011116003034a00b45c0d0182400f122041d01e94400c1161303190a10100ba4440d104803034014001601d003c5580d01d04649026140d44186192a1141041 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 664233633 1250 664232383 664232417
    0x91c06050705130b0306010509090406020d0908040f06051e0c10050a05040606080109030e040f1d060106020d090b0d0f0603020d1406060d0c050405070c08040f0504050606120403030c 80
    0x1092050100740c0d212640c440e90b2118851180506401c1075041345000d10400c00140d80180807a10340d141c003111400c40c41d90312840c042010f481001c01901c920350505d00907108021059010f40282c8d00d4142d00882a03a8940004543c24007171180c13080e0011118420317081d84c0c00c0b0094020130000000e90240c0e030161040f8502e0b10305440064488842441d0303100208414005103104141c00ba1681c030000f800000340d980c400070305103544131805502c26551440c1e0040300940903400400c262850140142c19503a60b5440c254a84a0034840d00002d40903c085040140e482a141c00e0b040d40c1800240c4c0303007485400140341d0024502c41980545135651000041701507a00d101460f07560900c40e080034032801003202c403c0c6041c42c0c000707421180a0703055070004200041201c81001c0c1610340540e0b0010781070380d03181000c13504e0034180750b40a0601d000c0003d021810840146510059801c10b80d0f091241c1c4e00d0715400d1115a115202c1142c2c44110300f2004180000d2080e0003d860482c11484d1000340f5490b11228 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 664234883 1250 664233633 664233641
    0x30703050f030403050d0c030e0f0a32040b211204091d060106091e0306050f010f05150d0c090504020a2606060403030f02010e031605100e03091c06 65
    0x41d201103540080b07401c00400100300b00e0031898107110f151201ca40d13074082e40d01a00145102c0c0c00144140b6641107080740c2c60b20351940407401003049803441d50344200c4c4036848904c1e4035004c1c4480410f80101d00468521404d041c050502a0400600200966204d41c40440707034131624420103580c0760041035814519030380c0c4000030f4005002a0700000071404480004110604010b03060b41149400c0355004005450b004101e540c00c4510080008243c55240c00800c448083d49800081946240109100403801c000c40300034140c4140200c8910580c0d207a0b01008203800791080f08800c495020805044465455084ce500245a606045480340e0312074000401b6604039840700e02c0050802990300380c070b140801d00c0410403840b103550b00380f10343c3c20b2450200719544124000074080c0001c190451090718404d43c461001d1210b1841500e0b11074004092400005c240c500054030a4840e061000c00e800c4114030030191154181c0707005519005819060044450349880700020001898884001240b29405 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 664236133 1250 664234883 664234903
    0xa0b070210050c0406110706050a0c020d020604030b06090a02070803220f030519030501080307081c0e0109030e0108091e030c07030b0106021c0801060e1c030e040b0102030c0c0f03070305 82
    0x83c1c115150b82c00c268005004405805504909901c0440d00308409600b140032036400f50410b03c0c00e10801d407001d001188120303074407100080d00071200180c000207020060506031b020f040201c0c0c0015054503083c4140c02070780514000a007400c0d604002281000c41030801d00c84607040d041e03400304030854984d140c102904030443c40c154049440050007072000c1c5001e0b0311014403640c0609040001c0c0d4180814160b5a02400c60000c01c0080700150241ba2404000040c4590448200090194440c0c0e0715945000e0304414404401151b04041859000d40c02030224501c540d0049009050a03210003501544000000d04090200e00080216080c000f2003402100081c500941107400c40d545030400080c50107584c010115582103040c0150300c9039550040c2640d046404c1c41c6815418555280e0006042824003034540320200a41100b0004040d000b01c9101c034181e41c11601001030850000069803244907000c0b1841c01c0c0e40002c400c204280c075168003032260b8804d01404860080d516541d4043c60001510 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 664237383 1250 664236133 664236151
    0xe0a1112070e121c110a1a070e03060c0a0311070305031b0c030c06060f09040201020d08060613080109020a06140702010309140304060818070b0d05071119020118080a0b07021005 78
    0x2440d003051082c1c01c1425150540343c503030018002014180c5400c41f04480d40c0b207003c041c5141200108402500c03c0d1921345078034500800b62102030a0100440c20180d0241e211500840c0c1032588032061401e140007560341d03281e055100c0310300e541e0350305080e1014440c250300028071300107084c08944548030003000a0000c2020000050502d800d2401c1000240a0f0214050b88269840410000103076804183c100b916840d50801c2984d503140c040000d1100c0c0542c0a0380da1040610a60018500c04150000c106680c0281c5000400d00e0325140229044d102c032a8448007460703010428807005500c66401685054085e144a0050a092402c0b940c210341c01a8443c1c00000e0b0500280010800666451000d5291000080002c18a890184001d6004c1c039180a00c209e50b0f210001141355000e580c009115401c135000b5505181503d103c410341001c2d20b4041640001e020103444894001d4640b012815100c882000700307885c08076541c0e0254113040052982c0114043c00c031950300450103034045d040c001e078415 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 664238633 1250 664237383 664237423
    0x51e03010f02041202120f0a0219030515011401030501081f02071703010f0b07020d1e06110c07050d02060405060f040f0308090f0103051006050904060f0e0a1112070e12 74
    0x3500401074240d280403006c50780e90304600c2041e0300d009000286450820f6054807400880982600c0000c00414141e1014045004045c80c0800c801110700c03141d410f0300c400300609808500c24030011001c0310390034000c3c0ca03215480500f82c01d0383d0920020300b070610700c0710098026161841650b2410701c01000040c14a810135800300060100800f480f007c840640050704905091440603000079504080313402c0098140040d01074550f0581e89103082d0a8078054018409010000540200030f0b159800401100303203d02030804045854544910b0750024a6001841c60382030138100720400100340d1000705425010a01000000307184100c0b0b0714210010750060807035a4480c0d01d00002e0041220b10107207580e04042c5030000300110b404c0c98100c19000e1302d880f803821544410a08000c2002403a041c0c00040f02500c3c420700c0013405d0001d0164981c0700b040c0155090001d840100070304c22440c090302146001c45101500010714017885210040b801d02c0b030051000c1c1e20000c10100a5051003882504200c5002070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 664239883 1250 664238633 664238669
    0xa0f0e16050102032704020405060304050c040605060a02150705220e070503060618031014010f0b0c071206020d050c1b070f051c1e0516051e03010f0204 67
    0x114410a80040100f030014505d441c2000c0000c0c07a8600140a070120450005c280300084c684641d4156405461301400e40340c5e40f8105030400540e503a084180306445642010700c0402c1074104242036800724046d0340c0040180c01d05101c80000c00e114003c1541040040074411410314280c01c540d0203208650441c5160100c0d410021804c00d0400020001307001d0000800c14402251140300440c0c0d06451180e04203100084848006070500c0d500c0b0861400c80fa080c0583c814481d00741484ad20304072220b0032031480c07085035504810029405a00200d4059802412081003501150300750090210f104160041c41c1c03c00c82e04804045541c02d40b018071100201090460b0308002401c0820700080d415001004401c0c50907071030fa5094182806502e0003007028101c00002000e41d83c4506000c1980f2403030310360700f0348051401c4500031420034905903581c1c4210a01b1100c9141c40305110800c1d1a000361141800d010a52002e00c0c02e60582034031503816668034000e80d100e100302d6202610142c00e01443e0381c090642 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 664241133 1250 664239883 664239913
    0x507030b0a0c030603081605011103011d01090b061e0403020d030906030c14040612140106080415020412120c0b0906010906050105040f1a0f03090d1715090a0f0e 71
    0x20b0444001450300c0c000701031000ca0507581c140c602c1c49179150070102d1032601500e03055001d4268090a01101240440003168081c22003000103110000480780c1e505507031f41c815502041d03c4001007c9a08880c04000b65844c118424151a000b12158821545410b0762540890031107107a0142c280d00149200100707001c40750f8503020b4011040700b50300d4043c0806404501c03805c45807080d40b040310140f00e0001c40d072a90400b1190800d023000300c45101401c942c1c0d0b80d03881000d00941c804440c1200c1d00821240c5080c148030b014400c0d2401d4038002c11b00c001409000e071f038911180c000a050480107005040719550000b52071f5920389403168034500058040c80d403400d010502662015080241808800d210031301202514200340c40c01c450320500b01c1d190381950304241c0b86091240100c05403040c0380020800440c1b104c001040d1080c400c05982d030b080000c0c0700594032454402d0548101036000580d0103100103a28040310060f8109210035000960342031004141000c032501869007003050340000d417034120303c00 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 664242383 1250 664241133 664241141
    0x30b01052e080f09030a0815040b0616050c15030a0903050c010c230406050f2a0105071419081f03050f15010b04121b141f0e011b0507030b0a 62
    0x841e608019070406c100c504c00942094001040c41c2c4000d113101220070241e690b1600000074401010300070b19038440c48000c00214002c5e401e0b03419200d510600c00c02c0107442c103000040720f0892103d00c003820309680b221907907a000362404000503020400180100a4005c10a216543d840d10480e2100a040b02c0384009003298012846110b00300e60300207000402440f90890202d6400907501d2030344a603501403a03070900b043c4d01000a55108500c1c401c840b80c1d0b550400540c4914000c603000c0d11002500c04911840719240d02c1011130500254007400024101c5a0164564a030444c5400758020010107413030b02c0500307550340154000c2c1c0c4e103a07000c082a00c213140414021010128405204241158184207980d00f061242d40b04d01109030f84010b07441c8040c8880d500700c0841c4280e0810004000e1903030b602c1c0e21062903036804403040c441c00f103800c41f0351a412051001041103640365154030b040202100019100c80600d01d0410040030340710303030b070110000780b052150b40040c51081c130300d211a908000c40c80d10304135 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 664243633 1250 664242383 664242391
    0xe04061814010b13060e0607060e0f010b0301110906070c1e2c1801091505070f1701060c02040609020a0314100302150a120606021e0304030b01052e080f 67
    0x2002003001135038180100485080150380075414000251200b143c04a030a038800c106001d48107601e80441040144e201150240a910b178076002405009840320415080b01c4000140f421075074000c01c48001c15081c80b00140a40701d02503408980f14660754501d05004030402c1c40300c0005101c100009214041c400c481d811520b045c81a100700c6c001c4600e242000e00040090807039500316889211500801d502508030080159000c0c1b071000c2a41480110b99010f044180c41d0000032401e45444036104922420b0914480700d0a84082003080c1d180000964a20ba059003044e80c000341c555401003046540c40c0018004120305607400112480c003201120951134000e00b00003808503481e08100301594501c04401003803a03c0707104455498550200c155228040d400c94400502d0401c0c40004440e0340229114120400d0003041e0480c03002d04801c01d41d2a031185000040070140d03500014801420901c0d85c1800001006151645211805507000094040c85040d0000200b44104010f6804a800c0c0c2c21904 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 664244883 1250 664243633 664243649
    0x30204030809062503090609120b06011209050318240d02030a0b030d09080d050f0f07050307051207060c030c0215070e1512090f0d0e0406181401 64
    0x5290440ea40d12140340b003420002403250601041c91225007040400d9501c06003905420a0000c000342c0c580036001d00d0f83d92190301c000c00c2d4403000000352070a40240c0e4150b161f81c8604008000d40c0c82e0001940c100b600c00c003072200c4140d03841120b580015401c100421140018803c0500c00255400030071281c07820314468032005c0c040f14140114280c850109640f86043e0101c00980c807030b650351243c07070000c00c44081c0050b07140c4140140d4454590b003005d2800c041d0342ca0107060b00c0340a0200c641c1500d941c0301e08542446c20f145c0410031b8503401c40358580034100e02442501a070b49448071030b88825141051100c0e0801c41d40e1030005598080080341d114042d003814032ba09042c030075900b10235806900e0384040b6141603000b41e00040040c052620580300b40758480700081208442040164001e040790b00a424528400d050901c00715000e17200010b0011408400803008100c3c5500550f8111075020b180340510390055210300c004180c4002841c054203034084100c1c170015000c5000c000320041c90b07a0680c0480c035 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 664246133 1250 664244883 664244887
    0x180c0c03020a060c0509040f1a090601210e01021216030c0e041a120c0111010b090408071703040602070b0703060e0105060a0519080403021c0503160c0c03050313060302 74
    0x10000790080381e20442e00380c01a01c0016030b0b8141400a40e158820101d0484d031084c0b41c0640c080f0a015250701c0811001c42407a10ba10400e00710205114405005a5001e07000c2031001c01c0d59495000100c0030308091a800d540e001c10b50350710103d02542a0380003041a4141210303d1010406225070507084c84800958510b41030102d41080341019105038040c9070701e18011a02c800d42a20340d60550902895000c002601c0181c408442c3c4086c3c54a600240031040e00090390082c5409510005005107000403c004040140b04d44503a40d501e0100d81c0042012500c840000c0d11a03880740c01c10320050b5204600803800980c3d5030000c0c2c5444010781d003000303001c1c0703041c03603d0000c0a0003030384103100c42541074a50039035503e0350701d240c0180266007074010100030300c803003201011444140365400b050050040c0d22a170200c5921650a0f040f140243c3c0070031100c040005c0d0305200146000303000003241200c00030281458583e450780c5480c1c0100d103e1050b001502d0591001803030070308101254101000a050301d00c2e00714 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 664247383 1250 664246133 664246157
    0x906210c14040905060108160506071a04050a120c02040e01020c0c010e04110f071a0f070f200a1205090f040504030207230a090504030215100f180c 65
    0x410111802081d060307150345412980320b80c0342e992248860f0f60f002000c072810303581d480d400c05944061090000030030b0194484001018102801a90071059000511a03c0d6203451400c81e6000b650040c403d581c00c2c410144058040f50301c0c03480c6554400b50544d80c05142900e40c0c0144410b903000c1041c001130980c41006144c50025010a2108480c0c200b445c01603202c0929500040240c50f03080941300040a00141d20f003206807814004000c214840c0f100e504000004001c00022180201c034001c86880343ca03400901d15611503803c01c8049407690030324008244160721941c10007052001c1c9a50f45038081a010014042d6100119007440c03401d00c0d14a14181004c808107030200d9400702040d008a480b04041410103009106c0103014042c1c0c03410f0400ea65064403400c100324104480518020f2900381404030f000d0300d0500415120f603070540c006090b8080700c40706414006d00002c04911005042000c040b48207100c0d882da090062444004160031640200c285004072403251001909100040b5007003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 664248633 1250 664247383 664247393
    0x30f3103030f0f1704390f0602030d1112010e0f0f090304030308041703070f080604050403140703210b01020c030f0d0f02010906021314040b1e03030c0304090621 71
    0x1410360004425003040c00d50700c0d01e2401191390007079207955000f800241080100307494911035407a10203c0b01100c041b6030440d0742d80c4c1891201002801a400180c00402c41071606000340c0e0040d441c8452003401641c503108407480c405040b0442078010244d8032000e04103100701c0c01d0400078100e400004420080341d1906100e07650039a00e114074031000702440400c400203010b2040900810b200e0320b01840c00d0507680d240018000f030008034900c0d5810041001000441c0280c10f00e440380d40e00c02d50303140c0c8030010403850110034003129400041007201008a0386d40d561840920202e82c5202d022075000700445c50b581100006428424001141400707640311400e50395192a001415500e0b0030a14144124101d007003903012400b5118603800500001e000040d11510213011840e0101101d00c980d10b030050001160b403c00044e00c0e00600c0459000d094818103c51401d035217054064a402c1c000c0443e03240c920348100890542d082544070f8100c4581e111070400148916540489200c0c03840451800103010729510 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 664249883 1250 664248633 664248647
    0x9020405180c041d01060803031014030a08092706040f2304020d08070507030606050303190e2106040b06030d050307210f0510080a05030f3103030f0f 66
    0x406115580720202001541542e2001d44c815802c1800244030342d81d01c42000e1582e03503006407034441d032203080b034440006e6183c4680c5060303800b1040100a000011200e46440c001d54200440d860ba00c541d0344502240d203140d00c18841c1c910300407503c0440d203d518100c0100811685410340c01d0302518108085a0143d48014962286400300910450342ca45c03124004500c04400a080003080d0101c0041c4400a01030001800401c980c4104000d110694448040c141c681c0125515490f4482c0000d030307904805800b60945101c885006005d80c1e46005660200064034101181c144589030404400c3c0420302c5022402268081c0055004025100c0c10f01402007503484010511402c01200b4400e03081d8091661030841420030380704005110001c034001845c001401c5c03c0d20028168001c40300d00003215100451040c21264000f8084e60510111600d025459842642207000701c008680700b1024182070401d80022800d00d03000c60362480303400c0d07183c09003220402c0348560089c40b0701680c800d8031450740884 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 664251133 1250 664249883 664249903
    0xd1115130503070c0902090f18130302010b03160914010308160213020c03031501080c04090e070f080d02121315020c09130201170f070507050c03100902040518 70
    0xc5941002156081140c118081c00700020000241e8103c0080d9201940e000b9040081c401c6030020581903000c010000704116a450b404020002400081c035a00c490011014580f8040c0c000407600b40d80c0701c00040c0c05c0800300102e0645c2036040010a004841c480d201303682ca00268800d200020f5411a01c0d44207050140c0f130342c40304000c1d9140036100119280c1034814440c250084d0070640d210465146020b403250000c0303900b1040c0c402555540303041c561103400740034001c01980814600e0a4181410040500101b800741800d034412420f00141a90710070695000030b1540300042e000c01f2900e084000e04200c8040b203030103208002840721a001c0043e4844010464403076084416030601a0315081e4103042c02800b4865016101c1002c10034601000107004108074400da83e91000e00820442c00100c000c03080d00d0b4424107074101e800068402d8050001000381c81e00a004071000c0f03c00d130f2000030f1700d4554218008003201d0f03200c000500840c20540a255000840c070f0180d10301400c6012050385d230750102c50b9 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 664252383 1250 664251133 664251151
    0x606050d0f0b06220f0b2205130f090804080312160f05071109010e0601020f1b0d0302150c25171605070801060812030403090506031b03090d1115 64
    0x1085000c4203003002c604d950018403030170702d07589080c42d80d548600340349420001080000120300c6500d200030a070400d1400c000e50f0001400c0790200103a04180000400745411010605662800c05101141055028000500c800d00c0215030b2001c3e041d0b810385c904000507100d920f0760040c0c0c0b0400202c4035000310305040400a98034080b625281141010a502c2e080d1031812134002003010300224402c0405014a48190009c2e000c44500905154503140d980032410300c607074601400c0030031a481c5403034501d071444403a90080c8100e40e00c8944e1044c01e0003c0e100266100d5020b40400148800c0c2c0c429409008907890038560f05038560f20000b6110714640304c003800e030340d0031110000203183c000d140748950215540326000000c980c81562240c81060003845540111995440f45a407031451061488045a110b176a05a071000641031400d41807001f143c0001d0000091308404a071070400c00304907040650710401000d001000c61104004014012040598484000f50017400101480c0428842c055400100c14 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 664253633 1250 664252383 664252417
    0x11010e10170a0f091b080a0f060b0328030f0507021008090f070801151a0f030403030b06120628050d1424130f0b190606050d0f0b06 58
    0x441c41004200d24060107000a1a110100d4140607440d03928500d00c0e405d64000e81e528684600f80d81d80c0d541c07050300000346140714004001d00000c1c240d07000306261100140441e1080c00f01c0f008600c42c2694540342d21000120000c1c0240181a0310864020481100c2d041c180e00e441c0300f54001c00e50040c84a18200c05008061002c1540c24031f0411003c028000f9490aa42c511a156103809018110054501e016483d08240120b00303512001080f074403070064070004611f80301c0c94500d0031010b0781000b0805c2c0c0a02d41e80d405041c48a0311146c005100b040b071404110395461500004010724070a94482d00d4002d0313850030090068840a00c4c400800780c40c1c0444c2d103125900d00c5458080c00c04a80240a020380b8001d000413051406000c0a9042c0071104040344480941e548002c0030a4050000302c0181907038001856003404205d064140c681c11000124a0401c5018503804000584816500c000c0000d64002428026103801d4402c1c080800e84851062000d8600700300011f2550040003043c40c000418 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 664254883 1250 664253633 664253641
    0x30c090105130b0a27061e23070210020109050c0d05071802040f14010c0209040317150f01020a0209011509090c05090a0b120c1b030711010e1017 64
    0x32002c1460050046002036030781c0d0301102100901000c0d01e48a00d4600c41d250b2039900514091136841c02060f503616a4074036107149a4040006400c3d00e05507410b606004d040d079041c1c1d10010f030886880d24001c0014a1140e80c4120038814044a030300d44400140442e4580408540000c90209202d900c0c40412030b1300070385895107030900c83d05142150348000c0f0803210341e00b41c08241080c01d4025008491425a07070080065450344a4031402901d125614002018000f910b80146002075220b13420034040d181c51045022200c10202e556441a201024807060710030703110f0414a04200441000311013072010303002d11409030b40030446501041c0a071a42035011010092501b5101e802d101d03008005241040c4003034800b1420240032039014032070f5075001d41480304000c04c2030340b41d00c4112400f00c0c100c00038640b43e994646006018035003001e45402041087d05041c10314120041002d4104540500c400050146580d03002400380640e4000d40b80c00342c0c074070304e51841c062a042a40b541c00c0c2201756540c04100c0d92 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 664256133 1250 664254883 664254907
    0x51905091c1112100e0601080618030a1b080a09051c0f0b070507021905030c0a030302030a030f110a091d0709120c120b0406060b0306030c1302040504052a030c090105 73
    0x80004130282d41c43c43c00c030480c5800c54002807200d040b0303401e810650b03000341c413807081840a4156035800c0407080d6000b0007002c11054450001610b807505d4860140c1c0c1c6600440d6148000e0340e11981d030b15170000c0d142007002d110a01e01500b4101211001c8602124101d10641e00d00c98003540c5010042c21005d5004000340b200c0d80200111041380b03034000c3c1642d4210b0392803c520000c240e050b0141501a00c2444001501c030f080074803e0781c1c20390b50590019810702c0001c420440241030100c018504180e01c0d40c034640b040b0409600a000410802d403152001c103810b0018050140c014500c40f10200c180040a00943c283c10014610943c0c005031140d40b00100c881c00d008a2105840e0b108810b260314622401d418803903143d590a006074030030582804455620a21072405001c1690f110303916070804804003c0c2e43c900070b124044526007015016013020790b07480c0050211901150606a00d221240c0940c2c02c0c01709050740c071000d41031003212007401c42c105451071412601814201a0501200041c4080050 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 664257383 1250 664256133 664256143
    0x1b06060509090f0601151b0c03021302120a11070b0a0b090a0605090f07020d0c020d080a020c03070801051e13061a041d06040b0403051905091c1112 65
    0x1001d071006a081c103144103a140d580510000c842e0031402118004106c4042e003022003980050b10b540da1343d88840e02c291001d800c0d120458011100d403405c901000006841d22840101090102c440060322002c1c04000322200050042c045100b107031410350425014542082a03c08040d081086200c2d40c1d03441d513603410020b000c00308015502425441c00c10003e9000c940160044d2001a117960b1074903203034101100c540550640d40c0101582204032800c410902c61980c03003510314001004d001c0181510b850f2070407a54024002040180c218045401e005e081c208017131401840c5460007005149054001a51452142004081101d0400d4046940b40c01400c00e600d10840d08100d04010489008906c0307818001509441d90069040801d051410b0401120310800c00d402c68000c1c1056039280e94480f502250002c00880038000c0034440fa9080702220340c01103c245034142c0754941d458414404100142484194204907040c41415102c00074401d85103c14070400140c030011240300c040130031036083c1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 664258633 1250 664257383 664257389
    0x20310051003140604020f01180b1e0c160803040e0c0f12150108010801110d02130312080103170a0e010e010504080d050418050412050901180312110601061b0606 71
    0x7810f00f00340c02042030030000c20070500481c401c03211b07044240d88500041d236064401400466104032111810000f028003880108480c41641c6441041d66074600b1080c0c1d0340341c05c01c2c3d41024190f801140441c104000305030305a40500000300c002c5050614148494880c880e0003010f0304034032080400c030401407120880c03d03110700d20b0a002d244920f034038101e044441c01c03046103900180050010400002e01742d4040c4941841401c903201518640001a0b1001c006580000c030303080e41100701c0e4580000455100204201030340b545549154144d49503080c01c1c19504d01545c0c500a600804018040c00c840e007000131081402d4003801c015181090314030060314036008552018165000707503200074202c698807100400a0342c4d80b0031041c04c070b080086501e0a003110300480e030080c104005081c22407040780c0501e01030007403076078145001c554038104024450800061544111405071600c1c203440001d0350071080d007a0049060800522083d85881d00c01000d0b20807600607600011040c03180e10092005580010000d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 664259883 1250 664258633 664258643
    0x607020901080c010206060103020c030a1803080708120703060f0314070e010609180509060612010b0310090b0f09071a04080d09150201020f0702060912010906020306031603020310051003 82
    0xc41d40c0e450703801c582c81c2c002c08005580140615400601e1540c0284255241c01002500035400d11307440b1389060b642160340c80c00c003074924518180000001118440244050b912800055840b001d292000d43c0902e403001d000c4000381414a00c051000103c0c940110044a40110030540c03542100840e007030400c6c00da034200c2000401e54000200d5007603042082e01c4112400052040210021022800101c4800755605180340d000380004c99020702e0180b040300c521084400c000500502e151001078a04151020311040c0340361115104801d01c8100b045c510744c000748d481d83c07104043c5418041d00361501294018001e41d14828100b85c0e200c900010195009040c44408407100c86400701c9014000440390300c03446400d175118070044042c41e8410300a54015501c00c140990402c0e00301d80c200405900120030840d00300020100c1079180207400d014000015000b80301c0107a480c24550245418440c05691018010031082c20810058400203204c41d51803030402c10010350780d15680c140140d42c01081d440646 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 664261133 1250 664259883 664259899
    0x91e030c20030c03150f090f2409060403090b0d02040305190611040f180e1005040204060501170402061602030303010b041d060612060112060f03060e1911060702 71
    0xc0d88103a0214600d8204008408845090341040f04250362800700312500103189a00c8030118145032984925503401024000a80314107010300843c451419106020344c24421002200c400300e11450007804c640c00207003c09c041c02d0b0511b41070314054450502403003004040400000d00100300201681528051a403003002e8644084031074a1046100089030815a982071030500b02c00f03068200c84089404556440780e0b980d030f1103403401580d00c12140c824060520b84540f03901d41c0c0c0100303582c203101e24154a480c52200060b80d0a1034010310003120344680066040c0002c070241c0a14254445600b00d6005604484031039031610302c014540110020844025054880403001103070311b84600c005802a20385251100c00d8600010751030f05800b01050780c801d0f820070400c000a44101411100140c2d1100042c103000719588041c0010340c0c04c03909280c3c8400b01e031044003c02030082103420300814a2a03150040280b18441c0102801660340007078075401802e00b41c500503503403032644940d0161410300b42c008003001 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 664262383 1250 664261133 664261163
    0x40b060f1e0306060f0915060418020c07060f02032b020c0d230f0c2b09090203040809130f020f0d0c020f030a0318050102070c1503091e030c 62
    0x1d46400c661007010300c20702a50000401a050011040030400001080d8184584420714440500e190b45508076030000410400131078803c05481c0ca14813040d42900005980b0030001d29000d0911a050700000301b00305a411404000d158000240c0c2e5144510203203194456625a016809510a18442c3c2c0780c254000b00301c0484110001c2943e0f50700005903121f05842c401e45848425024072110302c10104020180710300007074940c84002401c0e9000b140c1003101d03040115002440e120600703085141800003e00d1865801c025404001d1a0043c441e0f41010743c11420a03984081030b9006049032a40202c80c078003030340120801c541d00600b240c010350407411980c8140ca1501c0402e65449959100704072400d1602c6031031894400034041c00c1150341c41e0051070030030036101c200700c014050311102c1240200000e101c060200350b0a1000b4076099105540c11034440d031420b0014800d14070301164902c2410303d07001041e030228a0b01c01540750b8080c2c88101f9080c000d00a46801d8500c44e40120f0050030880c2c08100c80 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 664263633 1250 664262383 664262419
    0x150c190504030609060915061d06030f01060e07030e0115030f0213020a0c060c1707030513080301240f0e10090b030a09021f120c050403050f03280503040b060f 70
    0xb80301541c0903040740500e80d008031060605584042c0702d40320b1500b00b270020000f1403690b20280b50390400e0f40201a2401c00d00b40ca1042800e49132160809080242c2140038040142d03014810081c040c10140b009018540502da020807000c64588070180c80907043d00e6100c0110b41d94005000031310310394980b00f151120a0b1150042c41c41c8150b0303001704d982c82d00c0d002c0350b016601c1c00b8503a9000d00c003c810240903025074946c007080f80604409094500b1607500e20318690000380501014601270b12840541000304c100340072004410b000d0403103d031014003004804031014664402000c0501d00c1040e81d86103034103000b072101200c0d84cc042d540001d04244001c02401201d82454004070512030088560035038840180c100700c61003411070b50440c004181d4020044010340195007060b448929642803260a107580c0c8e4032402d0a15110900041c8540c000060480d40b05944400da90032281505006504020b800e04000e4030350701c0081c1c006408040078074009141c0740e4501c10000300454010b825900000d0140041c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 664264883 1250 664263633 664263641
    0x10140d020a021204030b070c02060904020403031e090b12071e0c11060a09090509150f010306050702070b122a0903010b09041a07020102270102150c19050403060906 72
    0x301c00018022240c6009407003510030152003c0d01d4004003c045242c440c90019900040d9600003245c000400b8031411800c0c3d65541b0181000310302917220000c2140114a182c091900a20039a6041c40019081404a06020015500070342644005c802c22a1280c00058500a0101006840c0c40031203c0e07100740103603406894014180d1003900c5101100880c1c1d81013001f1400381d24101d2002515041d007c00001c1c049400a5410142290035501c03500b00403040c101c2004001c451020b4800c58050041041100d1031180b2580218a44003400d0b1041c10b00c0410006881001002402c14044401043c25400d007040c4094200a10030300541c3c58008101d100c04142d08000d40f0b05110b94601031a20700c0c18200405200c0c4600c0d4850000c103802c0140030a10960704201030b102808565090040c0710b11008001000c58030551100305c090480545040020301c0c140b4403001500c000500c8805010088440206903005400252054000d2540b034050444042c000d560016000070304012501c1e061011b203600c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 664266133 1250 664264883 664264897
    0xa050106091e0603210c12050a08161409010908150609090a050a02060711131e110a0f0c080403050a06180203101a1e01030c02150109020a0309061b0206070e010e10140d02 75
    0x114ac1096a80300c06145118030708462643e0085003d0308186822080140000c180c0c02c60141440280541c80e1407206160180002086c11480c8416003071090700e240800e021540315a6400051001806603541c1e41d8544018540080c010304001c10150204100600064a41100908191001c070702c208904e00c0034000034045807000d94810014518007403090b00400244550014040d45456154a000c8a42c07116072004003040210300466103000810380300013080118040c1d002070034030000701d0814800f220245004c076510701059121000c01a08c001c07891b07002c0c89112540000b6641508001c01c2002d03001414030300e0740034944204a0040036021140100082d8007a84c08000c03043c41883e0507030360b03001500200b201c854010001040780c000700350000c0c0780c1381105240105609070a560303020242d404420740c040761660041d802d441040e030304011701a4045100d00e040d01040c004040060030075910003401500644002e5051510140990075000d4544058a920b070703903a0005040b40c800a4010507 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 664267383 1250 664266133 664266137
    0x30c090f0906050915150108012d120b061e09180a14010b0a0509041e020607030c05061f06030e1212091501060e120a050106091e0603210c12050a 64
    0x3c5c00301701d0b4690081246256404180c69100459091078444103034003120b071100440d02224848030300303070403a5110440d030010844101107500b5509a0b20781018040d20083c003140c0100c07400000342403039050700300c80c00418403030a90300d407491600c40200507460008864055215407040171100c404008004040c0b21400380c00304004c00c4410100010130841e03984503c201540400c007000400c010800301d2410100000d1280462585254280d010806581002c0d9056010500815001c1c1c2800006d00103076034400701880c20200c2c400c42c1150100c910f03400b640284410555218600d150750702d030400c086182080b400c1c07076050302d9018615002400c103408642c1303103080f07009038800700f1440000e07040918103035581500c4195500b01410180090142071001034141da100d4590341001040b000e100b010041c2200c07650203d0311008450401401035680320b000100185007050400205442040085040c0e4030710a031801c40d2520b00c5000c03162200c40c500c0140c42000390789080c0781000c1e04100100301400c855 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 664268633 1250 664267383 664267423
    0x18060109050403052a0d030c030f09020303190203040302092d0c03040b040305130e062103031f0e0106050405012703020114040b03090303010906050604030c090f09060509 75
    0x16410344029074105540082c042903040c48580f1100c0c0040d10800c40c80c030b142c3c110502000b10350f02c1c015490151038003420000300b03503103440c19841c296050042c003917400d9460009103e014415404030341e492248407030000c905400081821240b0707109004850087d41c009080c002182007840741a200c04412004080d400c03412514881c84200c80303424254452641c6195007420f65480b0707120401e50701002030040342000030401011220782c545108030009440c400740d2640315450442c1c1809200078940516280d41240c250240f680c4038800422a5440701c11001d100b40d4032002c034841100b81d80070503044424001552000807c0450303000f009001101d0090342d91402d4400111110042281e180f802a031030080c1030902440594000d0140808401110003868a0301d60b0f102c242101e6902305940c030b0002e039000040100009030450056802509040718281c0c941450340c1e548650900f0b01c0d104d40c82a898603510064450f0043c2c6d8880740215030002c00a10481c90950150b60312600304a84031124a001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 664269883 1250 664268633 664268639
    0xf120e030909162102123903010b1b0d050c070e0105032d0708061f0617101a09040501080c01050f09030c0a030c030b010b1606020c15180601 62
    0x140d00b0711078161006900c42132065401c505000842c040480310300300003640c0801104400a0081d0700451007207401803440d45480641003480d028988104902c07105060b8000000c00c02c1c0c5c003002003240d044480c1010206d0b5214614084c0300d8001c5a40031003000035028000042c10f04581140c000c5c54080018400c1e0f4500c0d64641030000340f200c20a01600340c00d0790018040700e00742d04c41c016400b4468440781035480800c0d90348504540c83c28600f07401860742c6070000820711000080303070326151060380f0317070341801801440c244280146031f80110303045418442d01020120f10400c0d89500300b07401501c0307902035003221404605001401c50303000c204024011032800000041c44100455142e1403903070165240f80c40c0c1445041d035140341d5080207200c47d82c036014081c0301351143d07038925a84500561042d80b440c0c4e042c5155060099158405078070121104100b0016400381c4c40030680740750822a80701c0c200503110206046824030307105010410000c0c410000d005e000f04090070b800c060308145d0803030080b540310340e0f2 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 664271133 1250 664269883 664269901
    0x103050703050c19090b04090803090d02100203250e150301080606190519080106060f0809030307080c030a021b0c030709090b3c0f13030903030f120e030909 69
    0x380b03402c0750003e91805a5405c1c0320320000d03504405104003000300080380307da60b80c1c4c41d001c2260380140e64108443d130000d808154401d8043c0004003160110510860070741c5031007100c00e140000004139044079034174540301052800b40240c60949060b41c0281c500070501880324040c207401e50013030041800343e00c40c1c440081c00e5468002c6241e032040349001544008180b40030f0500046040e0301a2a1801c0c4c18003910100310b40e0024481c0c0402400f13142d98684c11141000405400c1c07180c0645900c02c40d0700100108202d06802c400440c1d000400240605c0d60717036031385004c158001d000301044050004041e084440c803e10380003400b00e60781c4000314291501c0b150b039501500100e514000c2c0080410f51201f001950412814180c2402c803001c5a80d00c02e150300c1b0021640e05401885402c103204107a05105000c10704002240095004114080c074407019070f282c2d14090246e01c03271880006e080040f681003aa030094802c0402c241e0318460580103105441d0103982d803035101d80001590078003a500203000a0510a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 664272383 1250 664271133 664271149
    0x60504020f030619020a050f0d05010306150e1302151204020102100911090a060b0a0f0e0a06212405040e0118030509031c0c0b060a05100e04140103050703050c 70
    0x70150030800704e254610120280c2c041c1d00f11143d03580c203100e814065038500c1498403004020b04a48807200092a60442c81d21760100c80011103802d00ca07901c140e5081c0080c0300c020003080d130084844000850b44590610002c4d50340b4039100414680c4007000300f5900ca000884800d050b0182d4802d8003950120b01840b040c2d00115410351a0207000210740118141c0d80e4148068003d412061110010854035202c1501c51b845501c1503900b00300180400c005040400e038069079283d5a000100d5079150303482d180c024010410701c04018490340c80d091500c6034a40120180e40041181c0444a4506e02c0007400c50313900e00041155885414016820414488110481885000140314021076802541440d50301d0403180c80c2c0100b40415018402d95007034100d0101c0b01c0d59020703440e16030359840007a69011407030710041c2204003501039170240c0078084050200384d4500c000b48829686526042540525180000d00039104051207141d503410640c0002c000d00c080441c550040c2d07801340c1c084556401950301402008 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 664273633 1250 664272383 664272391
    0x200702030f1b15070b0415270308070e1f020f010905060f0712050f1602070614280305040c1e050111010e0d020c120c090a0504051009060504020f0306 66
    0x10b110858004810361600071641c00d000034084404506004042c1e41c0c401d200c140c01c4e01e06507048088a86800124481800b0b40d40c4c2c2d2004c1c4000c6070000388080c00c40f02244003c0d0b880000c051100701400181460b110b000b080f00f00310030080040d100c0941e07880c0c00781080c561820007400140a0640c8003070003490140200e81010750301c80300404080d96402413075804610040d285404005424041030011066405520300031018448010443c2c100142d80c1c01071a95543d0702c2c5415500603074000c11443d908072150350741d6400c010342426512000480c48943c0d02103040800d007260308000d00302429095040d80483c0c03259105010b0b0700006c1d40c88140c074051303030a048074080b4813051440d01d00340030700d51080d0400125202e4101c00404e0901e100c140340740c1401c08038484500164800c5074a48005d03d0801c540a11040141c0701500d034a01d1500c000c2040d0706002803c05020549980c08941040420480d011889500140411190f016460100c028140950b81688180c0c0d424046103c5031070007195640c01 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 664274883 1250 664273633 664273663
    0x11401080c060a020f03030f010501170f1810020f07020910030b270f0d030609020c0a020d03050702030601060509041a010203071103190614090102070c03080904200702030f 76
    0x700341c0580c04201c259800442100114001c0201401c901102003000d94050b0f00341d804c00f92070359810400010600480020768100e1581c4010500052003a044107d41d000008805401c4401da42046c1e039500c0c1200303080f01c80b601c043c80010080841600c03240503255007482190903a05a84521101c80b514494078003024210025202c046040340601444a9102441e000440800074a040a4840c10000c520700c204289820449801c440da6500d4410100504078501085043c0740c2880b01e020354599009074020b020b1014003018600b8580120140c4102070760003002c640f04e940e101e140c0107225401001801d03005d00d05107602070030821001c55490040e44010b900660901c42c154a40241c458900302000c0c0c1c245c02101c0c40082002009102002c056005a201203940d04410f1000904e90030010204038840c4d105004160028900d400d20b002181d4020446540300d83c181c80009004003060350f2800d4004542c120043c6004803420301915940e0300880a0b00c0d2021802034100f81c13558908400589 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 664276133 1250 664274883 664274893
    0x5130602010221070e15031e070e01050d02130b070501060905150d02040b040e03070c091a12070801020703031a09010b0d0f0603020607030c0c0b2106030c0a030605010801140108 78
    0x1060080750f4515071205480c038220000c601c0c16408207080c00020162598800400400c10510035902592920402845e000320842e900d070003100100007030110b01d40700303041000c000740c86800708080341c046d10711b00f00800000e450581e40c0c5186491095210003412a07580d400d01c100094444503070302c0384900c00e007800c007000e07604259440304021075600401400c030303485135542c4612180c03178a491280104142c090b5000307599415050400101610081e40260304444c2400c40d548207000c03030f80c1c00c1501d03207010039207040f407003d0310f074544250030148550491525580301090070b2061584c16040350240100c1000010b1403203001005102800c00e090145502c8107804105903056080c10781e0040110403603100d0300088083c0c490f80010303191b5014460941c0000c400a50110130b0081c1d0042050041103850081444d1140c0704010a08049100038a0030076070301d0090005460b500d0910400c13200800080c141034800d42c82e460450000c010a02034030905610b443d007050707900110140b09906039141140100 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 664277383 1250 664276133 664276177
    0xd03060b0d050613050109050114040b06180d050109030c06050f0f0117070306060e06030706050a021b1f02100605040209030a06050a2004031e020918030f0406051306020102 76
    0x5000b018064039084091440314840e1041a8450306010f040202d5001c501c651500302000e611030382501b61030344540e20701104006c86545a80807501088542c80409107007405d00c400003001082000f201410030750a05d4400800c040d480302600b644030b4402c000400c01622420103030411480d04558080e02560307414014806c01c0411401402c4c540d695008560090740c80b6a102070545416501141c0301c0d22044090044914007803140c60301400040c0351290401150140c000c0d5a42d0300b411744c045200c480e1a01d048680c0e12601f100c0ea0b012460003091515056034040001d41c1e0f14442151010701a03d0b040e004103441c6418003c844020200900801d00000b140d0fc501009160150010780b107030380e8031722000055900700045030794410381042c01e0341c0d1035914504040c40040c40354100c244044802c0380c01c4100503030324212210b07000229021802d07088044003440b2880d51203500054a5401c0d004200050ba55501c44018540070343c0c4038541948003a038495080c2d0907405000000e00c6101c2400b0404 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 664278633 1250 664277383 664277407
    0x20a1505071d12070e01031218030f0503041508071e022e050c0c010e0a03090905070e13231036050a1d07050d02040212090a02030d03060b 61
    0x140311490b402803000081d820355803401032809115900040c0900300c014010000d01808a1a80c0300c454104d003012002104040b41c0c194900c40e05000040182e0914540034040c0807080003614040c20522884148650400e03d001d00522802c46101001a203101900740300084600c02d844890741541e00100380203840010b101e808030a03c1c00070182d600651070300861a078801401568022406028520365400e49001075a0950304440f00302d40300350b8080d9128900203944415070700f003180c26400000483e0317140d00804480a030729024110b030344210003111034135051440d076000f950b065041c41007101110384045008407810702c08480d07500d00e446800808102428180c1c109440c160b01c5000c0311140380c1c020b08103540744240184948400c1583d50010400080f0513846244e800f200081a2581500039600541da910320540c01000c2c05840488280da04640f190b4042e40e0941720314a042d0010b502c0c2814042d03585010000050b8803903c035020520720b0060003440b03814245c0b01141d40f42440c154000c544 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 664279883 1250 664278633 664278677
    0x30203030a1a0d0309050109080102180d0204020d09061b03050903070210021c090303120b21030d020f0d05010b13090c0e0904050d030c020304080a0f060e060403020a150507 76
    0x4948040c400c010358002c0b0a555521402806611030380700c204016003000c00040c840c8006804c05410f9070710401405400c42d100044e0100e5440c012500203035034201074404203000c0d00610145140c0f5606240c50b050401240360080304d003005103441d00d40d5035000035150850a03280d0589009019420070000c0b40c0c05820301c0d0302d010340704000d01c0c0100c2d8102c01c8142030340035482c00555808400541c0d400d8050007050782c88008010b83e1032079a5814456540c803680050b021100d00300c0c0300c490050b241488011042c0b0280180d8415514120045459590592100071203a10940f4030300784041c40c20f4001b0600313a900d482614001e03489400324040b000d080075a8030b0010105401450180b004180c1040440e50703d035140b00f07101394402c401030401d882880c039001d000c3c0c0b12020380120540d0022700061041540003d04000c415821295040401c100c0342405001401402502045070150b142003205142d000030701c45c3d804910411900c804112070b4201c1000301c800507146500060700e02e1000c0e6000c0044070394 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 664281133 1250 664279883 664279901
    0xc090303080a0504050712080702031c201c1706010f0c1106071e0c061e21061e06051207200714010809120f0307050d0f05180109030203030a 62
    0x441d0729542d191f102c0c9200f40c00b0400c0e8115403500001409408504083c080d031828148241003440100402c00c1d4054014a8a102000c541c81c0c60a44501c40102d800c00c228451020342a000c01005020044014940b40030104003071a8004400041113480d44507a601040c1501e07280d59400b98070000d552980034642c48241c03070980c004000c2c020040803a910b111103051003201102e05260b00e030104e1800b03602d20080d940c401c0c414030104034000c55042540f09401d1100d41010700c0c0140542e1842c091400c80d45504012443c2e81c185000008240d100100d22600d9440d41466040e0003140d9407030034101c41c940301c2d0046042c8400880004595481c1c003803614015071000e00805090000c0c5224180342c03801c0c18990144000c0b6000c0c0c40748244550700450100e40100300340016004500e40c0d00f910340f141d4403c2c0d41940710086800070001d0104d82c4210181d0f209091401814800e4412000c2040b014001c142c0781300b0490408820b400c100c20030b05214841003580e040d0080c42c11607640c03811900040690340703 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 664282383 1250 664281133 664281143
    0x16020a0f06020705101b030b030d0315120c1a0405240d0f02090a0803090901050121020c03120109200a030b06040b040e16082206050a050a0c090303080a0504 69
    0xc070070f90001035800c0c4194540c5c000308440001d460349071145003180048404014405042ca41940c0902e03544022070250030080c0903040100e01e42011184003446854a07a2012114450942500e010880c000d0703000c0003143d400d941485403003454074905000a128601c16581c2c00300c9840c240c5032070440101000790030320103080349450900800072110030948110007084511a540014201e145141542c0a0000741181000640c10000d8072004959882c0041c003a02c0c2c107000000c0300c4e20701c2c00300c07020310840c02c1c3d45075203d029500c407503080e11216903c0d00503008400b40000954008180e00d0500d104440c580d114150801100050860f0b0801da903038424201d9204042c0c0340c1e080c080c165180e21000b04020454801c1c2c82c1d6a942c588081014189070103081ca0302400008506d02c00d05a80c400c0742c0c81d0300598000154031201030441d111903401e840407607000b001a400c0408026428445074003451182510000038044175030040e400726503184460000801240160000c80e120050703130390007158003c2c070403 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 664283633 1250 664282383 664282387
    0x712080c0304020d081c0e01180201090b030a0905151b0f0d0b06090424060903050715022b020c060309070e10170d030f060509071b12120516020a0f0602 67
    0x106c0d1000900c039940c10307582a0380070313210810f21030100d009200c0c40325a00c000001d44031600b03103503500091070001240315408502001001184401001d41e101c1c08000340d10900700c680380d50141a5003103a03400c0c00c40d912032039009481c00440e10402c0d000c049404514030282080d01e410100c24144008100500c3c0355034001c0d4040c80b0a40c01e5850301d10540e8130b40c00c003100c4950558812a10308a0b015105500400200044890100000b13200000c80b5001c1d00d844188840407142d0721030b0124680703100e1031044010715030b0719141c1801c0365110080c12042d00b5060703401d83d1003101d81802800500e100c256a241c0e220b42c08642c0810400c05260042c9030003804034980286944e41d2121951304105844001000030707000041c00403801a09886050b14280b400402800001d19050004d443c03e800102000e00b4030002c00340c060b848994052050101640c85030261041c0368029800a01e4540d9840401c048189840b0114007021070302c1c5131031052254558014580360b101544c5266141500b10003c03108140c003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 664284883 1250 664283633 664283647
    0x30308070c1b060512060a060e010503041704030c03051b010203090f0d120215100503060106030903051204050102041806080d050c030705030307030203060117090c120718020712080c0304020d08 85
    0x141030003140082c0035135582c00d80c90309440e00300210042409402c3e2440b546002c0010800140c0141c21f5500c0000242080c913285e588504200d803e8280e0b80000c201c40300340014000c801c00c0754000d80501980d00a0341183c80b0f20340c4040803848000044581c0d1809640103120125031403404203440580c225003d03101d02d03200010b980c2c8401d00c1c528082198005038010700203960f4036a403841141e80e0710401503070000140910305804039895200c10f00491080680b210f00081c1854060f4080320010350496009410624181c1807081c002e4002d4014205d43e4001e03422080021420350181c05c0036600440b000d40249080c0701c0742030782c4603403100c40030101d58003007481950041842803025500c2900b05890250ba01d07c1e00344001004e070001d61003501003540c50a01485481080000c03045c0c403080e01605d1042072039640d06145e07031a042c0e4a510942da50160780740c1404124005801400c2400c1c4240421744404400d440140e6030301404441080d420b035004e10002e005403400500090304540245503032460106 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 664286133 1250 664284883 664284923
    0x905100b041503060b0a05090a0b1807050d020915120402030106050d11060901030e030304030f12020708090f0609060a03020405120c03060406050a270302120a050d09020f0406030f0516030308070c 86
    0x8a4012049c5a61841412058100941c60342100081d200d00040d0501e00488040c1c96409990108000168003040111203600c440c000e0342a900400000c080c1c0340d000912a0b0401c1c0c60b400c581c00c901139420010001410305043d00304482c03050303021110f002940d19410130b00009401c68041c1c0c0e4105525000a00142e040074801035001d94002c0d6a0383d5a02281401e002d0608040d40e107003030200510400900c0003041c401d1042d12110681107801d42d07041d040e51400188907000d04502154044400200078414941640c02400cca400035180c10f040404441c2e502c0d80c40d005a09141601600b000300090300003506c50740455488100402c1c0028001401540b4440050412039902140040c2415602c141038040054410203400e10080c28038040d00391000400394003403201030301c1c01a0344500320003086594028030128102406002040503d0f600d007468018414030402c243e4040c0248400f000380c1550544580094a405481c0c030812030321803800c2240d9a6681d5801641d648001c3c61100300304403 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 664287383 1250 664286133 664286149
    0x3050c0a0605010e0403170408030114010e0402030709210b1303170c0901121b0c050109050609010618110a0c080c0706020609190c03061e0905100b041503060b0a05 72
    0x11003040b844c042e0301d240514000d05080540426401101d07216000c20000034007070421641507074070038441544030000030170068032420800301c4003940c81400481008211030b440840300c01218140b00d00843d0000d01d540d03a40180314010740b0083d0009080400088404010240103194a03200349404034583c1d2600c02c1d030000ca400c0c203a443c038001c45000182d10301e142da8021903561614003080c6040280c00e00c0c4c020500a010890384004041c0809103144606200003980182d40c169040803d43d0f00620741041580e000f411203000e2910803200c912810041d1190520401000004400740e0f01d00d8070280301000c0d500798500780011294220200080210844240003d00c0104280d400528807410082240c030b040082d910034a65001e05034002c80b4000c18000640c10342200d801c91030020750020030b169029000c80031040891034107401e1449207002c2050008242606d4001140208169555030007040103030b0340d884044400030400148103002094241d8040004a2002422000015543c0d004240c000c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 664288633 1250 664287383 664287389
    0xa1b06020f090a05120a0b06030a0b10030311030a080105010827070302010e040209060702060a2606010909050c09010e0f100c050d05030f04140c0d050609070f08030703050c0a060501 80
    0x40000c1480c02c1107007402c0c401d04021303140071a10492905120443c80c2e50700c00c0c040030003030055070b900c9001c40c0b6a0b440c140083c5d41026049400d24405152800d400b905943c40c42c401240021002c40c00c032075580e0000300c20340759081b03c40e60b1030780d245918000044030701400103040303c036004035880d1403802001240c080710250f00c2001405003000c1e41c91400050007940d4a2191680214010842640300d0b50740c10040b00c403550360480c0c920b6240c1801d6101150784000d160500110081c10064140380001c080300114820002681e0b46130045855500c400107880040c0c4807040108014001321b0f2841d07001d00c1e0840c1404c40c0c09441607549007101400243c21403000000340c004500d452011800380002805503481c01e02d000d0810342d240d814811041501d07210700170b0001c2c1850607140c110001c46c80080c094000000002007007003252403900d0400310b0312007030241d4440c6120302c20002c0000c0c80076035405605c000c440c2c0c0342028604040c5581c84c103a4155014402c82052801491203d0300001c81600c01c00d806 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 664289883 1250 664288633 664288657
    0x6051c1e08181c0b1807080c1e09012402030910050304171803010609020a090b0c0708061618060e041112090309012a0602070302010b031e070f03080a1b0602 69
    0x60f0b0500c14442900c0603170420030326840d500550710a001c0004001250300c40d445042c1c41031a040c01d01f82442c0f0405c01040c1c50070302d40c0007000e80000104101441b90030b00c01441490fa203101644030146081c2d07540d01c01d00740c0c12504110300f0840280118090f50103550b020b07005011041051101070f80311290342d801100c000094000c884146145410240f040c00c1c003900d41c4071800c62078000c4000c2c024050b41e4040c40303003440c140340014600c6540c4109020105c000c003801012101141406a043c04454010900c07030300000314203110796004000c030403038404200e1b201519070034072020b5184148006481c05400d034144800341000000492a20140000e100e042040055910365500100052400310400e144503502c101581d024003500b10440840c100e125880fa80059071800701386000d90240142415140d4180034403407001101030310452200044e01c030582c0035942030540303440c00042c0900540c00060031818040c4150901203004103074050300e4203d6009601425011552020140d90110940540e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 664291133 1250 664289883 664289903
    0x10e090a0515071107030803010b09030a05120a12050f0402040c17040b01151106060607140303040c03060b0a0e060d0201030905030f0d1512031206051c1e08181c 71
    0x15070301800c00c5100d000248045c01e0b00502c0c0d0340342c1e0402d81c0018020324461110004043c43c0c1c5170b40420441c641c280e440411358405e1782d000c0300d21030040e4010b003c144003c9003c0d514088054440b500c0303494400c0c0b20140466519480c1c50302400010f10024520030305000c0c04481440181400f107010328400c620411580781a0f60400265009032101024888144180e090682c0142c40740417071041d03400601074802c1600d13901d090908003603a61041d40614003d002c000140014005046080d0301a00d0142405200000c01001807000000042c0708111803d0742c1c0384041450f074070700082c80d0000e041c014900854103000b50f4456a0955125045055001d1030002d0454a0701e081402406100d021485103001d8143c540000c40f1440d000310311000307042202c280d0500800c186a5440b010141130040d005e00c80c229220980600c5400d8000815101e1103101c8030350f111075500c1e10034064402580500842c2c2400014407603040d0b445403460072503500200754840b44208104130102034034081d000b541181 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 664292383 1250 664291133 664291141
    0x9241103161103150c0a03061a0a0315080a0b040809040c0c030e090103020d02060d060b0a11060604112d071a0f06030d050a02071701050105090a020c06010e090a0515 73
    0x1090b5005641d86840c000d41011007411301007141d04108590118405e600c050391040802c10031001851f203074200c0800001030850114488400c41c010740108040c2e278400300000b01e20303136036802c03840080e9200d0401c2c568014110343c40011181c0717140381d0300a4480e242180c100301a031b4001400303584148030b0b828006000e1101603410301d6808101c903d403054041e075004030294155000304407011034048019015450001d1091403007540da44c0183d008180001c881900e406401c080100f11000822212081d44940c134045135180c5050302c1000244005813840f07901d490899640605105901c00e0741c05000300806a42d030001000f030340001d05145200d417281001031180c421810360364400c06015043d41c10350301c1d000c00c007054070001000100103903a41002c584540990804078038040058004420815503c9002c03685100c054000d141640c202f12050b06c0303255600d145000890083c001e1000300c96014500400c212207028412a0304121003605031080c607010350302c646103048248000c0700301c1c45884102700 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 664293633 1250 664292383 664292393
    0x1404020d06080d1205040201020309040b120109080a02010c080603100902010c0609110a090c12020903071d09012702040207030e19080c0f030322050d08040608070924110316 76
    0x542074900c01308000c20082c1000c0d00000e58030700803c01264011a80c4083e0b00081e0380d2202e00070b005904403a8003c0c410b454091410743c0851700549600000f40d8240259156882c8c010800c00380301d414081c00900c2201d9040f00460042d001410050b410310440001d000041401802010003a0b8060f140e180301c255102d505105403410a45d1142d596141381c010103414003540032400d0041310481e200c01584450105000900f455025031016000c1c100b460075100704843d0901c000c5100e44a03000080046649039030f0015070240c0304c100390310500513070b00e01401c2c018070f095409000c48602900d05540c1c2690f42c5008101242010ba142c0c0600f0703200f06c0400c0140c8401080524120103056030005030751481000407a5680c01512444401070300c04244416110804011a000401d03008021545184541c03c0400c8a60301ca40030702c5000030304100000b08414042e841840850740143d40403515a050203c50f99030b4007501d01c803500704003c824400303009822403c00c040c00062201040e60801c4c0003c620b00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 664294883 1250 664293633 664293647
    0x8060103150605010512090705100e1003050f0f0a110a0513060e01120b0f030d110f0d12050a2a030501170604140309061602190b03011404020d06080d 66
    0x207210315061820610059922600b45e5100000071564805541c0728010b189050107482c0e0065500321030145030031203425038402200d0754920f00590702e01111aa0408080303041d10310031075600d0050040d00e0007203000d0800681d811640309480550006180341c54030b03580004c035407203104020001840416100c15000000a0f5100104010300381041d140030380d8000030707121002000100813a142e46030b054007030390341342d0307101d00040c40038001d041d18031825200e1000340803095120b1200c100c600c00e201800a014a00081c0300064400e15151054061003420401d030142c01e00806d159030301030310fa158240203504605607204108105201752100b0005108009048440c1640003010b0001e12b05003195080c90041020781c0c1040d00482d04a07003003210050803034903520070120b0694024000003049012000d50440790000248211441015240c400180c0c07440c0d10603034060340084110800040000700f041003190b0580d00da000c0d10260074068001d04450885070f8035480048240c0286e03074006100d03130748842 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 664296133 1250 664294883 664294913
    0x913021207081b0402130e01030b01080109150203040519080a14030c161a0a0207120f0905040e0c0405040501062105060f06040615020a030f090e040b0a02070c08060103 74
    0xc01040010301d000780081c2e58002e00f03a5646001040c1d1030790f0f003503d41c0b20b540444050492800d0440e44140d603601942c85c00481c244001d840401411001181001041c090880001d800040c448090005625044000c0d40007030b00440300c07840b5032107a00d9461035800e0714250805004104580d01e8481071540900714442d181c041141e003031030810400101070a4001650170903000312825004100451401c42d440c401c0000150348500310708401c1000c6406650010180c2500c241d014801034101e4040640c1c520485600c0303140402e0b540c0000307109500b003a6001c80b0000c0000740498001c0841040450200d610580342902e00d41d46401c8140070075941030380c1c080311080844901159115151720b803a85c0fa1400500068555840c2c82d006c50300d0b581d5560002c00203041d0028458aa6001c034123800703540c42d01462012004119107907940807038a0300400c2e11100311055401d48031056075a642d148450030000405a0000320780c01e00403030011803c2e0690946c0680148001019294154101580c12100c422 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 664297383 1250 664296133 664296169
    0x31003021206220506131727010e1807030b10020618070e070e060403150c020c0402092202071b0303141305090a0902040f0623030c010f0e091302 64
    0x5420f44000420014185a01000c541c28400d41c9219901e0b2500d5505820340f6500c10081001c541c0420105040074141c1c1c040c1100d17142d510307100c010400195021140521150b82c0031081580e80094882d44000050f071181c101c0ca8001580404140040c100c189910114001a8800006c0114242e0075070003104001c40440c0080a00520f07000081900302001803203401045000341e8100c48030b46501060700c000c0d60f0b11003008182c0708940380102c0024510398020500600c0744a000c07210f06d04003442101c920642c05000e6800c0382c0c1c08102220080c698201150b00c50503030800000d0003142c1d20001030140424582c0249590525500700100048080e0442c8051035604105c1000b03c4601d408052041781c0c001e60700c2c4003681d610008401d000701079031240a9001410070302c4411016610350300c0780064680405208080407041c1000704a8a20060000e82e003580c400d0040181941c000c02d11403155500714070300301c0200c1546001160020405942c0d4082124118103000110b2505c103c0402d4442041 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 664298633 1250 664297383 664297441
    0x109060305030f0a11390319170403111503100e040302191115070b040605130503181e030616051b030a020106050321031003021206 58
    0x150325416200c1c41045405030080c0c0001820511031800340013000311301c2c2035840c00e90311811070b0340031b00900c003200a6048a50040000842002e088204440007142c103a0141c020450701301480c200c50140c0700000f400f501c15181c02210402c440706000c0003070002d540308242c4420000c1001060103514103510460ba65002410f00030000c481202d04041e10851305010030f40100c40e2906d04099003400301c051040e062404c11a060941170021040e40d5800b00c0c842500e45a003881100d01c8608110300403040000d040c548000301060100d10640c1000d070304408203090480c081103032a039500d0b03e103906c0005141182c201c01680d401d403a2400d90304101e900c160380c02055200400050020f61120350040079641900a4804a807034810301c980b080c3c82042c40b400d0044a80c50107001a00359407608022080f400660a1450100381800d02103140146000d440d0100c000c8185650304160441c0c1004002d80590161140000056a075050b0a9002181140080c0007141000d10b40a400307002d240258000300d4a42c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 664299883 1250 664298633 664298639
    0x201110615061c02121b07050703141c12140103150f0b0402120412050a020303130f0605240a06020714060d0606020d030c030c080c0d0905060a020909010906 69
    0x40111a188100045420581d039140f016920815041c900320f05209451011074020203081205004901034201c22001848030b048400c51442c00c1e1040b00402130464103ea4000c10006503600348611802c508001a074003014445009010540f840d8074000c3e0002d051f003a10140c1e40340c1603104004560b01e194030a10821340c115124000ca5542311255003644503501d0704010004940b81d4048045140d00400540d960800c00008150f40c80090741c065640002402e0030015240c001c2c0221042034500d03401460559590142ca5581e540e034070342c801c0c0c2e4014400c010a00006e0040c1c403601e8851412892901c01c46460b0100c0084200480320105002e1035000600b440304940004900089900710500a0002c1e08048041501c3d80a00401d603101c40e4240900842e04039000b1601e04041310f06035a04014010940300c044013034900c4a500e410100e1448804240401e900e40c0041100c0c4500c200c02290341607860384c0b02444d2400840d100c0c196281d02142504040c0340c283d011340e005112112091102c00c0c1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 664301133 1250 664299883 664299901
    0xf0218150103061a0a120f0207140a02101803050105100e06010309030813020a05040e03070b1f060806030307050f0c0109050a210c030b010e0f01080f070611010f0609060302011106 79
    0x5001c03c03811130002c2c0081200c6803404d02c41c1c02182c043c01443d07a400c0c45407000000300341d0042e402c04a0110346120100c2d4171461030140000d481110b846c4c00800084544078114403c3c2d9000c80345c0782c50380340030b29998040400800e20074001c1a0164a1031405208854901440c8881c2c40c0b0019180a0405040c0300051000c00d910110464000031002c0d40419142103502c00a21194182d1344000e40050500051382100000440984042401248911080d90703800b00240480782861010403c1c02c1c40042c0c085c050b40e0320800407036510501c0601201e1602c116621a1460020800c480107071683c40300f41510500c1d43c2c081d40c0c1c4001040c041d90800c4205041801203000c0703e00c805841043c1c1c10b0000c440006221000c2c56200056810074060340b1656110300003411104001c44000700200c080300000aa030020004905981c40e040e98082c10040d420b100c008c98006c0043c40c441d004a44d2107062001e00304142c1d00c0744070010051204006845880d40c0300250000c01d000400c16019007190041220b012 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 664302383 1250 664301133 664301159
    0x20a0314030c07140c09060916050a1704200d0302030d050405160602160e0105060a0e1311070501050f060307090f091e0501110306030d0c0f021815010306 68
    0x40800d1005070380301d5031001180d0410b0701403504040e100c0e8008000b030414200000c521400005002d54402800d40d5815060060756030007030307030401d4808104507440007009100300c4c06455500842d00e00354840ca600100c061721001d0f001d840c140c0d08a0700c4055030718180c5000b40344000c100207003590b03410003480701d81d01c01030b440e40542d0302955500ca407518009401c020007841440e0040007142d031403010300c680750b000c002d40c0ea010707400043c40040c5000c10302158098035146c52a0483e10300078004c9103403400414040784c8a0568007041d98022100304209801d0304014084d84c20386800340140180c89041a042290940300c000d405151602d0411081c40042d0310041000c0c8192074803003101040c40180600d9080c018021003801170501c00b400303440c084605c1e80401d084440c4600a000a101d95403107040003001d80e00c02918059410f5202e843d5044c8081c1c0180701e00281180614502d5140d11001d03004150340c22a0751321020881150b110400a14400048008070b007054207203000c1203002c0c1028030b119001 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 664303633 1250 664302383 664302407
    0x8071505060301270c030803011d091c0324080109031b170c030d02121f05010504050f060405030d030903022a09191a040b0105030c0403020d0c0317030a0b01020a03 72
    0x1c13450940d0b25005e002c11034403002c00843d4802c5400c0c0d5691383d0b8002481d00c10048817011840992508003003402c10400040c140081200eaa0381240d0301010031000754005c0c04449208100c03500141040031134101c0704d46e103100043c0202c4002190740002031030b00800c450062070074010342c81583ca46030404540840681c28181444801003580c0d44108010300c0e20b580505040e02e07404c00c1c00022460150a401503290b8005c06044c019401c07210010740894414240500645000440a000c20015490004003600c41d020014140c140b4050710b800c046414020000012400300e42c4524a01b003c00d941000008000c2e03e001c00c110b904a6282c1650641006031100580c1c401c4500c0e10100f420404d4031100e020807804070719010800542c0742c0d204200840000380f2464811391409400716440e5008404891242011400b440c0c40c01e07041d03034204040713500d02603005d0381c01c01e4210201000199880030314049100342c0154480d141c0c5841d4148034151040c500e102411500300c903455100080d0420410604 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 664304883 1250 664303633 664303691
    0x503011a0a051201030c14010206041104050c0405060f090f09070903230f0d0810050102060406091a040c08190803060108070201112206030501081b01090308071505060301 75
    0x80c41c401c0312070445050003079203420304064020400000800014114a03c2110030038402404ca1811402c01a03880310000c031401741c19000f8161058180d4a0f190780400da00c2070700d1800e1142425240c0c0e0128055130468100303500d445000042d1310060345040ca106440100301182da810b0503207400700c4010a082c00350702c07004000c00500007121a03446170304460960002c039688201c8001e0455110065665260000c01401041e000e001041020200920703d01c291101a00100425180c682d0f54030001e0a801500752400105041300a800c840021541030042d80111100c2c590242051002820310046010001c61069041030384000103c5040580e40d00103000d01b80303401030741c1d213110381a8050504a105480911000108100c110f4400412820142d0015070b1010030742c0d8842400781c04407102801055500d83c0425444500284291080e444ea03140601d882c454813a985d548900807a0030603142140c20042001e959012080284961584000c040b0001d1000c8220038418040701c54680500c042 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 664306133 1250 664304883 664304887
    0x219080402060d0f050612070602070e0c040b0c160e040209040609050f010c2a02030304030f0305120a1e090b0c0a02070315020304031103070209010e1f0303120c0503011a 75
    0xc1503548400c140c4901c1201414188904a01c9106440050104a0f2442e114421000b1901001e1000152101c29100150020304100b070070a05840c4101c40d00400070b49440004010101e1f00d00c0c1058080c0c040085070030b00800b414010b459a28903041002d030020400e10010004200150b130f10105141d4010b5000207000801c50b200d41460b6041460700302000c1c826600b00482d4500c019440000607604094141186034803000c14008600803828912000c4d5140d403040c8818004940130a031031200051007805c01c5031420490f4480e03206110401c84215210660300d64020b148188454040d040003c00c000d030400210714107682d030140c6580040e2021080c8800410300e0341000d80200300d000040c5030441d14034030f29012041b094001a600c222401c034000f591403413035201ca42000005450065900a280620716030800103039045180b00100310329207400002c4100050f203500125030038055806a60385140c03c2e210b003140b5070141c0e40c001440d4010002c0800042010302945485035202da030003c41225 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 664307383 1250 664306133 664306141
    0x3309150b160b07120b040207020307050402091f0f140c0703140106050306042105030f04080d09021002010f0501052b02030a1e0c09020f0702041113030602040513021908 74
    0x21070503624010041010640805010300036030000e080302d161072070210f03050040f41d0400080c00142d00074680001c0d00b582c000b4005018520b0943c010780000d8002a04210078141c145201a440c13440321070000000c12000d403031301440b00703a00100008405441100703640c5010050003c85503074543c103200c0604061090107010051842c20340080b0b0050100600f1a8442c1c20542404508140c102c2c198809042098010ba11400e000b0425280714001e4518282115595901d038460f00c0d9201d030910b8640035907200d040c44010390701c05008802003445940002a01c91010031a0006c07258180c03c42881012401c0b14113030a002c24442d02803448802c1d84007400c040c034440c4080303031808410380c0740105030112a40d15002851185240722031049e001c1c400860a85684101c2c80080b0b10803034002d118460b900300040c0001d03040a8005682e081c0ba154a030f41d181140840c4a8450b450154002f140d10b02e80008007003220340f401d20450150b408800b5021450403090411202115410380d090ba018422600002 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 664308633 1250 664307383 664307407
    0x1008012102060d111b0d20010f1e2714330106050f030606070f0510020403061a090f220f0203250b0903013309150b 51
    0x40c42c0000407000741070241c4c1c88a5003482070344d81c000018410040110035081d2800b000300280c1c403000014251640d0ba20084c0b14100c0c2d56894071081d10b82e401a648626003101881e00c10f1040d4044a100701d05070350400301e04d40e0101815aa20490f909032020901d80790341e542020001d04410041d030340a011038007081f0782c6e09052420145039200c4c0c0c0c0c0044034001007141c201007184094203000011a04114426a207403041942c2c28003c00e03107030030344055061002030540c0c1892402002214080d10010000102958440341741c4141e48030400a200e801284c2001041580c2c0118204201132041016602d94078130301103540100300802401240004901091000d080d81010306038240402e290703040d08560758103103501083d40b03c100807400f80c03049071000602041d480b9a80604099606000780455203045020307420f0750031803075295905540c5d44160564101c02101c291554034141c201c8501c0d245501035180640034a01c5e8001d083c054208240d0f42c15850385a04203d059039101100719803210038420302 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 664309883 1250 664308633 664308637
    0x19080f102d1502060103140105010b0d0f0b1009090c020307050c0108070903140a0b150a0512030d02071104110a05091507150e16032004110307030506100801210206 72
    0x4044560000d4403810031a5541c0852440e050701e0107a004007d01c00c115500803800c03203000344519500d002e0103120b0070711109240e400100410404000c046150007002c80000c010065000310000400da40e4041004a080d083c040c203482980c175800035505005843d102d503038846400450302c904000c0d413000090395035405880100061600040c04d068460a00c051640e600c1010320015154866050005142e04400f0758485100b800301800c1a01c10514000a0005210303004094400900040c031091252034554070181c02018000c00d80c41610020030414802222030728542007114680801aa0409541040c2280e61314071060740c1201011046112601180c0079504c00101301e800c0901c2000c0c010170b9240c104a48590b00070054482c4005548032141c00c04101b8800207183d015040c0e20706400c00e00900a06001000c060b0003c00c43c8001c11030810415071086508030b01180d500e009002d6076042210b41c1c41d04200a900b00350300954103010322002a62030041a1165003480c41c40110115156501 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 664311133 1250 664309883 664309889
    0x40b060702091b0c010c0e100507061a0d0c0527040b10121202010b0f0d030e06041a03010812040e06040519023103030e1002010219080f102d 62
    0x107402e44032184da61650340a08100d404150005054070540c01140c6040071b20720858649546030145010026510b0b0405010b03200032100b0210740d142080c2c00780b0703103898403903811440c49607050410780b40c1420208840300c1101c9810b000b6480e0b81000d18141160305030101a08a40c202940324110343c1d03506034020b2210690b400c0303412074101410840041049501c60105000c00356002803080480c160306002c50183c0040c0e00b65032003501e0b64503000110f03019420094600001400c40c42c541034440704011030303400c052080c45254040000041040340781c03e002032000728000303442d80d81c9090310308502080080d102620403481240c0d1803000c104404800744c0f00301c1d0088e0649400303640301c03200810141c111420904078640143c05048114410420034034030070068940c1600d60b00ca22444c0f0006000d180c0c800e000941040d0340d801c00410b1540a08080681c4480c4050f42da808441e240401d042c8500d190b000d0159090000220010f118030708016061184281c2c500310300400500c030881e1030340150021a8 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 664312383 1250 664311133 664311181
    0x4060801060c2f04050703050603032a0d0c17040302060405010f0225080d0c05060403030b01120207111516110a03020a180506030604050a120903060507030614040b06070209 76
    0x9155008440f520000718907845030101e0381040179079074a500580c05e5a804491085e4541c20410080303401888a80d004d44081040709814551030030149451854000020300101c0404d8860803203a041012000340c01444501c02d0300d203181041d196502040440c0600d0203a20305104003110000e1015100300708215100c41c1a5010070003000450403610303080e08042c0a054558001c900c1a90481d60240d50b6003103602c2e030320030010b250b280d41300c0d2003c600801a03400e10070304000010704651010446030000e4104c080c080c000707001000701c10104001c10b044000c8099141c141e0140704602d034402c040f0510840c0650082c01c2c580e26401c1c6200050110040c07a0802580100740d004003060040102c9281d50040d00254030070841c13520f0b04000c043e610319048400501503403090503c80006042d0358003d120348a05400e04882c542d441c4c0e500c0c90141c40b800c50b00400044e0341d50608002c1549030040c5c100d034900307060f5400c01000b98010007141d030324419030b08003a0054421360042000f182c800b94006807002045 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 664313633 1250 664312383 664312433
    0x110d0e0a11100e061603030c0c030c11120f06010801140c071401020912060121051f020d0614030601091b0302070c080f06150414060f0a03060c020f0f010204060801060c 74
    0x818171003607900886080950000345022a0640924010101c0c0e8180e250107440e2014034503655034a40204409407401141c03c10400894689a820104075007a00c107402d00b000b6240c60b6051400040c04c68089414208801d01c0342400c0c4001c18810f5811201c0254115017000080000040c40ca8007a10030482d00c0c03500900b103000180998400880c015050321158601404440c901c2c40d01400b821254410151081c0c01103016200f1804140141300b2a50901840c05401c1c21500301d181004c0300c20039840101040d00d03046020201d1b140602c40c2901404c2460820440072400000d0a9400c200211048092540c009506014800824080001082600300f1101d441c1300e5041c41070b840d000251403046810003040e0040f002c40c039081c09682d400301c00c90358885580c1c1e6a0101001010040c11280c56004000c2450120109440e8001c1141442158004000e40304000c8622803410034000343c1e80480383d1051100348001680441040c1c11103606180c40c0b030481c45103081c40341c00140450040c039030303200030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 664314883 1250 664313633 664313647
    0xe0d02010c02070801060b22051906030b100f0311040f0303020708100b01120b04021c02031503010905072d091b0c0308071d04110d0e0a11100e06 64
    0x4150070191141419034281c514950f03032800700302d003a20520700500c201c3e07102c18400c0c0d568864408107400145501804207005103603541c0d021030f00500c1c004a41520700a034800c41070201d03a80502545820700c20946540d030100850103001030120009070410b900301034403040c0390404540e45000303a070007034a555034206109503070b00c0c50069a1144c00b071140d0b1310300c1c0c010f411000350000003038851070751b0303000c0180c6844951401107520b00e03000b0441444002d0b80a6804c1c41496612010101d01c01101d01030a240165a03051402032185000e8040e00c0d41c910907070500003070b1130000e803010903070004031001c8102c1c0b6809144003c0041191580090170740000000b0300e80001504038061700a20102e601098501a2921010320f08071510400104094007086240004c502c07803030300c584c4004900c05416401d140080c0d00b4080042d040c2c0700044054105420045921800e450300e40c444c0c0c10060031a80d0090a4119096032403819820307006c806035208207550214064424003965076141d001038020402130391014 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 664316133 1250 664314883 664314887
    0x2040513020306150909150f070915030b092a031506030a09171821070605070c05040b03100c0207090525020601060e040207050c0a061d09040201080f0a0e0d 69
    0x488401840703440185e010613408140070801c554161500380c20b01c0b6195558906000403200098142c3d4200624440300041703003000010300d18040c8099950108041d1440341c20002c003d50f010b0945030040381000040d0b5a04000c0b44211031a80351702000250b2241e075149207208025204106454200c1e90000400c00b9416250340940c60f150b1160b000c94415091b0540c1404060050103030001e113031039412038904541d15101c040040110342035445082c1c2100c08503000f42c185855588000d02003000450308004100410814002070710050fa001c01502100d000060ba0313580d0301c0410945855526540b03a503a1a04c00d004440250003e40010310143c10140c103e445056050307040c119034600815910203e5a01c0407483e00c0c100c54066803800c074442c0071201000003d50043c84112118442c0000780100c5891700c1821400070040c81d1220f50f5050800c4402000c03080c1402c206a00c42c03040c4101700310040c3c3e001614a508207030700c240c102c2995a1414103070801807200c1e5480314040c2c40340c218100c41180d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 664317383 1250 664316133 664316161
    0xa020708120f0109020715240807090e0d08060d0326090d03140c21090f1011030a0b12060406021804060b090409081b07090606170402040513020306 65
    0x640381196080103a0303131045203004a00403c20000d1004015038080500c0400c503030401205c881c0b0302c803844091503542158084500000303510640716504090004c014a003180e00c1404488444140506480040d40c58014001c0c1340050207117200301260707225030003898403880318014030403124172141d403000d203001ca01040d1071002281d698a9510500d01c0e090251b5120380240c9507034805a042010f09a21144200c26880c0c10004072040350041950381203180541c03484050b80126680b201906032407452800d0700341800b003090314440d643d90819403884000740c0004100c0380e010740d15400005a08401a002543d1228aa040c12500d84510783c00c1c4000e0040c5940280328a80e14007402440c0d10140300309203c162451403040d9030000d0020300c90040030f82050b400a140c03a0740b041c04428a00140034071044a40076000c3e221003980d81c040d510501c008100c5214200160109040032407070340d0780d111140b140003c8000c2000380901c0e2a40c3c0411524040d5110701410542d00406842541c07800308407001d121 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 664318633 1250 664317383 664317391
    0x91103040b010b1603030e12120402010912083412120608060408090a1e030b1b0703030c020c040612060518030f180d0b0901050f07020a03080a02070812 67
    0x641c0c4050000140c1c11000d004603003c180840c504628280565242034006100754010315900c2e0050040f03e10464803030000174010507010b00054a500d051074000104030303844a4011019804906680d440411107840c2503c0650007607254440281800c180756000c200140c450b00c2519070801c01d1200d0402100040c0500341007910f603144542014595a09002da503454411a095070b000000032602081c0007400070120910301800700e007038240e5145109042c4410b0034585051650b2840428010000f00d8201250020b108407014184500040004403551251110040c103040da10700b004503c03240240000c880004008204101455584100c0d455003c044030003102d4451401c000100c0c0000441450391502d081c0c00015810030100c42440c5546901c503217a80300902f00807d2001d08965240c1d0302c40d07040036200315a0b01e42d032401d082d00c8403402d446c1c0c00b80141005a1103802040f900641c00243c080c40140c061800c000039840300200c2c02c00905c20b030400500101070000d04201d541002c0e450440c01 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 664319883 1250 664318633 664318643
    0x408071505090c100e15040509180114071d011812051510030209130605040f0618030806010513090204060512010b0906030a02030408162a0806041b09110304 69
    0x1501c00f0002008008004240071401049906010f680c031803c120102c00c5450111112080c5000e88030000035284400440756040d22104001e00c80130751007002c2c0510b0481e174188010301c046509058201528151003841d50715403d610350120031445a110b84d140c1c0b6a00800c0c194000d440503103402c04129898210041510f00f1711500c540c0c2c8100020b45200700d0702c01d01c0320b2080d6045881c03c1d60308104940c1c0300500744071051001c06000401054161040d180510b01c03d8a0859003c100c0345800b00540707200903403010b8000007050b01607021a8000b00080c1d48281e003440c04c20f030340da04038690302c20085c4c1058200d540710510100b030200d100c540020040241c80182641c1d101143e980316210201c910500400c55003091081c80801d98408a640155400501c6604a0303820f011223042d20102018115038103403002041f19120400c100085400700042c10350300200ca2054500306070240b90788040280c0014481d1600c00742d0346125000d4030b0200e2010700b0615405200042340d800d400140c0790010784050ba1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 664321133 1250 664319883 664319893
    0xd0c05030705030714220f0f050105030313030206220806071701080c010c1a040c0512010b1c05150a090b01050a031a0a020f0412050d08040812040807150509 69
    0x400b40f90002e00601110281d9184001040d051003e00c0382e0380e2891551850030104046900a0180d070602480c1400520f4060028145248031644010b0700c00691042e4000d400802080030900d840c2d40040041d6501a2a400c3d0394440c0c07001c8120b05030762a581c0c070f03148030b42c110900030030202004280306000d1100c5555080c080e07038481440e441090000c2c0b0821807150701c507400d6180070754000c80b0540400c1d0f015550ba003450490015440c0000081114100c643d80c400e0007040c001c0b807800d5100380d030b04209941c000300410b0902078041424120b402d004200d006445c041d010b000c0000400200c0200e40c4c81d50b420301000d081c4141e01801070140e44c01d08a91882504001007070311300700403103008100c036005040420300f4450f03000280d10041000d406004841d07000c10413006803842c000010002051040340b80d4a1035609402c0150070072507100b842804000980088c0030100380180140c0c0c079418440f003400002c80d222407400689a10440c00d00410500140054a203004019488a030ac00ca0352441929 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 664322383 1250 664321133 664321139
    0xd0210090929010306121b2d090b031b04090204020a0810081603030c03141801020f061003080a0e10030f180312020a090503070902031b0304020d02010305150d0c050307 74
    0xd429502c0710b02900b86d030000e207913401c00301060710300003072860110711092036141503070722207103c451600034141800007030408030400f40303205014040d9214000c0440d26000c101c80e140c1d010000380c0314100c0040ac0421003551504450050741c82d40e0240200c84c0c1c0c000c0c4119030b03d01022201403c0000110b504007200c00401c400014070100c0420640302c5a200301a40c3d07000d0300c0c255941a00da15483c03003410740401620310100958803500d04001e000012640e122180c60a07503040009280c10300180348203440760803080a20030300d0b01c488022130041c1c944c000700d11074072100485002c031410240d613409e19500142c5041980c07480d0f0340592006000b074205000c2400101140301c1010369031100510000d0001301d0f601c29640000e003140e4050410034080d4a07082d49e040390398200003031403c1c0550700f1001c0c50541c00410301940301452401355007528003c82c01c9505600d090340016500602c2000e0283c10b241d29140010840154a14100810348004003a101d06440c0c03030a112040c0c2e031103809a01c3c02442545404 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 664323633 1250 664322383 664322387
    0x270501060e010e0103080a050a0302120c0d06140a05040b0102030c030304150509030c060f070c02030616020c010207030c0b0706060b0d0c2304091a06270105090d021009092901 77
    0x15038183c81c0c100181070b2070701201f102c08407413980c0103860324020150309002c4030424041c140d0b2000c6c002c180c0d0b0b003002502c0e004070b581d03c1c0d02141d401d07502000c4c1d074011004203000c071522243d000d001214000c407070001e404825a00140d003140f0038214603407e03a010000070030040042c022042541a246103600300056503540a009035280b19243d0000c41075031214000a00d071030a55507000354010601e14280300340180c140c4c040ba103401c105503035000d071001800f800e030340c1c605a0412501420010034401008041c1c603589401040c0d442038011044a124000740e40410b0081a4021800a0954580580c0d80315100c115180040401141000000710b4007940b030a00310702010307900100c12282d16041444c0c1403900782244010010001407107c51b4000c6045d0342c0381075a1344005840c94800201500c11007099500086103d403100308030faa414014140001006034581485034040c0c40d905480b041c1c0c8190b1898029500d500f000d0340001002401c2c6240c00142160305002c841521800000c01c111401e034803401 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 664324883 1250 664323633 664323659
    0xc0e06030403120b0310060620192d06090c0b0301050a0509040227010f050a0308030406051f080106080c0901030b04020d1a01060f1107030b0a270501060e01 69
    0x80500054a1114401403c41c0640e0001c1d540210007011950f40c0d020b62214401602c056030b11001c0403903159184400001200700d00b0b0180e040d03603c409460303500040740d80da100c400c641c048064450405c1107619400303030510840002120201c403040040422041c5090700c041d0141240440b1004820040000c00303c148a040d02c2c16030b200180390006070f0742000d0910008200040c016070340500582508419820440094411505070200c081c3d81907040c100d6403003e045079a80004d0044158540c10400b2441c0131080d02c0c0c0280c2d00c0341003c01e160701c03003680c0d03035000b4140c1104c4420410b030200700015000c00154004404c95070840b098806210b80a010000503400c00d1001070598624500014018940b10010142d080c0c03164407004900700390181e1a985112007600500301241813030105402d41c54100007521001031260004040b00f60540d40e502c107580d140034194240494075082200307401e10244018407d01c030412003043d5000c0070070307040c040c1c0a03184c5031061140c807640c13440020400c50b040001e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 664326133 1250 664324883 664324891
    0x8030603011506022e0609020910050a050d0e0a02092a07020a1403030d020304050307170304050714060c0a0c0611030a0c1104020919050108150f090603150a0c0e0603 73
    0x90282d07845507400c3c11040585c10311307410f418403980401000414242d0b20842000e0b12003200e0050321042000144440c6010001000060040601c00504a542d10904039107422890030004079000300520080c510388408210000d41c010344030310401007807100082040301340090701154201401e0004852617014841c085020390403120415080c411600740d001c840280c540c2c00b0301140d14101c07000c401101241c206a40803695608009844014051b4400000502980030388070035117542003e83c4d0b1990360304054496442c1c0e1040c03030a400f203501e50347e030020f441049130f5040942e808018107140040c0220724900441000c124010114060400d0020030b45401c40746580311300300f82040c0d40d00c0d2202182801010745034010b4023041011a65140c101001505482d030703d00190415003441c001502031840200984607114020748034141c1030f070340c10100f0582020140d550003d55103e00010904280300c0c40c400c0740301c040042040c8009280558082d0416040c0307030ba24041c6200600040080300d00c8150703 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 664327383 1250 664326133 664326137
    0x120c19030f060c050f040312080a140a0906110c0312010e06100e0a09020c010b040c11030714010b0301021902100c05030c2d1e03010602070e04060f0908030603011506 73
    0x1440c41c000352440d840052900114140141814030f0300d0111180c03540700b03802c205c0b107004d006902080041d4100060030b0704a0403513102131004800202c02c0c60440e03d4000c1110055980b160008e0040c40110340c03200d006200102c0c03225a50782d26a03941e440e500da110388504005000408000250305c040d45000b6030103264005d00e104503031807200030211000100f90840f07940c410907201000450301280e100501010103803800124058180a003000200e51130005848180300d584101442140400700c1124050380d880560301400a401030503040c01820403080300c5070950301c001020101110740102c084c80304060340d8200d8011208142c1083c05030707500c0c080901d020800c10710114090700344000c0681585e55004526006888142d0003004c042038502e0341400e6056030018420000100070500b1029403034125004c0e504c1d45d45842c100075580e540520411101c800c071752021a0070000142c00100400f10130040a200384800c030705010605031f0007a0751062096107001e441001c0c24007a0502c5408807111a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 664328633 1250 664327383 664327403
    0xa0e060318152707080303070906030f05090d030f0f020408010b1203090f0904110d0809010e1e041113081014040f080a051c0f1d070b1305120c1903 65
    0x11400c43d0310440141904150b90007a01d5001c10245010400b95100300585d50f25082071078a041e90107400c4403c160f9420348ca41d400c00b41001300c030301000600009407807601e250004649048010741c4005003181d6039040103040c00010006940c5005411002807444d04a0b81c4403090241d000d9420b58a20600403066002440b0140c00546460304d1248594000d0284596032950513561000904562a00808880360217000c5007508072960b120048881b010800d440443c091441250034031656084061554800c944602d102f10460030b0001c10b81c3e804078080300702d1800154030740c258103440f001140a0704800310324149040b01031816008031140078603084144541d0b081c1403a00c0e504400d62141100341e040c003508102d40301d440d000c4c40c0018000401c138410001840340c5116200710680b4071038600d4004400d00200422960030021139501c0885aa188400e5500c034510304044d02c040e04198400395021100c080b210017402c001154100b0313400f000b02d50407500c80d200c04402c0306264503036010151106500f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 664329883 1250 664328633 664328671
    0x40b09010318380f01030b0c0a020318042301030209060f0f2809060e0a0509060106031523010306170d080c0705060c0a0909050f0403050a0e06031815 66
    0xc865014031050107510b440060350b405800500f000c0e103009680c81840051000010018403c00424560300080100038040c0303081c00b015030080d40c031700421a07109400a003d40c00c43ca903c1e580d40d0701c0001d9483d0300042c407200600860445c551010300c02d10040c2e005961407000501c141c80c11085c0c46c100100024181d6688010220a1000b4a5492000d408200300480381d01d42d04980d00840c420020944041d01286841c2000301c1c00c641481c1c09024468618100002c0c0080440c011171100d040d14041c4c540000c43c0245903001070446c940743d0f0b100c0b000721901c2ca10030000c0030031040e880d43c000004c00c1e01d00b8080d150762402d20b580012800810b040f0503401c0038800022940c4109451508806040403c50400344a501c80034280350090b1900340c206d9100094040ca1349405c20b2151004080c0c00900308a076140c50b0450040b400d01c0140020104400080c1c02003000d401602484030704600a42107503200c0c90b004902d4810202c44440345d400d1031003900d021180c00c8a03114840340c032640c5d4689288800d004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 664331133 1250 664329883 664329923
    0x6010f15080415020d14010b13170a030f02070b030109241a0a0908030f0918070f050c010e0d08010906080f07030803041509120e09040309030209100803040b09010318 73
    0x300c0408040c076450740c0c690301d40709241b01c541d40c3c040d091204404e40d0710b00500c1340001070032420350f210289884020b82c1e00c4429610100d0b940c6542c5825090144400b820407004038200a025049003c1c0502d0110020031000700d141e1010b81da800c03001c1d440d603450881e4000701900b030312100c1c0716210701255003011141c40d500c10f003400390456101d61300304801c140792070b064001e09640001d5460490220b020408010341e2030205d000d4050f031070708184107490350b00700008020190142c09034901c050080000c5c0302c4e4811a425070140ca5144a410155505401404001488604203119140c440340c01c0c69000704200c0c2010410002152101c0c0040107580d2450341c1c1e8202d903800041040c3d41f101e41c02074049001d440103006e001308003445050405881c58012001030103d00d90325002d213014105820820002a40103c01c06054a8040f104079440e0794600c000c2252101440d003143d40310740404500022038148100140110310000d0320244076080b5007408070340d40c1e00343c05003019055042c18000070032044 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 664332383 1250 664331133 664331137
    0x9120c071502150114041d0a11180115140304110307090213050f0105040f0e0109140405060f0901020d090305091813080c0a0f0f050721060b1206010f1508041502 71
    0x100000e130010841f00e0087c2c01c4480307517504c0c074a1403541070f40041018a0800040183c4254080e0080f580080310000345040200149414020000c0d402c240313001c031100d401c1c05818101c0b500c55000c6515580da1034640740c0b11420340e0a1351078050080c85444070100d4070206500965080d58000400d5942c2030380344c0310410143c251810300c050f05008007000b022030710a040c44682005081070600030700309035141485846c100ca0300c110b5401041c5100c541800001032021139000e42108054000401d1611507480440c028804e940456a4603464800c82002300768000d009842c054904454510004a001c2e96490070080c0440d14107081001c54921900003440c004007800f11503000f50110761000b08280d480c1c525591031000240ea456404480402c1002020000c140c050222401d0070f01580e106801c4200840000c1d5400803c45a1508107130082030f00c402000c05085108441141e825594400c0e48600e1a5103a005494103444890700794442070b80a1030f6020301807035200c100807a1303a801181c0d41c14025 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 664333633 1250 664332383 664332419
    0x30601173408030414012d1403072a030c0f1419060b030d0f12090506010905070f0903020a181b0e10020c060702040509120c0715021501 60
    0x80c410a070945000300d0380c03602051020702400c8004540e00c0e4100710390841819841c3c403540b410002000c0d10070f641c0c5014107028100c8001078402c804180848403c0075603160002c840d11800b443ca0100420000300da100d07082e41098800601c4080307caa0102000c00b250390108400a000b10315400d805800040c480110f503e1464010b031a0003680c00e413419101418682c1101d041358074041d400c0700c82c00c01c1c0704040c4210b03203030044200c000f8803c0d010a5840a403408441074412400d0041101c8840344943c0590466510301d640601520925038403951700500600080d40c02c81d001909200880d030400b801080180c040d039400800710000c55140070054120b1245001c1c080c907100c0d0722030b9540c1c80c019140d48142c8000c01e46907211030901c548004117005d40300c42003004e440119030081c0c01000d031a4440340202c5113241d8042d45c001c10a135844100e580d180c10400352801c560400009042d0800c000046490700655802003590071652500c43e41c02c0741c2e181088001e01811043c05001040020006480380541c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 664334883 1250 664333633 664333693
    0x108150402011b05010605100f080a150504050f070905150f1c090b1f0e1321210509060703050406110d0221010303020304150c0b130203060117 63
    0x401183c41c0101103080049000c41d90740e03440746014045494583c0014040007000d2a042203200c500300070081c101c00e0080d11080000341d031407800481d0a02207400b1100a088054030a01c540e007030042641034a04001c8070036000042c1303058008160342c6014072804190303040703100d01d003420500c0f80d034180c182e1503100500c1603003181131240c40c50b452031203940212540a40280b110000ca0f10300035621410621007400210300d80f5600040901c06c13039051080c0150000a501d0f1224482c40d81c924122505000d40d440e074099040d1001c40e400c102c0c0394403400031031040c2031182001c03214244140000342600ea003501e03228030b560803001c0052610b510039031003d0390041c02600003154220007500d00c14125446880d50420700c6400043c68854900131180209110301d84800303408003980345442c02900c2c0c1c0114002c0003d82000c403410164000d1050000d41034194201c50018101e09081c80c414420000b0a0b0080f8000c3c022840002103032036006ea902002e44d500c01c8003a0000c9110b0003039408420410280504d5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 664336133 1250 664334883 664334897
    0x60c0804090f090c03060209030d230c030c03040e160c0b0408090307030213090b090a05030702060304030509030d0e18010f140303070501090b06011103030105060a03050a1b090603060e010815040201 87
    0x200d131094420000950060f40c00694840031041414140a00d0115001c05d0042c010502c0000801000007192040f2820241d00c3d216080341028900b036114000e210380345440049004192000308094840c025900c4880651080032440001c2c4e440c080f0f0401e024111000c4c42c00020041180680207004c1e90398020243d40d5010746a070300283c40310310700c0703089801c503a99203070959410041d05515060300418200001c10710784c1559074600d030396841200002400703080b0100210301014050010341e0304020000b010703540c0744415400010407a404040e40540f060400d9413a0b02000f90f03152080c0742c140e50640750b10080da03900b0085d4910320043c40c0b545042d003522040040401003802071080402e4284260f00402203802c21800040c0400900042c8035080c1c0c1080004000c580ea070601105c10030705079418045020390312060003800802c1c40b5006081c1c10a5120101c0d2a40356101d2188800c1d2031150702c04002c081e03150788e41c071140b0308004d00550301113500c0303115201040390014409550040c81403601d18 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 664337383 1250 664336133 664336151
    0x705030a150602060601170f04061d01060b0a03110909070f05040509042001080118151d01030309090603151a12100b0117040b070e030109051006060c0804090f 70
    0x385590000b41c1c80a00182c201e5010711030b60790f91203860010b00303088010148985041941c0c4452804c03030040c1004080b59079030a950907049501034076010242c044000204200e0380c0d50303244211503030304c01001e8400203031038440a4201215400c1c191903090001170045d24450382d0750542500d00c004080703a0902441010700c0f0004160343c2d6005041d20a03842070031454034030480b682c1481000359a00c40550f040c004400010710400402c06606151610040e01c0420380700094100c81c4c80c0701c502604041034802050000741c071420f0391741c07160a0482c0e00ca50341e0703441d1b01d0f82e90b00085000c40d070343c1c2c1c04014148402960400c08045154100145200b0a007802c0400c1c0700800001400351141541802d409420001c4120758a4080c0c0c490104010000c0c28008011036442c84000013002d13000700300600f6405244041503829205d41c1d0a00380c4c1501c0a4020804500141420b036507170035060066030384060810b2030106095218120480e0790340c0d03015110a042c02d0822800d4406003034450303031040c48c003685c13a81c4407 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 664338633 1250 664337383 664337411
    0x1c020f01031d0a0618050a060203130c1220011211040f080f070503010c0c08210a02040816050a0632030105130905030d020f0903010c170f07080705030a 67
    0x2000b01c80c00000041a145a0600e0700806072000d03003a08402c00d41c0e034040010040341b00032400c01405a40281d006a4a82e1800120341e1020110344000d1f10019081d1030101d039110320750008000c082d0040074047c00740d50380c1140c82040c02100248103800691001d000c0d00e40c0003400d400c95140a410512801d00b8a07840b000445414502980204a698010640004a10707001e00142010703090560091003405a41c00d8003404011030280000d0a0480028101200c030b0110a00440f0003c0400c4903181a410103001039070107134101d03005002c120b002c0d0312001e80641900380c0c00031003110805895221340c0c0d4502300083d50301f801440603000c60061440001107900080040e003114407042000016242e504040500c4103815500000624192412014001140d00041558000c0380c82c05005a6141040100b0807454000c80900f00d405600b03003a0300f14259070708104c4143d0700c140c5d003000881c12a0f4544055021505060300c1003c0480c40010128454505c02d400a50f404110084081246425980c01d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 664339883 1250 664338633 664338671
    0x903170c070b070201060b030606071a0414300c071e0906060e010e090702070306090b0405010c081608060604051f031b02070521070602030a020c1c020f0103 69
    0x88544110002410010042c20142854101400b48000c001d40e9041051354130a92101503c41c510652003c02e000040080586c50b002e4040d001c4241c3c405981040d141810040c402e10400d46054013440721031a2080504a5001e00f08104c0c7c1d03050682e107a541102c8185082d0700001a802850081d950003007143ca021150003000e0801c8850f035091214581514481110043d0300080100020080c001055a038040c0c140303240c48004542000c2c0c01d494407031040e444c2440c00d0703000819440c00d00c0742240c2803040c1d0020351845140294020301c6002c4a060040368000022244100039008030340c17050b441c2520481849a00107409811645410380b500d0014000e42c4000b41d891040d00c40c0e691031403c0ca66490301400b00c809074581240740c01484079500103902ca407082e0251f540101d201081000c054009450038111012401c42965603098966200a44070340c4000d041c3c0c8090710038460b1142ca40d0a180c031007840c0c0e01c1402c0b40c6a4206a40581c20000e0030004814907904042d11100d41714140400c1c003c07 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 664341133 1250 664339883 664339891
    0x40504020d020a031505010f05061903063f0312021305041a150f040911071e0308010b090f091306021305010801290d091a1504051009090317 62
    0x101d21710f4070304800d6001c1400d80e1016000f0614200c00b054081155031602da0690b41041c3c5142020301c016001442c5c00c4005002650011200d414000b6403802c2c5141d40c0c0c000c0761b00980001303142c180545495828154440700f1010020001380c101039455000865075806400007124119a61849035500c4002505455041804185291806883d101e152510105519015804011650510044a100d8851070040d4440c2c0c1d08225141c4001d041440314003000c45440c20761288120711450051020f81c601110031440031000b00301214008240e070007402c0300b03681e08020000d1100c2c800d110b801c001e01440e420003801080403044124184800198540042c040e40194500303440021454440010031a80e01a0b0005500030028011001c2040319010f0010101e42513035081c6584001d902482c200500c28484045c19024588420b460300810500e006405003101a40f01403511110808200171a8401e44441506110090303003048a00001c0d0414400c19000e4203111030359001600130007184903800c803 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 664342383 1250 664341133 664341143
    0x20705010c090905130206031314150106170108120f0904065316060201051015020d0f032c06070c0302150c0408010e161d06040504020d020a03 63
    0x41e401c0c0003180e40f91050750790100c444203c3c56011140da402003129484064118600f000c4490703480014044554020040462242e0403500280442c4510071400d160a000c1d410018081c00f02034055103005500070340c141d5002c1002780000790200c054006503a4000c0010500325030050040c0080c0360b50750b00c100001007000c0c08500c5e9018070407280141000001140c00071441509042703403018411142c2850b128151913040001a00069000e02840e2403000301c100500403044580102c0c0441c1c0c190051809001b6100341080340070b89882008070342c0b43d07445103ea401a4807240208041a1155200045012090a0001d80c002407076003203551842005c2c2c201810f1900f0180c21880c0031324100f010a50001c0c3c07034900b41c620741c0c0c503a40c0e000b034603443c602c901c600514003a000480e072400f0181084400a05035030300204030360b0114507201c548407002e42086040600040d50009014204c00c1015410320019981d4010b4682e1007200300402488060410380e0044100680d610068840e90018405176000e6 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 664343633 1250 664342383 664342397
    0x105131502071a0a1d0d020607030207080606010e030d2a050c0f150d05040201140c01050f1f0b130f0e0421212021101503020705010c 59
    0x600f00f100d2142e41126015190701c0c04109070000182d004600794080c841c0d1440c134600c4810002c0002d40e43c1c0d018214043d6220400080d803400f00b6400013041c408446002c0b0998503107079500f10043d240c3c0c40180c89803036050740000c00800d203907510640b20398041d180710031100c41c440003071540c60726441d90200f4400c0740c6950003a203161302c252374084084603954104032640180036010954050b181d01402e420746006d82e46800200301168060004999800042c100b81d82d2a61442d0500034042c00b410b8401c0b0115004100118105511012003030051a003820003000c001d03441c0181c035040700d5014000200d60011141d4010800041c4c0749a03100060101c40a0441c250401e42000801090391100310086200c41c100c000c07900c1d0341c001b561100a2a54a004012444100c4201d40044c184c1c000790840d046801c101007075220a04500075040803103016600145141c0d011540126820058030064850150203004024007031003050391108034023451401500f0b042e07640e680c4d81e0030f483c03c1901c088081500 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 664344883 1250 664343633 664343639
    0xe010509041d0a0c0905040f0b0403020118060c11060709050d170304060c080a0605240705060903030106030e01020306150a020f03030702030403061a2211041d061e010513150207 78
    0x420240300150402c17540420450801c0e60703514a03001d6100800800f1014800001001e044c001e50020503404000780000c19008481d20700343c002080c01e0240c8001080d1403c1d801c640840e000606c0d588214582d0322000c801314100000c100990014a80407149560180c00c1711908014400185000b10711a410102c0c0b840010301d00500000030060006c50034070700d865400c000030b940740c40c8811070302003181d400c043c1c3c5504c9945c9480e01034401c64401911a118060034008001c400200440c1200c03c0d80c1d03001c108030101903a4440c00d0f813100391285640079950002c00e15450703050200500c402c1099004507407800305841c02c5181960000c40d1400013507000868100b0622089001b00303c13154011511000d040d0956000042e08108040c220b00c11513255044008441510743e4460042e5803800d1000325211903650f82c48400000d1a0000e06000e83d0000010900c0c60500c4401410b0b0380c4080030b01110590030040c011161504100c03400b9480e5584520f00166031100702c034040b9000d90031580a40a1141 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 664346133 1250 664344883 664344893
    0x222090501062622030e1302040b0415020c0a080601050a150f0327080d0e120d020706060e01170618070512070305011104081c0e010509041d0a 63
    0x805078405010301015102c054404001e070a00c400c03003d241c420000d2600e440d0708070f0351584103d044440035020400b00300c1c40c1c0241500080b64031132004d81102c4a00c1d4501c0e0541402042c1c0c061407044a094038400e10003482001240300070595280d50b240b0440e0582c0d8003d50005814801541c48800c03590803500040c03106050503410000a00385c0502c83c5806c02007000c1d4018450201e1000d0300302016904c5110f002c0d0100c1314a200d003003628080c02c844003242e1050400307040c554031280380040c0712490010b00e9007001001003120305030710b10900016824002c40b4240200030f036221050444491350741d034801190300c451490000d03001c2c040081d0040c0300000d0007540310b840c00f4805480320060815210001441c000700151600a036001074900d11501e081e100303601392400a09404c01005542400302265101310990054402c5800b484215810358074003500c41c0c070702207082201810005000504880441d40180e00030203540602501c00981c03040c0d81d25800d095400c84880007041d60b08001200c0050103 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 664347383 1250 664346133 664346141
    0x706060b270105071b050301050a0c0e0349050a020f0a05060105010c02030709110c070e090601060503180d030f1410120503040e040c06030c030513080d022209 70
    0x145018a0500180c1d10403002030403c0c0600b81c801061320b81c0d8200d4107900c0304481e81c1848010203020703009204c0750501c0c04070340b000b806030404203000240000200b044d0310310b000210712a5102000303070800d6019004901020080f02030070411155064449004070311030018000c1001004055524107442d0a440d4030b00078104000840c0c00c0d8126400440e1038400b080c0045007050455100342002c00d0140300d03e02c00b103030500107650700c000200e919065511780c3d0031155000411940e10340381c0030b0f101039a4940e00c4504500c00e0a440b40d00f42d83d8012001880800d008200441c0c025804541c400400c85c00f1144040c605401c0c0f981e60f03c0041d07223668a40f0302e41c20160140380310341310329690f8400e0b903468400b0205144510622811100c01c860741a40c200f884410b0003140c024009900b4801407600e000c0c1425046961980700d80000685072840c8000014800d1003414024400c5c202421402e6407542c407447e109030080320700c20300641d500b08400703000034103104a606441c5101d843c410503034628054240f002c072 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 664348633 1250 664347383 664347427
    0xb1f080f07110601060503060d02041811060c0303060f040f0c1206140102030919150e090a0608030d0c030e1504020f010314070c03140703020a350306060706060b 71
    0x30000070021102c00910120310310b03055070054500103449644040c0001c40380324a800000e900a441c1002c0900300d0f982421040d19828080c694400c8031000c188244403c51007804800c080b107400038800b290303082c40c0125081c0480c0310020070200b0740c00140c401c6401190010015840424000c42c8445007545040c09613000405c909071984802c0681c41700003039124499456064072400c8210103850032180c0e02003841e8040d05802c02d0016070003101c4440506000382100c0b00c0c0f8481c0701604c0004007603124a00450f0195000d5801550070085000d07440d4014101800c4000305241d207940041001d1101002001e0b460190161084e0580c00c00340144078803402c0c2c1401c01410903040c45168000244405d0441c0c4c1c01140c2031511118044441c08c2c121045400b03030449800f080400541c00301411341c00194180080c2c001d802e4034072198000b510455005091a041d441e03868604041d1160f00d030412800703154800409404103107040d0b000c2d5030b0182219000d80010641110204500c050003080c1e640e99000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 664349883 1250 664348633 664348637
    0x1202040e0901060b09010909091502210903030103030c1103010e030a030605041a010c240c0509011b1112070504090c03050f031c09020402070f080a020f1f0b1f080f07 73
    0x2400ca40170300000c1c0103800c98090712124541302d44501041049a00321005103003c00d0358115100d0b0074000110000800c0300840038100440100428100368010088038100d80c0c0c1074444071030140b10340c1e40301441c171001d01c1c200a5041d540c0346200d414002080c001050760388015900010038909042c1000121100300003950f04021302d5038401452030340c1115019000c0d03504440b049403034544625003c06070401b181c0710f14480340d003040b0660a006d504440500b1790b05000f600d40c4100f10290041d0f1364401c0e4501100039240d40c0b50108501c10301d04003544880302901c0e241d070603250817549410115003980e00c1c0304401c03241050340c50010014002d045c402d298503000c404001e18501544050500141c0b00700c4160780c1c502d07030340c0c506043c000c55807140d0440b640168003104800700120310b030428011640203000501c2c00b40c022100b050340380001c041a040c0b50340803c40c030381c6c00d400303a01c50b07041c0001003100060094003d111414000010403254860400c02001070340d035051140f03807110841107074a5002e084102 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 664351133 1250 664349883 664349887
    0xe01061103031b0313060f0c0801081506060901020102071b17070e04150e010c090312210b0109030f200105091c0203010b0a0305010b040518060f071202040e0901060b 73
    0x40d0349803450070703900d0a110ba0099a0b46170b48448a0001c6104218107008244528004440345c4414003a000341510082644078404c0c0760382d960154513201c44100807602c201890301f00001d6482d1401c0c002a0000142c10700c001030400c1e9180c7e403011903c03100368142017201010040d040010b0b0302c18011000c2c94006100141c1922403904c0c00119001c100070b0001401d2035074045518a02c8482d590000b101011900002c2c000c001c00a040941451321a020aa981d940d103101000b005c2d5020781c010101d44100000500403000d140e91001c07008002c21b1960742d04024140000102161200c41301004c40d6000e010502e1100ca200c21001008807040070b0064180b220a01c01244580d4640281c4403040e4841c1a0b00d10604c481c0740b0020b80100050300348190312494514020062050540c010064240251020401502c1c2c01c5a5060040c50b40d2034500b056031b01c0140028101d50402003d16044541030400c542070071272480e0044143c1e00175030000081031807800d0411410f90000d0180000410400d4070040c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 664352383 1250 664351133 664351141
    0x15030e0c0f030d0f021216030e01090506070204090f02061b0c012d030f020315010305090714060c07030807031d0d03140a271503020f120a0212010e0106110303 70
    0x90720f5040040d4400b051046000685844d14020710441809920301840b8594542840740d1401781c07003c94540540015801001001c080c1d406810988113484000342000e0070b100a035802c01029001c089030858460354024965001070319050050000d0f4001c5060722801000c00e08100d5142078048800c42d0304001004100c170151079080e0106101c2c203c0e80e42800103980b02d000c4c0090f0080c02101c40c5414005200100704011100700c401404150142680e06015a446000b0215911301103405807411070500c8e17541006e02c4d403400b44020003100c2c240c4400d88085590703039103864125800c0882c0607030102c3c20100c0003402e200c2d565444019a244211380c3d1900c0190715803002800000c400c281c040702141c001410042890182c4607964580c4250303800351984041040708804d43e40014400e440c1801480903202c000e4a000c0d000fa2030101e00e4060500703040c81c60202c0e01020b01c01d8080c02008949500304603c0655200400403140a02030f011002b1103503500d04070004044c00790702140c0345400d030011b00c04c0c8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 664353633 1250 664352383 664352389
    0x7060606111b010c030e1e0a17030d0c1407030806090c0c100b1801090c08011211040c0525110103090c030b060109050316060206070c03080f0c0415030e0c0f 69
    0x4022803607081ca884c020400d02440c1c01e03180466048082d6900030b5111010420907001e0200c0700c558a08241c65805c2969584d0f034172203000040c5c9200f02c1406030018000c0c882d103c0110751280503840c281d443c0501c000c020305040c1c440ac039444044150005410b54042100504100c00d00580000e002c1110328038000b00c0c90002521019080800008283c40d074034030b445070340d58080c440365000020000c0c13128034ad656141c2d180e0051000f0081400814000d100001c1c442c90440340ca141103642141c5481100014070040100a01d03441c103403181407040601403141c1c40e903a11112543c003406a11b4441442c01881d0424a142548236000641014280300c2801300240550241c0000c607640310b9611070480d01c601d001600c00d142682c00c13154151180588402007608500f04510840340a5000c0d1030198a034103404994a03070034140c02402048502000c200044030544025500c00840c6160f41d06064680840321400c00422050000081d00d0381402030504406001e030800c00d1100321102c010b103004103004 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 664354883 1250 664353633 664353673
    0x803030921092107060e0414011802131809210c060905010e030307120509030306062d0d020c0106092705010b04060f031a0106020318060f0706060611 66
    0x1403034010861024050030a00c40e401d8008240d03d104403d940d5a5600e441009041140d440c1c8000d00c950308105080c85807482007402e69050368140864450103480010041d170103584071041c0c1c401c10301848600040c0703201001c01a05000351a18401055013086800d00f03181c004104009082c8403075460340424122600004805112580b0060200d2102280e04001f4010706178440b00f280c45010000400107000d0b800700d0000602421194200866114500496501e0004442c001d404c42410040c1d18401c40c8010a80300b0a0001c48180e14100300b11207008806036000361220411280e000305008141080031f00030304018061a40040250100300311030a0002c501c0d11102c0d002022100201500380f010a4000e00d215040c040d0060190660701c00f0f0311603028600e4801540d1588861070030344441140c402203e41242d000e98011400d2580301c0d80f4030032080c80030050b0164046020004038494140702c00140103a18001c46001402c24688400a4444001c12a5400c016002036144040c4081903202c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 664356133 1250 664354883 664354897
    0x301091b120f02040506120f182d07080d020714030a0303051b040e060f0105030f070e060d0905010e01111303030e0d08070b06012c090403090f0803030921 68
    0x30120300440b2050510b4000d1140d43c00030b90300f0007000101154441a090301150051205402c407003416940d12600d030440e0a22060003003001e40240b12003543c1196001003098200c2070907040c1d04180019030690524020003680803001c650802c1807a0104941c042c8081070041280301c415100525100c00040d0300c503c0d082d98001c0601d659140481c00c1c8201c54070040c2141c400c00d202483e03a6545456030021601421a00f4500c80c68402d8920420340d403003407066900507030b14441ea0490b50f4a4a0304260361100740742051903041a4140b043c00d518a0a07409244182802500002042204c00d07042a007590074040008205610400003900c4c48040e03528030308101d0703805103080c81000c004080001e000403203100e806847c185c03001c100e02c030900030b100740d18901419090b01d4016021a00000180241c00c030b001c818800e004100104818604020151a91003846442d003624071a49690078813034216020b803c03044035544040100a0035100400c191190f03208044202d031b000d8800c001910055100d0340c1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 664357383 1250 664356133 664356167
    0x503040b07090807080f01050a1a1005090d0f350a0e0d0302100510050d0311011b0c0b060402040b04050d061b050901090504090309031e0c0b0301091b 66
    0x30014818911802c41d580143c07864000f680c603103503600c095050307442e0300c10403c031042c951a000c00700701440300d1440741d4200c188200c103000c0320205034081000200403000d002c0c2c80a01c0802c101c0366000f40e0300d18a10319501c40c842d0b030190301024a94200740c128204086d103551640301c00422100c44100d40b480d8268006121804c040365501d82e8210304031803d0105205080e00210f0141c42c2d07408050300400e1006003070740b071820b041250350341e0301590000601d0944a0160021440508140400d2240c445a036100742e5490010400345245a003042240c03030281810700000c0e08810004007000180c050389600000304540960401c0d003480201c19891041f48205485410041000800c11601d034110303000369012840b20070081d5072018806025503010110b8180000c645440c046075a28080c850b2031402c640650b11030302d0031800d6903038403611008101c040012039010140c920b0002001069080040c01d10710a4a507100d502d4421500d003a00d51100c0d03484003503032403c260000d08a521040784a00c41810b8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 664358633 1250 664357383 664357403
    0x2d070e06100e092809170a021e0a0507090c02030909090a0c080c040b0105040f0b0913050c0403110d050a1106070602220806090304030213021b010c020616050304 71
    0x60704161008859801e1480d007208410b000c005000301c02c00025101c107001c00280800307201c60350b5a5101110f540103801841d03228600c8080700100201c4000e08102c50075070040b00c0442c502c0000d201650002d924403090154002c44102c02080340610001c001001c1e5800c042c03010941ca600702035124000c0115180c0940c182d9400a608a4010058401c0143c0c00c81c042c5d000030380e02c6050f00307900c030042a402c841c025420940d80d90000d5204100310703011501000308803203401d414555440d0a41c2d00c40544070350301086003040d2000402007407056902561a0142d000d550f05c0c40c40c40c1c11208002d402c08407600c160b004d442aa408104049101d000c01b41d800b000a285000c142c40000d010360044810140c220303480840c215211554900b0032100d0342c1544a004041d845d0340b11206941d40304102d4100c041d90300144810001401c040e45c011901c040414405800c1038400d0300e4004401c2080030008899a4661b4040fa81c07194040c8a0342d90400c204e4100000c41040c010000740c004c0c840948010518501 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 664359883 1250 664358633 664358659
    0x509010308030a02072a0501020c10050708030901090c0f090f060e271005010519080706140904020c1506040c021b0307090504053a0e010903052d070e06 67
    0x100103d18402084940003d03c1071071301b83e41031312144034624003480b0302600c03036001c400080d81313484040500a004261b60310380c0f07020034944c0c515000e6003000d058406990740350540d00f400212620311502c0a01540304036a40902c0c5001a9502a00e81d605044607610345024024410903210740d0020b80c2c44022240c441e0007000c03034299440009011024a245103007c0c10303207800c0780c045503a04a541210000c030345120720320042c40e01d1014101524071a4a4030340d4000390003040443d01440c44c00106540c0b801805040104102c04107059a00c84850180c403500007400c0c095402e040c001185410040176101080b515058810195a034504a040101d050304410061866075404100403030240240c5141130140741132078904a076030340c0000c2040c0303440600002032100c0c4048110500030705032078014080f080000d403c000242c8490b91884845410821000d6000c00482e17010400b030014208100390302c50300c2404684031183d421005135210703c010703084510204024030b10a1340040d0048010ae401c1e001c840300d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 664361133 1250 664359883 664359893
    0x1a070f050a0c09020a091508241305070f170703020f0c030d090210030b03120c010e01110901020c03061608180a0506040b0108061003120e060c0f070509010308030a0207 74
    0x5540a00520800c0282000f2420101540143c80841420b4071980800f0741c490046294054040c080c0c800043c0d40200025110002c8042c075007201542c0c4c00c0e080d0317641300c07003400414000300e011406140040d0300d86003403100d05540000c400459002915002d070813554500179a000f8041c000d08003904068000c1f034a00c0040c1d18031000c440041d01041d040b2581e031030840e0010b001400c03c182d003d0b441244d04080100f03046010f40200d002042005000c1c0040e84200b0140c01701c0c9410030790b40e07003a05641c0e4405540c0d6080c02403203604885850501d9660b11041d004000a1419070741040490182c0c10040600281d08003030001032a100e616070034400201e5990001c51402c00c64440c071f441c0c5440c800d074650308003440000b107540c6000d24000e0202806503038807840344c0d950380c540c00c0d28485408400020100301140c8010460f64107402d652030719100039103141d0f0000711141c00c4045040f039140c1022400bc100301c1410007003c07004040680310444a90324540380e65603240401052100260340021b00001004 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 664362383 1250 664361133 664361143
    0x90a170f0a1203050601050705060a020a0c080c0705030c04020c070e150604120c0504020705100e0f011e2307050702130f0e0d02031912061a0309071a070f05 69
    0x22100049511000300d50604a40c403501a0700b900300030916000102e029544a401215046ca4000e40200131945030165564002d40c050121041041599903040c030000c0c024800401c09555400001d00b012800c0408050174400090000e62150f44100310184900c40301068000407a20345450040e0103035a84421088018136414550303038842000900420304200106410303458601840300110280e480d04144412482908809841a800031001c9000300c180f42e0400c620000102041d00c50396640c4101042c250703001c0d010940c2d850601c1403230340f40741e44210b48034800c00e551041043e13a80b40070124440308203444001e0200703000c210307002600c4815512000100210450311f01410080301d01807114080050800c1056194103000e003520004440d40300000f958a80c103c201104200c03a00100c005640407000341c0400c60a41c1d4944900103100902281c0c20b4202e8001803030076907600c0ca41181d400c0e003056429040042c003194011050a03002c1c0500007175600c03c5500c01902c50f80403505003040c81c605 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 664363633 1250 664362383 664362403
    0x11030702100c0c110319150501060504060503130f021e030606040207021005130f0906090b010c02010207062a03020115060206010803040506030903130801021e0f090603061206040c0e0c090a17 84
    0x40c0520f0001c10070807da0043e0349030304071042c174400c1080d6620f80d0001c4440313200e248039078000500d0520114111700383c641070780707170b0f541c0d1180c1c00e0000b401c0c11503400b00b0508c01c00a54017407148050118440031b1410140445988600e003111f0440c50300509500046000180216403000c00402003036171100944403980c0c2e4805441496103600312071381d8440e40304010300202c1c01007203d07090900f40565038030b500900c80440703400d5050300070301600e50a0040450f4140303c41f68420103c90002c000201c02d89180c481d841c04554040e50000c00c2e9410402e05a240c0c500f0551b0000c030465101c0030040204100200c05d4405484049601aa8a8aa0000b243e00d140a04502d00b602c41c038203124000b4001300154014500c8901140040000306095203203c010350040501075000b42d4010801280207180a000860b03000d40020100760000d040140c0303c515044048408032141c00c04d100b0144101418014030590100d21204500e1034a0140d1010035180740c05445046596001c4070f111039000e1406101040c20 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 664364883 1250 664363633 664363663
    0xe0318060c0109050d1115070f0215010914010b041a0d0e19030206090d020319021f021218031b011815060609030c030b0c07020411030702100c0c1103 66
    0x200c0300490030130940f2046410104000b05041e00103a00c0b002c00d0200e55400301d0b207035800e401c00e02d42e07440d860242c4a00316034008280441c05818a1281d041c100e03941c1445c082c00795030400180d0541d045500104000c0182c2000041c94001c6c41300704200c08410100908144800b80e4180c0c07a00d14150350000603002c0200a400c9901541e0751007600444240300e05080d045c0640d084420a0f12891800c80d1101c2c0c1088284005800400514a000661400401c0d54419078411100b801030020001b107140100c9502d40070216800041e06081203a400480d250845a080f1640007541400c12206560b44501900130880d4500307041d0400c50780c0303030a6020350000c4421403400460707030b003681c074010b046456109101026503140c4840419000e11542c081400c0e81c8c0e020440050395411031b01c070300c2208071009140300450f0008014010068482d030180c4034118484003483d035140e04006d8006410013101d141400c5c078a13440c010740240915030014890540c142c0010000c0580420030002c00d00303050100c104020 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 664366133 1250 664364883 664364891
    0xf0c0302120d021006080d0507021206070c050d0314042003010e03071b0305030313060b0d030f1e210204080a0812070e060319021b010c0905040e0318060c01 69
    0x1440e00c0c01003191144001d541c3d081e2160f900342008603000b2220140500441c03a4007080d000c80005001f60700820768140003c0c4000060a5007a80d420715040040b9031341c50025484c20b2043d0100001000111154a4541800d020481c90070190304808440200050140c29664205189082110440c0d400b0160040c00a0103030301c01041d150341c0e4960121000316030b407008680700642020607420310002038941c0a0055842d580303c40b41900c650440014081c2e41e281e541d915400c1d01c40d942c0b11010001c89110ba100d000c0300402a0b0406071116401d0315284136442e400040504d801c962080d84410040c1c9035001c50b503004440b07003000340c009005d11b4000000c1842921105028495440040c0c03644060060034028559525541101c1e08039014031007541284d0180007007920408200b0201a415254010040c1846000c0725070710001032000b90442c0e85070750749003203403a20302d940252800d0190000703480038400c452007060440c3c2e8900c80c084071110074070031118940100740e4038002215600e0301c5510080c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 664367383 1250 664366133 664366159
    0x8070f050c070e1e13020103020a11070f050414090a06020a0203090a091b050a050a12230a0c030204052119060b0a1a090405191a100306030b01030f0c0302 68
    0x1030280030203813141200d92007854441c3d041e45000e0100c01c0e20600c00d042e0105103d0303100d0750041d0b010350082069031003402a02101014000f00400c0400000c064402c00d10310318070300d042c00f84021251500c14513115a40b43c24200020f0705000580140000e1b400040181e84415400c0128110b0081c0c2c650b4540c09220b1078400030b1030102a030041d00c0e803094013000d8820032071440b42003580c0340d104168000000c9001404070000300ea01030b140da400c0c2000182008101c40540c014082d00c4222400091508003080390b0910458140c40c3c030411f900020306007021481c050820340021716814403011940c1e10160040038005194206001c060050328071100c1c5900c050f5039a2500030040c16003042440c3c0260481040001e070981c174107115140060034a084c0354070304504d54043c80003401c0c0c01030000070032007100e8035101c20500c01031160400c503540032004500114403490400c0300011400d02407208040c1400002d102003002c16514904690303004200c0402850b607483c0c00a501001030344042d5002c07666003103203 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 664368633 1250 664367383 664367399
    0x180311130e071e050d0c0603090203010906050c07050f0f07030204090618030504090c080c031801090b0901061a130b0a0905150d051014061e180907050a08070f050c07 73
    0x700d064925000242e61400b0380380c10500c211102d83e0701c006000e86c46402c400b085407a00aa1080084900207800462044c030242c48200503282e050f603144034681000102602840300601c10b0048001414000e0090b4107030868940f603079a200340c0006841181d40c1c2d04640c04000103a40f200441003449082100c508040c1d040141c503a070400e1081070b46444c02d0414441c91103106001c0c0c548a00611258181103442c2c040c106101c0ca01c0e8588120305942da126440e0f804249010704940c0710f50840700020a00c00d0900d042180a0350750000706490b080c40c01c1c8400b092022250407240c0564100603d166111840244d0894008010780c0c0401d4205803410308190524480c10000c040c511040380d0188010345403008961461000c5114600c0b481d4031500304911540383c51030040c0a46001062807400d450035800711048a0345c000e50210404c58580c0301008160306044110983c481f00e2814400d017041c2d103014020341107100017848401040b4070b480d200300f45140580191a10700e1808002c54212a40391201 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 664369883 1250 664368633 664368659
    0xa0813051b30100203101406070c030804170105010506030402010e0a0e0103150b010507021518090a060504060e0c03010618031a0601080109020711090a0608060c0a180311130e07 78
    0x2c09861805005421038104000d8000c50f07000e42c160014452101d0f2074035910001e00901012800e83c06002001108c02040c0c0b003c06000196000d80e50456039103180207034100310810b4030103802d00c49074146401040715584181c20759070f11580a0134002404c0c0080b9000500d20ba0b01504601c181106041c0048140b003103a2558500d8000142010481c030703914074005444501840c880207502224040c01002d600115001030030008101541c2e00c40003003c8071001840c100803ca5540001a41d0ba0004001c00e141a0040b900108810b20740341c030050500042c40c6000780710501528052011202c500720603142048940c4005540040d1400c401d00e0b121001c101500c02c080e42e8941c0061500130011a840030f8500c00c030b13505580c1c000720400503a22000141f1808940040141c40030320f0ba590340009004905014442c030802c106211079681d2003619074050f0041c10240e140f0b45c02241c0c0d0240900c0090710100f00c40b4449481143c030804034021039140f18001c2c10608401f16118003c5440015801101a031 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 664371133 1250 664369883 664369969
    0x90501140f0c100e0d110606011d06041d13020139110a0618031e020d03020d0f05030411061c020a02151b091009090c050a0813051b 58
    0x25610440311700c050442e2a880409046000740d0480f0300807690640c0100018540b4103c10200d80000c0e4a4160010f415074100d540080d103400c445107103c9494200e038280d110f078004403032174450000895580000b0110111100208240448141c04072180601e60b00b200500b140700c58490b5040d04444e18000307000c1981c8001041c021410b0000114407140242021000c0e10142112001380700d14503224030300140f842c9030750708410b0000310407a940581c940b01c0124458901a4009242c130400c0c04030020804031141c60558100b0a042c41484005518500684c00420044400f1072710361880038240302500140fa50310b40d40e068400030703444c40c03480d40128203070300701d541c001e03005288a56459004040c2400d12040102100308104114040cad858002041c0990944234940241c126403168204411994602c00c0c80c4d0100e040401d102c071030329500040043d480741810803035081103400c1d551103969400d07608841c80e211060500502005441f202c1d400e00751214203003840610700c40100c42e0340c40ca80703010f03071 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 664372383 1250 664371133 664371161
    0x50c0a0206030c120604060b0d0f0b0604060302070c080f030a300605010e06120412020a060e03190f02150a0b09180c03061e060109031a060f01090501140f0c10 70
    0x1340008040340303010b11500d4115810764985914000a1005076802000c04405803404256100305a9051b41c07101409400644460f481c010b03a82c0559080603401040654414525507100842075038003102e0220940c2c0c400c07035217420032454a50314842440000700c0c14101d01144c4034a00410004002450b81144080b01c0085e01e850007240e0201081c0100c41c451081e80508a082240120300000d004101050a1440510646030b50032801d81d24202581c0b00c014a0703048aa1010800d20108900031036034140605450a011802208400c0040d4036000e017030700403807800c940310b03400600c91418507000140c8020f001011000185040b10890000d4000d00703035100303103520802d100001f00c0d04000500394010703404c2a4240b0b040304070480325440030303010090842c2c0c10010a00780000024101100c06d521400703030481a24100d10f0400309115004505071401c90410030340c10010092641c0160003030306d01c003607000c20207540d41b005881c0e81c01545c42034030080e00c540d128035002d400c40c4202e81d501c0061041108 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 664373633 1250 664372383 664372417
    0x5040b0c0a0b150108130201021507081e040b0415060b040b041503060f0b030910051614311d15180601050a0207080d020703020111030a0807050c0a0206030c 69
    0x466003c400f88203a01c040b40441d510300045242802074050a0119610510403104954801c603110100d020007a0340d41c0300450348103002d004443c005c5d5800c070003100702103000454040c94151119080c441c00984003500c000104a6005c0300e41c0307032a4105201400300f11085030744d50b507558000e440c0580c1c00380c412611019031030724040880c24401d010f030030f00b00c0d0b200c9130b040c8900c24104234100840ba8000b40c030401c494818805080d211203168000d00c0d1140d5819101d00c50039102055001d400d5446211003d04d449a04100030007070ba817119048131962080c410f07402140940c20b000701440c1c2454a0300000c0c3ca580291403941211145040c00e28400d0342100c3c082c82c02e034041c0360184003200c200110315101c3c69003140001502ea5205201402052800e44100c074941595420603e003071506900015005030021801842907581250581c951200706200862604035440801400d039180036202008100340014041d11807601002100c9816400600305581c0342005a2100c10a900c040c04a40c040703100 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 664374883 1250 664373633 664373641
    0x40807050312040611160905090f0c0a140f040515150702090109050705160803062b11010c12031b0f0f0503090304030f1101020f190b0705040b0c0a0b 66
    0x3002c0341c0c09050101c050556400c00c0d0802130b00740c54181d00d1a48034607041c440d5030b419041c1b825440384014010a000c043c00126400d00c607000c1801c0c0700030380703075007900312381c0b1248104c0b82d50303104d545542d01207e82c42504019100808800114054a44003540b0703031060400091000e07601000fa440300483d04210390780ca0140041e82d266079094002c140c00a0360051148004011042403070300081d03804840303031521a160054907c140c41d0b544011b40000d9030001070110421501d0704041072040010035014120070320424a0240b070b10038201c4982401000210b60000c2c3c1c6501c0c0c0d01a08080d00381e0b47e8451103030340d104511554010000d208d2000c040107402c1000c400042c0c41c03406607100303d4030b215840d0380396140404004800d541507800a07000142c1840100800800300c0c4030812a818002d100780320038503009039004002480c040d49107175500b180d60010346144460310142c0413118040390340840101d00e15910340c1802c0d0340c00d000f5503100036110003001420101d0440046a0300c4c17601c601c100012100d40d21 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 664376133 1250 664374883 664374889
    0x506061912081b0a11041a03211c0e07050a060206150102071a030609091c0c020d020a080a05010f060b07080f0f0a0815010c11090604060509010b04080705 68
    0x34070685038403041c580201d038040b41c800802001e60312001a03c0600041c262480a8a072042000040c0d420140c590030010103860103014480c54a518458100400f031031020010751954820102c44582c24450b620030003603400c2040a903403d5052443c20b02c42141085990000500060b400c40e82c554080c8100200326032403e00c2c5030109039801079004051a648050703240e248490181910390551280440c00200001121108e26413407601c4140e20f502c034203000060100c10f40c409040e44d001078000c0d8068100c8445044125200c0b0409480d110040e55440d0011801d0b01d0083c204c081d4100702c500001080150300025800303d1648101c000f004940413888182044071824015003030220410072494000c5494031000e051024205c925091030807000141020244d88a0340001e008130300c02d0743c00c00c680300c141c0440501e868030003800c06c0540701c14140d4076104400110ba002c43d1144607500b0109801703031500d40c00b40c4051f141c0903003441c0c0d07196180c050a140a8000344101003441c841c040340480c040c1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 664377383 1250 664376133 664376179
    0x110a0b031503150a150b0316020708010606021903050d050a0902090a06080601050114211e010e0105060304050a020306070e100e032e0c030b0a06050a0e130216050606 73
    0x2520102d1854611340300d001080d00949124041c0ba491402c110f4004101c03036543d0390042d4010240040d00301c1c181c2140e6003020741807000301e038003244050f49410390800c030040e0045508000001003100030900c1400ca45400e582c0d501a41c0c0200c10030500c5d100030841c0f4180e146d07001c1c101950003224054850380e40d00b983c04007560203601515071503401c19801084a94000c00b05840c06444504c4a1402d10300d000c1d4002513550071046201c010950064103000d11030b9192015141030b41c01004015000d581040a03165003840c0601c01e190041100000003001d000d024000c00c441d40d41c1c000d064500a04100c000100112031003d07841d817180c0414260203640d68050300d1400510b8101a02030140b80340b40c0c0114070f11a80e508440120002c10114444141300190b00c6010303c00d41c80c0351400204400039505200c81d40e081034010700b00f030000030090700ca44a50440c1b8403034140c3e1000c0302d0100c8188241c01c9080080d0040698041c1c5840038040140c0c00c001c00400d01f0744c42410180d031010002030002c0d214100403 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 664378633 1250 664377383 664377403
    0x209011110051b1603030b0301091a04020a050105071a0703020d0c0e0108010803070203070905040f0f051501210609060b1806042d0203100e0a0e011109060412110a0b031503 76
    0x961180c4c3c80380c0b00024000e41050700c0c000c10080002900d040c090300c3d424040315100f41c0d090700e44000017040004601e8030351080b6016040a01e00581000e4159440f5028820040e4640780d11080800c001041c0030b12a80480e004070010040030300804d590900060b002c0c1e00c01100041c08503064034004980c40d28001305651145400034002c12f0780c0c926000c0c0340c2c801010b0240c410786101918110060128462043d85070b42c29205500500c1c00c4612840c41c51060b69068001c4020041c1090456203411701e440680212182c1010300010620150710345440100845504181c06c40c2d42c120f40c64440156001324988a01c0c0c0c244c80038001e000c1d17a21030040003d01b004030139020010080ca20300050410700e42c0515400791b600514041031740c0c1c45803010040d00008840e155649510707003508800c03a110a009520a0350b0300c020865040c408040d0004226000b40d0003009c1074101034110301000e20290b20140c3d1010240074013580c071210380742d280030401540304440c000348441421586000a06000885940c0c0d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 664379883 1250 664378633 664378657
    0xa060201020a02010b030c060d05040c0b0c061906050915130501080d09080106030c1703041a072a05040f111602030d0804111c060e0d090819060209011110051b 70
    0xe40303101200d40c0b9000301340c013400c1533442840000e00860701c02c2c0010002c18025800d00c0c0107240c5450401e4425030064010360801002500f072500070440c68030381007800c07508180c0400c0c00581000600c8042130760741c2610044c0c0141141000c0002035001c0d0085003901000105070384001c2d07010b80383c44090b07003601c600d4480102880c00038002000344050340401a07a400100b0025249004d0751080c8403403440c04580d82000700b4460010b10402001992182d8920401c203900c035000d50600300140d194020601885001c2c040c07500c1d004811154015940039049440c01e60080c03544421031100b004140e0a00040101d0007441070001c61340100c0d000b2070407d4800c0b640801c0495000c0315035030500c480d40d80b049400c882407089054000c00058014064031110400c50300044c242401c6540c40142030345001c0d8072402c041c0e08036078520f005440980c9441031200e5000f2402580da8850a80100e034907250440782500c440c0200c428100d1005615040a0300400b0448003030302d01549829552042d03885a240ca1000e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 664381133 1250 664379883 664379887
    0x170108060c03190f0204170c090613090b18060f1306020a0309080307031406040605011d0f030703210503060f01080402150f072904061107020a060201020a02010b030c06 74
    0x790001000d005540c840b00c01a4000c11241070640341d035040d1030076480c00c00e0b00302d43c001c5820f0003200e18003800100e002c045000207101c2c0074008404160910400380c10103009010010b5241250300b0550816200c81c0c0e400004640b0900e0041500740380680c1180c803007d0b032030182e880400c80c42c0030001601402040b0740c100e000c05c5c0340a143c2c3e404009510190700304051544604240e00031810381400b441c4102400e85000c079180c1c4400600e28488a00200628403e41c0b4000e001d0040d82d80c41444802d01c18180b40c1d000344210720310b4000450602000200e55858413540d0004030800031418819000d00c003110941c0b0f85040000398041c1c1c2d060000f11069500404290380070307001c96215074002c40c0c100e0700183c00001a071002c01074403051980600105803080500042c2c0e80c041000c0351b840d40e090a504040f22031001800c0280214040c0e0000e0400307040e82d03072601d01c14918a000b10b4122015a94004e00c20292650340c0e85020703001c1d4000e86100700240d441c01c0706104c41c41c00c01140142440b54014541c074 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 664382383 1250 664381133 664381141
    0x3070501020903060c0c070b1e040e060102010c020f1b0604051017061c1203060902040b04030507080705010804081b0607030509013b0705030106091509110a050a0e030a03090617010806 81
    0x48d0341e42c100c50660101500390007082ea00d5040c5403801040505140303074040310140b80c07110019007903071542101c40303003107600c0543c0515aa0b13601082e116000308540c1c054504400503500000c06600480d00f14a0340b04840c000d03003516007604800e01d0020b0b07800303000205410741d0b2400b0811008840d084105205a031b00749000788000b5203401510b03c041000b40c1070010740707144c4078080d40341240c000341c21103100040005014801d2003400c100f4903005040410081100d6070800c40001c2c040075010307000801d030242c0400c10941c001d9241c05400030100700401140c140703281000c00100640000c1d20b868195510744403d0025102d84070300203078065074400700b05130802c090740100c0c070041c0f603d400204071480c0201800424259801e00900c002001031000100c0c240001d040f0380350329948507501c50507025141801030845036074481c064594101203802d0440d16041da07400e0507241c0508071680c6552500a8804031001c01d50004071800c10382d10740340d407034146090302c0300d62000824400380a0080c6540c0300030002 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 664383633 1250 664382383 664382399
    0x6071805130b0d0b0405070518011a280e0a0602061b09010903020a23011e0c0807020405090706030507020a051507020c030d050324060d0b01090803070501020903060c0c07 75
    0x11000c400c0080d01003030203c3c610b41c60340241c0b088241c40c12946034106030010026031400500b0f00b1b848103c82d403c012034951503c02d008001c0e02d048036081c01e1401d000310f62505003d42c8040c8600c1c3e8085494a1050220310700d4034010b1800300403a448a00c980003807000824020320000b0704610541c1003454000e081c0c08000b0301c2034840c0c0c100c040c200b4108154407001000603180d41e0650402400000b00303e024119000c44220b81c00b413002042c00f0304120311819030390078100c20180c0f440e6103c59036042c05240c2c4050390420310914416440040c4d080350401081c4141d6910000e00901101d580b681c0070011a118403004907150f2802c0e8201505039841210215001c0d40194032483e044a100e00440c3e1040ca081e8010900345180301500c000803840100c2007018440c014070a59200b80005500040c1c0d0421400c00940305008000711165007513950304c0ca541d01a4001c03011607024200600850f40c41d2492840d21501030b5003c81c2055010380a107038086001c075aa00070966254001d10006045101c2c101112 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 664384883 1250 664383633 664383641
    0x706030212131b0303030203061f050a0507080904060b070209071b140106090c05190212041422090c0e0f0f040305090a0303170f041e060608010c020607180513 70
    0x42924060403e0790060601ca40c403404080045110380c6001d078803407401c40304200300d1494404860103190158079192900c2c583c420122844025941411a1903051034240f81d002805046240e681040c60914042214444040507254080c42103800344099650140100c1e80e0410386244044c0300c15070a40e060340002c401c0c901c900460b1050000000d100703a40e0b03160010541300c40035904030100e01c00056254824603a0380384901101e9440c0014450503081c1848045d6030300c03d0340325022403100000c0400010b039980d41000610013404c21035401c514100202da841c014540b41e6411035081400644c002002d880c003001003407003203000315014000c9541d5084070308003000c00100201d0421204001c1a070043d0303100c2108402450081e40e4000044066030340b0409c00c5440074001c00300383c2c603014080000103014071425000c288030089500c81940800d140c200094032044d0008482c650074502401141c0703500103083c038480c1782070741d880001c0d041404e000003084900601138550401412104405140180e0300 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 664386133 1250 664384883 664384921
    0x140f0402070203010f0605030708010506010c11010c1a090d020a020303040e060d08130e0105040b0d02040b1311092e0302031905070c06240e0a0603080d0501080706030212 75
    0x10000d458156190b0019003140c200c400c0c0c44d4203c0d552480b0070301240c02c0800000c0003808103013001304404d0904200107000700300e1000c0300a20200c41804000ca990b40300d10f01d0302011580c0280704010b0b07e01e0300000c41d42c080400700c807c4001b5100310104c074840588000b4041443c2d540180146243c07a0410340d513407011041c01005583c0100b4480e040400003210741c1c000b0702c00400130320070740300260b81088141482c0c410b041c2e03c0607200700c6c101070300d0840381d6a6800c2c030244c11950489000407500c030484003144032071107402d1840c40070515101100289040310b00040c00c00d0403045449020241c01c9220400110043c3c4058080480720410321105443c00382e402990401c01c1440920500d0b107448981c58182e0f4011241c240000e040a4561000c00026010320501d01c1c10418100d44100e504a081c2d2848245900c1a03001c0faa02c400b001c01d21400c50341d44800c0c05540c009000c6a51040005c0203c000741c00280701d407a665210310940081c3c218828401c1d40c10000410114806544a040c883c600c4802e80c80 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 664387383 1250 664386133 664386139
    0x4050f06070f0c2003060a02090f04050606121b16110a0602060c032a0712050906180d0206030412110d0905010f11191511031602030412080c16140f 65
    0x11010f102e5a0300f000120f00c15400c1f4034016903120100d41c10710581e42c100018480c011030408050000325030707030369058425108250f140c5600ea5511070458074140b410041e00c152940a0005a0000c045078006c00440c41502400c40d43c105002d0b40000c1c048a1034451040200580100021450048501e4002c6400070500e14403a0080c1d0504010384002d0020001d00c040d00d400c000407104204040a0300d100010592424994200120440031981c01e12a070300019111003a240720000503691000e40d840e802e5038001d09905e46a1400e40340240001c400d0f007a250f00485c40c5080701c054109400100d6200b404403941d9401e28840c500030041d43e211003000e200200348a900703490800c001100300b00020f503c040740030141940340c450b400d1144001d0b0140111041c91800d05404083c00300c0607030116074100c4034154056900d41850b0f9001c0381540a6a000000c0b009161301191003442903100c040d1041d59040310603603290782e207614421086e51081e07108180c0700c0300c0149104200d51404162443c036114000d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 664388489 1106 664387383 664387433
    0xc020f0a031b0812090703050f0d0c060b0f1815190509100f0e010341100f1b09082104090504050f06070f0c 48
    0x40c402c0140c1990b042c08000b41001215001c503402851100d050400604105220130303140d07a004d11040e07941e881fa50301620b019030702c04107c80f942801140ca501ca6620303a141d0700d44000e0b03d80e11030815880f8815442d401d0054036102c030900b03241e410301900c46409152001c5480111003844e00094003592080c41c1c461591001d44800c0e000355201141c560303900799a0140412011200c0e500314030001300510340001891500030f00c81c64141c071b2040403c0424a804114801722185403883c5020341c0d50300d0312444100181c211244030000001c0c01d420b8440d07140015030b9610607a26000380c0c9840c403a43d50090b4084016455103414000c0b01d803840c200c1c80b000d190102040c1d5900c5044040c2200c1e40782c44600300c240d0815002160001c0c1718610040c4568034003811700344d484024500c28030506004000009100c02e10038140d400018020382c0b103900c01020203468818401c0e8842025400074000 = true := by decide +kernel

theorem cover : BRFrame.Cov 664208633 664388489 := by
  have h0 := BRFrame.cov_init 664208633
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664208633 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 664208633 ≤ n) (h2 : n < 664388489) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
