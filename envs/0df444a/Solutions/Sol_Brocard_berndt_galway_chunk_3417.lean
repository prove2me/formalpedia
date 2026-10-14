-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3417
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:36:31.693798+00:00
-- url     : https://prove2.me/submissions/34df65d6-a4d7-4121-9a5d-7d24608257d4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 614388489 ≤ n < 614568345 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 614389739 1250 614388489 614388529
    0x60f0105220803040303020c011d0f0d170a080402120303100e101a0a17060310020d061e0f09140411041104090b0f0913141f1b0f0905 59
    0x40442c50000900003000610300940040c50012060000102a4a0412001c0080c04210b510448090390b4144451441a0341220f12030001c0809041c60300490f048040c010000303010014100b260300703401c604c881d0f11403070003224141d204480c000b80c015128881150403215100d0181d0051180800029540e5000320180800000c15074803403c0d180a8220406469050a003004c20140d07409680071002e44842500400710785e00500304074000c2a529011401022101c40c1c003c95502d030715000c189e10070320042c02140e4030046580c03000c81103d60a04c4c40c6025902102c1003003040030412407a103024482c07080c0f0f04c200300c240c20750360383c0e84800040f00310b8541034035805a1140d0423940310f24184000341000d000030490002c1c2030508801041041c0c0350340e0340c11501070860300d41003000803050b40107451289a040a400500140070201d5035003000c07080f128180203100002c00300079403103c103036000031030900150000d00c80c40b0170b65140c00d546d017441c1024400001a02000b042c04a82013180100c0f60180075802d13 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 614390989 1250 614389739 614389807
    0x74103071a07080301090b0916081605090406060801060807050c0c1c06050c09031e061b12130209010501020114181911030d090308090405070c1401090b060f0105 71
    0x194083c2c042c0d000b81e001407040c42d210b0ba050841c500e00b404605400007850003003044010b45a80000c2d010000041c554200003405021802c2d005000c0c40c100d1718281d0005000f0030440e601c508012b84408001c2c05040000384107800090403960003030307044603072150301c4c0001040050411402c20420032942c900039a07400303210314215000240c041c0a100d00503504005941c0d00c5004402c01e051801e84644000328001c503c0f0488490201c0c00401e03840d8001c854a501c4091044a2039141107191241c05040385019801030100541480454189200f01c0d00c00c6904c0095a661003004a0995541100480740c00d47c41002044030b840011a110320307101e4252040c1d90200e02c1034540d215a00004000c20740d400d0384c548007140011314090204030340f40c01c05410110300d03403821030720f555101e07009020070180200d64039004a80050300480d1100b03070f465030068062622000d07074280e01e8060318586104444480b00100070504520741107644030411007040c1d4400303003081c40c2c025000c240200341d0100784007001c80150f = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 614392239 1250 614390989 614390993
    0x10516080f0919140a030804050d14151b0c0d030c021c0908060a02041a0c0106150e040f110904020d0e07060f0e03010501030c09020304020102074103071a07 69
    0x2c0882c24000003c1191050400d00d403002c002440049007030040d00c510381c600c0c41800020581c50950b02030f00d01c19140c114601500b0726204023416414034141c0c00c513204003011040210720308044103204076204041d00102c00d000d4400c403100740c000e400300a407203030b0804a502d0084620a038080301211307203648100d44042e440300300c072a6511403400c07000301c0c0050002e2000344551b1134100201900030255160841c44c0502e8949070340400414031150310301003c00081c100940704001d42100010740035a100c0c2420001a40c0c6024020303200480d441400b803803c3c0a00c460f604c42d10340c0f081844588030f101030b252030545071208220080d0701c00b40c2118092a540d503200d00c84140b081200d10042d10351912011208a402c644c007410881e043f890b014840d0307040034010b100290502080c141220321401d0090780f00e40f81c9100607403c0030001d4101c14076154800949034030038440b1141103c1c40300c03000a0900351440c001c501c10005c400f00c4407150342d0140d01018040088043c0d040c10850304010740a0740d079042006e2a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 614393489 1250 614392239 614392249
    0x7030b0409080d02120c07020307060f0c0804090b1207030506071803050106090c02061302030a06051e090d140301030b0117030705063121031104081506010516080f09 73
    0x184500f96550303940451514224000e1042aa400c030402d04041350800b0030641c0000d0b503c1c00f0320b0091004104060f03034010150f13405802c1d0381e584140d1100c11640c480c0d8507968840000c000d2000540d2050258014019660304081407220559400001074460340d078034440241d03003000d4203103104460103400420002c0800c01c2845a08040d0001d8600030a404000f940001d2900501401d0f00f44609802c550050050f5800540c000c0d500b944648007003240c0e42c034011000051103100c1444e19407031107090304000c4083c0f00415601e02c1d410040e107a0010b12004402c040d04a0b0000f40002044001d20304c00502180d1a40c6015101401040c0d044070324068050b0b8030242003580c282d41d050300c01d010540c94500b401008030301510400c0c0b860380c03036424450601d45070107a00450811000380001090b985401305d0620907001b400585040c03c849590b1144c1d100f0615641e21988585010340c04d08800c003003010703503106108030380502c081824802030710760464503150010b40c048100308081d035208105960040d118 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 614394739 1250 614393489 614393497
    0x114070e0603090c01031112040c1d07090e06180708100902090a0911040f0f050406050d1208071b08031602120f091309140c1f030b15130602210307030b040908 70
    0x8110310041d0ac240c036100c0400ca480c84020a4480d00002000800464580c0001a1421030703901803821012516000013289050540c030b00445080c044c0301c0c041000c45a0001c043c14040c6910015203146185e403640c4204c100c2c007a00c0351b2203502440b0030300204003510a58100c60300b41e2520302c440a18180d5607080c0e104140080b603000d400b04560310030003044640f40a2080b140206000c1c1d030b40092083c0b85a44228445140c40303c800c080c801d003180403c0076940b1500306107008500b50341c100c042c1c80c4031a017802002a081103802c41d072410030f282c800408440c404a10714401e05049940b450415001c0c030710613000c941103840c02a412140c005001c1200811602908006a00070b8a680c8400c00c0e1090000d414000c4a4041e0f50180c1e02d02c0d041c80301c4810140c088400700d4207052a0000308039400c1800182c0411001c01c0c0455821000300e0030b41d80d940c80014045045805640840301400790f004950304040d601c0344003001c603400003030000608a41c000d070040081c400d8020000100902240d45001c004c0c3c01c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 614395989 1250 614394739 614394743
    0x2060c0102040b1306110615041806020a2c0603010312120216021201050103110d170a050a09080706020a0809121e010b01110a060b060c0114070e0603090c0103111204 73
    0x200580c4c10000150071140a556008040001d080c152030561002080d040100892a02032503441008036540780110701c200800079442002075640d0344411034006c12110b01c4c55a42d0703042d10f440030b214441c020751001c058900c140c8007502141c190303071840e21802c0c00c400c54810010b0030310090091421074035410303100410100308a010441400ca025005202c1802c101d92000d9289030714002c014004207020030031013000000300720f0340380413110018600701501c5007410505540d860800324041c1784094100001e826010303026520700c9125a40ca901059882c1e11903c01d850141e085211904042501c50004008081018103901081c070500c005e010716080803410b0011081c1c100402042d0303016421701804403012000d18024041c50000600c0036240c94140f0b400038003407580c4c0c048204403604e034001511312400a01c1c0c020003444d08640c245891406044402500098141c2402c4243d458041e0649005a090303074010050081031400540042840b80000000040f05002e80c004201409048511440c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 614397239 1250 614395989 614396017
    0x403090e010905250c05011e0b0a03080a0e010e091905090703031b03021e0115060807170601050906070501270201050f0d0b060a050703111902060c0102040b 69
    0x203240c59044151036406802280c80a4208000d11041d0400c03030301180c1e00c412040000c00c00c9100b8424080e96940e00c80c0b43c00811079400d0015035051107402c40c080d030400c1c46521109000c00310451040007440c06c51070000601c02c4c04140704528415100d540e00740010343d018180003880307401d41400103104c04000c40307450b4000c1a100304200c02c0c605050003826000356441008044050550343c01808004004034000120520292804140340c420001c1000404031400341400c010b06040c051800303802204244102030100080000ba100c0c03040c52260301c0b50525a0311401c41050b8a555484d1640f4041c003d1410040b0611002400f0781d2160700904000d4410400000c40e2400c00c1c40301600341da01105a0603145c0084210440545d8100044440c550b104000d46640d8054240a0788001c04400340099000071004c140d50000503004401016824081e031503565105409450b0a680d074560074010001f5050348080007001030070040041e1141c3e02c000000903042c540c4a9000b003102d82c0041031045002 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 614398489 1250 614397239 614397257
    0xd02030c03090706110a031d060f0a0201110702090a050403030915020a110a030f050c01090c0b0315150405040207080c2d06040c14030c0406030c05190e0708090f060403 74
    0x80c2c41c04016000041c155803c240740c414030204021030b20341c0500d01002e010b10500282d802101e00380d0310038551341c00100900c80c6841d099030315020101c6411a8104802540ca0030604001d80c000e00800e4612482e07004207000321994481c048000034001c081c004409040d100c010318000503003601c4481c980440d1200c5c00685031100c1c0303140204400000c07101050203800016a103004254014808141c2c002035041c01a0781d21402e20354607004101d4074902500503d5548008540e941d4080700950003009901c10541c60000070004003c02070304580c48200f0469000c01c020002420190090704007140130b0110241410540c0b0120750419101d00c0d00c0070001c0103189441030410a0034100c201d6601140b0300200b0340e80c0340566400104c03400c0d038040c811110070392805c2603010350760230000081a10380142c03080c810ba03590f80c9400900c80385180100c602c02c00041920320300c0703030540942042c1111f46481503030102c0e4072030a0080e540d13100081c1c04403000e4025900d0120582004100b05406140310b0b0b03451800c9 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 614399739 1250 614398489 614398501
    0x3060301060e090c0603091612060606081312030b1807080c2d1603110705031216080405030d0509031204060c110102012903010c08090a0807080d02030c03 68
    0x2196038503005120042c2c03810041c4030049000190b020f042c00026200c80780d07a030b1a2404001e103000217184640c66000160500821000c030084000d5403014403401b003d0100985694050700c8800003140c0305840204003000301d20210b010000aa058042e0500300011fa05003501c0c0400d04104588042c6c22040c4150720030700c00d5035035102000a40c06042e0014407410b00341040765212580d40c101c05600115a600c07216030f800400710f181115401e85541202c4400b00041e442e0103010110740081c4032000340500407002441c0d0402007240c6030900110b41c2e405191108000b00303500b0b204100882a0742c0c014090001240780d0f02c04111a8440450545a00d0b0300c56141724101071900c1080d090390f8079050010300081040e90f411803102c000300f0380d0214075007a545103840d0040b4014420b080b03000c05500e50720b07040442c00c036071424070801d4581320540003802081030540c01a40c0e0b000c0251008030841d40030030f1b00300e4045242c1002070480240304804841c0703450003001800301641c1040c0d40d00024800d001091090f = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 614400989 1250 614399739 614399741
    0x902100314063703050f0718020a0912030c14160e09030405030307052a0f04020309010f0501090b281e03050a08121e060f040e060103030503010612020405032a030a030503060301 78
    0x500c1030391b1a0010400981000005110401c010a11848403600818102c0c1d61134043c4c0c00241c060301e220110340c0e840c0001c9040040280340740c81c00c1504d041711202400c40d8419004260150b4958440f211916000d21b002007000302c1c600024041e00c2c031740c00103000208080e0345c18001494140c0c081c00c001c2080e011190303001103071844903008601031941c01c0b100342401500c0300d07100b408006038120780c010707101e5840503580b5004d8500c5c81c1140359080d152000200c1c0d0198150b00c0b42c0f10004054412601c80c1502d0034184200265402045032400c1c2488020441c16144807029107011003800500700d40b041c0c2d1b03030f0307603203458803448180c115140e050104070600c4001494400a511032194510f86080b007113135280a0107440c0018281602811050310703c09040d441e59000a80d00040e040104d441c80c0d80c1d40e040080c403641080c000c4000207042e00c80c06050200c079a0080e20705650000340604401e2403001c914002d2508074501d041d4a1001340d83d004035155a041c40081c0d4610b000c2d03203030316a40740780c0b8a04142c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 614402239 1250 614400989 614401003
    0xf0603131502071208130f060219030b0d020918030c030a0f0c030c110d0506090307110d0c05221a010306081b04051e01030303090210031406370305 65
    0x4a4051050048002103810b898180e6070200c0907040030617207070300d50400007400c1100640c005003400c00409001410003082da4000c0640201078810300c180c42c1b0300344c8000c4043e190b103d0f01e0643d001c035502c0c1081016260002c416600810010040800c02540045003415034200d048004450340011400c1c000c919007040c10a4448101841c10300f64030302440c1c2d8090207110000310090104d00d84400d89481c9900da4182d030f4801c05070000d04450305454140340480c0e8990001301d040b0b4080850901040c0941011303580803401c1640a00f82c0c82d41c203400c01082c0039803d455040b05424480f58101d004c068402548901d600080c861480c0c01402c420140004d005e0360101d512003403242e40040d1941c0c0705a1040081e4003440c8104840100703094643c0350003003070810100e01542003000200301c000400c140d056031100c6202403094400d44407150400780e00f5401c4900c240526040c003820b030f200041c942e00d007210300023600f50f0404e02120841d9003055288424000f003c89280310701d15220b18140284802000b0007 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 614403489 1250 614402239 614402273
    0x70f030216060c02131109150904110c0d0f0309020d060b0a08061b1804060602060a150513090201031b020a0501060e0c0901050a050f130314010c08150f060313 70
    0x3003d01c02c1d06902054415030580003541019586400ca0140e1401078001c0740d02c1071034020b0155005908c140300c0c04001354004003200d44030700e140403650a6004208070a40b400d101d00d40300540380703451003800152440803210030ba900030150345054000060359040d5030a08480c1c02124001034104c11041030050a040c541c111035042d500020400c0580c2d01c1000d4000c2c0b01f107144c600226104c1c440e09040b80c4c1d0715881c0c11100380e80642000d40c08290302e0350028a0a20405500c4011301420080300c000c040c43d0442c0d4050b0607000840305254829188507600301e901124810324000640111580f01680c154401d144410010f8001e044243c083c40000d00820018000700c2c042601542404480b0702d0191088410741814081c0c0401c0c40240c45000b030068510010104503820381d0b518110341c111840301034501040b03d5400546003d0500c0e00d405208088050015480d0b210b1103440d044107200402c0c52a00416603c4a5200c601c5040c81d00c558024500441d501d242c1c038481d22005242002124031a840d903 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 614404739 1250 614403489 614403497
    0xc09040b1617060f03030409091a070e0f01051b0a030f0f08092e0e01050a2a0302090a03083c03060603070306050915040c0314010306020a05070f03021606 68
    0x10520200428200560094000c13070320604040c0803034005c02d0840c055944a102e17035610b00060842444440b500220070b0314509411401d86a503610740a4940b183c040d000c2c3c80c0c000811035419149940503000800b43e444005990400d84290324842034038014440000300e00040714442c007001c42c81d8011200e20950078260a107081c0c107242481905549054075a41140803901300000c041204044100d001d0a070440c8801c01e1202094840305039000c1c0805484061005281030f070400d94020711f03401041100c910f021450750600b000d00f1422400f030b41107944250b62103e240f00340040040c454400804100401a90b8040080594203840501781c04441c41c24100e061500c061520b60842d83e001c41e60300c1001100c0345030f1aa1601b04040700200702e540c1009030003c94810038000f02900a10743d11011850864090280098815007142542d10104c10609100030a00c010720001d030341900500702c0703000709240c600e0030940c090311083c1003d14086400c0d0003607001020700a03030314410080701d600a041c042c14 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 614405989 1250 614404739 614404757
    0xc040c170408030a0b0d12090b03070e0f04060b0d09060b03070506041802160308060415080a02060f0705060f0a1413060c0e030304230307150503090c09040b16 70
    0x1141006580300030002440c030a030010020301584040c0d8481048400068240001164240380203814001d800c65000e0114031402000160301d100401203a01c5001e480c1d80350105440d20740705116038808a5000d907540151990804602807008501801220104d0700c00450341745800c0c1010300860702c004060354000d403c1840140015200c0300c00f10f034101c4041c2c00c100c004060f1110041e05c02070140006512002d0380c1d0140701c81c1410390014459005900032102000360101c0030b082c05203410b80610034030003180c2000d00c0040152030700c20040c1c1030800d0391144061602115a0700c65051940c222421039000800f0028012286014407135590040b140c1e201c42d07441428818801283c1c41000a0024007550f1a40c060b0007045104c0c5409505c07120300a421240c885480310021040d80d0310b200701e000c03990925150050514940062600d040ba0000c0c540250300c40e0b0020b200700c880340d100402400e424452065110115214503d0b0544114014107222001d03040400c1c1250f03c1c208461901e07410456121 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 614407239 1250 614405989 614406017
    0x1101020901080c070c050415081e280c060206040510180204091a040503030601030c0c023f0304090507030903120e010b120c0103051b180f030f0c040c 66
    0xc000c0d04420400f4406840c2c54840c64070102051840d0019500f050400d0b0100d0202c100540321032003560031000664510070101c014100c07201c050103805041d240e116043c070412500100340c4118041d2808044002801c40750340b80d0210342c0056600c4400145c0c014800c00003071283c180080802c0d1210080d050011854802a005c40c040020740d01030320440d81e03403041e4001c0142c81100c103001d020402010482a1900d400c01c1d80c1c4a0300b0807071300313a8003003030130030109401480c881c10110704104e0380140069584030404000d140c1c3c00c3e5400489144806903108034800b15134240c04000c0c41c04196034015607469041003801400e454020b00420145810200d040b0b0000760411480c0c3d01001764110001088007001900ca40504004a6001e070442c00d030301207400411002180640001c80300303803020b1007036858264095401c40502c0c0c02d488440030b01032090349540f41e020b0810b0000030b8401000c40b010346000200090030001d41d406100c10990104c3c425500b18100fa00074044604030794117000b80d05507216 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 614408489 1250 614407239 614407247
    0x27070c0305190903120c03140c102705030309010c050405010c02012706050c21030708040203120a0305040501050a0c05070305071e081b03032203020f0f030a1101020901 74
    0xc65210b400c0010340780000810b6902c2144558015500f06429040040f07825001402014200c18141c00248100740b8074100b011101d02141c2900c0d00300c0d80200100e000d41c4502e08001d0641c8400c0f00d034110b4500018002c210450391205031024001c102850340e0f403d0030800c0900312140718813103200740701c0140400c0100d82e0700f0080c81c81343e41d0317020700380100c1184000e00c50360f52219188400d640f045454a60202e00241d015014000074a12201200c1031826200c00c0c80020408804c00a0202c41c030810001c0c0820344680c144580152001d0201c400340c4655030400725058200c1c0c081c490020756114100000d10100b4090281c03c4220310b80301308000f280e0910010418410070502a00740503000446004008040c1d070040c065804080ca007c0320bc146030f15041e52681e05c5170001008281420f0503a44aa900c00300c00c69004868035913a20ba000125102040102000c9500a41c1580105200300700358100c28807590304103011040145599080d801d001810602d05a0150002e603031050207100a00e90304 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 614409739 1250 614408489 614408497
    0x414030c0d08031b030c090301140f070c11030d120b040905101104080a0f031409060d0509010b092d1b250c050406121101050f0927070c0305 62
    0x65030315a07960301c982c80e0313006030700c55094140003813a800010030016140800151031068000c40081c0071200e420015070341541c00030381e2a020342410003400304822501800080000a2042441d4a0300c2118400003034141406140b440c404212a80a0340e002d0886502c40c50700c40c0344040744c040140e00081e444290faa10204081d650303680390740316004889101400c2c1501c000b8200e107422280310411624010408840e0800c0840102d80304901410680100005907588041c0c050640350403c0400706003c0b01404000d089001c1700d55940c407a0070900d880d0307035600c184900d620200507600348003061003080c0740001201c0d10780807603d000e10510520142008004554811800c0c18030745030310804d088032610a09590a1114002c15001c43c03004020041200c0412600e0450341008107581e0380c4280002c400403004010091010303071540810560050000e04046d9060700c00b003030308080008002c034071603a10b4005c0c196101401401001480441d01000c564410f100d0b18041c00d8519450340c002c0c0140c01 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 614410989 1250 614409739 614409743
    0x105091609030821010b091f05030a09060204090c030e0d030e060f100b12010f0b0304020f120124050a08030708030a0c0c1203020d050601020327040e01110414030c0d 73
    0x1074001424203202e00c51004403840ca802c030250601c500d507983d00546c040c40e800081198000c005a40e000c04600c01e8101c002c0381a82c0c0c45443e40303851641c0301c031038940045c1404c04040703911613402d010105001d0820b00ca0120304040980300020031010040e80186000100c1000008160401454404504010550b0360308020881848a07503600c400c0c620a21440340f6800c940590800803400c0010649032440b1581220005150360016035140c5280511500c8104c401a400104140705000c01d420241000350b000f0880c84000a1a14804500c0d028508040d54124041c4040000c00344214a040e4580a00515810300194680140c035580d901550100815000b81556612100e0040354040c034030150400f0b42c00013600682d41c040c0c02e0080e009400a1143c032454510740400503006500000840c2c03455401c0f034109014000c881c1c0e10540034032100c1641c5582103516409040603000b024010083c04201300f0a216450b175050038000074400702010000b41c071a0740001b001394104c0d01c4403c2c00c402595 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 614412239 1250 614410989 614411003
    0x1a0420060711030106080a03020a1b210c050a06020708120a0c0f050a0609030801060e10120c05070812090615060304020d02011e08090706030603230a0f0b010509160903 74
    0x201c030318400a130042c5070741e1b0700100446c010b00680b072080540c0484d400358524071464411520150028400000010300d008001c0790f0040219a01d00c406051111111514410038005400945440110b4010085644500d015922021081c00504018007180c2d41da22100d100700c070f0820910940040043c070790410045c0025140500030400d2080500903400010b0700120b051207580d40d240790091401900b4811240001c0441c0c01e040560f290101c0000e000001036a201c0c0f40010118000c00f008207030b035044071014030100304009000141c0c2c88010340b40300ea2800084190602c0d10340031039420280c0c02020007019455890f4294255590781046d66003142d0141c444030b460662a10041c0d130741110701801c0303038140300c8099615030000b94803820f0381c0e10801103076040d90032050340d4990680a0740c2d85030000078a44c546e41620022a0641d60991070746541c4001d0494600030059210316600b01c250300026251481020014001070800c00e00084c0c0003d1000c4200442418400000f4882401400000d00c40 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 614413489 1250 614412239 614412263
    0x50c0702040905122a031206010f20150c041d06010e090a0606030605101e140706060509070f02030a08061306060201052521091a04200607 61
    0x202c0020000d5541940c420308400b03580d0341c010203176a8950fa02c0c02c1c0310b039090505040072581000300048146c80c420325501d18802041e4a600005440c844d09502020003009a6451480c205400c00b1102c800c06541002c09003035130b0b1040343ca83e00c01034503005050500055003040100040c0309010300951f011a0301c48014000740d203079040100e07483e81d0600c0e0f45a5020702d01009002d1440750741e031300030340899284e601c040000703507518428040c08417140c440140214903500305452030f40f420040120b08100c0d5a1800040207010b0395080c09003038104250655506a0b580001c2c011070a041840320b40003001401c080c001c041559a00030759a205e00c0110074208910800450740c240ca17020080b00c4100c800a078244460b80d203c020085c02000f003101c4008000c9014010207141c8070f4941e6509460499540d0380ca400c409400302a4100c940c1e0340c246c030f0f10300c49568049440c00b0900a42070031441d00c0c0340c4801c84c2c941d82050300f00404061038040342a0810320060840c0e82a030b6980d0f4080f2221158801030902031 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 614414739 1250 614413489 614413493
    0xf0904050d050d110307020f060736120f0605010602031201090218030708030a030f0e03030c0307110624040c080a1a0d060b01110c0105040303031d01060609060909050c07020409 78
    0x135143c0740003d6642c8501c084103100e049600414132030f002c0302041080381c05e25030b1441e034201d4480b18188400e264840c2c040b15184100b224412111101d940301c102d07508001a5203c14650022014000a44100905c21114010032665019190050521388001e50912032540041c0035248010310800c031480c0d42c0041c490640c40081c4103603903416400102135960741036035600d0781a1680d11280603800000c1c5403c40711060903405200ba1042d5408040040d41190340da07210305280d5a001425402c140000f100e100d030700c0180b0800406105d4407141d9008a90219030800c050030b5103c00d98001480b850400402c0300c4007070350201d603031a4800480c9030b010a049040c440e12803542e000701d14415030048441e400c54810b01046400c409014602030f83c0c0c80300c940c01c00004050b15200c02290050000300c04110800c042840303604502428046951000d03411101e60980e02c0c2140e072150310550200303078140c208006080d00001d2017801407103200400e002c107180c91040001c491182c200024410b6650307042e0036003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 614415989 1250 614414739 614414741
    0x8040b0a090f020a0605130905010b04060e13020c01020a031803170601090816050306070504060e0402070c090e0c0111012c030f032809020907030902031903030504020f0904050d050d 80
    0x1a5103a0003401d00804c3c661180d000038a0f55111440070034078804002d42c00134641c0d815200d014100c4000b104001d041c0303418110111201c150031000107a1148026508915104461008201709020000010303a81e09001c00040e050707921a2807203200040b030b211313550400710703400c4030841d0403000c0a181d02c3e5400355601401070301d002d21681c100400e00d01ca01e242010303032160041c904109890707044041700da4070740c2c80000031070b0300b48601e000700400901014910160b80c00c154024068042c0306082c80c2d1505516100613104648050000d00703259404141401160350b00454000a43e1081c04024450f0781c8101d135011440000c40f00000c1c03000d1105165030915034000b40141c1c1c1c42510700782ca8482c0c0d40c4c10100d1081105d0728140b0111001034003483d0303541d0760b901c105225a244c0c85902030420420f560315450300360300030304451400b42d816002d481172044000311030219204865120b41c4000603181002c1c01484a110510110b10340600b10040c1448049040090101220541c92030403613946d0410085280c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 614417239 1250 614415989 614416013
    0x6040e071a0711030604020a1403012d050f010510120b09100e160f0e0d020a1d0a1505130e0114041202060c18041104030303050f0708040b0a09 63
    0x1550780810044401840d904070002c0862500a00c80d81d44800c10010400d51500e90550713000358000e100010400c4641c101d80c2c44084d00a100030000201703014480722003602035a0807a03c20328074107020903040610304454030605400c01126582c5440960602d00030a1170010403615a406200019031080600d845d1500001d00008020340028490f0520300d44110f580300540c010780c080c1121540000c4d01510b20004841000c9180d903841403542020058142d81014061164540001c0c0c002c040d4400b50f150440308000800b40391107403110021034410032044400c0081d190b116990300345114400303403115900c44601641c00840340070800010704112031000742400d008104c015401d00041a000c5145450b405200b14011406081c060011b12801c07030300e030704e0101c0d64040500000d002100404008881030b0703c60b00300107000042d01c02d0304c1314000303005504603a0040f40082d80701c004210b807504664149a40205142c24010f28908150351099141c58009280d4099290785006c101c003402840b12401c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 614418489 1250 614417239 614417249
    0x60609020403060e120901082815050316080c060a0c0606030506040209060d03170703061809030e090702060708131211010b1516050102130f1409040b06040e07 70
    0xc650300ca03034900e00312000e043d201490714814010343d12144a5000c40713608942d0800c0c0c050792103050951743c2061b44402e40c00f13041c2d41c90791031045000d8403448542451082140044003250211522407414041510f0801c244110f02c4072048012800c00800f00c0c00281c0000c4c0740c40441d0340688514032120116810051618041c003120704041002017031100c0400d203a80520b00940e08140c10341e41700d9090142460000100500180b43d4010400c1ca0120213103400340c000b1486e240100300107507145540705200d00030031341000300d450759440c0ba441090f401210130014118140c03140e21480c94074600103500c644009001000b4080d83c0800502d0341c10016074900c0c02c40e50300031608504c0914002e001440d03000b088501112941c60145601c05515022141c060340310503400240d03141c04510f680c00c61106a0302c1004481e190f40920007600c800b110881c5034809450004a4044120310b01340401d0910246100b1042c0540400001d001c089a140c1d40480d070302050503200411000d40c24a040d03403070005940d201c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 614419739 1250 614418489 614418491
    0x302040e0c0618150f030601090f120f080c031b160614180402270402160303020f041a0c060a0c080a091b0f030b01050402042d0803070c060206091216060609 69
    0x8440030400c05c0c4000740d0700070002070f65221031103601c2d205822058500da0040c2400c00e031418518a0000304023003c064043e42c85146468113101051030000d00e5500446030100d2912001180b03010f20380400c0200041e1803507602e203909200751034114003400880c040c0c0702c281200540015100b00710303010205101c4600c84007602c119500c107590b5a00d44034030000d00c20110302c40e07511341c26007507038500d07081c001d9421440c600c0480301541c4026a50542c001d6111381c000c0d40e014103062000007580b50780c00000324410700100894036a1144a003c81c681030400051503c80c44c20314050b0392007a00781d071040b5001e078421103c240000705842142080030101040c86005242e120b090500810140c061480138012070b445480d06000316600da000f0001079000b00d0007601c1d000c10502001304a482c4c032a09000030700c1c0c0c422030030500d0002c0e122090f45003154402c00c41511015403100041010300d604014041d071003c600c6010702003010b0181c40200240c030449030f4031311401c881105040b00f0700000ba807000d0010901da1070 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 614420989 1250 614419739 614419747
    0x5131109042402091309110d0f0206040905070f0c03080121060e0106080c041b081902040303020a030e030105070819060803070f0c06140d05040c0803070c0302040e0c061815 76
    0x2c08041e610460601e4082d01d00d100815060303408a004040d801da600500030000c00384000c0038040c8030100413409550058040c180c01000d078944100500103070003c5078010030a450310b0600a403a10b400c94403001d00304070308070307030300d00c01090744110f0103410b4034040003003915440140354807520714030345454020301103d01d0320b43c614100300c00551001d0308403881a4140c81000200c03c0c1000f01700e507041e01c9403101010011691844180c89046510382c424505900b040031480783e100400100d030803030740040b030142e8890181202815003240000e0f21460046000740080d182602e001080ca00c00540841d80d103180f40c2ca404070409505030400d1025055550031603440c0d19107801c0c040c41e02c00007a08240e030707203144002c00400c04611a042006001910000b22484e10501c0e0103050014580148162281540031102040c0c501d82400105456800368aa03c003003242507004000031240148406a85c9500540c080c0402c1e0711040c0540d001d64002c0c6c00c20b948554003007000310ba50803000000c080300842d4009 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 614422239 1250 614420989 614421053
    0x6040e01050a1a040c1d1908010207020a09051302040504031e020c09010e010e010b0d060306060b1305040b030a151d031b0604022101140c0d0513110904 67
    0x142c403d900540e0003031940c1111121142c241310480c3c082c946182d00180341c000080300d201c15000380500780c054010381030544800401c0c1541e000303a074160300004096500007810b217040d80b400010f01d40c05007080900400982c01c09888004285003941d10003800f40b0f0700c820019043c140500c0c200c407680ca110504642d0b8001c034036a0029280c80b2010380e46445a0203090000c510000d07038143c0641a14404040f00c14241d00f031210b55541d0342c11401d8124840758035100040001600c0f4040d1800401c1418000e40d1142d0f5886001401d00742642c00903070290b80307401c492417000d980005551310910303001442c015039080c2c154000d1001d00122166400c25013000c0c40c16581e64800040201842e13200000c5076403100300e05000d41c1d51107030030076140a0350090300610000c105003404101400c0c9000b00380b0000031710071410600414031420448044100303c0001c20001c2861203503000700c0e640161400f4604025070b8840d52040f24922054880d03034001e05605000500700b003181c1800f00782e00c245404a81a0142d401 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 614423489 1250 614422239 614422241
    0xf073014190516030c030b04080d0c0f0e0f01090527010e1f0b04090c020c0406090b010e22090201051b0604020f01021c05132309010f030c0e06040e01050a 68
    0xb21914400c04908401c104100c62190042d0b80d4450a030b001c01a141d900d0f00c40d00050054000d4a881c0410064406566824807840000551585500fa840304800c540940581c00e08101d40780108610b1010400d0382e0703800102c400c25114101d81c01701c0c60288260142c0c448520b94041c0c6a1a80403000010552a410361082407050a40040c8140030802c5003840039070804492140c11120a028001409440c046400111010590744101c0f0001313042c1c1e0001900341e50b81e5521401f086a501d0290b02402d59108a400d001e842c7c3c2900d880c5400c004442403c00300b0765138040381c1603486a42c0e1a41c07e003107a00c52400c440800c406d0200101c00b101505148039121681514100d203c0c0ca124a0000c055500203c1e0300001102e00010031540030b10320000965450b407000003e100d2410783c0c22004a1118100c00e400c13807141003040d40205185042c4030038070a0182c01a0030090050b1100703542000080c211000340c4056070000f0840c5005c5445031030120b0090140001c207440b003542800c040004c900b03e5 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 614424739 1250 614423489 614423533
    0xc120c060c1e030f09060a033b030f0403060b0f09010f091802030a230f060412111906140406020a09151d0a0509090f073014 55
    0x7000700c102c82004a92032150b690f4440d00c51080c0301c5020034001c0303814030b15042018246042071030070701156030322000088840944007899050708446a40b030001e400c2e2069840c0c0c1004a90000d002145062400f01c107158650244d40f00082ca070a40300d40b00c0c450075854940c81d602076880040c0c240b00c10303540c643e2140d241d415491b01034101a40d00d4284c049154104c0030f440d20450715000307005003468100f29203602c08518801d40070349181800612010008840c01c0000d10380703080c1040d010300301c10b041c00c0c6084240c203a445154907041040c42e24929060040c01300310301c00994a4514500702502180c54100080c0c0240078034032061036092403c01c418004103400800310a416551142c2c100e030707140c848110114442e1684400051062241191500124091112450402420705401d01d681d10002084414101c8008040b0f400c51501e403184505c00300944805840500c80149040c9400d4034001c00304000c101c00c2071502d02260907005c05001d0f2040341f45000c94a40015659803440120103a007250003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 614425989 1250 614424739 614424763
    0x4020d0c120b030111090103051e0705070b01290318060a090210030501060519050d0c032f0a0f03180b07020c010903020603010e0c0c161805090c120c060c 68
    0x4100406003820340303010310032900f05021035451142428024001100141801442b000c0c000ca015040011705990700c0c41d10354071901c255a50b0301c1e6260090f140a0480c6041a40309910040c0c050072484010b0b28820042a017501c200485c10303850759186080070b10702d034003100b00b01c100c0c0e40200014441c0d402070940180d04c40b40d009642d8408481410b0384110101c1e01c003440340c4000142c043c0004015500c5140e800b4010845a280540c00c142c0c02d1302900381103c103030003c540003181c1e0740d04450031a1840d0710f8181c4005554022440401500312540170b00c90b1040c050003208010701050a0440d281c0203910203500ba03240e003c40402501031914002c0c9505c0e07403e4446101501c10000940015881000c8420a0340e45c0034200a0641e480e041c801c00c14640081c01c02d112281080c040144035550800600d0070740807544031808106450003c0031034900080c0840703080c1071401c2108001500078002480c00f201c04040e075460140070b00310f0001030308000864204981c008400900b10f540d000f00081d801c0d045d10 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 614427239 1250 614425989 614425991
    0x30b1f030c0e071d060903010b0301020d020d0c0c05250806070f0207081b1002010b12010515040513030810090c020303060411130e100f170f01020a09120204020d0c12 73
    0x5150340c101035a9041c4d0090340c1e109582d22000d040d00e01c40c1802000341c11540c01c080d0010500964180000782a078112400505940350301051016034035429010303501e105040740c02d0282c03401181d07469032070720340c05000c144180c5541402e42c0d141c495401c490782e800003048000300760342642c2000d46005042c01c0108501c03000510404402007074190300441c00080340c506c12504400c461504a00b4004805c6440c0c0102007035540c2d62044a41c69207502c0b0800e0741ca445180000242c505d009a0903245a45c0000340302402a07280500308a1500440c0c0c01e42d041c25605400c181c0019a105200200c07114801d400c04401d050500c6075000060f03030000080c42c040c0008603400e00c84054808074208843c0101c040700c0c000e010700760500b044501c0d02e400d0319a030042c00e80103024246680319a401682920301740e000003003c807184010030328407050a0181c116444140b20007036203410802ca0340102248a03034012803080c1080016402d0031903075030358110341038031314561028840041c5000c40039140f400ea9402c00c000d95 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 614428489 1250 614427239 614427241
    0x10b0f0102060702030417030405030a0c1814150d17180d0302032506181a0f07120e0a0c0302030d050301081002030703021209070617010807030b1f030c0e 68
    0x950700202e1154451500c0f40d00541c107261070903620303c0c00b4140c4110603581c180010003004c90547c6080c00000103080c059030700b0100c102c0ca404810000d4400314220703081507d2400b0f40722440d54007920201c580000003826040f840b04030041c0011143e50070500024004400503180911122a100c0070701010080c0d00e48178240010844144030350b40d0140c040090058008011100c841034590007894040c040c054a840340100300350b03840904503041c030b000c08044440b003441c01c2810891035250301c92070000880a4101c10f41017440c0c2c0400e01c54409000c0c3c90501c07003400e480001c45540c0707170701a245030346912048825004080c1441091041f55000580c083d0194145001d100c074000c2040700c0c100d172410b4004080000810240070001c0d00094051010940c0802903510a0f4000390030880c0200e019502030320903c1d141a030040c15104940c1004c2c1c00990300d02c4010009030300042003c0085030342056107003483c0d07600c00f41060030407000ca0805890500c40c061003c030500440c800c2d0b1100351101c0c6008001e072 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 614429739 1250 614428489 614428519
    0xc0102030f0d0e1501030813080a02131806051e010806040b0714040506030a0509071d0f060f15030702100603051f0f06060c020a09061d040c0512010b 66
    0x381d104407112000724250410610103002c0c269030010100c0c50610094451a01e01e920f118200c4030000e9100b0740d8403040c0030a0003003200074007400301c20040401e100102018101580460140e2048041c5403e006a0f100c003e00001400c2c01c0b02c0c400b0159108204000c685850503a50451038014143c00b420352007000004615072900007043d90281c0d40010f04c50442d5a00d2043c00c0303400c03520031218601c0c43c090511002450f501c0b108081c0d07020340303203100d40030034175107442c6022501d00305080d031110703010000e006081c1d200f00d280340300304c030b5040b104003040b402d13903a0f640720086011000005c4040e904141c3c0c00a000b0940c2030b8640145004000f59401d403007000c1c00002102003030f9025808003a0058203c02c040000c19840d0311290b5a00302d00042d0045000c000c043ea050b0101c0380d0320390003003001c1030407032001004504d065064103014100c551800c101c07407401c20030519140c561510b6440301000c06d52004ca0148100005018001e10009200244102d1440a0301d80039128003000f150142040c1c03410500 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 614430989 1250 614429739 614429743
    0x602040e0a0c050d0504021804060515030d0f20070f06032405010c151b020f1c110109020d1208100b030c0a120c1707080708070e03160e01080c0102 65
    0x498000b069842c01c0c1006103804000c4018036010380120703406a148600608848000c13000c507407080d40240000181e9107020601c4075240d901e2000324620a421000a6410340d03a00048040d82c125024540064a40d02c9034a0000c451002060084414440c140000890360f03480302044050700c019a40c141300c4a41c40f00d420341b03600d08072005071090581c0129003d0295520440c3c1d03800410340181400f8808108250207282110603501024080f000110340d114a080c0d010444031040c518100c004020040510020b001481c00a40e10081040b04100c6007011040d0300b50425806603800826000744106141340849800061807080c0c40823030047e50000d94201c10340d0715842c0031102800006c5e450341ea10f00c6106060740d403041074002c051100c00300c4d4644c400312036403044543c480030700e855641114440140b013201082d80242441c0810503038008010320306902903c000e0f04919541800410403d042000905100514000140c42c1c20020070000d04116005240390403150840190b0b0080c0c815100126 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 614432239 1250 614430989 614431001
    0xf050f07020f012706090602060408030a0c050d050f0714161509080c06010306050c1815073e03031209010603081206040c09140114160602040e0a 64
    0x412240400c0c008000942003101d001080c0300750500d44540c003031002c0f03d010b50a006081c26218040d80c1c14003020f01103150080480b44c090811070006209c14541a6100f110031310001707141c4c19050b500d4a040710002d42c043d01c281c03800448148014041c0349400254410780c0601200c1c4030740011240040c081603958003600321404048009012407000c015a1256188140d061480e14480d507a40da6107500030502d200081d10340f010403c0d01401195146040c854150384011300744000c2400c081040ba84c00804030f080c0c0410156007614031100361600800c402555009004015108010100032000d4081208041e5010190b56404803c9c42006501160746980c80b202a10758140c1d00403c0b0041c0d5458004080343d40c0482120000b140e040c1e00c80d65402000c0d0004c0c9440d40b4030305c401c03005209243c80e242c05844040941450000310b613500e4101d1842030031214a0300302e41404900500310000b100040d0403200030281c0304103020499003041c41e014000351301600c5400c62202080002c65401020340c0102c0d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 614433489 1250 614432239 614432257
    0xc0d03110316080c0c0a03021507030b030303040b04050a02090a090c09060b0d0203061f08040c080604080304021c020a08030d051b19050706140f16141803060f04030f05 74
    0xd0548031078440b040d110300f5409807400c1c103181d00910980110000400055a41a200b540944210f0807894207003400700030302400300e405041c181074003400b40341c03000000e413580250803032421102e030703100d034200329040040b0b0313031000381d0041c4c011810821401d1741c5401501c06240325001c0f240d401903036144d0700c004030360060203035201900d810030010300d2014194024503081031004040e030f0104501e07040580c0756518950106404116400c0c100000d102d003400908001b0803503180a4030251a080c0e030386514a100042c0000d10034185035035400c41a54200701038044145c1d016000307080c45502d81c24113660300d410040c0090603460030b080c001800609c5039001d034405440d400c44842d0038031a445810340384035103a07070072a201000b40500070200810b110307020f4950b9660071440315125904006a80042118000301207460100d0b40000c151a0340da030294003404070314980615a62203181c0d43e016040300b1081e40ba001035041c415001400720a0148c148124061442030f200c81d8212040c1c5c10050350240610700c80c0c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 614434739 1250 614433489 614433511
    0xf020306011d0306280c020c090c0a05070602030a090b07020c1c05120a0c080313031b02030709020903010b0306250815130b1905010e0406031e02150c0d031103 70
    0x30881c40032040280e24900c2c04007002e000c0080b031001d01105d003120a403180c0900164003450148900781413103c05c280e045420b54017000e01e07001d12036401501350b10907900300804040d400000211101800c1d80a1030501c1d034000d0a9030094144600029503500ca5410300c1b030f10a03200320845e41d02c420750040c0a241d071240e008003c3d02c0d007603640400f85075058015a0308501400260400500000c02501c010340c8111511100c103035503440e440c00c0040c4550180c4503002442c981d941503101c0980c1c2c0024208040f14444d00001d43e0310382c21800030038023404c2805c04681e010710403801407203400109101e4400c3d1410f00c8520b00c40142010b440c0407a4541d005551900700040e000032152018241240907224981010341d01140b190210404682c070070b035a01c440d4500301c900c0d410342880b43d0342e8003102e420030413641290140101c60a548810f603500c040000b50840c901c9154458000711344402104500c40c86024403055160038403441c0540d01c0f034120020300c40001c0d01d480000f80040010314140c1e406540382500c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 614435989 1250 614434739 614434741
    0x3010f14070513050f03010b030601061809021c09061b0306050414010e0f070c12020a020a060f1202070f050102041815060804020103020c0708070b040e2203210f020306011d0306 78
    0xe005ea0501a048904c4d05035413141c841460039201080307464002c0000e41c0d40c0c042081130317810940c1d441e411150000311125004022050075003840c12016070a081d030386140064803141e6450940006c0c41071603c2c10486011004d0090146501342d4004070031a40d0940b820f000042090380c0302200300209001c3c04502001c0900803c840c20101444540d00c113100c0e080c18808100f4039141c0071450003030300881c080160b01050f003400840c00d08107540c1c40102464140601d940c44404400340080840c581d0501d00345a0114800041c00f018980c42140160484000c5540700d44943c42c2d04124101700d83d05420300c0e420851b0390b0641c0454505040201d030385903a0389010b5a246c0c0d0340118040c3d400031030041c04a106801c0c01180e0071106001d46002000d0710500c0aa03114544504451108002403078182d410440e44d21262203640d43c20b2019100740c2c0e0510344080c45d00b04441402c00c03045c00c401006070201d0f01d44001d198100086500540c040c1c00241c9481018040d04881c1c0e00020300425011901a00558 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 614437239 1250 614435989 614435999
    0x19060f05100c03091a18030a1106090604030b0a02030919150203040503071401051812040b0f0c01062606060a0b03100302040e0c042a1b0203010f14070513 68
    0x101c2d56186075200340781144c0d07155902c500030a60b0522041000c502c0020004024032013185902141909407401d40c05410106480e407500c004100c2c1603d640c1d4010180019081e50660320300080310301840e4410305513200e506141044200a4204031480f184c0d510a407000820b014804e01c803034000481d802004030888045600d50740b0080d41002c0e008884610040c008500000c65040c0c5260216004c1000010326103000c0145c00c0000ca514201403080360090305c41d850394082c0c51422a4160b5029036440c80d036405065805061901c00d07419046415440c016000c82c24501c0580c81d441c45e070f03070381c5070f03013020104450341151741c69040c266036417580508000d00811241c0c010001440d030160b0f9440c0901c010035600d40204060301e00b0801e0354242600300b00080095440c0a00c0303680c40022101413801c04038121140d00b03414800303003900d0250500440b210301d1841e540d001d43e0a20080c940c040c00a04c40c559040611101400e100192120054050b03000104020700c034200b0385da251100b500e0480030f06840c01d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 614438489 1250 614437239 614437247
    0x90b0c06060d060914060f1302090f0402010e0a080c0a06140a0e031f052a221503021b030c070501050705012d050c0331050619060f0510 60
    0x4908110740103500c80394200301280909a020345c104a081c000740c005444c0140002c0c40000004001103080e000c19150702c0c0140c2c0319005460360282c00036111b10b401d6240d9000503034241c64008402a4001c55001020031030ba08040303000361803031006450030282507880d00c00907500c280d02446140148481407200540b1035210b0707464442c0751030002d010340d40001d0215104a104441d00c0d20446e42c15030702c031828000d48071078074244950718102c1201004c4034083c140f03612a48900c0303100c1c4100c030068a1114801401200e03801c07410010b100041c111112900400406006500b01964152038414048140d40c407404000c800c9907043c022083c003506040d0300b0440192003e0f00445e9044c0c2d500d641e101140c0044208995402e0103100b012019081008911b07080d003003e1340e1000b018060b000800707000307004014903810689802004070407010102c03610703222402217600c01c400308042d08603c100028420800c0c0720350401c101d04245004e040c00b5268a441146072107000d5072103806d8100b48480d02c0d4854061003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 614439739 1250 614438489 614438509
    0x18042c0127020d020406080f031c020a0203120406060902040e150901080303010b070602040909080c0709090b010512030c0a111809120a1215060912020907110312010e0106090b0c0606 80
    0x2c002e000243c070715115a14a482c005802311200392580c00007400d61a01084140f1032510700b0310341d4078103515203800341400a4490284580e01500120071001141c03c000e41c51304034002910121900710740b07542d40c4281c407c248503001d0300d5028001c16000608042e40c1064241a81601c203124000d61843c0d1804200c207506501a10065810543c240000315807298540120180f06c2e00030a012503d400c00a0842818944154003129000346801c0e251300010f100b401d040d5045171070403208821040821505107080d441043c01942c1e450081c0030505c4204007042c042d040d03d0180a940d0195607641280c0701c0d450920007a80c9488469101540d030040c0b140d4440003c2118030164901401084d801e0b92521095603070302000c1500c0c1d626000d41c24010380d5400818280181200120010b104a264002c141c002501801140c1040081e011018407124100b085032400212a9a80001582d464915400b000380c01e003d804001a40e1100004084025406550020100c00003414041d1150800c01c008a00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 614440989 1250 614439739 614439743
    0x1303080c010b0301180b160f180306090c0f1a03160e0907020106030b0708071d061c0902150705031206182401020f0318042c0127020d 59
    0x2480b0604042162001c1c003405220415405103d0796208403460180c003201c40042290340c07803ca100000300300061380142000041c0c900b03406c1031040110f03c0041018001c1d51030304007800f0981800794038010400d900d101401254480007900c59180d484080c1c10781c100b426426100300b000c2090001c02c464966403c000c0e1072075405800c00140b01c0d00d285001c175508000803a045000750759101e50410a02c00022a1280c1c80f0402d450300b0005071805240192001e15002c035000709907a0103980d0b03000184c90301001c550540410701a8044107461190a00001e0010000b0490084004d0280f00300f50307079840c10517105095401009076050501905e4401010710004201a900000e024000a1520740d00712606000360800741e40d202c2e06080d820300c01407000c0140380e0582d0440d4811062143c1e0290007100355140101b201c0c0340e0200c2c20301c0810006010704682145541c90400b14900b1099a029841e940800c3c0707883c050003488001805912004e2491142072221440d5212484107001440c0210036080700c54 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 614442239 1250 614440989 614440991
    0xa03060b1201050f0718050604360903020f070b1b01091b080c0a0501200703080c0703030906052704021201030b071404030c0501030c090b030a05060f03031303080c01 73
    0x70054804503094641c142d40a1300240f40020a00040c181c0c032050580d0104d55440810485c0c52510010403480d1040f44614006441310222030008004403115003a82065242790b00150308803103600c5c1200429620302c1c11005486900c00f008070940000c2898400c0700c01c02c06080c0d050144a03030000017190044204075034195a1048503200140c808040d000d41081e030400c02000d43c0381045002882c0680d0418891f109021074201008142c1e8800c14082d001c0c1c151408a80001c0c2034100c4092410b803054200038000100840c400000314070014008013168001c0c0e60b1000c1a80d5502d6040e1618030a8000140060748900c03201c4040c1c0024480720094880064001403401016585442d42002d00b07800c1140c08801e403c00340509a40d00c0400e801c5126194202c1610301851603039405040719842c4201c41c1810740b40c0d15010651801800310310024100c48014503a00d20384004c0b8040102030880c0c0d030074821850010100d0007414000240c5100c0d452100c881c00b045410f589460420390448100c0e000c0325 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 614443489 1250 614442239 614442259
    0x50109050c01321b060c030402040f050f18070512160b070c21020409061409120415050405090108070906150e210708060402030d0302093106080606040c030b0a03060b 73
    0x203d503003006490300c06c2649442d40c40d1a030800f441004160703401402c50310300303d50a1105101d0542e194180c51600041a4860b14500d2611406103d003030128580c02154001c0700030106400030036010070044400b0705400350140029498680c3c88800303014202c0e02402400082000344000b66285005994461030102005c0b00340712903500180948800420440b5025140c2c1034600540350910045a040740100c0c001d000415000112950700d409030f4819040325000c5801010140d40c007a0b07040f100501030280040c0c0c031035a143d003a400d0f540c5a003841400211443c044002a0b062400b4040c010650642d0780c2d02d060300c40e0107008000d00070310300289242c140c901d40c4800883c010410010b01c0002c0220402420f220b2a06004150402600d03006502c141801005840110742d10091014024282140d21808208002d1604c40c0c010103c94801c00c4114034110003c01e00b84000129244101c0c401c442c03d001036180310004405079107030600c4d1141c02800616040c030000d40603400030059807001030711240312 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 614444739 1250 614443489 614443537
    0x60908191a0106020a0311030301140f060f0703050c1b3d02010f180803011a07021c210503010b070516030b0402130612030503060d050109050c0132 65
    0x78600a90056001d42c3c03201884104240c3c0245441c905c010101024505540c900f04000b8103090b00c00c026544580c050104440c502e52f40d1a0a40d1169003010075955100c400a281c00b034002d5000780541c02c100d1087c80040c000070305130100b1028202e4400342c1011140c8060380200d4180c407103490702d0482d802c80780c41c1441540340c1c1c82402840d00409140c1c00454a108000502c45c21030300070b1040c201c81545841d046c9004928400100d80c11540351906100721141e00e04010002ea003e1000000e5102512420466840c1d1200000701010750184a501c0700c010703001200c01d040305c281e4102e1040451000c0c401005400e2020025020090080b0b060382c20b0072424010040110b400d64108681004040c014070085d810101c03038041000170341c80020040b890400340124a070f8001244020f040000020000e0107a840324048820704550000007480b9000b01440c04035150071900051714001000c03894603240030510914050411128200501c04c1c4043d14944d001040e0f00845414240305800002404 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 614445989 1250 614444739 614444783
    0x13080a1502071a091b0108041e02150313110d02030601170a05010203090313080304030c150c060905011d070614030907081c03060b030c03060d0c090c080a0606090819 73
    0x1200e0744c83c40000d17100960001543c1d01d8090b400025503070401051004200028000401140281c40c0f0300b050b00750143c00741d10010b51440b04c207411900101c80003206205101040402200680e88030300400d410007003039641404100d40e030600b80694554080d00040000d46441085030700303805c0e203480c2503403040281e0761205400c0e6401a82c1525844c1d1002400c80705200401070b083c40644015030196181c18915115030300c1100f00c90082150141030101400d00083c0101c0401400c2c591041c82440140c6407814114000c19100d84c50a080710344000314003628a0f808145101038442c0340e210564520134900c15541c854000038481030305032040e0702010400400800202c0001d414074034400140c0d2042450040aa40c502e610800b4004824030038000c91100b01c9060340e50101080e10207199030403460400380b203000e1581c0d0080d0401440e01d25500385891b800880d007442142420070a0140c2903075060221451b00007840341605a40101515840c65800c4880c2c484501d401f40c078400342030000240e5688 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 614447239 1250 614445989 614445991
    0x9090a0f0e010e07080d08070906080619180b27090c09090609070f0311010e01181404051305070e0a0e06010f0303030c140307030c030f1113080a1502071a 68
    0x600742e00031135040149060811100006880707520b045492820b0a00f0f01411456075805108148042c1c02c0010303603030341c48544640781c8003443c12182d00c100700e80c0d8440d4074072148440c64601d00c1c80ea007401c0f10315665040c1010018860585144200c0085403000305184101c0d102500c0b100e064054504148441d51f80c440140d80100c091502030b102c0d070b00b03000300d645290000941c04213070311108201c5c00300082080e0724098804004c081c2070420ba403084c100c1c01241e581a4401142c3c1c4550341c1410041881406141220304e190000e680800a5445410700440010032107100144076074062035040c8003c2c2002c294190300720380e01c1c103804104c030b810540c034080c00c108090f005403c01e034100344010403c0c0340d414081c1c1d42c80c81d90503040007000c0c5042c081145600303100082c0302c5401d1544810b0f6185d509440382c1e00080301e882084404011101074001d06c0181903000c14014111003118441c0421001d40225003c0d0308158080cd148010004224030080650450041658a980500300809403002c44440003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 614448489 1250 614447239 614447261
    0x10050d02180f1e06060703200105010303032712030b060c0a0302011424010e0a0801020d0501030302010e0303090d2105070e01180509010e0406200409060b09090a0f0e01 74
    0x40c40d04141030583e1820a050071002d05041d20f003402125224002140d400d5501403801e21075811080d500c1d62560b14002d9103c4441d03610f0700d0000401e06030b1650040000380e040046203122584684400003c0c0c40780e90300c0145c85c0c100b24007a480c07001402580303c010a504041d01450529052181040c286500d4400c2580940d440758020000b49200081d40c9600010f141460104031003020b600c01d8240500e41c40b158148006000f01d94410741d200070b414001020240c000390342d103040340444603010300400e11040700598203100a0071034030368010003076030301c1039012500a00841e2000c6808035000c502ca41c080409403001800d50420b000780c140211440b40e0807070780b10f50a01c03d0b011800186040580490550203102a86003030103e6038604d90454111042c2030844202c2c2c0d165414610000c0c00841402001c84520030948544801010041c004850302c42c9410405942d4230355a0705800d2141d00b80880d4002030202c0080c80c00b81c51940440d4055008400005510101c00b0400b0300f103501ca1102 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 614449739 1250 614448489 614448511
    0x1202130807030f111c031d030102070c24020318010c020a060206071107080a0303110405030d110f03090a05011808010f0f0e0c01050a05160b0a0f050a0510050d0218 72
    0x903002c14002c40c0c0014041d100f4081c0c0b03a0600d15a44ca040e410740c1c3c0b005c03440c002020810a400343e00c0d45044008040030080300b000b0300131503407074172039203040f00040881d482600c02e036582e240c00c0d44980c5034500e60011100b0070150044c502c2e0104007099030070046481e651351814044605010700160311a039102c0e87c040e090390380081965040ca0310000e801749111529441c801c1d40140020322203070700082520042c003589405e012800c8490341c0308a466034000e40c0c1102d6007502c5503400701c02c00c440d0300103400455401c1d600c2c2a00e206c2040031100c641c4901c42d42040c2500b11a02c030608102651058420482628080d03803503110054898020398255000224104401920780c0141c09210b0158820442c1c00f8080100400e400030413080043c03d0b90040c5071060301409070200e51440c0400509403041c6901d07500440404407071a04403020401070a10b20340c45000305207000c000510b610600c0c4601d90082120b40c40c1c088409103004100001c241e20000e04980184000c210301e4400303c800c4000601803011401 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 614450989 1250 614449739 614449763
    0x100c0816080421051c090e040b010612050108070501141e03150d0c0306050c07080c011409010c171005030102030c0705013602010302190807020c10120213080703 71
    0x2161030f0307030b40c030118505541802900303604100091000801040303242140254407250a20684151040899036020080040e054020002048044092503050300d50303d4030ac112542c030f0029044000c0340d41c2402242d085038880202030210790300541001c00c21118500c40c01e883d14103c10200420030068503d24290401e0100c20b000a900903018600030312a020b46e0107594132070207519403401c2010a03203c06401203584101080845040e6421143c9064000b03800541d106c511000d418020104030304509001c5c1400d0010846000c8180520060b8240c00d94540d1f03140300180298601600025202c504d030780b09002c0c400100e81d2028001f070741c822250700e844d40d500e40c2a60304003107080d03401a405c07800402e1a19503411140001d485401c7c01d14035203210300003401c6411480140c00910078888110400c4014421100d013060380914080d2240d11143d00b66645819484140300801d4111300c00400441c209202c40c41c100342d00d941c05801000b00b8240b90310041983e400c162400c212154009440100a0360 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 614452239 1250 614450989 614450999
    0x1a012304110a1e0212181207030309030b0c030613050604020d06080a023c15031504110405010c0204050a09120c060e030301060504050f0109181406040902100c08160804 74
    0x24050950790340f0540041c144440e802e001c0e001d154400d0716941c60102448141c03291145e2503068252650861680071540125140d00b400b030081c5802e4441102c03450300700e000180e035607041c41d030903640221009007004001c81a4804070324041c0c2002000030b9007060f800d104840180900b4015000100500d034094606400a0300510a86414581280c80ca815410742548041e44501d448011242c82e603030301c00100e50082c4c00016210031103000c3c0c4030380c070844040148805c03841c003c594850591002c603401c1005458200ba241038500580c490b060102e55450042005400c0c940c120b25444074122000003441c4c1159640c90844462014500c400a50204035480401460f07105c0c0041d0b000015004504662508400a0103403180e4081c444c018298400c04698990058100c030014000081c00e0681c1c0440010b100002002040510b00c01d441240d800303d245400c1c148980702e40706402808000b00c410182c20191444c60301120200c841c032804008891212021440d1b05041502c1542015542c52401d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 614453489 1250 614452239 614452277
    0xa030c3522080613081210090c08040809060f0403050703080901090f0305030a03090312061e050114030402091314060a050121110607050f0106031a012304110a 70
    0x140540380c5440300005818000c02000042d8641d02c0303865003c501182c030340e85151160f06405078800b51b2991034400c2c003d0010340380683c0f0340242030310800702c3c0410840c1f006020840e45140d080da005054140100040c01450400a008000041000390300e5071505a5070b40d0b1b058904000f980c0207aa419001180c03040580da03108880400900002c0080a43c5600310340303c81d42c0301c1c81209000001d042c1c1d160014000c260107600c12515065513880704100c066582c4007100f8000140c0701c64145080702004d40841d1941c060b40f071000808400b0f00909013140e40e645c0c24802c3d0040064a1038010501200004000403c0300b1440c100801c02480500090b00f080c20401e001e65a040e0001d451392028441d04055003001450f4441d0308075040b01c0d01103285403030200495058442c4090250840c061080d000303c0307510301500584112445410243d4440910242101c00145d00380680c1c40b130a00c4488400688620030042214032100090002410080510b0041c510b58402d00611021861204200e07050a0751 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 614454739 1250 614453489 614453527
    0x80a030e0904050d3c080c1309020a05130902070c090608030703030f0b060f1c06240306091406010207090216140c040203041407080a030c35 62
    0x156095034140c10a5501c3c070f80c13203200801100e4104414140002442ca8518a402c40d01ca64003441c0c114000c686800c403454107140c107003207150220700324402044445070200c0860b408144034081c18003915060424000c0070358004174402c41089410721181842510240c003e00040201038401680d0b5070452811861250b926804401400c0c41c00c0020864a04040100c0b0700c2c044d4185000505106000c0f00b500090901003071607504503001240070f9280e403030081c0c0282261125981a50760b00700d408076403d026074001e401514850340c0700112010f40c141c4520080c0500302020305010580c40e4507064030f00200c80b820180700c44200100b1302400000d503014460300b0b02501d0900720561414014804800501c602c0c980000c0015174144503403007901005008402035504014000e5580e424682443c0c410070003081007000c0c1c140101140018525000110494180e1b403503141e0440184413a1202c400390340301c29009408032128111040252100b20081c03103000341408101c1501e9101d112901894911 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 614455989 1250 614454739 614454767
    0x30e070501080106300e0f12121009020a1e030c0905060c01061e030212060103240216030f0306050613090903020a0602040f031101170c090105070c080a03 68
    0x6040500c01039a121114505444280c2030880c610080300484903200d06905440034100c0e00607001500e40b0440d04d130010f6031001030301002c5825456012104a85560b601002440621000c1000340b8440d01c0b640c40309540840261f040566040da60142c240c03d83e0b205140c03100010742c1402e000c5004401408041d034044450b85020405804440c101404c21a494000d05125201c0424900051300003500503030701600600d07003a0003081080c6100d0340c502100e1404100c3c81154920001c0341091400079813241200d4109503010103041025401100c2e2003004101c14520139001c104254800d481d03400c50030b1016200f995813032040008043e00400b11540c80d0040b5115039400c0002d21f400f000e15a18460903501004000295241c0c0f80c6010b070324000c40c4050040819002007400958842040203500481e0300940000520410319801114008070442c4401c60007001c102c045040e4950300b40c0a85228001810003070302e4842540c48a0391011841d5002ca002c0364841014034040541c404c1c10240246 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 614457239 1250 614455989 614455993
    0x1060201020a02420402040c02060f060d06060b0309150105011b060b01051b0303040b010b070b04030c0305130803030a0b0303040510030507050403080d09140609070b03040206130f06030e 82
    0x114822030000c4d02c40c10755030b05100b580c072400000a0024101ea94076401c98640c1d24199500090184044050381d02040b0f40c103911170791800800c81c1001d400490740f141b098400180c01c1015568a0080000031065000c068854036511800032030b4004002000314040c1101c4002400410500c045010f00030300c050304182d04028440d00b0368000c0b040c031103180380d04165000c440402c0f007528401c0100c5031802009484640e0b00200715217580d141001100640c042d50003443c440c9020780e03d0300207020341c3d44604c03031008048054400004001c40d203e06106612103200e841d00a188c160640c5010b05240083e400a8035503401c00024440022407500c01c050b21241d003500a181001d28080c00505c070b22208485001c01d25803110000f82d0054420401c64020b19401010603864240c155031440041034099821500300155041c01007030100e00250442c8541c00703a5000b06401414681c036040302e500080c0040740c00c0036052040d03104003050440c42c0e03c00b074800764141090003840d182000b404d90701c203008803040315 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 614458489 1250 614457239 614457247
    0x9020a06140a03050c12130302010509160519090f022d0f1b0d1d190909020d05030c0c1507030e010e0f030f031b0705031c020a0f05060a050106020102 66
    0x424041c050707500b14496070800003400d98400e040d00165205200c10800414589010080040031849280a070203010764002c02c034503522518000d548070160072240c3d030b00c0d40041500b002140b40c1040f54080c407412110114a440340d88649140a6521003a140a200f580201d850792803040802d8144000c0708401c0c1c404100181c16407103002c214894007182e400400400603001e0710903e09598000120213800c2d04803180c0d81a009002840c0312000c0380791134401070310300c125500c461510001e50000908840307175000d0450b1030b0840c00c1001b00b82c0c00502302c0c0c1240e0007600c080003080c014405070480c0c1301c8034400b03018485c0303001e000c101c10482010401c01450b0014012940403d40c00312a60164400070b00708030b2400108500040c481c040201041585407244544d03d0301c08045c0070018043c0006501c0c80700200e4803101135403030303290201e41c0078040c1c042c1d00c41c01c00080c040d071118220303518031a4180180d800d0f083e19502c4494800000d140103076000da12950500c8500080c0344969070060629100840c14 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 614459739 1250 614458489 614458517
    0xd1416140609060909181009120f02070608091203010f0e07020d0c061a0d140c040603110907140301030f021c0231060602070812040303081315020c0109020a06 70
    0x200c0c0203c013840d40c000d15884001071005000100c0c0c800c10145004100c42c00529030425980160070a04011121901149880b002041c0a543e40d4194000d03c1d8016094003403c03c0300440f00208000c20540c013600c500301e12003255480301c1000f0340c00b0f001e0030a1405581070411950804007100503100400b10b5000d2000d41c50070b0ba03031204c0703c8803a580d0b100e0004106220004484280c031556008003a0b03010806a60502c10009412084003141c2d62140c283e600c126410802c10080311064800074054100c40c5091a03d60701c1c082000341d6108149040c4000e85103d00700300e000540e0030036001128604003120560003035141907606c02403c02021480c070200c0e034519501045480101190700c14283c4c0e0302c100495010301a03282d901101e10040c0d039081140c640d43d02c02c02946c1e150710340701d0164140207040a020310700c11000200da0607643c058840c482941c54144010b04017000c04001510405141c15030340d90301056a000038107050703026100100380324246004004841030a64091307000c2c848400b281382c035 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 614460989 1250 614459739 614459749
    0x31203060a030809040906181a071202160807120e0a15050a110f071805010305120d0207020603040b06091e18010b0a0b030103170307020303060d1416140609 69
    0xa0b00e90040b0140c0d100c035803c10100e0060104448000c0132517060003980300948502910402c7d040e4081c1400b0b03d000300075004802400342041d00e546000400401192158551030780041600c805c04800ca03a54582c030b162104079080d0031100003110640025031540d44a15030003081c0c244810411105107158600c0c01122888202c00d003501181030010104503d01d4090013407009a01044041054443c8030069003c4182c0340d00d00d0340103030740a0062900301c40c4480040e034440c4a06903a07202009007410458080c0665180c1c0007018030f91222902007101c0e10046c1c03035000146001d64418841d8900a041036010031a81035401408141200f0034060342c00f000728107003c0015045042888a003800302c0c411400f079800341055088543e00004855070015625000b01c00031030480e4012411400d001c4503108082d40140300968514005a00c1440031840d585070403003035452103d1040c41c2003036030100300c042524200701441c440301145d9036200400b0881107070400b0598480c040121109441e00400a0003e0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 614462239 1250 614460989 614461009
    0x70b03100e04020418081309022109070f06020309012d0305060f0603130b090714150c060a1b02010c050304060902030f07030803101710270302010b03120306 69
    0x8000c0c1200d000b00d8255200d0760300000450701d520700743c288050614144510240d10843c800d020600501d0000520700100d442900e00e140c0340c2c0d0304105500b510301070541000e10005032040200b4024454000b80c101001500c1c18001c00c425005561210b007010000341006441c030b10300c00f11035190208840d92540602c60500d594440c0c42c10000395030307161391011031004401d940049030009000010f11500c0b0846001d1a4408c5210700d02d0b18420b6658111480d45901061050154012038100c0081070f44c03405540c1c1d603403448490b40b1004e0410303030300c0381815261a0040d40c25190040e69548100c040740c01c00380300f4041400850000380300300441e0500050040c0b00080000d04243d83d50324410085580c24010407181c10451001c89101d07035120b040c6104aa070098901c2d1500c185210000a02541815407512245424801902c2c0c01c280b0000c498001c1d000e82c01e2801c1280d802030302520601c0c05002e1111440c50702035400002c2058100040c940b40214003001201041024803c102c03159075480e0f020 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 614463489 1250 614462239 614462249
    0xe07050319060b0a09081209090c090301021c0b010905040e19050c030d09140d08030c030402030a0b011805091b010c08040504090f05192d050706050309070b0310 71
    0x440c6411000c901107401440c070358001800080000a42c20300725a4004410401d440502c002e40e0500d07480012041300500c254000d85400070390140010b186c00b60b450028006200700900098500300072003140107a65040050380550040d51902009450f503403001450018110542d02046140c034481d030a1503440201c0101303e444400c200201404002051014111014000d01100c84105281d00c010340b401403540104006d07240f9001142107149401d03049102103d800440e900c0c0341da00d40714054070301c41d4070082059030103204404168001440840c440c60081115400034122600d440381c04034240c81e00500030b07851650007080c040701d070b9401402d6000c01c0d829003420101084845480c008510780500c0e070155034010b1900107624180460b0310400c6a8492040d405c0d103052203848121200d107000702c0c60002e031449074803000311b01e03440c213510348012143c07010110440418412a03640360f14212464012400050002c4244020b00004102c084041c0000344440380c1540352040361f402c4000200c1c4a5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 614464739 1250 614463489 614463511
    0x12090c10051b030706061d090304230d0c030809040b0604080c0603071107080a060e010c14030c072306060a03120c0606050915150a080c0a14030a060603060e070503 72
    0x110303210b07010007002141c0d905030703205400340b14499a4005080354004c546000c5010310540c0c80018844071808401c440544005100c010f01c00d00d9003c040080170481000302640142190492602080480d164180114490a90266645210000d00c8142c859206080e4052203041c0820721150202061121130002c00340c07200c41c0c032956010303c1101e0b42c00080600c0311440c05510400300e046040403426541c12802944184408103820b04000c0c02c03135039a0481c18002078200450415800c544038000d5401034828100c2c00d080c980181c0343c4100800c84110080c0316980e100780c00a11407113007400b60b81d40c0000304442810746035244d51901e40c61410443e141c1000c105c1a19038800070031a05a103d403000d0080031344110402d14018203011b840241e07160407503110700b100000c40701d103008c0401c088a1200205070b817295001e0f00c4950540c4440d811035400c600c24080303002020007640100d00c015500c40c884180021070b00300d01d040b4001e81120015000030465071207060402c0301c02e6421a003182d81003045509 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 614465989 1250 614464739 614464777
    0x201c02030702120d140316030b0307091503260a0e1804030e0316060509040902060904020a0503010f090603020607030f180807080601050307261212090c1005 69
    0x102203085108440000b58040751020106018890000310308505822035200e4815507039508070b4503d0a400110b55400045502260440941d84660003550104101604072601c840d01c6044a0040c1d445004074189003007481e010400601915107095444009032100084007440d400b60b03100b110380b168203240c0c070900001c80e006070140d440e1001e4104a1000701c001027509802c0a10740200795441c8800214883d2280000005925680407080401c5503003d407101381c540410341091001922030f0035805e0b0b03030020013800a001c16480d0b0707000030051940740ba40c0e440d550b90305110800b152010150010001d00d4540301d414401a210b500071a420980c050821401e1545610021100380306007812140200495400c00034120b03100042c0c2009071041c0c5c2065400f16038a42080c103030b40d506c15100b054030f8044981107039003501c114608518080c80d010802d0b2052002c44404141060341b0100c80b10b001c0400030010000c44100034401c440c003c0e14220340302c203a40c031819034008000d4000c403409281c01000240c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 614467239 1250 614465989 614466043
    0x13050d0c0b0a1e03140609090d0c020109030b0a090c17060114030a21090504110d020a09120309150203120c0d06030b100e07051e030613020d05040320 66
    0x2541e084000f460303015004100040358020040c1c100100c040d102d10100b10042501d82c5400c408841c81010020300526010340010300c2154074249140c0181c1c10b02190200201c003103a0b10078807451040d01c92982c0070034001c3c41ca00e00030080e40d210341d101868003902c08084110f1982c01007025411a43d41640080040c0360308000282020070700c5500500c0c00c0502c140e0452580b00403e000703620003081d40c550181072580e0703001f0321003a560404c00b40c10b6154000c0000c484107403d158040c00124450380b078410f24803500c0d40e00d020403090180c5c01c1030f4042451880104610310458600100c0200d662000d182010113580c0c2d2148956030260a08200c0c6038003044680d2801345540c842d20065401540860315030600822034140c1900d20300408510000c04400178114502a20403150440000e22000a00840c131405007030700d035000030f04555403140b0701c00b05240c0303551340340d001900c032500480000007441e080c1840e000e00f64038401111240041e0ba80c80e985e503030075074001c541e44c4201240820000c0b03122a401c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 614468489 1250 614467239 614467247
    0x20d020607050a0509040513110f010519171e0a0b0f010c0201110102210601080c07120c240b010201050601170a09170a03290f0d051213050d0c0b0a 65
    0x10303005a0047e1900382000100b0600c002c04185050003080d03d4600c1500b9103060055014900740c0550118000304105402042400350b02c02030500980b410b0b294200210b844101d08800c10f0b51400e00c051000640d004808031607050442d000340d01a0070421825084001040d01e0031490740740541402903200820302964000c9150804109112000715660b00d251540b82d05281000010018410500c00c00075415501070340e0030300d0288055419041c1411059501d902050061304041d00400a2803024440007504d03900c0201c101c00080f0001400d445884c036100d004a0ba40415114110fa050405008450f41c200711002d5a60016122003516940c5450000c2d0150480100040c40c44d01c0c1c0906094580da01d42c40544982c1e001c60780c00707000382c52103880404218004c0d040040c1500826001445c01490150310348404080050b00440c03000d8015100c241c144840318003c001c00010010350329042c0003c0070300c0740f0044c020440b8080c548a2a64489450000c000d0040752290680090203810840c0170f = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 614469739 1250 614468489 614468497
    0xc0f160b0d0615030e250b07050a0b010312020f01050f012d15110304030b0f070c02100e01030b150a080c0d0e03180f100f0302070f050a02010807020d020607050a05 72
    0x43d0011040456000090041c400c1484841c501e0060a15042d500c102503000030411030400101a41e80a0500c80d80790295401203004840e2489070002040000e8083c07888030340294010070102850040740751001c0d080080c008100d007032a03454002080400d4201402e03607410f45030131000286600c500e600701c00c8100d0851524416808800a400148015140744166210300b5503540d0f118002d01380790b211031341e05d02840c00700411100c060b0002900054050103919803200c0c142c40d201c140d41115402069444060303841041c0050186100d01c485075030180560080c00c0401da4460715081c4245c40c0d0b40145020f42e0600c10308201842e4045075003201c2c000107440c00d44102d140708101c0c9040304617a1503960f030301a041d500782e46003817a03d414000e071503c0601d503009020b0240c180c0700c09000030340c422651642c0c000e003052300f85682407007188045003442a00c41481441503004120704580d500001d0411000140340f1000c55110034038815400b60f001c40c80c0e5401200d030741825038413140c50100545103402 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 614470989 1250 614469739 614469749
    0x30c1209080a0c1e0b0708130e0f0a06050a0b03180c030f03040306050c070809040c12090804180509030a0f140c010b09011401051606021303080c0f160b0d06 69
    0x4220a0300e9003d028100d2069811100d0319242644074640c1155550b03034400c140d12480036a0402442003070085120440244610440703001f000d152291154074100c544e0340c041c0c0c1d003c0d03c940c0c080000c000a0804074440c24000e44011552081c4091500c200e403890f610004141039507407411001541105c000c03c12041e07c09003001401d0303840070040c440001d03a403600075100c2030385e4003420000030603284078010044845207500301a0305454402c0d803805200c050031045220301c0c20401840d00c1030700c00304214401c42080604ca441c8150752145000030885810014182c2023400314500014000c000c03034008110381510b04079050504281806c20703401e80701c1c1c81c4c80030074400c4280d00c0000c00702900f21043d071180d20303c0041283c40c40440c0c0d0301d8440081c4c0004481d040070780403030410000100c400e6158425000d019215800151030800d2113a02c407a4080201c0e402160391a4000c201c52194500a00c105196103102400038240859102c0c1360114040c0344d40316424040d01c0c0011a9407800110350000e04c0584 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 614472239 1250 614470989 614470993
    0x501021f0f0e0601060206040b070309020901030b042105040321050405090a2a020f06091e240412031109041821020c0904050606100c0606061808030304030c120908 72
    0xd80c5da420040c0d141c90045800b00c17520182c1200140b00d50780213100700564035802030301c0b041c0c0303030f070b0840d40c42600d10306000d00180c031030035501551004164580c5100c05031030500342d583c00380ca5038a9071a04007014066000324041e1001300f98504002982d12405450489000f01d5444200e81c4660b680d4038000d020300d061001681a0812001d40400498000344025101c254225841e840043e05400e407107041c256508180c030f0700202e144a61105102064481d4405441b043e161580401d0300c0355800c0c0c0e92a20017a8150b05803810400c0103006840840803820001410705201d40e005041030100325200d020401c1e441142e640c0a904005111041000f003110381c80400083c072078100844e202c11240643c1c0000c0c005119102406c0c0c06030800850240c0240c2d88030004202c079448a808104400300280018410400030100203c04036000380030fa440280455100e02c0c2c030024521429170025203075500401402c0c1e008009101c0022761140d515810b8030342145162102880c00c100466240348075074003080140c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 614473489 1250 614472239 614472241
    0xf07031508120405130219110c090412030c0807020a060903170a140109090b04060e1c0806010905150702090c09041104080606030616180902040605070c0501021f0f0e06 74
    0x103201d44010019141c0448004688588081c1c507003086e03210f01040f0b909150380d00005070486038080c0300d038500d2043c404000e0b81d886500030390200c0d04407442140c0603550150180c0c94030040e160584200c400070030301464240414540103602954821040c2c100602181e81c40242c5000c1c1441811381a081c81803520001019040001000d005850070050031401814501c0000030740400a100b80b103401548010a40c1c0c5640e1151142c1d8006c01259281d8259405004c003074061284000b040c0d0110f402c00b5480d0703407030941000b0000401038881e40d00301c0c82c0204201540a0100d02c4158140d61a481c0d040b20b00700300c107607a42c2c0c2c2c0102c2c003409030480e45c80e00242030905040c01750007080003030300a83e00c40782c04980c001e42d00c42c002c15556040980b09006d40f1800ca80603101a0b501c502d6449100c410b10701140d072511175036801d21004a03403241c1d0020b400940c01080c1c4104002040c01100e000744800d01c010720031080055000f1100e0b110951141d8115507841031013610032072040e0440341c1c0220b0398030140c48071 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 614474739 1250 614473489 614473513
    0x3040b07050f01050a05012303031620010206040201052209020f0a030f0b1f0c081b061008031804090209010b07330b0303070f03020c1005030f07031508 67
    0xc0c0d14812450350030300f0350074000080d01c41d103464443c860494041500c08000740c2c03034100c9040c60f20716810800b180c05000c10803101080c1c0300036004010310380d4401c04443d0180c40740c052000c2c0b14003d0b4517650b6030454100c84140000b60303a025041c1c0b90501c0c0c0000c1c1d8041c00c84010b0300c0b8200f01e02810751008000600205000a805524102070f024840480d1014000301007004904000c90390512401c9a02542084000c1080c45040140c940c002400e03040900101150342c8580280744c02500480c101d0380303140025003007803000c03e002054100c00340641141040e800d00140c1d40c0c40b0700914400c0b0044890701c1c22a60f00e03e5030f45801c08984580c01800e002e40c01d507141c40b000c2d00c165100709400d0720600303000146c0f00303045485032440c00c020803600ca0b60400c00122420354000500f9411640c3c6070f06100500c08035010480c0e200d0b141500d107100b9002400d4061078401840450f100111100c0140b00742801040396042c01d00070178a50088151034000340070f00034020071449150325a0843e21181c406d50400c244 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 614475989 1250 614474739 614474743
    0x12031f0609090c020307050d08060a030b0903070309090e0a02041e091a070f0e01050306040615020c030115080a020d06060b040603050a15033314160207080d0503070203040b0705 78
    0x140c52445030b0501886941c0001a60349104851000340640d1201c084111f00602c56514113801120080152080640d00d46507680708600c241e44c4c0c6c041079000080c000c4c0c1059040b051000003071076080c0d018421500c01c8103101d903c401f08480040d0189440314001624600e0704a80070307501c0c1c611802c013001b0401c02418041819080d000c0d008005602c0040813411030350082151095202c4541d40310b11140e480d440044941da00b0150034030350043d840300e1021030030120b0010356048454440e40240310420b070741001c0509503204030030001a4000c0c0b011050142030004a21780d0746158041d90b030f10741042c03141d04e02407005000940c0118020b40005c503001c52110303410340040f806210440d0003440b000c41c2d030030f4080c1d040b200300c0d22005004040d180c18004184501e035038000c4c050000071500d0002292a101d51609036525a10a6941601030804000c604e552189420410042034130042c21002e003418420345e92030156444a400b03029000c000194107500c20411500901001300f07905880e01d540703140c81d43d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 614477239 1250 614475989 614476007
    0xa0b030f0307050a06110316030c0311040605030603010506090c09150c030a171006080a09050c0622090c0507140115030f2109090216050613050f030403020312031f06 73
    0xc0314075041203010051100f541c0709403030098a00d21800107088c0e1102e00254010220021158145621429a5031a84004c0c501030300003483c40341c031400da0b41c0c40c02c3c0d000c00d421900c0003803071284101d01c21001d02c4a2090341c0029210700c920282c1705601a82004525207a40740240c4140315101d10001070007000c51350f409101040c03130140c900100c51312502c60312840880c00356580644400034440306d00003002540150880680b141c0500c041da80f0703164841001c108943d12404074441d600c0e0060304134840c030000c0d41c101d1400400761414200300004040b42b0042c800d00c103200000d00356004003111115111401e40c045c845818420b901c50b243c0c9950303403170000b00303100741001c0036946c0200403c50401c4251001813a580040d8040d030704e03400540d0806410744025000b030051170204003035003502e440018000708030030f90090011400c038001100c5c05181c158a060800a4110840e800038081000140c42c000f543d0b061500c000c00083c0e03120342d100d41c82c0300403141c41c041c13200c40784034442e0000103500d82e000f040b51 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 614478489 1250 614477239 614477243
    0x90a0c14010525051002070506060108041e03020606030706020c03030d090c0f030501091e1101050a03090b1305160b0d0b060c012309070506040b07050c10020d0801050103140a0b030f0307050a 84
    0x2440c0aa6040c0c045d07041203000701c060181c001d80103580025915849084116030044c81107429803890301d54088051300541100c039046000d070b0300103000d1100078078082100d07100910841c401000a004040d021036220b009500030704071032a4503600d80000f04240c0381000c0c0080d0017020b80c010340d941e0362420801e010b0802400261030001c100ca664608020041c40c0011406410404002e110410500110740d5544540c800d007042503a80c5040c000000d000c00704090041101110715081c0d240c0d9400d2150600c40722842c000c0b41c882242e00c0410800542c10169800e510707690900140780d41d10080458de10b0702c9036149031403c0d9464009075504c074a1303484d0003000d10a919000b24100958a40161569903031160054a42c80407060004101d02d0701c1c050000c0610a1055082c0c074104642e44021801110141d1810170258211a00300c600d070310303484000140100740901c4c05229010304d9800c4841a0380014101c0d00c08162540ca0148040e10100480ac2081c0d4000f03040700d9888180307050483e282c82c040c80301 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 614479739 1250 614478489 614478493
    0x30d030b1806060a080402150705070302090115091814070f080624130909050303090d0e0f0105130305030f090301061401171003020310020703020105090a0c1401052505 74
    0x511600c008910240c0b84581030140185141508485041e136171520010022a4481e07104c03000c030f101c3c480310500a00404c0e84642c009203c00307130540c410040070020580060400c0a41c40c58035140403030b44400d05400f242ca240c41207800901c280354914016015242007480851880c00c00d110300030349d105444941d02c10305075481d040c04e916600d04102c03601c488401d55142409600d48007840c2030a90754005d200356a60014030b400070995035100e0600356080300005031840e40021080294030360701070110130350041c40d92a00711a48500140001c0c050781000c0c02480c10170401042d5182c0f0144280c4c200c0001c2c64110b41100e4403520868003101c40c079401844028020350a100c0002240042c098120a400205842d00241c00003101c610002c4140020640320035020030703540020158500b4417039802c0c00405810056911182414041d0a5130390190903501c4070b03405a02c408000c90700c1000c2c0c10b02641c084070040320000001d00c00480d02d5000f010800303007628401c0c1d1b109040c1040c3c50400790300050700c5a41 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 614480989 1250 614479739 614479759
    0x913081e090108060f0604090f090c141c02012003070b0f0105040c0912240c02010f061e0e0a111911030301030804050f0d080c0a030206100f0311030c030d030b 70
    0x20500c00c5e0900c61a109a401c0201400140104861034018440d044038620001072030988644400300410b84551240407001840340340104030b802d1402e90000002c440c03040c01c8110854a500003803408411b0f035814440401c200e018205018001e008942819800022110940c1080b548844c1303070b26001e100b03a900c100d1410345840d22860080d28074404459804018076000101a110482516400d401c03a040040500409000d500c0e40c81c41814400d403c2340c0e00008240f01080c1070201110406e07004a0501c031741002c2840c0c2c4284040303a000096038981d500c252120385904220f0006010700392001d04000401041c50840341701135001602da03403906c698514800f21810750302c1c0c41d16480280000f620001003048280310900781005141008800034164580c0d00d689503e4500c1035821446440049402c030f904460103150f410032045400c03442510380007400503d40781d440d11040025100c000c025a060500d944610303541800a074200c1c40c0040c00791114039000f144014010554898800c1c425002c0f00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 614482239 1250 614480989 614481001
    0xe040527070b030a0f060e041b0506042603250606090209090403140d020414090a0501060507030e2e020d051c1802060c0307020a080a020913081e090108 67
    0xd1400c0c00c403150b480c0e4161554031050020405003d0303881901130b00e80e8440750001101846141381c10721171405200d0034043d5001032540c0924001c0e15510043c4900000d200072300c0a4110032034109a4101949083c1110b2003069014a007140240c1d00b04403086d0713009600f2010655400c0c8401e02644d40f04000030001d458503003c642c0124007800c80746540088a02c0d000400080c06911460f1918281e0400c490034605503200d0001640e22a03040003119445c2080c4420403800d1001800d500681f41241c280010740c10108010100c1c024008050204841c1e80171540064441c40c881c0551950500400d40000c118103507807840714002c00c407020005200e415102d00800e0300c41c3e4280c600e81c82c9003c07401044040840c0c901800b52811000c92220034200d40384040050799100c004100002503100a103031648107900401180c241c0c0790380a92003541084c1032003801a541c4080702580014010380f2460f2880725070505d581c940c056480078400c66210421185c604010150141c0b03203a10f001d81e1041d5080d9110713 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 614483489 1250 614482239 614482243
    0xf090b0c070e1311060715060609060329190b07053a080702030c1c0f0c021c0510050403023703030b0f030111041d090606010804030e040527 62
    0x22a20207081c041440400020904e0005d0080c40821700401c0c1c80340c2c00103001d411940441307040354018004958030307200c1007058079014040e10240400002200f140b4034a149803405030800e41c4640d4511031012031254000c03c2d010501200063b01806d508207484106070310b00705607540320f0b80c0040f901b602110300350300c051405000c6070307114103410070300e00c2c401d041509031019280f4000103401f060550000388041c081c0c80c2c10401031007084418180c500101e251004070003815050b686080d040802109002100150300c50b03507200080003100c0b01c51280c1e010000e041c4242008803043c0009240e600305000e002c10f0681c002018072015101840c01c40a260002241e03030a842642c80c1c510880721300405100300401d010f45d2020440d10405044035015085660009084880c2d400301001e581300f0209082c089032141c0360029507030415614000c1d6240c200750040310380e500c10040000d8100b000030300011301050711802110300303c0d0201610170b218608248410794103409514988000c440c00e9400700400750500 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 614484739 1250 614483489 614483521
    0x50c150709081b100c1209181107171204030e030d080405100c020f0a0b090d0201020a1e02120403083a0b0f19060306050402040509070f090b0c070e 65
    0x40040714404821040305024130700903009000c0061204043c2c5110204480c0603d010201e800c56503800340c042d040038080a110b40301c0340001c0813214034007a241901038107200111030410ba0801d01000408020407181071161042c1403440403002101401c0c801055004202060717130010841c151a441071020400302c8810004a074051310980c0103500c0740c4a09038403036000c00340511151050b1984a130400e8125850144410300c12602c5815000800900b082e00380309500e40c044881c40254540803848400915494105004500502d100050901524020400d012040000118013a160b0b43d690902e80019041180d81c000001419520110000e0480c50401c1c0b003940d8030b0106802604507881810b005000020304141c000e0307440800e03000c0c1a5505118042c641e0100040e14001e18140346004060350041d902030390040c0c0c010301041c08103a942102c03081e0310922501d0410a80c2106100c2141c02c440f003648402010390300001c0404607002c022a0740010344542410b810484c0e1140c81202c011581c0c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 614485989 1250 614484739 614484763
    0x9110c010c140a0e030c0306011d01090605061c06090504032c22020702192102031e1603060501060f18030204020f0c0d021b06071a07050c15070908 65
    0x7a00f0403c3c0403009000d503100140281c405001c030b4010103100008a0b20304038082e041449655900843c020010b0b2154082901400c40000e082c06560300e0300011411900a8061213080f500d400150784604102903480200104024607050049060600f00907100a1120008001c10380c402e6007221010301c60300913214025000a428248011140c001c550104201e2241c0005481d4003001036001581c2c3c3c0034401c0042e4907400b503003c020a45403442200341510016150045280d01c009450056600420034010103855160501c070b012400b2100c0c0c43c02c0c0000c82c050400440110720002c41401102e90026060f64243e46a40b07421200c0d4401c00c2e6005807400e0402414403004060520050819401605082c0884444c0ca406c0034442e005c0c450030411000384210059002131859804400b11241403071070f0b807506441503803a2031003a8a4500040c02000d007641c141200020104a0217481001201c000345c1801042c0d80131804000c210165045065a814000400c03401d0080b42c00b07a40400c0c0b080c0c400d2 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 614487239 1250 614485989 614486027
    0x31103030f060f1201061d010503190605041a040308010303020c060708040b0702180c030603060c070302100e0f01091a010503151306180f150b0109050105090a09110c010c 75
    0x265821041009000d800c00e03d040e0001109000400c40e1002401208050300b8040034184480307400c001c1c140e04035030051317100303920030380c88030805a2420303520120208180303030070503004a0340c0d60792800e02644205130860b0084150a1358010481410340c4040c42074140d078841d070b0030749624520b00e404010042c003c51350050031540c800c000400c40c11441c44001c2081c140b01906110317040c245100b81c800c21040413600707458201000030030032000b8035060007140e80c0301100d00749450801c4070ba0348009507150002d10041e6066030355103007507020000041040c401484120300c000d1141c61241d2502e58041210541802c5400340759000120b02440d001c0341c0300c1000e420364100804659680d00b804182d03200101c9082d0b9402d540c0f4403596000d0b41e40400303203080c0c680c028500c00c40c1640141c40c1605000c1040004103e0fa80d2621036441c2d46682c1c001c8102c0c0882c0d5003480d22549174050080040c6400c1110760101030300b140b9044203035182a0850000e030084040a400801040340728903000daa00b10101c00002c0001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 614488489 1250 614487239 614487241
    0x6070f080a1803020a0b0109020f07120c0204020a02010c021203061005030c071a01060215330405070c1401020a0e101e0207090b0a1d0c0c011404031103030f 69
    0x80c4211003096104004034000715a1030300780c614a85031260420303010340058106055400502200c005628010319100008515003404012018024054058004d02c160003100c030303d50031180b080c048494100d07002801155600c0b960403019009200c1444c400c4058000c080200700121210801d5901c03441001c0c1545200243c412412202e651004066200400c4180001408141103c45a07198289ca0310000c0ba102c1d4102078029281400b0344085105c80c0700d43c0c408000301c0d01c100c0d802810700b07401000480070101441040c0309014006101c0c2c8039402c54640800c205015a02c182060079843c040d6810b40010000c4000307280c00e030b201d0803820070040ba44218070321034103003064010a010b43c2c40b2880d0054580664551282006d040041ea60307005a01c540000d01c40102c1343d01c81c1c0c0f410f02108840b005e006c14a018040c6c00110440403101e24901600d200084141a00700200c900200b2060001c114180b401c0e10000c4541505480c10341c0080c00030700c1300c0d0105000000469000f400342442c8404c403 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 614489739 1250 614488489 614488517
    0x90c0103270314071a1503070605030a090807060f0507020d2a080a030f18030206010915030b100801050606210c0c10091b0510051305090a020c010b030607 68
    0x500080e420220100020342503115051000f003000b81c074002d88134040c0350803031500881c00c1c0d025500c009841d00d000d0700c2c40f4282d90461590002000030448410307003015504c1c1e640740081c250040c1110140540340c003100044d10300030400c2c1c03030344116415181c928040000340c40f640340c00ca82d1010001410808107801040b402c01c10355542a0f40a0601003400800300b20410b6a41c1e165100d400c00e00800300071130303204d1407100072041107802003072125621001c1d4a088540c8584000390b60721010b00c90b0701c40c0f180d62011007980320b001c0d00050303001468104001106a003030626030b03040040013902c01c801043d445c0c01c0110307003989400c50403108241e50003c801801600200d46074035009001501c0f440344043e04010864000c20240f0245601d220b48110020300c4258906048548a803514580c81002c251480c0038045650b071090ba403030640345a03290031610740582040e41101e00c0720310341256030701c07104000030000c510b1020f170010120001840024070500801205142d940c0c28240c8a460205a0420100c0d034 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 614490989 1250 614489739 614489801
    0x150b041a1e0c0a1203050711030a050403170706060b0d0f0603151a0a0f05010e040e0303220f0f140705060f0a0909060b04050111280203010b100305090c0103 69
    0x80c000da400984043c3c0d0300a41c1d482000d20715071480100030070b448104101c1c01c00e400c102d080f00c41c1078461001d185071031503500300200184150700008003141c110b16145400d00d4085000c1e114450307801203080210a44030140003286400c45110003808078140f0182008040e800c0c0a06401ca03075105003166001c80c80301204501038800e0034007061500b104049418415920158400014204880c1455134582090001040203180041841c00f40d41044400307011000e00200300c07944070b400480c5001c0c0c140700c8401d02580031580c180018014014030007007841172000c1c1c00d41513500c8506c2824046180903090803125103031203452284650040040c860420003484440061500264502d0801905a12821200121500c50f00f00900628011800b4801540c0208408080d8080c590080c0440850304824004014810340c13070000b80c0005841410031900d0035040782075101802040403582c0400d442c1c0040c020602120b4001051055901c44c004d40d50103441003440e900342c65440101c210009050b108 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 614492239 1250 614490989 614490997
    0x180e030403020f0609130501090c020a02090117070e0903040e061f0302030c0706060803040627060e01031b08090730081204120e0108011202040c0201150b041a1e 71
    0x25804c060b0811001805d90f440e901c4401c41400c140c000010386c1d5040c021103030304469200c04403000f594030003d08140540d550902d01070441300c502c0c024500190010941500744001c40c0e01411601ca080c0c1c0900070300101c04000780066409048a4890540e5a41f080101290380c0440100ba00b507082800400454400e40055600c00310510040d460191913680702c1d011542660305c0f64003150004074040c0030315a070000c00c000c0c9a040701950000304000c80300989007005080c2c811101070040d40f2011654990094020f1101042c40040d44038103030f4010340c0d02600c2c2060031200079190380204034012070001c020b42030311071000e01c0c00d001c080072403045a00c01409100c28010140d0b08410280120500c5101d660705041c0b150344507610103d00000724200c0900000c2254405034103005100e80140300301070a12115254064044901007903091070703640164010664110098003083e05410f011481c07000b804010401c440120b84117a151703c842c0f4040c10400d0080402c192074103100c17001c401c40e0810f1120080c0c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 614493489 1250 614492239 614492269
    0x6070e061c110414090612030a08070e0409060c09091104061209080703020d030b0904211e0c03021b1f03060f03031214010b2d0f0301180e03040302 65
    0x203800503162400500c0e0f500190b01140c10510324080c4a803113400e201c0c0c00190802815140001c4440d0040340098803405800c400204000c014400100701c2481540c0703a601d4a00058020041c4800a080c030501900d00c028820380411030010000410f51101d1040341c0e410b016441d9420305103130404800b00c6020900024640c4982e45a0a03010081040381004083c041d100e038004100401c5600c2e00902603525141d07603a0311402d2080204804241032890f5104844c01009060990200c403900503910360664000c800780f08802030100280c0180c000240980d40760007038007241c0d054000340c0c0084003990014200740303400c04207400700e0b0b002234805002d0307010000c142800c000c01e00390344805150f00803010691082c2c0000f610509010100400c0d84119142240807416040256040c504038006e1032040c40ca922490003076400d4045244000c0c01204500400710a00881c3d86004103000d1100e283c000b030244400001034002000b4401d0424403c0d80b855040682c051f605051850302000100c00080d050 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 614494739 1250 614493489 614493491
    0xd0c05071508180a020a0302042a030b041a0a0e040f060c0f09080102120105091e13050d090e0105010c0606150f030b0321090105070807050303060306070e061c 70
    0x21503100140c95048101d0001665801260702d04401e000030403040039003410895402c01c81d0603001685518404ca4280d0390191b80100d00c3c5819030007120038001c0701c10300c3c2621122501032094255030b07260308045140c0508460a0100c1d80260480d4a00844500d00355603200405039801c0107000c0000080951090141d0705030480c94429440b8031040e40d21a05034180000c6d840124095401e8019032440042e183d4031000b1030400c4940c3c0c05011404806003d100c1c4113880300400500750105031000307000c94481140b402d5116090037108000e410400e9101111030303000d0303507946a000030f1003403d00c070080b180c490303e00480991814005481d5500462419911a6100c101c003043d0ba00142880442000455464410248180c00010221041d41c080e09120390003101103090070003450142c0701000025007042c1d0369984100c00050b1000d1254010060042c0780c04601e09003840302c0413001d51b20070002541518610750705d08008441c0300d20300081d403030b80c08941070010f40e200a803031039080d840810318800 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 614495989 1250 614494739 614494753
    0x10c05090315072001200c0c120c040e1b040e0303070c060b090f090111040f0b0c0106090501030804141507060b03010608030d0e0114090c0111190c14030d020d0c05 72
    0x100020785556200308402c51b9103e50640700302100c2c82003594101202407a106041640c802000754441d40c0002c07460f44200c242607240d241c40101803000f0000040c00600410409182660454076130131151040044a5030581d007000083c01e02d40910004012518050743ca9a500c4660a80c1c150100310000d60301e03c1e540b003800d091181c0743e05540e140582c20282c8617803210316000001909444501c2851081c0d66010b01082040007841c40510040d160b01c110f66039120803001000500400042e03200400050070f1000001c18411004010816070354210011b07411401c5902c1485015080354200001c00c20382005850049003c0e91b00c10300786010000c0002c0b40c90b0b03965400b014034581080500e00311044d41c0b17420310b451036407003413107000046010708000031060300d4111703515500c0700c00c2c2d1210340e8140880002030b404583c81c10b01c13801d0300c1280d44504914132036100d030821040768800750050000340b84040b44144070030715000685c0d44050007141e00820664140309400c460391072014404441c1449801 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 614497239 1250 614495989 614496017
    0x203062206180b071734091d010b0d0203181c0201140c0306101209060c0806040228030212040b1f06050d110403050f0a05010c0509031507 61
    0x20140071002801c80808030041c04041c1000d41e030060000d0504001e201c2000069882c1c0aa180d03503031079000c420346100414480d0609800303103c02c031042e40d00040c3d119074448030521041c1c01c0094541a20103a00001e16622340030310725000190760a000b07601c1101000d2018200e44d2115800440e44001c4501610010300d1101c9500380c601014034042d0355601e500b13a280411070507824484c0802544860b4508980741c100b2144100300381c8805040540100d00348842d5048050013050b42900c401c018141c00c100d040e4840c200880106983c00103031000070003510110300c03149021300a5075002e52002c2c0d400f02c680b648090102001c000b00c01300704400e045c0c0a01082c00c2c5086c0460072144075500514242d50a841e00a081c00300642011101c8a94141200428410680d2213015078078201402080006c5000055005c207040340602d510040c0207104141d00010b640e000412280384940c030902c000e002c0c0501c2e081c0c00b980e00e801030403211034255010001e1000c4120340c0400c0c1c00d0f003205c454248209030544107 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 614498489 1250 614497239 614497241
    0x303020c03031504050a23060f0901060f1d0108161b0f11040204061236031205011518030f240506010c06091104150602070b04030203062206 62
    0x40710040b0f04100b07440c50b51003460400e4055a903000c091100100a40c0c07240d52424800c400582000b1050034070a0b200080b980d84800f05c0540a00e82c000303294000b1036039952001003400318801c1004000600d0076000d4010140881500800d40d04141c40c0e52840d983ca01410304d80e03c401c003800301c0c42000107142207490340c42100c4107014403490081300d41c180388111038140780418204040c0703458055803041000300017250340500d01e85400140158017107102e1340c03c00103012400b80c61060142880c6801503035988020328070804901254429192002a84105a869011074400b4403618007158282d840d01101148907004c003030071501032003450000b600d84a4031060011042440222920750b0803414105461460204085442a0780c410070b100a01d04a00002c02e038180c5107200512040e00c03001d0f40c1c8100076030080400101035014200b00401c140c950140011040c1a01c035501c0540240381004c100c44504104032400d4075005030043c03401d078890707a13194113420543d0500404040d803400c101800284d19 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 614499739 1250 614498489 614498491
    0x3020106230a2913091802040c030603020a0b07030915180b0703120902010302090409120f02030301120b1902040909120513140d0503120709081b06070303020c0303 72
    0x10020041091021103418042d080b0001d421162843c00e0144800261410b9001d010f8012920b0900030b41c0c80b0700052038440303030904490b000240307481d003070481ca9140035401d0b00d40d10348000e0080b103081c00611840c400070380845020f030002075080741d16808140440d5408000814003a8482d2500410745030740ca044101740ca403980a003200028420381040b9800550017242a0040e0461010441c54011682d9000c1e100d082c5c2112003000b41a1070342d012070150b81c00f0ba07056035264074010300140951920340ca031441c0e00b00d000c0d012030804500d01458102d6a03620000917a070580d01141100e030fa5604058442c03070284180100001d07225055800e01181070b400b40c0c000b41c00146007882000c9070b46040c910b010b540e0201a2045407040000920441e10034451044420085400081046c400c10348040080ba01e84c411542003d082c9210000d02d88410400010074180300b050b859840320307004c1e0741b1842c2c100e8030341004a80c410306e2415058551160344c54101c2c020040300303210341801403a010f185212a425604 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 614500989 1250 614499739 614499779
    0x3070f1428090b19120e150f070f05070f020a0b0f03010e0f2a160b100801020a020d0f020c1e01030c02010e1f0207050f0d020c0f0a05010c03020106 65
    0x11401c650a68102c0012400741801d40b0380c050401da4503030b240070544030350081c50504100c0f10040801034201542e0125010000000644150880f0404202140502950080c1e0000d07404000144040d21588102c040030490340d40d514a0701c902502c0e103c0700c00304500001c0ea803120049034000740841401c0300a040d40d4005421306d0341c40e076240c031000c0611808020721040d550404a403c0080000b170407486c406c0d8034030ad0341d0214107414071510801c0d001801581e02d190481c18041807860300784001000001c0c881c001c000000949143c40720182409e0f800307040d0021016038003c40b0b280e940039000726900c1858804bd4811202969244d20000346100340342c49481c034084d00088110421541d0501840308c00c1c0105000030700a204c001c261182c0d9540420005c181c88103590b420b6132a05042ca50119403415030404210f4101542d0350000c0c42d1940c15418060025100c1c0c40e5910b2064101000441c80004006205103080351801c00196407540c0c98003000c40031950b0b9a0300114001c1003902c9413004040e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 614502239 1250 614500989 614501047
    0x30504060b09130c1d01050402070312051905060f0f1002190f0b09150109020d0e0109030908160315050c090d051608011a150c0f0105040b060603070f14 67
    0x43e001e043c440005103103900070101c00c0692002040c603a1144014850444a007075400607a68040c81c2011110b4a0070742e05042070103803c200074400c6850b1034140080d00b041d0005820440b50711000d0400046a60a510050f00581081003440eaa8900041c01c010b40415a00548400c96800242c54048818ac03180c2101c00d041c0890301c41c4203011850500c103038842a0300e40108006401804d41001e0b5581c14411020075640000d01d0109011450f04110565003e0600a00641c0310518000d05a01228040c29449108501c40360f000040c0718002002140d80002c4507109030700c07140302c0300d50181c00300402e02d040e0541c003081107041903122054039195040c012400b51094400e4440b006d1400d460a500410705607040c4a401c50480d00070420303200310060121068000c2c0500205546540d019019403c9172074040c581e191141602c040d00814070513440754601d2922a5141d0013003004c0340c08103035040c1c6d00045464450138819805044e1110a481030700c490740c1d041c803225010600041881d118410800 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 614503489 1250 614502239 614502271
    0xb0d0822060305060310050a11031306050c07030c021009180f110705100c0c05100510060507120c2a050f040203010503250e0109020702010e011e030504060b09 70
    0x4011514080340140005203410301141c24a40006a5510000382c400154a60f6840100704131050705d40c80952a200440c16803030301d902c0c2c51500b0315403442c1080400d42d2110300349030006205420017421200000d5144d1101d070a100415020b0042181c01030081800303100c3d0740040813500c038042504c0620b84118494001c0b0740003c00f203a50300166401a03141c030311104d07000e0000000140020601404900004d0390000f000307040c4150859042c0c58100307019019008641c000311401210380c0200b441520041820030380d240e43d49404903030b58400d1030000f0b090b1300041002078042e1845290044061070084503170303516040001509440b0010300300b035100c0154203481c0b000c01040c2040f0713040803034000c400c5a085045615101c04241c550340d0503002c00509840003440c4011358001180c031301000d441c104010001079a11140c1c5070000350310955060307011680e206140c0b141984103803010424014010310440180e00c240c00c1c03c0e0090705001d40200c44c0c280c0c8886442c40700303495055a4901c208071000c0c1031042c07 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 614504739 1250 614503489 614503537
    0x50c07021002070501051204020319030206010e2d1305030c03040503070e090a0b0a021c0b0f0406030c0b0f0c010e010c081609050906040e0708031e18040b0d08 70
    0x2410820070051419900165410800ca80e000001d54414140700050111156a1480000c0c140f0a82c5200c0a01041000250b10103250340041e015058401e440328034051904c403c4514440a843d1800d14840d080520031407658001d54850b00365001540c4202911094040b035a80c4c5d815034000741c441c0107003644003040400c10340ca010083d880081c46408142c1855003006c503d4940c0303035000702c0e0002c4d01c3d080554010030150621503044070000346071800340000320070140703221402501108503c51311031103031080072810502d818800d5100320303640001a0010f10785898510a01900b00c1240490262401c0c000e00d07159000a001b00d45c01c800d035601c000100301c00e445401030b040c2c0c0009480040080c3c9510041f900c05034011030403106550040701d1003101030b074902c0d002501801c0e03145952502405042000200724074000007510280420070b035054156501c226120540e802018040c07115080c00c140c244080b410107a01c02a6084400703050110090752984400d02c00f507001d46032401003145400c1c00070712 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 614505989 1250 614504739 614504749
    0xa08010f0b04020c12070206040e09010506040b0303120718091b09060c03170a0b060c0a030e0607020d1101030e070e330111030c0d170106030917030c0d050c0702 71
    0xc071009003100d0460030600610590b42d556001010002002c420029500055548040550b0300604190b200303043c1d03902d0100100c9000c0c2c0740564086004900741a0781c1e481d40e00e404020b50714a152560354074800c640d41c4040480301b2104404130b80c400c0085499000c583c140d6a0b0050b0304c0540b1003000e908502d601c000c5c2c002880325007994010700030460011110000664410741200c1c0e000005204080c090702e030004140000c004400c1c02c03e601040c00074003c19000004501c0c0c02c0c1441c065143e60307084102c81d1007800064032504030000d5029000c4034401002030440b05a40030050030614000941d0310348070034100d1801e0456000591b4461105040101d5180003103070b0b2860001307001015400c005100030b44060f6102c0b00115640c1440018100801310900070400c0c0c510800e4031804aa845038150b01c030140620014800c40340c01e8645050022410074000e00600310042d5124107680d4080101903450809600081d01507400110100030721198030100d1301640307010303040c810b107407964800d45841008 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 614507239 1250 614505989 614506001
    0xd0507020a050a03031707121d0709150b18040513141c05071104020d06050114030105090c3007020615011d010306051315080601140d03020c0a08010f 66
    0x203071180b41003c00c2400007a030302c6001e48040d4000302039508069155440d0035252841042010b804042ca00064482481a90f10321490204084400e1703c0b00345448502031016a520031441950203c9400d100b0440700c0c040000038204000c910f0180803c2c103c01c0301c00642503070343c03c0e80d0000c040c0e40700034010014010100003040c055031070000100050b0360240d410000c0da00b44a8501c80c02e0040119000d0240100c80664001400300180110760b201390007000c040040499004040c0090803031844403100f00c040b10101c9060700c00050480580365281c9150400d154001912101c0401a908490346208115215050701c80500c0c900300c00345281c01d0710001e1400c500103042c6d441000110101c071a95903045003040544680b04100204003146240c0141d002e07001c154000c1d0f030415038050582d8412009988801709048034070b074200c00400c1d59020415a982420302940120480814032a003851030600e40c24100c00d40b00f0300640302e000b0800400901005070f82c1e80034501c1c6946031a0020f0007e5203911541c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 614508489 1250 614507239 614507249
    0x50109060206070e0d03120501032d17031e04030e0f030c010f05030c2503090501020703030906120603050613021908061303171e010b0a081f080d0507020a 68
    0x10b10482c5848200140b0103401001078601030440100410145032043c01014010b020507807081c0700359696407900030500180b07031500d0084a00c00c0403000b0401440718152842040e0025071140300e00f07020007642d030303a41e500c043c000300b1041000444040000009454662145001c2d8a031a860b50701403205100c0305405e010807a51281c1c004582d5001030b680c100c210582081020300e402130710396842d00600070301d40c4542e020035035210102d81813120408040c050b625070381d1381c42580c620b000d07aa80c4130300580c2e440707441c1e0000030f000c14032964052141d80d00c10000170040302c0501c0d401141c4580c5d00d4a800d4281300f01030b1804c1d050455207042102c1582841000f18800704100c144580e1401d103849017541d105d0302c01400001c45060004240e4041c14030401c404003080e6091100d0880ba420041c0480464002c0d124031440702d48004000000c084000c14240d42d01000180c4410480f984e40322801034544c0d42407400c080c2d00c021030b00d0340440c95100030424840c1c0003c0a0319456a202510700400206048036801 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 614509739 1250 614508489 614508493
    0x1b090105060316030e0f2a0301140129030403120b1504180b0301050c0406080108061b0a1809060504110301150f021c080f13120c051f02040501090602 66
    0x7840103401d024694000f03000c1051030006040400341200604080c5c04d0301980d204d0f407049225140d0a81060020005d40701000303503400034010300c0c0005060070399155200d084805094500100a04841d001061b00c168289500428505001c102480c89580080c2c07020780000d260080600c02d8007000384261491408210340400e40c10382110070f27841f004e00c40c6000c0c1d0305003844410904046501a5000303016a00d000070300921161030060380e07081c0540c00602c0b501c000202d070a03000142c1004007084040c0100702c20303e03042c401c0300d045010b6852240d20281180040001c4c2d02c00c1043e043d81c0c0303141900040d01c5080404102145070030100b2007901c075a02583c00d04c2d050100010041d01412480744090004903090501d01307141d550300c1c03d0b8240030043d005402d030f00041181180004d036018418078411031801054071030315114002800d100d03c0c0c142d84018110b480030f105592082e401001d100d00d51a01c901c080b40d109180450301c1710102044181c0f417011003500032505000039a007207a6a10701a10032440 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 614510989 1250 614509739 614509741
    0xf0e0f07050901180603060504080306090c03090604170d050906060103110319110c0109030f120903020c04020f1e04030b0f040807080d0605180a06080c01120513051b0901050603 78
    0x80001c0318410181302d40486062682c1c00c0c43c01c1500160070810046070085020800c501d081c4c14610030f1a44102c8416100d01d123903400081c3c041c00c900301503c0c0207001000003011155903c0d5200140d06080c1361107440ad00c071050043c802c142503240071306841200c0d400041e00290078810005070503603494156400c1000418030400114000304584024000850400860400b94000075060315100f8144542c03000d50034920710809068104030000c0740c0c0107040d41e5072512400070312091404c4810141000b00180c204800c02586d43c0340680107800c1000000707960781d2a0003220391469508840a030480c140020000c10b0800a024a10543c90b500c020150956102441e066680344e075503200780306000340801400f04948050301c0d00da0307010401902010b86240060488a081404000000c0702e000861310300f0400007240e101c4c40410f8202d00303c41d068484100082d040b081c2030000e4040200750b0081e540716501c4090204108200c0c1009501c00c1000c0001c580c40440c1c240406014142c000a01901d0100 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 614512239 1250 614510989 614510999
    0xa06051c15050a0e07090b0f060a020c0d0c0504090b01031205090303030117190609050d030605031e010e0d1106010510090e04020310050c0903060a0c0503011a0705010f0e0f07 77
    0x18007150302141d450040000d1550719148400c00501500005a50900c41d01c038000c43c070240c5a034001c13582d0000865021864075400d4041128510400104078010b030081c0355080d49608040000411661007000101c0d1010340710004a0101c170f110710419200d00350408010030a2000020400245000b60b2030b02030b15104581c1c012039903a100c10f110b1000c130006143d94040740b40500f405511140115a907000c1d80c0a0598140a00505020ba50684481c02803088401c000d500a1050b0341c00c40b9000b401070100c600552800340c0c3c9200e000d0312041c80f80d5407126040090b002c0c0c2800050784a294039207070b07a0140a450b007205490483e0503088280510154101c4160080c1c00000503022611500202d01299582c0d1000c80d041c481c03000d00c021006030038002800000b1036104042e0a07a84001c0e000c50b0381c00d6881c0300c001070035200c03104400c00c00702e04100300501000406603030b52002540c007500c2041c9440c800b0740c0c805003101e81c4c070082d08000aa031000c0a010b020010720036500c1000d100c3d8010300d2501d00340 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 614513489 1250 614512239 614512253
    0xc030629040c0e0111010e1204050117060319061803020d0f0906020a08031e01031101020f0105040b0408030403090b0a1715011202030615040b040603060e040c03020f180a06051c 78
    0xc3c0e0030035040c400c040c000342c3c04030700d401d420400c0080c0c81d002c261040c405c031494800b08503810a005540c0441d1000312100c0c80720f0b80706010740784100b000500609448a542003d101d04018400d0107595240c0c0300d904042064440c10041c640862199000f0302400002110003030441c20021800401c02102400800210381d0020322032401c04e8100144c1a0780703071115014009902c401d07407069240d511a20000006028290480c3c0003502000c1c0c00344d44810003c5024207088071030444000b031204404401103404100881c01865100d807180c1001109251240c1403400c03240c0005145030005240d13a88140c416003507a40300d09401c0f41c2d0600101400101601c000781a40c1c1012020b511016804400954145c4d90300003440030203550144050f0b038035170304c03250082403583c828010b200c0801c4c14071174001103041d00c240400d8415034000c040708024506541c00c010700040303403480c100e40c44000072811712443c4034180d41c0b103230146101c24000500c091a220038001f03074507054134040428411310881c0710041000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 614514739 1250 614513489 614513507
    0x3010b0d05100815100b13120c0f171005090318012f071a0409020703051324030b06180a0801092a0605090103090c030629040c 56
    0x30101001c612581c1d0108940103080c1554444012481103003900040000268113150150760640c4030024400c2e00c0d03030704180041c4609080010b010a41c150100022034403014003006a900c078031424060a90350b14403a402c800856082070324244803204500072404c1040106900d102e411340428442c80c9400c1120380e40328051115800c1080802500c2044542c2c4241e00c0c6219044450201c0100280c040301040d000300007208040d00140b01e25400424050680950f45000c002113403000742c070b010f04020b1160080d4200c568202c05100c81444907003046010110090068803421601c045004000303005031f140301c8412a2030400f032605d030010581c9543c66010849074031148609401160480a074003040b04441c0e0340c1d00c41403880d441d0003211030802030343c2880031100c5000e14056040d041c0d4061980c00b41d030701103442803d01140e400c100003095135000f60010340025000d00006001c2c035659840355010b441226140e5045400300b800400407880c25292002d40074441554200000d540b8054054220f0304 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 614515989 1250 614514739 614514757
    0x601231005090f040204060f08090a0803070f0509030a08091906090b1315050304170405010c1401090c0f0f060302040812031b0706050105132009011101052a03010b 72
    0x1030010b005071102c01c0450b409400141046584c0c5070b469000805c02051600440000b440c03500c003181a1100000300002260340040b8150f01d0740e02d890304140c0d1b0b500742984031882070180a10503800303250313811b1049020050142900c20765406842042010744000020b03102e03c000e100d5142803025039405285e2500340c5000540d0169142118400c64030081029449504000b010101c11001e00713511001a5000d503100d0001d900210300848480e041c18040c602816002407411840350020038001551719144100000c00010399440341c0c0c607450700000b210340180030f245045801c20042070403287c0c9400d0083c03046260460030141081405070b01d40b000706041d04450000840030484603071100b0b119105d410450215203642d22518071b80035010b000c092040d144601409404010403524a026074207001e8a150f00c0d0240e4000501102c0d906608034030003041c1040183c502c5210401000d100703080c061002e84516801c0d02085d806005000303d030503120b110000401388010002c80041400742c0d800e0a0f = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 614517239 1250 614515989 614515997
    0x303050106210e10020301180606090b090d03031b08090705040204121205090618040c0f02031b071508010512010e461109011a1c0e06012310 62
    0x100f95a0a545004600500800001c0c80000005000110502c1c000a80100004140070403541c03840e003559004614403582e40c400b801008540218a001a002c14040303100f0705000850405440e03201d1000c064011514001c541d1030390905c00d41c42010407808004040449080d032910b410503240d046681000c00d0010051490890148078060054090703a548110192001e0748036850f01a200810940444205009a15000310070118a2003518004030940068004510340000980a032034610604c8101d41c109000e1960b001c640710700b09080c40e91a410382a9038801d11541130800700b03c00c9680c8000310403181d0380b400306081d13200c040c0801d0a40124800c5c00d0700201c500c846441c070a88001c07540e60303003080340042e1403900700891380480003424020340502c12940c500d80304401803000081c000c1c0580480703945400c40d1000e29809005c0206500c04400d0360803200108006e08440a0b00d540b10346151180d01320303500500c0440c4605000440c070400980031074144020001c04074041c1c03041d540300c0c4402c00c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 614518489 1250 614517239 614517251
    0xe070512070513020415020703060f020702090606130e090d0311030f040b0a0b1f08060d1121060f070f020307080d09080c0a030e0a05040e0303060d020d0f0f030305010621 75
    0x3c52079074183c4000344601c202800f400c207401c100003903e030300140c0401c88095192100c0315401a01030f1080e220840d6024003c0406070b00d8140402206030001d40d84c1180f00c2c25661400724400d4050340ca024010000e120052284c560b040c00c0c080d0540380184c242400b070500a1080119154007076100740e07005038002e01400e45a0700c4051f0014041c00042004680200301029140d015042c143c0c0905886081ca035114810368494008001041c0c07582c0d040a00b9a2102d43d820b43d00c82c2c50b2000c8640000c0e0007110180c0d1200c51038003146800d1000803181c400744408a4010000c4c840c2d0000c81d03107858402c407840990f26181e595230340c0003014020012440c41c010f594503007040c03c008454084804440e00320013107603118812482d0080030548507a0300c260003001003080000c3d25040c140504004031040d08061811651260203104080300f58482c1613038081900300c40800801c910155045078640200340811003122030341030140c140c8106a1102040100510792207000845444100c101c079442d900c1d0204007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 614519739 1250 614518489 614518519
    0x2041a0c1c0908070609140306070c060c0201091b03020102011b080f04320f03041d10050a06021005070f0c020d060204260c0406050102070611030f030a0e0705120705 73
    0x2210b0080d00035501912650700d010030503a810060040441d6200c2d610031191108140078103480e0300c000d80b1803a020403c00440750000501c3c7c1c0c1c00010035009076200024111145444200078405c0031030141d0101520380d281401503503428010f14251865185032894090b10b075002c01040050002c001520170740890700481c0c20130491000040800c0c098200c102e0795004c2840c02c0310a120a94030005a052103030003140490118040203070780c00c4400302000e030041034000b06401c02c3d803180024505071910500c5c1c48046a02d64400c4880c0000d800700c0c1d802405201c0540c0003640c11900041c01ea10207005c4010385c1c0e0f91099134403085640c20b5540c10380d51140b001c00a4603010300640210f03080640d001d00c40e03004003404003a148400d114041c801200711040d04841d0020310040302c0960003103600581200d0070a0040e80e0082c440642c02d8903a4030106d03480c21001160004035034101355450502c1c01d0722501030402d028030400051001d400704071008000c022110302e000769503000341d102d0750317000380ca43c5280c402c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 614520989 1250 614519739 614519747
    0x40602030a18052a060d0b040902060a05071b030b06300a0b130503040b0a020f122701050406030c0504080a0c17010c09030807021306030602041a0c1c 66
    0x100c006841e2424081c900c07440c0c0303051900c9510280780c1805141303880d07401030300071480185180e00e440c101030502441d00c5124800e000190031080400c1b42c00c140c0b580261070060701c80c48000c0c0070050f81503840700d44820712803500a00d101c29460f5201c07070783c1c00d01c1c5100340302040c108805180c000c601210150300d2189030072003802402c0000c4d071044c4c0500b65101c0880d101100007088508003140b00b01d8000010760b0b03c5100b01c3c0c101d142544000750207a8000d0009205d1800c240d00201007081c2d46004451003c1000d40b0010300d440b8980503d00c0a1107804030341900d00c400c105030b48003001110710501003080003c110000b402130285103e00307810107855840460465001c0d100b190003912038170050321a524802d0400588585003403040d60101d8010b900480119003040c8140a1708a0b916a01c0300000383c50350b00c82c15456005508240e07070101c20640d0312000300720a403040500640c8110005030b16685480303500c503020010000c209525070001c0040c0c4448101c00f060f0950041d04c1d038800c1405c80d46029504407 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 614522239 1250 614520989 614521001
    0x15010210020d090b01091b02011506140f0403240207050d0e0105040305060108010e0f03070c060f0909020a0816111504210c12090302060306040c0302090604031104050c12040602030a 80
    0x24200608100000c035506c2031682110340c51500c001c1e14252040a10703041203080347c00906003811001800030302030010a1207044040c00c0005602e988904040c9c041034090141e40c0b1552080310101540350043c05e81d11254400300b564002c1e04401141041c1494403100c2c0c64a400d82e2442c010019030b41c4011506a005005580c003031608070084816a41c0c544d490203000303203031038030001403288108403842c2c0b80385e20004111214103900c1844c103070806140030001d4420b000c028840c0c0051100d1800c01254030620351018290540444d0340390007a600b0040e11700786800040409100070060040c00715444520b00041e0040e8010071404412800d030f9450401c41d4298001038a24001d0015040754000220340c00700c0c41000740d40c0148000041100d9854007503c5070f0415210003504a03100380001001c5290583c00070002d015107090140c9408955000614282e1240d00115000450540d12040509140c030403590711100e1150b18500e880c00352800c210340210002c2004001d5a00000020102034558000b1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 614523489 1250 614522239 614522243
    0x1f051014101211071124040b030705390f1207020613031b05040203060a05040504060b1c150c02280203070e010504150b0d0218120601060815010210020d09 68
    0x1a00c031801817a040c0a25080c6103503503403058401094041d14010031600d440340081220310518901480e1409920040e04002e10300414000140450354505100300c1944001d80050460f030718890144441c40d0011266002201e015940420121503a106002803414607001e4003241590b1030341c3b06840003500a1107a81c0000d011030304040790010070007003060721415940045215038615941c983d01444124001151a5a804110000100b190b414244d0107150800d01807400402d106464002141002281411003814032071406100c4080c07208007040128018440e440500c0030040c816002940d40d0100300981d5902c41c101c0d4402c2d201e5081e21803000c20381e543d02800b03441440e03648000c80c045281d002d1282a00890400d6001c400e0f07583c4820514050320405440582050a107031007860080d045400107010000c12082e5008a0b503603180d4000381c8119110000340002e6040100084c954140604042d42c82d5030b0480107600c85a0b0007042c2d000202d60f11000c0140ca0302030300087c14029107106180 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 614524739 1250 614523489 614523521
    0x110c03030f0a02060a09080909062107062a11060408060109050114030d2019060506040c080f0a0507030f050709151713051f0510141012 60
    0x850020740c01d0050202c2c4419074080d50b18940d20080c03081705890b454180104250010400c0482500d0070190356038001c20050001e001580184408030149070500c00b01251035403084004015070365000c0a0300c0c04100d2442200c10040c10041c0c8056044c1c0a040d000400b100901c80000e001d5440b02c0b0192002000000110b8000f03507900c103400d100801c420700420039500001e2100442904000a280b4003540590717a40050b21880701b0034504201a10300200c203824001e04d401a4800344800312208011030281a0008440c00c2007800c11044035580c007001001d02084008103c100002401d50721790020078041d01141c0c96540131011001001014070456401d0710301400c2c02580c9034401d480c0d400f0390301440b400c04010100320074140d51500d00d80b404c03403c03040707505c8000a04442041101e1500c861241381119014003048103801245005c05030140c2450743e6401c1003150311302440c10f5400051118452203d404848032010800d9046044069428003a1302c0ca02d01c441c403809a03000c084000c00c4c0900d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 614525989 1250 614524739 614524747
    0x51b090a020f030a1a1908070f060806010f050d141f0b040b090102010906050c030f0c03100314011b050d050c0f07020f01110d050703080109020c0703150b1804051905060106110c0303 80
    0x1001c2400c0c0700c0c1402020035502c104100400c04090344032849e41a2003554841210903501c00d001140c00b03101c0d00d030b0a030f803c00c0028460034800c000d05010f820031050342014544d20a02d0310304403122010880d8030b005c03800442c00c0301c81049120050011a0300f602c040c008210f5451058000603400341809650081c10709142a080209001c0c004001d0350082561800d0029107031904005045540815620807450508180f81000040d000600b10324802c84484004600e0380c1192124034000d4a080c00306001180c8005403840003602203204071540a5443c145a6007060041e481150290199000c000e00800400ca13503400903038004c12107001c41510007011280c2841100c24003c003950044a4124049078106001087c080d034140281c130a104140d80041c8021031070764940b0400004e0540584010f150f492820381c0c02904e8140d004485050014444621340c1001d180491070045081d01e0030502082188403080000e0011555038110358480c0391402660014442140c10000c1d1a060380da89803000203 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 614527239 1250 614525989 614526019
    0x6030408031f1503142509230a06080103151d06070e030708060f13080c010f02070308090a0c18060b0d052d0a020a0507051b090a020f030a1a 62
    0x80c240c0b90b543c00a60380030310403003034a522514085ca409032a02042c00c10024882c20000c0c401140c00041c100356031811400540da41c4800790010f03d0302ea918180b02d0800521514041e0a01c0f108000040c001071500180030342c5180c8840707814040c01c02a007980b0503141d2015002e1000181054280c4003080800d6651783c1c200b4038000361a910359840401d0090142c4000045c0110000c5101032141c00b1002c61039420b903440e40f000b4403100c01d17005012641101d00b40701c00e8501d140309125100c400b8104840050380e5420504001d40100801012140c0d0795200111110018003c1ea4144088035400340c00d03407602c16030035080103000c0e0000760844c001040021405a81c207401d25045540104010740a65800c992040703520030380c00a80c0c841301010381d005a4085143d01805034010300d1540c0e51490b01d01d040482d02e030340c0c003400c0c1881040c060304500c0034008110700c00d1a04c41d55a50700302d01314140461610b8160180c0c602c1c18000186000d60041d0b840707407120864122240400c8c49950001c0c420000e900c0342c4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 614528489 1250 614527239 614527259
    0xf1306060e0f07180e01050d050a0f0302030408011506020d030e28020907020c49052802040b031002191d0a03110a051002030418060506030408031f 65
    0x3107a0200010340341340e810b0148964482681c006903428040d4030141c3c0d03030928050004035006e4001c115514400e84920101240b9601120480103219901941e070310351508040c02d003920916000d04500c0c2e000a002080010b0300000e218241d003d640c20081603513042d40c1c20060610f041b0450315040052814200e0940300030a00102130118401c5503001c2c40d9071140142242d0310b0807002d81c0980c01403010078010040080741a401c60890311000c20b803030a081c640c500204002c9841d511212501d1481c0d000317105c10400b061011280201105440841c41c6138403541542500741205000307070285590707410746030590314144607403002002142c0c825541c801c0c00501e07010360030350600e080f00005500030741c8080c000008510201e9410034011b0015160300d0450302c0e00603004d4002c0b03040707e41c48042034500240a031241850305074190f0080d000346489034a0404043c0e051415000100134491804106000d159038020540341c000b600315403178903101d98548030a80198000520140b10020f0b103180e0006402900c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 614529739 1250 614528489 614528491
    0x200d03020702041a060909040501060b160b0601021203010623160b070315090b060d0e01020405040c090506070b0702070b0c010507120b030a14120318150f1306060e0f 73
    0x82560204800c0804d82c03100c02040c00015400e56004400300b0a1403844e1401d503660940242c00384000092040d65401c8e2110f85502407085200c0060803540004148120f19a4188c3e0004081c0040e000b490840d886c1d442191205000d51070900212410540303944005000809100000c0c1d002590b0310041d1041c2c0e0043d44400c5031007120302e182031074000b6145601c02d0144c14084201748020002c1030b030a020084c0054122110701940095003408410418448c60103050f401b0969180010b99840c188801c0c082036804184410050200d078060811582d250801150081c68002001d9640c40e01e40075022801c1083c6036000b501c00300400b00e6803106000042d40618003802c2d10f51034840ea02c41da21460310050703508500c80c260349038005000507000304281802101d41129118103459000e00c0c5405081d402d0b40045d00c42c1901c645012405400d198003c002d81034204c010b860020fa0a464000101d031482c6900801c1d9032900342d086160790b02080720729000301020300118407d5401d81e1411a910040002c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 614530989 1250 614529739 614529743
    0x70915090911120d0c172116030903021005091908130f0302011b030306050d050601050f03030c06150105071208061516031d0d140607020319200d030207 67
    0x381003881141c618800541c124601302191604200100030752141500c64502e0003005000311001c02619840c0b8580400c0305041d458582080621414000c00507580c5442c414520340615103005030110100e500024100810f01d00080b020505a5801c1002400c210b01100c01d420568600103c040030883e010001c1c00942c500406c18824550380c0f01480f520002a600c000b03030104600380c2000240c503550041984006001e03040c04105590b841c004101d9480609006607001e8001030300601152034851403120b86510120001e50400054036025601c03a203000d03181c8404c20112b0360443ca0203034003d00983d07840c903400114080c034440405201a0181804540d83d0f07104151001d40d40c00c1a103080002d07100d204c04622403084600d0740036a01a507501d04c00c00040790b03010b07403e04484a05039459030114542c1610404040014008140c007251030f10a000d00f09006540040c015103480350010003461035003000a1a101c003d10b03a51000b00c05100111f01009100c0d070161000501030300e60140c000f0050340d8 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 614532239 1250 614530989 614530999
    0xd030503150f060d1a03060106090306110405090c07060b0301140a2307030b012003130b04081902121e120723031605060406050f0405070915090911 65
    0x20000c80100403503601e0b4124038552101c0203000c880482142a80402c0420000880000e111041c0c407001a1528800364000e20000b003d0038414820028103000380e081c003550025005040074145400209519401050180503001c049401c10a01c112074200d83c0d0104000303802008031083c48030715906880c01c21079004c1c01e0281001110601a00d41c084044a24003000c2c0090f0b846440b020801c0303000c5c22003030000c91304000d2680c190791508840b8055a84043c445080110780d100d4108450240ca60065400700c50051001d1000700844800814074000d04001e02c0400c4103140420302c0040c00105585c16003100c1071003200700310b44c0c01e4a1611402805e40b441e000c21107510006203a4090118071070314800510740c07203c0f00303484810007180344507000c608000b030b0080e2424400b2407001c45c03103000101d11068815510480074001846818401c3d00c2e000b003940501400540f0301921202c2d60380351241711314406541e03104030350040384031600741902c0a4003a2940511a07640c1c103017010080301b6140d40d0030328428 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 614533489 1250 614532239 614532271
    0x60606080f06010f02060c0c0c090a020d110f070f02060d0218011b0507030209071403040c15030615080705040f0e06041422061d16080303011a09030106050d030503 72
    0x96001d00c2c60503130802000e500808640e03070750710540d00494002c0140b0220603c1060703c81d007550b545400d022403140300001d000685130f036000070300041590800c019101c02d2050130403e0504c038091040403a0043ca801a81c0f00405000038404688903110780c104105206101203603810030300e20508816403024001740c0e40d1070008084811901d550844200f002451944092000c00050405c06100c2d131b40003a0302d041c01030061083c00345a5510340c0c01200c003299500d200410901250515008941800c12140f404004040c203207010b80d10f44184c447d6285e01807251910000d500103100701c088070094800c440c5040400d503030322070260900800a459141c465420304081c504400201859144202000d10b240308015203041d0040400d50880601911055101c00803003c2d403480d1600f110203004015002000d92001e4034900d0300c00c031202c603041203065030001c000401800101d1809010300003c1021b21561303a10403c40020b0040030b030b5500050304110f41100343c00905400c42d000d54454550a41c4200c49 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 614534739 1250 614533489 614533501
    0x905160f020c0a030605180607171f180b031c0e04020705073c05211002130f14011d09070e0303120412090e1009020c0703060606080f 59
    0xc81c000107440b143c1001003000d040000c111a40c125030f4001c018148100440010460f40b40d040c000b0072621403000c82e0140fa00b0b07069180004a002d544910030070b01180d140590001082c12a805501c505095100200d803540b01c0748040361310886200500600302ca51149041c10016990311a444245001c1030b05445210741c10308013402241d040f50390100c00b40c0811810318500406003507001c500c0030002d5200c0d40004000c109550305040c40e85015880400015160004112624411a4004150101d8584401d0f0000302c0011028007101c100c80e80540c94140c00c4208051640752070b408240c040200e51000515003086030884016041d0a076192200180305910640c1d2100762210025046082900020000e510444111101c04001415a407400e0342c8031800c1c060040090b50143e444a1041442c0c01001d41c100c2020f000400c3d81e50800ca5262401c81d40095006e038a40c031480b04840d400140740c4100d46018030001b005150b005904008194403500000c1c450f410880d43c0080301c10b088030100b50 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 614535989 1250 614534739 614534743
    0xa0b0a1805071805060d02120a060207061d0c01120515030106030b011a1305010c030c0f12031d1507051e0a03110906070f0212071701051f031403040905160f02 70
    0x40302d1720b4050004c048480360341d42404001c01400700e41c130002d13000c0c16211000040040c0020b00059000b1350300414516600d81943c0c03100c03402030400040d1075105044003c10343e600054803241003030703c030140090395a440490001203201200070480d81940303420300210820040420041c103030f8103080c036842407011b0444030344829403085101186100013400c8041045610403881c006400b4460301d4000b0280205070b581c9070b80030803405811502d070800403140000c003035410307c1200c541da01a0031028000a510020164031201d0820199802009680c0040c03100c500030011201035850822000301c81040e07982890449401c08080c5a0000b0b09040c401d40c03006000b8000d072408280020112454254281d807000941140d43c0c4040ba00004400007140c07000005001820040c4807c0c1c1031491004529003510b400c40d0401400844105141c0c0b00f2412000f12824102d4181d950104100c080401c003112498518040d950051064504020400c1000e80b1503243c0841610019101c001e1003c4040805907 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 614537239 1250 614535989 614535991
    0x30d02030403050f0d09030b0703110d0b04050a051e0c16030207080d031505041e020d0b010306050a0b0f0c16030f02100906020c100c0c030305070b0a020403050a0b0a1805071805 78
    0x900000c6c0130120034004120164a410707040300481c140002c42d4000c5c10042c01c09500302c2c0030030400c802d5580003a1029410030740240c550108041d2020002407402403142072110b045440e00b03c00e45010000060300d002180422503c80300b09940b40d411243c0c0340351038000d60790205070003441d046000c2c05010701200e9000303001c2c3c550340c1d83c161014107070a18204001e0000401c031806c500d00e0300300209001407413042d405100070106000103030303004500041c0b49000581500e400c1d600660090105100410100701c84006881c0a030b000303843c0b25039455004030340040c07404c007080b151040c1066800e81c1c0002005008042407240c035100343c2d59444860309000054501203160701c00e213005070b00030002000c92490985002c8840c503da9040100b09449641c5445001c18020b410840c0420342c00034200c0d09000b11008515482054414150310305400c60b81c800340c0791664808000c1c0045480700203e0102c2400d904400c580140820f44c29032050240d08119a03101100d100300f000100c3c403401c113080410351a000b51 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 614538489 1250 614537239 614537263
    0x519170111070f05190305031605070c030320030310090509031905030a09080c010624090b030a0209040f0b0132030a0e12070302240402040515030d02030403050f 71
    0x39070308101c5643c581c0f0300d00a0852100f01e81501454806905041620407200c0759140a55074160b102d10340f01c007410100c803040580d5681400024071080002807003455011003600d906183c28075904150003c88030703031502c2c03050700046140800710420181d14030300c1203060308403050b810b410300094440c0c940103600e91050003040f000c680304070746449407540d000320010340d000880c00a00041c3c0400030f40301c0044540140840b80f03e16510794000f04002c0c280d84404030401c1642042840c0280840003003e02244418403035850b0500700807000408020803039064440750480503100380131547e02c50400400030200f200445000c550002c480c80043d00780101e10781d1142043d80b0840c454400c200c09480100d0300700600d10101161207098050305214140700450b040500c002d54661103182c9454003a09000d4080c0b0481d0645075103020b0010034000c0911000e80043d010b443c0081c0c0341d01d41c54403104c002d4446040043d01441002c43c0c0d074101c0b50780000200100d80c02001900c110310100b8601545640d090484 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 614539739 1250 614538489 614538521
    0x60810060c11040b1216080f060c0a080915070c0303060b04060e04020d02040f03081b0c0603010504090c0f06051b030a08160c020904120807020601060912050705191701 74
    0x507510283c01e2a038000d101482c001002c454880740260407203480c011509030074145021108404001d2404100600380c1d084820703102601203807500d444059a14086c0c80d00c1041000402004508400428031098095000743c80314140303140342c626400303850002e95040450000f41b4100c3d000680d41c8150f0165819030b0501d568120011041a0812010f5002030180c0e143c080d60030840055005042c0644000852107080c810303032074420080300c403e030800c01004544102c0d009030b8910f5005603038200031641500d50448000940e00304500344554064402d4001c1c0d1041e04d8a0f140c041402c60700311000e0030600c140c1d0501480185680160303a0307103034025091244041145100401d00c0f00781440302d803003050b460707074034003d10b04400c56000034007900000d640c2550102c071048036424141e40d200350070369030091040c0001d20403540340050042c00d4920f948030310602804040320b45401c011090106100800e401411640d40070181e1944160b101068030407024410100c4094100521040c010b000c2802c080320300c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 614540989 1250 614539739 614539763
    0x23013f03270e0f250c031b03021e0a0f080a0203072f03070806040303050c120a1a010c11010809030417010f0506030a0f080d060305010212010302090601090807180e07060810060c 78
    0x6a850300302074171084080c84103150f442c1070112800000450028001e60060a0310300300c1d480c540f40c1b08500e00c064464160000d109100200f03400581844020b680009103e80d12840301c40120f0071401003401c01010801703204185201203201d40f203c220407101c0c034804607400a07824410155284800c5c400c0022581089000be000300b4081d0340484d51144002c0202860901c5509183e6184c94080b00c810001980e910040340040c01000400d070709808083c200707055080703101c0c4c50310200700710652002030400c041000050f6113a207050080d00d00609640490448050503018254041c0046140e1041401d160800003521031900140e00c2c590780307806c1071452400d101c0a45914990360302100c00040310544503040000001e109100900120134185504511035045104005002401900c01410082c214100740a44c1c10041031510171510700030f102c165504c0400d200e41c5d0180c038010305041270500611100142c42904940405e1040d544503285021780383c2c84450a84012034413040151108038a04 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 614542239 1250 614540989 614541061
    0x7060906050c1c0302041a0a1b0b0a0504050309150c060714031902070b010b0706050115050d091b03031707050310050423013f03270e0f 60
    0xf14011040e9a14507016181644840907001310340c1400c0c03e400048070700058140702e0280e1002c0c0038541810703000c04240701880d15440c0c072040b0b158003074502025541e0f5000850100001041140c0d0003202c05489517200c21036180308600160032180d940c000d14029440052400c5110b1002c4c8503905060010440c190f48a450400f42201a2a200008400d134200196408118207070b4440b8000d11138046100d545860724580b04040c0c590692044070040014043c011311702c0c0d0450203907805015001400500040141040c803051600d00e07100c565100710b15071003c01819880899842c9c20385d80d8040d000410780310a50b088034284000c9030b507640d500c01c1c01c0b8130900c100d16182e0010b0704240e0000304100349164079400c40012541d001e81c41a6400d06c00d804c0d204e03216544803213100c0900190000d944120040909900302c61b011040002020810344044042c0030f17070b0f08083c200d8840540340d16800c02c029100e0101d201c00d450306603044c0b1038103002000040d21203a600b210001002485590b0011940660 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 614543489 1250 614542239 614542273
    0xf0301060e0121050118022403072102120609011208270a08010b19030215031003060f020307030608060601120c020703140a110604080604030f030f050907060906050c 73
    0x4000048883e09000c4203050210302c00340a01c1e504400b11182ca40341d000302901c1041844070700d0b80d0f42d060300d07060600b205403041c10420302541e43c000c4c45070408000740b0800703c5040d0415090100307403951842c07020526407282c02c00b22040324031526044c2e4031265580d1700d03040c0b00c01848162000c000e008003010000400040d0600107141040444100c9120700b0503071200c0011920b0314242c119038100c5c0e5441036000c0b040c0c941450340400c407040031240e8a210341d013543c001c11290040441207802510001020450005503012010019504400d00308100b01d00c0c3d081c0c81000e58001c0d21010002802e250000c50701c21408039409016003016100d02c1004100d0f404020050031a440c800425030044d1007000000c82d607030048000d41c02e8003040c05041510103e1405220f03201c60542564000d240502041c000e0f82d00003c1c00d1a00300340c05050100c81d43c0c40241c0114003400f64109900c148a0420090000c4980005040400d60390907454509403940c83e200200e42030302070000c4002442c2d0050454180341418 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 614544739 1250 614543489 614543519
    0xc03090a171b060405011d0c0f270406050604060e1f0b0d051017030d020f0921010f02160201270b1305030c060a210c0e0f0301060e01 59
    0x100400c0c10b410071010180c45100040203401000164000c0c500b00010880280324188502e404001040b43d0511503000c0e00d9900e40692a03503500a01905003a41c4650350362941e200e0450015103541c109140111038900c1c2d1504094500301c0b021800c010104189252502964094800c0740d0312200640c3d0361488540d446a00022941d48100b08802d0040f5502480d18014100c00a64144c085410305015a00c014845142d038800100221840140ca540710808012074040e5890345102586619001c409005988948031007954441d400308410b41c03000d24440c40c00700c1800c40c3d0344001c0000480078600b54099224031303490805c003482c0c80201c402c01503000f16801a0b814001c00110b0700d00320180d50702d40d090641030f904003141c1c3c0e62002c941c4107602041c008504001d0070065024294089445020035400d0103080300000078000c1034422100205d902c10201d0060300c41c004001d01c0040743d1a0700c06030182c0300c6029600d0244c01d100e9150465810140580303012501400c1c807581035a8032700209005100f403 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 614545989 1250 614544739 614544773
    0x3090b0f060d06020301080d09050a050907050f0c010609090b0603070e181c020a170405030307060f1808090f0603060a0312020a0c03050105010e0609040c0b1b031306080c03090a 78
    0x1002caa041d101256140c4041c60282c061070004001c5102c0740d41026100c1c1070361303a12151060f60482818402d0303450780c0406607048041400c1c41600ca01c2003202c80351660207007204c207210a600c1c002001400d5402070300001c0206002c0c90003208180c451b54103050321801c03280038042480090101040c40b000351441e010320304501210680300a81010503444009210701d0440a006a2040d64114203010160364224000c288150102d4074152410b00880c1e243d01a820003e00040c2e5100f100040d01001504490400c2c5079070003004038100c1c41440c0401198200b012800e001e07110100031640300d0f0406504171303402142d009040200e070f00d103195180c90429004013041c1045000f00183c10000810300040c901c0a18400e10000c80c4640c1403840b01c0700d039480010007192085100c00103103c00b00d840a00b07484150b0700c07544e08041d9203003420074418030040c030820300011a0b40b0000585002d5141003914960984110b5580e40d0405c1c1c84a020490284c001910400c000da08001701d1500003c0c141124800b16803 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 614547239 1250 614545989 614545999
    0x5010e040906050c04033305060418150b0f13090201020a0f1a0705121302120f01020903191502070c051f02011407090b070c0b0417070603090b0f06 65
    0x5090340d0b0b540403e0316001e070f0310941c403500003150510030000031201d8003040c48118049841e4a544500003005c0e440ea036107520044050b901d0001c2a41c0b41c44603004400881c03603441c6880020f992901c1c2080300b003035106008003412461b00c1f10b403002c20319007803921240e4610000c10b8204403401d68034000307006000848089055204140c00c5400060103102c0d0040482e001d905034030342443c030b00000c484507044010150760400c00204030103c042d2030681e282503040b44c00203128000b21000d51000c1044198043c1251000307106052003251410815002007001c524141c0584045078101448d2008141c00403200524001c01000307440290383c5664060804c80e03000c1c0f41c100720744940d18404103c807051041c0180c2100c1021382e9884284580902580c1240e95130348281034914680141e004207d203c0e1405007450b101c02c0080c80c002403000501c0c801d4040c2400084d503a9845a43c0c0500c1003031400f0f01d5201030301074007503110700284040c0a8031546100c9604414111303065038407011646050000109056408 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 614548489 1250 614547239 614547251
    0xc07080d15030c0608060d17130503011e060b0702031e03090a06080402031b150c0309040e0d09120b070509010210090b1b1e071a04080316110705010e04 67
    0x311481d405460700460040080c50122824500000c1c4078800c0140854000c002140780240001c076105243d85209402c940d1881e1601c044d02c9100c0e4140903a0351000341c1c90340c01c00301d526420300c0b030355500744000303a10303180080000c0c40c1d580480f40e84c83d0041c480040c2d03158200e40d6004074076904880c46480d50340e080c00300f035a1600d00c02c5800508040515004000090408400c01c4118141041410f0f400c0e607109842024032110003000442141ca0340c45510742044001c01c015290b548100141e80c040d2000500c14041c0d4180d900f071040c0d6800d690345c14040011210000004c02645016051320001c0d081130206440d43c1c2ca40074280c0e281e6014079010380c1103200d45c1c0190300f0702201c640325010405100c0d030300b1000c5900303100403002c512101c605001036098804000c00035000714a0081510005030020103d62200154142031030702135402c0705143d4039060030108020070402c8241c011441000fa0720a07050300000707900760413139401c00390740c40c03080c440ea02c00c00060206602940644040680050000c654 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 614549739 1250 614548489 614548511
    0x1518063003021e16090902101413080114010501211805010c030c02160807090b150304050c1e0d02090a0204180f0c14071106090a060e03150c07080d 65
    0x2d42083c1820f41d0700c440e0081181101900c0304914464000c001c890317400d2000155603000181d2240807074603502c00740308410034210801020001620400d03c08409036100440e518030300740e0701800f030000c4080e10b24510440007050541c0503100c1c50070300d00018115412028100e81480c4028101800c080781910b065900703030f85c001842401150001d884031759010034131044046001c0e103003003000005003490340c1400700c05005082002441d10101c40800c030b000303d02d46401d039010941000b5588440201d81e4000001c0109100700043c200007400e209541c5030304401402d040740d40d04900d403208900da00c9000c81d400030f0b000d4980300060542015000304011301d400d9480360103807265202078161000c4162540020041c0d640f041c8034050400078681003060700c202c400e840c4c03111180b041300f80061500c001c40c800c05c3ca80e62501c00586103141d20142c04400426115030380588026100400030303100e80324ad04030b0b80840340ca0f10490580902075418800f801d0000310765070055a500107500348a00c10f039071180540b803 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 614550989 1250 614549739 614549773
    0x804050f041e020d11070503090301110a0c170d02040f031e151a0a06030e120a09050d050c03060705040509090d0e06070618080c0709050702120a03151806300302 71
    0x86c0d014891002150380b054003000341802d4440302521041071400c144044840c964000c6802c1d02051303401404500c4c400101100d006050041008103a629840802c01141040b800a4854207072406503c00103010109a60380c00300b16a95600300424514102805440c404d015030419070700801e055400705910800d0b6030100f4040e29007075100600007503c4010081203180c0610861040c45010340e411880d0500c0a10701030400f00c072a114413401043d0080500d01885420f00c03030504031800c02030070b8a031241841c81009046030018001d1610880c48031000c0348800c00d0000303e0140341d441e5920b440c0ca04583c0c04042050701d4102d40300540e040c03500c400d414040c81c100a000b541420340304928558441c200444860318100044c2c01101009141c4014000d0340354000604159902010422690f00c00343c51108a016100c594050724101c0900040030544c0d4899806140030f00c051100c00b00300581c1c2e01c050304529202414000e101100001e000803488618402d10242c8040c0640101c1d10800c1440d101c041c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 614552239 1250 614550989 614550997
    0x903180d0b04050106181b080c070501050708192f1b010204060f02070e01031115030f06030c04060522060305030d050406050a1a011110090804050f041e020d11 70
    0x3ca1a940d1920309021500400317140359100d07100c8250400c082098066801301a0307540c505100305201c400000541214000c0c8100c88401d07900200910071428518005050341406451307410302030038190004900007081e845021000380031405c00161040071008802246950600110210308003004141c0700b8040e82504001d8418200d000140d032140740240003040854003000fa5021508600010001c1c50805001c181c1541d030041502203040c02c41c0400075801c100100b8104008100200410801d409003200c074500c06c0c00c0507405d58407010406c00030001100c3c0315008907544001842c1f1074604e041074110300420b01200204c070008180d030f10703a26003178910740040342d074208440c2d100c404020800c546405480d4001c12644d105002c49600e00c002e036001d180d600500b840c1048400c03100750400d02c0081001c480840b41451042003200900e04041c2035683c03003401500e006900050600e00c01742454400e20000e4040d542a42080301d00d0445020301070b41c02251150081600c0c0c560545112000400078 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 614553489 1250 614552239 614552243
    0x70b030c030a0c09210c060e06040911130303230a2a08040e220b0103030f35101214070e2403060f06010309020102190501060303020f060903180d0b04 66
    0x4262980c0c05c1e403925004881c81608030208110350b5030440c000c00e80f5038409440540e880796201140c10f00540d80004102e0051800d90148000444000414590410b8000c0a20407542c1c0f640c031480c0715000c05d100054440c1004440000d0345030300c880f100510500d500081201001000030b050b03031502e0380382c00c1e005070011341090014080707003414000300d218182a007840e543d50194050348424659106d22040c20414030014061000800c00c41c801944151314040710280b145161840d0107805803a100c144141081400c10040340c1c1c24003090100000002c07540455a40446604400310160380d44503107885548080140c1e8419031001043d444109058584107404140819181d00100c100001d0000080003059019400c810140b00c0d440081c0c0c0c0340700754001c40c00c1c280171a89210900c0100d181c0f115100750004c5003280e17402500100481034006404990080c1c0c00c40706400034181d071590b03d0320401e4442401c03d500410190003800c082018118544070300038a2605405115140d6240a1104840c1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 614554739 1250 614553489 614553539
    0x2190308010603381c020a030305031314010506011101201c020a030903120b03061b0702030303090a121d0108040305041e0602060703061d040507030f08030702070b030c030a0c09 78
    0x101c007104d0300f0840009154201c401004c0c622441175a0003090a90302e2500020b01040380000c0051500406960080642548000320201d038982040d4001c0c020101070b41e003940016440c1e107491074460b00c14064a0b101a1451528084400780c3e520b8560b1b150748407001c0144489400e00c408680301907984042d00c04d00c03e940d140420410b089240007403105144040c810399181c070300494811192000205a42d20404011400c002644800c4401a0078042c00c48000d42c10b110004c2005007200c800324541d04194410700004821003031b0000103540126500c000b002d5902c00703c01040c0c50740d600c41c20b48650000e009003400f42c9000d03250340c5090782001071084000006810000f0410046178100312681d4041800c0c40c080104070304140c09140c44840d410b0048840d03140341c00100d01404014000350b0002e6600540000382d842180c9001c0c2415007003200c1200c0035008801001039a801500c084a2060224001c890b240d903480c460743d50700600c250b120001c00c10080790004195000c482005e401a1030910700 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 614555989 1250 614554739 614554841
    0x703091209031506060f0e030c060a1206080c030a1104060e0c090a090c050702190e040c1a12070507050a0512120901020f090909030f130602190308010603 68
    0x400c003042c00c0120341a943c040c0d1810108000300765201041c1d105152031454010100840440040e18210018000640c070a200141c001d0a543e0000c800400c902c8200400707001150340c2c2d140207511007000e8001c80d6015002140c8407000a60400300304866083c0050001a000c0e444444440f6841b03411210a80040d41c005a00c2090b4500481220b00416442405221040c01000001c1c800c1c00340000c024010070819210300144002c031080700016001e04070902c10f0343e00d86800c00c11001c104074860908000b66211060071030843e46001c40d00009258a480c501584a003401182e140c1e21038001990a80105100c0e40c000480c280041e002d40b140d1100c115803511070000100f00029006002c0e91210307031041009104150040c010b81e405050b04039910b20303c0383c0d5088202c034207502c40c1c403e0500c002600040c3c0d40c030f541d00c5403c03100340666016a088458400342040e402c02c5801c58485c0140c04101c181c001040700d540b1076008001050300300703541c040c0805103480b201d081f64000d90000c2a501d040500c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 614557239 1250 614555989 614555993
    0xc0801050c120a05071b06020c060c041d07020309090a14090c03070501020a02100f0908100f0501062c0a0504021b0c062701091701150f0b04050603070309120903 71
    0x542298000c8101c00d02088141009400030384804944024140d85c071030322684a105201088e416a10a00290010350f925441c00450012143d401806414001d080c00b001940a021000e01d025100c4c445540085240000b4001000b904460003000c0c0d5592070780f281d40d00220048803078003807401060510002c0c078004090070300b010704001050304001d04540c0310822000250b660401c20105040450921300c05200040302c048499080300d4000024508c9440f9108090090703a900401100e40c203504100003a0341c0b00d40048510303d118050038442a40120320003050f0700e0704180d072515400340040000402da2750b10720103e02681c00084000a182e03154040c50f5454800c140301005443c04200c0d1280d2600030340c40fa1030700d6038500c1d10b41c0c0ea82c2c0034100099203803402d902400c2214050304c0c000303038245442a82854118003801d00d14a83e401d010420160003e03061211110345025100c049920074249070401d0103110307040d0401480c0604044d114003907080803c004c0c03800e034039050b013190b0760781c01404e4214 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 614558489 1250 614557239 614557267
    0x301020c0c040608030a02070b0f090a0609030b0c16151b1e030605010807050c120c0604030f031505011d040603050a050705060304030c0209090c030f150a0603020604030308040c0801050c 82
    0x281c4c007183e0250010000d15080d1507001c00d2110545040c4c1e5805a00c51445880c0c032001802681d076240c0d0400c0b010034010500300d80107040340003140d100c2e1440f220701c1d64610b4406503580c0900900c61144007071034400d1400180038002d615803030700d104440004848000862089120940203419004074840f862031050300c06248028900381c1d4514181031050030f00d8080028020403009040c501040408038a016810b2001d100d5080340c480006c0d006915684201212602c1d0741c070603681200840c2145d054009928040d0186048460805160906461500006440c0500c21509044070b092825003104041d58551003440082c501402c0285000300d940c1c90004c0c07400942d074000e1803083c40c05004100002c4d03030143d80c41c50ba0660540d01c042242c0c4a0070900f5141010204000b507260150fa03101802829000a0720280f2400c0754507450341e0790300ea503c0580102e07031240c0006900040c3c02c00061010074040c01c0c1c5141c01030300c6242403521050340c6040c03090840314103a812400241e0300085546141c506 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 614559739 1250 614558489 614558501
    0x4261f020c15060904150603060c0e01020f010c02060a0f060503190201021911040c1e05180114040b1b0f010203100617042607061410061d0a050301020c0c04 69
    0x315820240c02e802c0400018141d42801072000b8001c0341e200ca903180200445030018402168420380c2409000c24401018010182100030031b4014031405039140301c080310500458038034130550f030050b02c029168141c0340320180404040d8622856111400012191410852142c0307103c40380005803c62190f80c8002410002c252001d140c01d03030244540e01000c188204441042da00044a0000312a41c0c680416134183d44022009080442002420740d589038002c0010210b86881d0b82c04210140348000054880803070200f01c6900c0c42e503007480700340a01e0340c150009003443e00e504c6100c0141011101625071404810200080340c0c1d075004820320428640d1102400c0240c0301c542001c80704140e1480c0040281480100040c0c0003100800102c80c040c43c400d00c0c040c210055802c4000c0d83c030021800d1080160040702410085510301e4000124010032520a000c160703815995a00b0140d0f5140b281d034141c484c201100a64402c80784180054107540910003404106c1a9001414500402204000460300 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 614560989 1250 614559739 614559763
    0xc0306120708070b07061122120b063703030f0914040f0b06070f050709110304140313090f0b03030405010e01030f090b0108060f0a0204261f020c 64
    0x22007028207212262001c40c0040c1513548129a2984500050030020050207817a01034035902c000010b003207804103035012901104908031840e0024219035800d0818000c44200501605054030000414458030b407c00ba000038402c007000c0100d010210050400c41c1a1010507802158012107800800c20560800100941c134035250411a400f140707800c1d028039444003e01d031280e00c200c0d030b107540d03004c110405503008081e0201c0140446486044518040d0300c5d00e40141c50a550300d12624000080030380381409031945000e5605a018116140d03581c45090080074442900c400380014491140e510320a514076200503e010400480da400a11154000b00c4074000e14160103900708005c144100d0340c00400b250307d44070080c0381c000b41045007039006000070441340000402c881c0d2400000203800300001440c501030020001c940040d0707124010090220f01c60b500c1898100c106041401c00c0e2980e20a8940340c1100c01141070fa100f90f880d8640c00d17070001c0d001034101e280165011a040007080c0003001100f01c510 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 614562239 1250 614560989 614560993
    0x3040602030c151005040c121b08090304030f2405040f020f12210706060306021c02040e01050402160605070306143003040906080304050f0607110112020702090c030612 74
    0x414103c48138030f680201800380d98007540d10f80e8080c036281440341010007a00f00584004100f0544c4501c01d240391100305c540c44e100000d44800c040b801011000c0200c50450780c4c04003029200d5140c5907200007802c172045c0e859200c1c2181900248071604980c3c0103c51045129503228050002944108080800c45051301c80c0985426040e48071482c40c000307448101880032110b58500480e14000d810402d12a000f8000c15041c1040710001c03c201064016084902c400c51002c0100300d9044018012801248500c0e590344100c0d40c01004541407075401849800090400190008555211342c000c0e81e0098a00d000000c1e510201040b03114076050030025061801c607050401480c040c080c084640c0328002c20781000300b2003c02c0c0f20914540c03c00032900180340852091103060b0b600c0c3c00d04d0303032280c001303208032409833080c03054103030035407034200c04481845900403150350844c01d1610045512030908480d0f100038903401c00115000da03031600c03149841840d448040c543d9034684001484440301c410210b01c15a9 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 614563489 1250 614562239 614562241
    0x709060315051e061215040b070c150903050f130306060902091815100e011b030c11010e041a040c02010e121c02030a0903090b0c1209060c03040602030c15 68
    0x80020f0101d03602e25580140041c000e6403944400038071030700d8100d800c001c01c030300c00d04810310b5402d4002c05e0800d00c81d07800749000d0501035032540c2c2d00755807400d6043d500411001617071580220b0300740150300c1035078500d000c1d00e00305d401c0090400782e25125500111000d025080012001c20800003a40601c0000d801030442c01d6080804000104101070180704118007410405070008405c1103000d0700184d00c0d20301c010851180640c0c1017402510b000c00b0301c0f000304e0000b43c1101c00d0441d2094460030088199074036559124081e0782e180ca90142071081441c0440c1044019000032030b142c2d465000304894510350304444907410a0760810002110100d540560546e410300c85001440fa0010a084c184c03444081100c03980c4200c01c42114988040c481a081c901a2001c0144403030388072264489a030a6100f525180052030701c84141c05120300403a10b02d11829406040064022810310700544001200901182d04001300303207103040d08541168000b000140c4c404600b100e801a000c00810781d503803143c544842d0003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 614564739 1250 614563489 614563501
    0x201140109061a07050f120c0601060c0f031d060a050a020105010509041e0809030d09031e05030a120b04020301060819020304030e010509010c17030a15050f01031d070906031505 78
    0x90203850400d20f000b201d40c00300b1401c09004d41400308280d0301a008060f10007010082c2c903a8210360f0481f800e5a1454400c4038000700307800380600c1745424210f400c06040007540f500d9a41c1100e52440c00248403c41003140b41d102103890b00e03031801400100c0516200c075900c132941c3c0d0800900311a4140c1c0444d10500405040c40082043d41ca4682c1c60b010000c0500d0703c80054604142985100d00268550140710f00c0e4a03e5080d6640100407070296031080390001c028043c108004e41c19101c8a0780094002e4100300710790503090303000714a221203002480354049121220500042c1c00ca810076030000010036414020481c2031a000100c00c400d40349211000c43c110f0406842c020003260701d00c0310f810706010300006d0341d20440c1e01660a095480741d001c81002001500490300d00c00c1e5410a480200280e418986c0190702d285008440205480010b481ca1484124010044001c0c0041c14450b04503c00624198014402d00780550320281c11484e0000c40c06a1a6251880004200080c8048481c0c038050502107 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 614565989 1250 614564739 614564759
    0xa0b03070b041a160b0915161209020a260a050c010908121207090801051501020d0207060e28170705010e010e0f042702091501050d0f0b10020114010906 67
    0xe003a682250300040c40c0d03903e1b1004030b45007640109002e85032030064030400c03032507840004006004821540e5480800c03120070349181e00b62800500d009600208100d4107001101180707141e071007907203e200e456040e148001c40106041c2102130000381e07480c1d0400310078410556042030300000140000001000c44034444265001c282c00f4101076041c90340032845c0810310309131107000380d81c0c094480c10b0020001d40c01c048030a54020480700e1040d90150003440c40180d11a400420310310107c4116440d07150090f1901005c008200c81640c00a00a10310030b2200e4030624160103540c04082c194040c3c11581b00000c4010242c501005a84200d04000030041c543d899640d01600c805600c2d8805e541340c101c140000c0002030003424982030701080b401c4910100c0d00c4046502c0c802d40c2030541c0252003d409070380702e00700d04643d540c4c0900760b0140480c1e010440b181480c21503601c03180c000001c80704001000229a00058004e0010300403050040c1c1d1150848955140340e84169401000b04a00c00c011803443d05003890 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 614567239 1250 614565989 614566027
    0x5041a041107050318060f0a1d150d110f0c070e010801200a1e03021e03012103020307050a0c03060e010c0f0f05090405010902070c210b0a0b03070b041a 67
    0xc1ca844a50780c0c8400701645070801581d01c40e1020080483d1121008c0d00b000f01103a099040c1480807a44503094130180d41410007103608050400b201d09850000c5000c150405400e045008803c6451b04002d4550244018405802d0441040c005000000e01c5d000314000c4e2185c041e00080d481c1e9141a202d19100540e018802085151114041e502c07140c20007416245410503180d2200701001c0312501101d4541c6c9036004013a1601020003481c1010142c940c2c150380d6005c00d0080d8031158a84403180d210043c1d402d41500516482441204e00c1c181c4c0c41c0d41d4076030420041c004115040724044400b8030400c0f0060140c1109c062100c0001c0107207807005130008000c481820110410700020001007030349a0302c1941154110a00500705010b596510420040294405081a140100f950602044e030008610301c42811110165044141c000f051301c4503400507030058100f40c041c50741c4580c4045075072070a003e414002c1c02d04401d00f40e2075615010b0501c014084001047c0054042040000194203101d6501c03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 614568345 1106 614567239 614567257
    0x9060f0f030c030206090613181d1b01120203011401030b03030a080105090c07050a0605041202070506030a02130b191e0c0b1005041a0411070503 64
    0x540d450001601008040101d142010405440c0c1040074000402006102c03d10780b01c24019194104d002551100d428841d103d02c0d0134000207828461a021541000c14082040c2c0e00703221340540b0350342c41081190080424000310500c5900ca09400d5600d20301c0740d2802c5582e56101d06814489484404801d80083d090010f02d50343d40c00d01000345d51541030a0b44640c021030b400c000400680c0a40100650f07103203e000c1c8162400b040c001c00480c48850700035880001c180c1842d0500425692900c0400001e5500c088020400364031808100c0340d101c50184d1005032603020041e1000c0495500e54000c484031580031030b03002281050344070b43c03154229094072030807840d00c20fa400600741d4039425140c01005c2602c20070b05001242a401030b0550042c500c10049240903290b40c0014111003089184105070600c0707440d41800c5040900c54001c100d4091f180301820500c8641d1819500c0c4556510 = true := by decide +kernel

theorem cover : BRFrame.Cov 614388489 614568345 := by
  have h0 := BRFrame.cov_init 614388489
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614388489 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 614388489 ≤ n) (h2 : n < 614568345) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
