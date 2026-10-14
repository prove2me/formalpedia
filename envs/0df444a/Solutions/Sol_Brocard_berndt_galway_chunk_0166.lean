-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0166
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:13:25.767189+00:00
-- url     : https://prove2.me/submissions/29e79a54-329e-4e6d-829f-dfebb2844944

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 29676264 ≤ n < 29856120 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 29677514 1250 29676264 29676281
    0xc0907030906060e07030f06090501080307020402070c030203160602010c0e01050f0a020726010e030705070509040f080d020301051306060906050a090503070308120a06030f0f080d060f1806030b010603 88
    0x3555107410380803a0701350040f59118018162660001000c02030001c00408a440039000a00c1d001d08080041002c0c000000540d00c003590100e90040e82c4082514001c108082035500003034043c0149141e030450045407840d6031b402c65500307070000d021110440c00101c0741b075a5407000944c042103040c414281d40c1601000600b40c1488c080c0102d91f019071b2144c00d07a080780482202550048066500c2409150f0400c0c01031020349807125000710f0508034240e0380d03141c0311a068014103000d1701e0150001010300003c2004d0110b001c0d000540290342d025141c80b6103001c2e600c00d0254900071060680b80d95920304640c4036600881e5002d60700c00f4001d40c18480f040b1890740c0701c00003010030400c425201041c1c9503420311124004602c501011a40c0b0507043d115035070081d90040a984030750345840400c1000c50044a504081c1c3d56004010010b4a04117261a0350180261006a0ba1141c41c2c044041049114540741200b900c3c400d1030401804001c02090b24183c4000307005c0146505429001000114040c5d0001c440 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 29678764 1250 29677514 29677523
    0xc0602030403030e0604050309100c0c0302040c120c090e010510120b04090c080a1a160813050d02010603020321040905061c03020d08133f080f0106020c09070309 71
    0x2030741e0158004d4103203424415070302651103810000300b076001c51034480c101950240860918071180794007501e4850030540144006400341da100c20003101a14814039400120010410b000c20444c031030b42d140204150014094090501c20540000c1560700d00001d0055882241d60b075034807501184089000003030490b001003141c01542b9003403d03100140618007000003402c0501e00411914200342404019444400c44109151307032140d003480310705881d09554461858160400ea451601c9001e54007003a030120950142542c0540e602695103143c0c103420100860b4000c50480750080c0c05092042c4070700403801082041d4036801c01c010001c0000c2c503003101c2c1c1e004a000348041d041000401e800c1c502c0e0750100d481200140c03c2510b010603909d42120800750400e0384001d00c49510982c81d541d00e0b00b800c5d800301c440c1d1011100300b0350030790402d228103603242c1c407040c02c5820010358020026405010382d503080d0703214940c07544c40c1400030034590310004003c100510000c00c0d14840d0b07144c45500b9070003003180075029207 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 29680014 1250 29678764 29678771
    0x2040b0123120109050c0a0c1104020301081b030d0f0c021201110307090b120f04060f0e0706020c060310030b1323010b010f050306010e030109020d030c0b0f0402010c060203040303 79
    0x20400c407014038148118540401d055565016006150b0001e80e105030001040c2914080030302c014021a6410303a9041034030f604200300003191504020003407421007481c0a522900000c0003159060001c502c05011505400c0e4102410480e2810540c44814003c034180c009965018038030740051043d4a0305851a001410901e181042048030500752070102c40040542d44000060102280c0d014012030000e02d0031041190520000360600748600c0300160103805034000081c003040a02506a01065030350061a5040000d401000221a00d4188911603400075025807114501ea50070000201d07803085001c2c0c02d81302a054156503e6540325407025002500110fa25003c0100140500b01c4c07030f03001d0300d01c5c0d41c940410358840500b68900351981c94040c141000944ea2800130300c50b4010b01500c4c2c010703109003010810301c0100b80129004101c041d601a61020b0021950424517820120300301d2050701a50032005659105040d4205104c016030300240052581c0e1081404107a10f5405143c2192180c07034040b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 29681264 1250 29680014 29680037
    0x1020c010e1c0501020a0503090d08070906050d18050c0a0506031512100923010c021506041503120315060206040b1504050423010605010503011e08030f0d060e04080702040b01 77
    0xc3e401ca0b080300701645e002c034000005200e40b80000b0003112080b021a890300702c2107480c0c0850001e0414102e48503250901001040c1e014600706c29030411000c0c406210060640010b03c0d003072450792803e80144250181c0e004076000324160030800c044034424080c141021502203003204c20301a5003e554188688180545410450406401e01410760150300403004682030042c000112440314074039007540070741c036171618500e58a06500071130b00d0150010000c0031403582e559a68041009040c051188034100260000c01100b0080c00344503603c0c4001c01c40c6d0b0104030011b00000404403004081c0035020141c0e01c443d00150001e07400c4035090f9404442051854204105030b80424251071090314101c0d940b1058015a040c034111a1146030b10407000040244101032506d00082c0040c4018000d81d580358148540f100c0b01c00500c90141002042d0a0f400c0384c0c2e48044468106c45c079038000ba90030f1030101d800d1074030014200c03825035101c0d40941e80040c446407074483c0315803c100080482d0000d5030306100c1c035200b50 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 29682514 1250 29681264 29681273
    0xc0905060c1506040b090f0a06090b030a0b04020102030f040605030114030304030b010b160b0106080f0a0605011403180312071403071205060f030d03090308131a0a1107110f01020c010e1c 82
    0x325003e4801d07000119174506010300c4036402d8862780d40000507100c0c50003211605070380c0d000503645091908901808425112400100d0962254031190713100c3d80000900000c129a00c180103604880034410048007a02c00c2c1c0703003016180d11845c44090801e29990300140308c14640c0030001e10103030b90718240c0c1c451460003175583c088440b0004d0b48041d000c544044100003421107101503144d03008100c108100503803802c0a00180160801c43d039502c3d00e21801200241d4841c40040c0389101c00b09030002100c0c0c844d0141020440f220004403103000010f84519101145280071100380c81c080c410540b0744c500300000b1103503200e00078031009044541c802001c46901695071810b0088070080c0e4800c0c0c2d00880c80f000a414090b0050700046e1100c800341d00c0403070080700458440036030469540d440102e40c5145c0c0e241c142100d805046000074000e42c0070000a041402c00ca050340c000d030300840c81070398080800d021a40040e81c454510580460100e29022031825151a040603040488145440d4180450b01d85848 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 29683764 1250 29682514 29682529
    0x1060e010608060f150a02010b03010e010c0909020301150f05130905011a0f03150a03140304060908010516030f11030a0b04060503070b0a030c03090b04060c0905060c1506040b 77
    0x1000011908250050101603480711240b80d0150050351404164403040000c900201d0307965903e035101c04001b00b401c0200510030342201c1d5100354018000d0010440d010396450080480b40c4e05030020072803414001405290780e0080d28100c1c2c0003a421003046c0c0042c1f20042c1c51200c80ea0356118104101041000d91460a0110140c0604089440002c696052050354820248050701202002c40240958010901000210ba5016455030440021555120041225491150002454081c4000b1028184036001014004880141c4d861005580d6a20b114a080314000d40e040046002030205d030184c603500a400a081d802803c540020701c1c0b40f10a241d0190981094499004103511003a45002c1484d10f40110b002a010403006410403900e046460f03c82c0c1c0c4680c00180c0141034940c0c01010704a0b000c0c6e03000084c1a6000750007050685481d14101009049001303001c408125602c6000c249401c01d070041d10b0802e481d050013400306000c0c03403030030702c081010082c0700561003501c425030301c10b0070307169000e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 29685014 1250 29683764 29683769
    0x4260307021c080c070f0506070506151f0305091e0d0807020f0106060302030103020a0501080105030a0311120705030a02010501090b0a030f0c1208190e060306040b0a0b130f0b03091e0309030106 85
    0x8005d01031860034810645003040c4958001c42c818071040c0100000728402261545e0041400312603122411601c00c08102c0b00c1000c41070380724031400d40c07480d05000075805030440e62158603074209982c17000f00f40408500f41120071021503503569101e017907980d419a0043d410313140c006031640129406c20a9642c0090300317441c0b050b0040000650088010021801c003166003030007030701003420403544960426000c00d0f550a08072038040c0400844203429142180c042c0542c0400003000c2c150345036240c0c50303810b0641c0e907075100c00c01d0080190300c3d090001441e4000c903c514242c452000306081d814600d10349403660070517000d41e410b40f01c24030812000038040041c001c0ca0b101c43ea10a400b405d4544c2d504c95541031440c1c185040a000380701c5010100c403502d558440c12240c0c0503d04803000a402140003000c01c42140306900100d03001d0a0020b45c13811003160405032182101c2e580380c144003840e5104c84d0716620342d02003035400083e240e200f11a006501e8030900796500d5407031401d404403400c281032400000e0a581a55 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 29686264 1250 29685014 29685037
    0x121103011b031505120312040606030b01090207151104050f030102040509070207051516030c05010b0a0306020c19080304060c1103070b0403030f020a020706050901022104260307021c08 81
    0x7614440700c20300065030b039440100801c80340c4200d00010170900c15242c4c13087e2903403500b04045d25400101000655071110300503503040540d201d150360b122180710000303610036101074440518485501040c0301c4a40a1180025020803e4a00b01454002840090304840d5015035040d5000c3c4004241521100081441507495030f000301b495500c0c0405018a03040f001480c07960b898820800d812105041d10240b84181d42d00d460020700b0b2107081d040403801440d42100c4964014646200041400501c0d00030303005400148068882e0640c2100b040300200407d000001d00c4824140002004180e9a505c4521074882608010710300c4d03446094141e045500280b81150001c4805050200b8140d00d4890041d920403144011460320412101c0650f031240c83c1d108010812900245840c0d1076442408049240e0380a01a01207043c15a1260b01c00d1540003401114040043e50240c0d0000900c0140d10158408461018500e0190b468003400940c0f01061202240d0003440042c150010340050000c08508106 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 29687514 1250 29686264 29686271
    0x914010504021005040617270604050706091a07020d0807050a0606090506030c10050f040b07140a03080103061505061602030c01090503030406051b01020a020f06010e01121103011b03 80
    0x1d40b04000049200007040010018244070900600d50050b4298a8060744120140460741c0da042c07402c94800c07005c000012940c0c401620150364480c0004181340168446c8096480720341c0c441d0011200100c0307910540624540f11076511003240707158002003103420300142c000d005d00c0c005511542415071040d181103070940c0c4103442c22014059581701c0e4a001e001d1504003800181400e00000b076070f0308103410074184184641203070388401c00e0046080b1040816038110325500ca55440e021003406070420b00058483d400a8031050a02400102d1188034540d0f25807105907480e421034840400405500c0010780501801c40008a000da40f008041e004000c1c103100410036000f25031040c141000d4400c0140d40c1404a03c92050005035000310503101030354128903160782c0304e1030301002c0f0040300d0340c0c04a00c65426510015410314000d0f40403038500c0b54020303e9422904582d980b00b505240142d02442116008190051142d001480c10504480040801800412008540d04049001d81d82110b02c1c080441c0d507 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 29688764 1250 29687514 29687521
    0x6090803070e060406080403050c01060e01060509010908010c05220e0126060402010e040903091505040807170d08060d0204050109020901020f0102030c0403030e0d0506041112011a0f0409140105 85
    0x20b00250480303103040203607445400d040c80c11070040c0020b100039000a090040104001c0c590603001d520100c018106e030350a100c050f5a480c8030141503903015014990020324000c40208035007105000b100746151141d6981e51030031040c140c80c00009452510158150340e100c050025002241c1742c08103019040188403d505007050708200d1a58010f401c00c15085a00080200b102507030b013040c105a820309060310040354204d40c9240807290303100b058008008108a1030b8078904c0003a4041c0103401618541c0085840c855116021922203440e076480d0381010746d00c40c11103503044901c10914550020740c05030810603040110741c001002d0f120f0036001144442d5012941c98050740e4100b011451000141c1c00840c03550400c3c40c204034681c07280d40405403d10640c03405004558482d0350350a18000e030840d094a845040074500241c07403009094842d03208000086401000b00018401d10210221503444007038246241001c1c0410040d00380c0c2007030f921581d2013000348041011160070824501c5510300000b030b03c0c40c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 29690014 1250 29688764 29688767
    0x6050912010b010c060f020f03090c041d0705010507030e10030e0106050d030c0b090c0d0c03060606050c15070318060506130605090a0207291803032703070609080307 73
    0x550980344100160b0400318038040c5030740c03c8108010b07100e40201c00031a040703094841c1c1401038483c6d14892030078941c6c0042001140e13400405c101e8100c5804903000e02403841c0c100f001d650126852082c02c0303c20742140c10100403640c00781c802050101d00c6400c042040006103030003e4400070055401402203a142c070031200c4c3d0b0140a11540b070141504880e02807000010340c4004150780c200800042a07212a500801c002e04400c2000060840300240048500d00307191500c0c90010003035101c00c0b0b8a06007007a101280060084040d645010b06003c01410740840030004d090f200b010103041c540516030340346c1d440c6941085040600c0801070091002098506001d403d203e8261f50003800886c900b480c180b821b000e19568840c2d001c0d000a5400f034090380320409410402014a58425400980f09c0844030000540762000c20440c4600e16003004104900000701c0d1680e01c03440122030750388200d03400c000840440400c1e18020055414910200c0303080c80007a50700c182c11074100c044192120307a404810045080d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 29691264 1250 29690014 29690029
    0xb0304050f030a1418030613050c03030a050307120905060907031505010317070503040b12010302040c08060303041703070204020c1e070501020a02041a04110405040b010908070302010f0504030804060509 89
    0x412181c00110301c2c0840180c40280101d00042c807450b24a1400110780c0010b03401c2c04034441400200505448007401d10010030103c90020000c00c0303030a406024040b8a0a18001c02600c82888450f1140f030310b1591200d500311140d41400c08507001c215074a510f00e1020a0080207000c1c03042c80c020740100342440c00e60030320300c02c542007182d402c0170f04030f09080060000888103885180c1c0703080121002c0d900c5403010324102c7e0450046800c0b0125440c1c0103e00c1c1c002c030b0901408414100d82c004d880810224041242c100d80210048601c0c5030135510401081102d214200340303021502014509407420261175500041c142d81c0000000101d1307600120701d2900036940d901c1c51101000600c0c0c000c0907080c1c500030020391200c41c004006846190740e403036403105e106145600070005841c01481000500c03006c1141c40300540180c0200e501a900c1c0c409003046550251b600342080c0d90b10a0010081c0328a598011945407441400c03601c01c0103803d0000000180310440940042c201e244c03102c1da00c5600315418031558 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 29692514 1250 29691264 29691283
    0x7050a080d060905040521120703021803010507080402060c100e0106030506070c05060118060b0c01050f010f03080304020d05010e0307060519060605090103090602040503070308090a08070303170709050a0b030405 93
    0x41d1340352100340000030741c0000747ca042c052103100142000c041c880b641a0014040c405d0303407411510040c0c08004803603034954020301350f07500002080f01c00d07003020006045c00c8803802c0307412001003034a180c080381c0586004005084150300080444140000c11142e210a03107201504d0070340d10380e45500050040180c180440d56106200c0c0c0303040d82c0c60344400d8440b45d035190011311500d0340d00c8880c0c0311501c52280b081c1e04404040c04156400c2c1da51503c00c10700701402030904407000300524a082c400400c44921b130030030940884e90880092800c5445a03020071130303920000e480486080d076889107032517000751050001d000018015400003401c0e18214580281034626641d401721b030140307008000c2c000c0a070002c059880d543c1c003c1c600015594928030301440240700702d411155040c41100030000400a07141c00401d00c5040682e1941c240680c1c925046603220606e000040c00304210031800c03040558840d40d400d074402254981300910b075030780c0c90100d01207001310381004407a14400000c110922000300107080301e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 29693764 1250 29692514 29692529
    0x3150b070b090d030b090406050702011805030d0e0309150306030312010807080c010806060a030c0e061b010f0c1b0c0e040f140f060c0903030f0c0304060909050f011403010207050a080d06 82
    0x200b4070301036000846e0396000a1009003503d5a401c041803400c2d200b5400b050442c1c0e01240d40341e0304001d460500350f40d40c3c0c11100c5c1d1f80d0485030a000240f190b0171408000d4401c01c2201410b01c01d01450321401c0350200b03810050405405100501250480080741e0a809000b0700000001e022054101012242070049022880307040c40800700900140761220011640725160600d00010700b02a0080215092450741140c00c1c5d0001001c102c4000d41500410100b8030054400e008109100d0041808026200c082c5084408a126044c603084c40d14882d82041406511480c2511545a101c40a0704072000084e1015100282c000100d8000c111190101c49440c120000c020080303d1043d0f640581e0f9808010114032a01c1130110301201d064800f0070644503042ca1a050305511483e9903120250ba9030094840c0d1000180d1150000482003180c2c1f0902c1d00800940c500c000403a800d0903034a00c0408881014141c040d9400c02c42d5501040041c482001624460100507540e4820520721b0750546103030703400000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 29695014 1250 29693764 29693771
    0x60305010501051605010902040e06071b020306040b1803040803070c1202090c0f0702030102031503060f010b030f04080d18060f0c09030219080d0903050d05030606090103150b070b090d03 82
    0x4526038009091340d50350048a2040d1000003090300d0542d025050f1410025042801c10b03220b003496031004a06103103e8112a07540711a03c805180c500f0350380ca02400300181d05500440003207004503032300e40000c42c3d11540450301400202c0160041501d5a44203034401d05682d04080740800401840c00ca40c40c0051041d88240c400e24030083e00000c092500107022034814101c000b40b1500c201c0c103030409036641560001c00840d140c0c5840140844030010340c040b054440c3c01100b0000b81141400100681038410100d441421603031522400d010301c58001d04180c41c0c254080c4240710340000d01c3d000d91511200340010480885585142410565014110442c41d0500300000000c2890b440803c400403a90120341c0640d499204001c001c0b14032005410844290180058081040340c0004804003180c2c45501110440060450f0480d85070109582596010408100c682040d41c401e4000111201180b107400100560320b501445442d84001411544145440300300940700d101444a001c42060504061 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 29696264 1250 29695014 29695019
    0x180f0723090601120903090b0403050303010306140f071404030c030302030c010510140906040207020607050d0f0e0117071e0f170f010b030a0b040507030905160312030905030c0106030602120106030501 88
    0x44c08450307001001c0440280e40382ca003803003814802c41049000f0060344220300d42d556100e041098a81d8030900058541e1760601844c1000301d80b0038040e03c0d01c264603a86042c075050320780d0030040700c0d050007100c220141d0903414000030020440c244803401c000c61084d0021551013080e28141e40c00e540004020000444842008100103a10181080c0046808450000955560400140c020301075844041d41000c4041215000c10400003000f0743c01e610306440d404103108040000b1601500e42e40c202c1270000c0c0c07a1030802e01c201800c0280c0140c03c400641400503034034446000341c2003004001d40030480010f41e075030b01c2190100d4002004141001d55218807800500d0070381c00d00c0c0e608007810301c200d89150030000000f0700c0c01c0341c40307034069030009400500a010b1070411890040242048480596041c015000845c001403000c4059104030390340100c2d1308030b2000150206030000d0924000c240ca442c0010403049406120a109040c0030714898000140c0700c00e800001d1480c0350f001600141e041c5803070680103 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 29697514 1250 29696264 29696267
    0xa0303050a030b0406080f03090a09020405150901032901090618060503060604030c0806040c09140a0c1112030a050906090a0f02010e0306250512180f0723090601 71
    0x11a07040d01c55500300815034500034000b04000340f030a0380c0700458038011058240340d0910040f004100071076084403040d4000b601d0f2600a000c038821440b031190703c00e19490003600c1205200300500350a1105040018000c000400c0c042108039071211442034241910a005040b5a04000035002806e52441c1070b00b940e40c01d0442d0004900c040e409400107101000c80012107660340c0408450286910000f00441555038110b0195502c0c0140d8080b00c0c162450030001c40d4400480c07190b2001e0800076034902e016500e800c0e43c0c08000b40f009209080070480d03605d021a50048040008031601c0440040040d0b0324030b0520102030072118040c1c00c022079070708400180003190500041e041c04080d040244a5580741721880181c0d0030380091a1050780500544041006040110789001da1903400b4880d03030002548981001c8600313114a81701d110031800000089006540503007125a4103201410441d400c008036206081d2500c0e07032641c050144044040101400e442c0115000c9900020980c0d0020050800d07000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 29698764 1250 29697514 29697517
    0x7030504050d0f05030703050409110702030307150e03040b0304021c05060c0a05041a031b0406092903010308030907080105040f021e060301080a0201080c030c04031202011e060303020c0a030305 85
    0x40610034100a0040b4003842080c81d031014003154002c0842e543e80340645005445a00140300d41445580380500349941d10800804032203116a0041c069850101180d5512040102d031040c1030282d645c0e140040002d004080000b00041e0103100026030322460140b04010321041d101e4244010149007001c01c40c0000e0303000960940280b80e118500f40c60b04400c1008a6603070080e0350104803018034450303034540144004001513020f00c420a490b908058a4040300030000d114501c122800145c03560320400c12003181c0c55481040b4004014050b2a40115425205030340d0020707041610001070001c02e000e010801040003400a00e40e01c1c0c002d105501d05511082c500c640e0160010340140d241c2914013000722402200240540001040340b0744030358490000c65034a410b2110f04030302141c0c100e40170402003642d0030140c901c184c400c070070030603c0d0600b0741e52000f01c811040c602500666403034210080100500400801a5542c0103400045040c80c1d814024580100d40c407080e8002c0b030f10b140301480429030150 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 29700014 1250 29698764 29698769
    0x207141905100c0b040c08060a090b160207030203070e190608060109090f1202061812030106051e07080304020a090207030206041115040f0303020601050910030b04030302070206030f011a07030504 86
    0x103441c0740c0707490860202074500c42c0910324010013000100c0104000c00070040703410350036201c00100b21a0903035680300c3c5000403500c2101002d00103079000000194840314042040c4411070300c5106451603142c1d01d0b0b000ca17180c100a078004490f851a40c0040060709240c21020582e01007400c1818044a4030b003114481d1655010b008030b505081d101d0300c0c00c030305104640400306074299104503011214191440000d4903290140d900124403014101582e400e1200002c800240050081801c0d1841e464100c0c199a079900015804108040d049820403a40a141d0054101c0354040d9911560381c2c6040d20401024030b00680180d940b071032045c04070402203a030001e036460f40280c0c49580003264460087c005401840d038120b2aa02025002502242401006004404480c8a5000c0b01c413980d0300c5030f04100d0f4000c1c040759003045a105400e01007002c280341c80c044542103400ba080040c43c003150f540204030554030484000710510811070041290011443d52291552286080c072800d081281e9002051407042c1d1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 29701264 1250 29700014 29700019
    0xf05011209020907030906050726040303061a0d180809120c0a08100b03070509040f110d0f1103010b0d0609020303040801150303020606030606060a03150b0a0207141905 74
    0x2040368400c296111001c003a4004002401c01e280c203080050103445203000840b415030910010030103d602400003105a14070300c0e052110008095146582000c078028800e03010103850300000150340c03d41e0b441c00d41a00c4012035045a592081e480344000750390099850019804400c103404010907080c600f40d0b4042081140c56640048000503003510b0459514402ca41c8031440b200b002032a104000f408400103400d006013400510003e00030076840713980d40d108550700215408005000a51040001104144188100e44900740e100002c901c8410501601f1981044e0902c80d16081c04102d003000098244114003e00003003004102042200440000c000c00d280d440d00c20010466a0a000f83c40141403114020030040040e845100d04500c03003884250301600a92000c10000d04010400611462018090500e0b011081d80120000c2c03081d440c03d20700d02c00d1190340126910490500900c251016580101242d50a024503090b01202440a6521a09040130000e242c5880c2d4034146d411038004 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 29702514 1250 29701264 29701277
    0x10f050108060307031202150a0c0c02060d0212010311040f0510140111010203071e0305060f0603070c05060403030f0b010801030512030405031315080106020303150f01020c0406030602090f01090f0501 88
    0x82c840800e25040d0741390001004100f0103210303c483c15600042407821040c84060a58450701c844000384126981882004006465094004d0150030400d00400540d10300786001454245441811440c545081c2c0080706d0390100902886807a00d014054100c450410349002c002c94200345000c01d0350b5218500c242400341c00c1210b00c880c2c0c0740c0e00a408080503c6440d0000f5035172441d0032030700140445521980b00c281d4030000404800e20030b01c00d10445100f00c10107040d40a04c0100e81040000e280c00007051a020403241e0103440b00090810b1195a01543c46620041640c810103040201036aa040c2485810040048010400300b00001500103004054004182d03490312103050441c114428100d840c1075100080c000020703e880500700055003048640e844001598a60394200d840c0c0c8001c0d155190103014440d0074141c1841c01c074601c01d030b4262050049845248005001c01c05a404507030060350302681c040354018050401401c01030040303000346000c520170b80c10100c2c10441800b50340641c5042008 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 29703764 1250 29702514 29702521
    0x1507110c0109140613080307030f020a0b01050f0d020d12081303121d0d05090102060f01060503040212190317071407060e0c040e0303071808070303030e0a0b040c080c09010f050108 79
    0x151401103915025142c001c840c801703a02c9101d003a0381d941c485042200051040940481560b02c00b180e03140d8600da100f0300d80c654507481d042c20440c0b030305100c0705000d62150ba0908181c0040e514616004459031240c0d401b0344240d2101c07903014051000040c44c2100071020103a0b44000a5806883d40c0b4280510140000e20b0410a50ba20042011070000d00c450512a412542c002517420401800900c2d100344d0803907821341d440500786e4030020f800780700d540081481880402c0043c544442844e1498210b0422038034183d041e01e507180322040025100340c0106a8219100d145580c10304021380d40490342e410300320111555054446458440c1345030203407865030380e0001030031003410078045600103100c01003092100e0021049138076125401030700c080000ca4088280105000041c0d91080104d2b24668058408985140c40070780142500010b0b4840d0f6009440345000001c1340c50104500a901448540341c0c554104040e0519100103100b4051140c41d00740010400b030501c4908000a4503001c0c0b070316a02a85 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 29705014 1250 29703764 29703769
    0x11101020d050127060509010302040b040906020417010e06091c090302060324010c080d0e070905010f06080f13120509030d0305070e0d0b0a020a09081507110c010914 73
    0x505114400c04038200000041d41003a00f040032030b5013481a11403c2d020644144010049481c1c0c1e2007240d03000074001004001520341a4440014600094000304144c5d841e551600220780c401e0f04961415007800c3c03820000010248101c19030005108010442d50034a140e9131a03441c00301c54003403408a000b000306210385502c0303410340e2002140c1c064401e64503070520703808420300800c00d5942d0403800c9c01e54211504042d17100b8816101031942111119107400e1002000c0300c058502e11300301d507043c3c0c4949100002c020405109290003846101841450941404801800211b01410380d1115811443c140b003400f04050b007020052684c0401c0c1c0e080c031500d141030b09035507900401d12100c2d818040c603a4002803841d056081203201b50b41070f45d00c1441c038100d52003c00440710008207000c1c1042154034002141c00e031107503006148003043c40c24102d10b8555104038052400d80c4d90f08071111030f0309104080c40080c0341c00000c81c04525108034040c002c150711490009020058511a140715000350482c0c005240c1c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 29706264 1250 29705014 29705017
    0x609081e070b040305030306011205072001020408030309030405090f040c0506030a0b090a0516050406050f0c1e010e0d080103050606091902070b060f060a02030a050a121806060b090d0201110102 85
    0x510010b100551241c1e40ca04006480381c008440075808501880b41c40411241e0300d1140c140704a060b52202c0e002c200482410b1403a8501100c610b070700303d650801011410090030070107544152278030801541d60783c1c1008248640150042c01150341c0800c064180800202d196a548054074001d581082d12a0f4500e41160090509a0b42da190000d41c0d04062040c0c5003500d8000a2103444c01007644245040350310b40c1110b80d44107611a00000440070300c0310781d4020078004000c140d40300f00c1500f02c0ba201d0300d940030411040d40f8a440035503400da540c1e2000418552092040903203444040c05c110580350702d940c8600e07469103001050680b2031044140001c1042d05880074215952000050442d00c6420b00d1070858003040040d1400d0b80702da0084a0182468074200003242c000300d040798095814504122400d0350280c002550103418400c01d141420025116440703a4886040061510791140f11903007400307030444e05250409119402c003001850a180c66056640c3c01d45542842e088049051545166009 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 29707514 1250 29706264 29706269
    0x90e030318160b0d0501050a1d040c0503030c0601031b0315050406090602040b0a0212090d02010807110102070305030a050a110a0507030918020901080907140904081b010608070609081e07 82
    0x24062040380030462040d20405041d100b084d40c5420401a620341c1c04100f000c5445220f64483c030008040c00e03001c5041064102e6400512034040307007090546030400207046400400519100d80c0c0800f004000b4070030414101c1c06506000c00c4c01e1460036042d500c0700340342855031521003448a5141d101090030040143e0142d18026040241151115100d030f61300d0015910030f03d040401031107683d0111180b041c3d0101102c1c9130240003003041881080d56801903030042c1000b0074107000e1180b8114140c040840038002048468425070f10150740c4e181c002008802c81e800070380804482403422151001041c900c0089941c115120300345291101c0d400d203804c44040d60f168020748445e01c030f840d0303102440c002140c014002c040026211689603544e00e045103544d90341d861040c103040c0406460034445606140808541060090302094079150030500ca41c0d01510650401e80001e030b42d01c6108112400080c00314034041d2550303250074042a880c200c0d8459441c240010300c034000080d845c003144c40e6400d04000c203200 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 29708764 1250 29707514 29707543
    0x3102030403181404060605091f02100f060609080a02090406020906070204020417070b0c0703030e011b0b0709060315090f02070f0813151b020303090a0806040c090e030318 75
    0xc034980350721000e140e20f224040050301850810030003094460280042c0d031a1180060440c913070342403420748081141c41c004030102c019402510500185040a8091100c11490411011489500d401d500401714141c540c4440b402d80c000c0101200181d45000105d034015030032200c0941c0721840440060001c1c400c48034000e40c42480018001400016249040010010a400d8039500f0743d42f5046440e003840781c0564403401d60448002400040c0c003070000180801818901580790313810701d5600800c100200c4800f554426500820024050f41c016050b001501c12460240316000c4240c071420951704890107030004054036112840d080300c1c50b41e41900c9980781c0002400361012545d05100095612184040303042031212000401c5c8804080700b07400c205042581c41405103442c1d0300000d01c4800100b0001c80c1d040c00200301c0034030542c0d9100c0e940e1001e0072503140603055a05040c6041000008194030910286041891203800004c001c0156540003c04400c1201d00d000c10aa00300e0500540141c03065 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 29710014 1250 29708764 29708807
    0x40627050a0305060405070b04060906301e1a01080405030d02040b0408010b0d0305030103021009030804090b01020f0606031f0e1203041101030501030c12020a030605070804023102030403 82
    0x1c03c1c0540014154000c0d401441502c081584412442c405031140b40600c07008100340038030400080348120003900c1802011040c07a800c40180c080181401600c1d0a804402c260b1500400c4201c681c44e0031000000c1c0c041040c0400800307800c0080344041c96044402c443c1881640c40003c1c00340032007401295000015144115604e030b80399000700792160803d000d0b01c5502d610744840c40c40d0908249030000d150366015180c030344c00c6078a0741d42003014041d6800d0840041102400c00000015484030140015002c59403012883c660403400091030b0804511841c0440d6104e1014040b85480c08074801c0b00c100d0081ca20900e02410600c00c04018219000f4001003500c290540c956188170120083d40c0074900c60001070443c5c05000d0011400d50340207020252031a601344508216084d90121400c110074030181c40120542d43d0b07603d9040803990111004004150900208402c601d00300d11400620351424007003042e0242c10000c1e00c0c091881c1c01c4070000e8850b50000104090600885061028212811719030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 29711264 1250 29710014 29710019
    0x8030403020a0b070f090e060f0d030905030114150904030215040605040c050105030709170f0a05010f05060303030103080d2a020a03020d030c0c0f08040513140a02040627050a 77
    0x295552502c50301642c00200c804081540c8038401d500c8880d0405166a40110f49401e1610302c603814003002c2c0180e030344600c41401c0644103071183e5102e100300900a40b0344461107460031080c1403d40300030000900f2030009000800040903280e20400d07145040c01c0e075415041c1e070759a00c3c0c242e240002010030300305032038440400c1000300305c001e812240c4542e2141505081c0180d4032001504c1070300090b1005000b2440f2008288a0401551086129001520301300c03501c8281401d085d43c10b00710000010b50341651102c00100f900700b1540030342e6070401001e0700190300d558555101d0015034081e840070003815070745501c0d400d080c0381f8008142800c01c16003000c503030059121001020b5580c018005040b805030240220312007045000b8460801c00320900e8560742c4415043d0b0b070300c040046007602c408607040181840b000c9090f882c0c1e0300c1c0076070b01845c8112000542c002c01502501c3d84080007006441c0705401003009100181d808100d02002c41041aa07110b480d40010502c4002100680c11440d000107205000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 29712514 1250 29711264 29711267
    0x303091a0709050603060102150c0405060408070e060303070807060207061d0a03030b01030b01020c0d0804030c0f17010b0a0e0603010605030105090c040612020a05090702010204050405010b0901020c0301141b0708030403 96
    0x6801480280c49210314180c0d42c3c0d00740091400202c2d00390780035801c03480301c2e40101114100320030741c00101003150301d04e85a12480010401d401c40d030030810711036100110901600c6c200e0704005402180841c015070400c0b901e5910941c162080d5000204402d1b00420241d04002042d0005440c1400502d20303d074541c1541200341d40d950412440c25000242030a01c0c00c5101c0d4041d10951480c4407041c3d0162a8540950b024020000c241d030301e086414500401000000c20b80005000d805410107082441d0118074001800455540380341e030340c0c0b50305d0b454400d42071125a14007401c0411250b500c03000e4032080d5240d40010740140070a501543d015403d140410000039404180022001c000312020440710b511307804120384010542000a400058400061000d460300c4500340c0c7c1e100b103451001501e03142e00d0380f01060a40f04280e122140140c00030403c2d00b220368041c0305040c2c001c0019002000003840032004590383c0b000150030000600c00002c40003460b449150121024650081d40d0240e50f401c05240 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 29713764 1250 29712514 29712563
    0xf06041203180f06030e060f0103080307050c1002040303020d090609081c050c0601030305131a03070309050a060903050d051806070315032a12080910110d030c020d05070519030309 79
    0x1195155011f010b000505260f08004498140c0e40c20090a07400d654800006a42c00d9012002e1944030381b1030040c032540d01c6119030000300003a6229078007603c40103503611005040c2c10440e070411000c1c070912000500480c02c000410031f5a0501000069440160780d080607221449020000c2c55103000c1d5000110038542c0210013403c000c0e01403003150740042d66441e130b0340003400001d48480d03840304010804500c20b11310a030400064076020703100b6641c0b403202941c0c03507008507039141d00c04a0201b0408070f8541c2c0815482d10600b640f10070300d0359034025006060000d03140c441300003d002c1011b050b5030740820700d140070b147c10010002c1c66001c101201c0e04131603200340c401e500c1d09058081031a281c210710042a00036a01450685040d0300096990400307184a00300010501001d408504004000d4040d0b0f180d66020004c40440125a440005a4070652880207080c000401c90340024004200404800103100045141d1994900341c0d8100d241310f400e01d01140544014400a001d2024844040030107800115 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 29715014 1250 29713764 29713781
    0x40306020a0f0206061206040f061404060b01030c0c020f0d0302160b031005030102040503150411060f07020a050a06020a080705010b120304080c090103031409011101020d02090f06041203180f0603 86
    0x1000c0700e01030ba603404200640f6117903d1b94403d501d60088800f050014404e2081d42e011741d4802c0d030020179079a410140c0070803180000c540079242c260b1074a10051455030144140c3c0d0100f5003514003108c1d504403a40100308100c0843c03c50034055101c20320f003002414800d01a440c015003a20341078654080c1e443d5040e00c169002038480311202d03995404006414038052007110100ca40250142070031050014411092220040060b50341010303280b40c91510f60340e58001008038a01914440d42c5900d041d0041c0800d062840c0c129038051180541c1c24019690005410065154000103190340e0f02c074240740060250600d22000da0700140e030094621001c81001c400b07081522105002c4480f440038000400c407480c1c60038440540402c0b0008001c4104514040c024950224181841904807a80c01401402ca80c440140010483d50100380340c00c0394504640c41600c3d20380102d401e282002d0400305243c1d0325032010080181407040043c1d607244601102d0824100620a6080042650f561188060050070451 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 29716264 1250 29715014 29715017
    0x30606030303040b06130b03060115110a0309050d0303020909090303010312050906030604020a02210d0605010c0506071107031202010f0c0c030905010815130209030601050114030a050c040306020a0f 87
    0x1400201241000015248602e822800c04101d81e2500004e02007003819508500c003443da00c5506401c19902c0c200400340c0241406501c1c40404e9081010040100d459020201c160381c01203400c0002280d0302400c180184c484c103c84c2d0748000c501e50f240c150020701ca02c90f491a040000d900400c00b10550100c003441c122400b51710392418203c070b1174404840d40d220302040a0740c0613009101044413810103070b0180507040518011105100034450a20240b284039007280002003500160445051050340504070040c482804c1c005045001d590300c0c40d0f00c1e003d00411550801850101402c102001000a140119000312800042d14101c100003400703040310f00713400ca10003411f01c010344c01c05600c04c0d501d554a081c2c0642d80c00d08811b043c0b500464200e1005040d58010b8904d180780585c190350303086c0000050301001c400044e039401c200003d16082c904140d100d10305110310512031008241d017842c2101d6101c40b0030100080d25903584c004803e810301403508090402440411482c5038150000c56626848800c1d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 29717514 1250 29716264 29716273
    0x3071707080103030c02010c0b0f0603010f06050d02090a1b0203090a050a0303080414100c020708060108010507120c0203040306020a120b0603060d06020906041d010f06050306180402030c040c030b03 87
    0x4611405102190568944000400200042010920400c41142124414904101d08800e0fa40740d60305204400e032031059040c2d10003c10700406140901c6040300d441050b2000740030b41c0713180600242443c181454044d0086061000140c480c2043c0e40c00700343c5940211000c001c042c1802c0342e000b56290001862a8010140c08d940480c5c686441e032811350890b030340b41e590f552680e5aa0303555030381e86407880103101e00c003031092084680d401c08003402a030b20103d80950043c16000e1a00c3c0c0800c0c6440410703070200071030fa40342c5018042610b0b03200400321480004030401041140c690310040b0b203103100715840500780d20305c04204810081e40c841ca0b001c0d42042c0c203203401d2203002d01d203a00300507040c07100365030321a44420b041315120f000940b43c0d0007500075003030001c0000c0e040660b00d405981030303101c034030342c0110441810000512951700c22400758409001c1c10301c1c001c0d081d031800c00041041c0c0e5210b01d00041d07c0d60300030700010b021541c0410442c80b4400016105019a100500000e030152107141c0245109004 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 29718764 1250 29717514 29717537
    0x80f160308010e19180b0112020310060f030f03020a02090a091202060c180a15030617120714031309150509090d03050603030705060f0a0b03010912080c0c010905030307 74
    0xf0b8001046006034890000d2040b890440c070071580084c481c2c00101111288000c03589004226041c444500810003211010314010300c5c0e1041505204440b0030a54080d441c00340180101084041614140c982c000311364400352101d0b060582ca8a008000e000b0f40c00602e5408010036002190054420b080c4074510364019101409400c1c0d8071250115094080000140006118002d6040304040340d814041e0402c0000d03900c484032540031049108064000c2626003404101d10301641c2c1403240425a9180580ba02d85040303003901e10030340305055000e03200031500110100071540a00031a80c000d00e43d40071403881955500009405804039500008520360040300000d024101039549610a40780f800117000c8080c02500c1c25001003d0150490347c25100900036000000c0c01000001d004080740c200c248158034003203400c0c1c400e4404602c5903501a03410105480000b400041c7e6405448100e800c1600c0141e0782d6a01c5c410450141c0341c1d14103865800d0070440700511078040015402801d459403a02201c60 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 29720014 1250 29718764 29718779
    0x50c0319110a030804020108060d06051303110601060203030c0f04050409060608070504110f07050106051002030306151603030b010e040207060203100501090302090a0f0902090a0e0c04110d0504080f16030801 91
    0x80745090040c0115104000117401580f00350700130ba030312150003000100d900c403079500c0720000c59000303c888110103001e00310098280b5400038400b003507104158005101940c1083c1e0000d407030780000703000c0691041000c00c4d01101d1022010542d03000e060090300400c40d441d0f00d400d20801a001c140b0480f400340c040c800000c10242001c0c00389144840303448240c86d2030004001001c0302250b006100641e620355a5110120b80c0d07030780d08041108030121660080d0340b01d0905a041000c500741c84410420120420403415040104050124058540504000030225040e80042e03c080c2d0343c90540662152001420b80c0030000d0590107103000e141c0c00100e1860041d151401510b22240a00020354084e2483d4001449104140c00105007543c0034600412003040e20b901180c40c2a2064034960700310740d21000e605c40c5030081045001181c2000320307810b120340d660700380c00030350300e0311035416003601c1a61107000080030b1150000440707500c489801c803030a81d42d001c414040c1c80d82e007403808001c400080c1888000550803 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 29721264 1250 29720014 29720023
    0x20319032303130f140d0c05100204030308070302070201022805010f050615031009060902030105031b01092d060f080109090209010e1e0405010506040b09010e06010f050c031911 78
    0xc02c0f01c0100706480e1811a10752a040b50904c0a04032040403240c07103a030a0f01c0d141400501d05a07440d0740c41d04040c10000c0d240141c10804981d10302c0031007500c140000c1001c03a40c080800b54010101d0b0400580e11506400100c1c1040c4400360801c030450003141c103a5603401041901010800d0003140204403041100380c111083c1d400507a07019902c4034900c40900d0307000b08640001e50f00b1070700c101c0507602030560310113080e81910f50552008031019804001041a4107007401782110700b0640850400381c001c42000013801c0e00100b400b0311207061034601030280c40100c8008403020303052091100d5585d0340c8d5030741100030300440d02508007900103882c020002a4182040c0601403800d540100040712580c00d0036180c4000910080801a10380b0004811403400020002014040c1d40144004985854107d0034042901c00c54240b240c0113401140040045103640e80e9aa90011024a095181c8a58880088455028261010203039000020b18000502400101c00c00e103140541c03100e0030907180500689484 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 29722514 1250 29721264 29721271
    0x18010c0e090a0c11010509010605010f020604150203090a02060c01020a02010c0203121b0405060c0105090607110c130b06040e07020606010801060509010c0501150306020d05090c0a030609020319032303 88
    0x10012101c0410b039288280d4002000303550007403400c084905080740082d401e4800c240ca003038041d65035440080c0b0455901408441051810340010801402c103030355000400b052900c01720015540c0440424098031060184c510966001440261030300d200b505a18000d50100b6070b440003542c83e002d1094502e40c0040150f61078028014006c4a0551342d4943d485e41c00a010300350140103090030400403656549a001034581e951059000042602d09885414940075000d400c120511001100000e800300002641c080d00e40010b41d203441e910744201080502a20280b100c10750b0003100032401242160501c62080d104034040c1d401c548568940e54019203a4090a0043c000010f0f4204919012940150101c092951141d000095009554080d00148035030f02c3d0001c41d411600095103c0020000b4003d0030740141e0000b025101030012040090007007400c1d40300050546484081c0c3d40150354051002d560160b410308000001070f04a80707002086e070310254440945002d809480f031800b4502d181d055911 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 29723764 1250 29722514 29722519
    0xa051309060303050a0c030e1305100902091e040b0a08030a02070902030709030b060a0302120714060a05160804050904030c03081015111006090b150a050703031109030618010c0e 78
    0x241003174204040320205030418099003400503200030500b2a07105c000c00040782c24032032000000c075414040100010030300654031209100b070041c000202e440d07803440c61880141003020b107640300300d9415174040717170140254a40c40303540300056200010740c1030004401045c42600d82c1e425204210349800b134030402c80c00709440c1c88002440300101403000072802d050644e041080104100c254542da58002084254041002120341e0443c50b4204100b1488903440300312414119244c5042209071031000380580030f403020f00c0350a145000060000e2050b0b1400311006080c4c05070001e44203203828107000e01680f0650000305c00060b404030020344020002c040708400c0d0761030349444110160120204942084120740443c54a010384806549407070050702c601c0c00209207441020503002e90100801c00000800d44000c40c5590003017108005240e400011908c00b281d00d401c0028100203807511150b0b8901585070440c0c0c06103e030809000c2808400100401c494004c1e000038000810940300464102c0200c0032841d4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 29725014 1250 29723764 29723767
    0x7050304031d0102100c090906080304030b0a02031017030406091d01060e13051302030c0102030301030302030d090c030803070305010e0105100203032706130c06030b030a02010e060409020a05130906030305 90
    0x4400340e40700720000b40160510480703c03194040f0b0078000840f0aa00c0000000c90201d140c100900d162a003c1e1a00400005000e941882d1547d1034201c01e000300184550003d9a000000840085814110303c0241007802c51020b01c81052007040740d602d501600402c000b05848000c00100b00481504203e0740c07214045207001180d2030940240c40c8844840c0e2410f42c4108402502c4140090500c01c0380c6c0704000c084000320201280b4018541012207110710141190401c10044c0003081e0004119003c800c003449000440d041d00d400c054030313500c10b40e03080240202c00000c01c0c0300d000c9916400442c183e40180e511000e46980c0c88081103192001d02044101580042c03001518900303000c0001d550307420300703c00307841490340c5d05840a90a1540c12101c80114000b038940810a01c0300c2d035603da070050406420708102580384000003035511a800035009041119540f8100c6090b1115829240101403ca10641d150712400070042c0041e00400000056011100400512441035008007803c4035003507210726 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 29726264 1250 29725014 29725037
    0xe010501020a1103031c0501091b050403120c02060c010b030709020c0703031805040c110c0306060904080a17090703061802010e0607140a0305071103010608030406030207052505090705030403 84
    0x50f01c01c0a60103200c00c0c1d06020070b00c41565076103250840000c80440300c0c20300040b41d60601410104440c00301c40035101030f010340101d004813140c005003250248d80c0c00100222041e070014004072890800104001d4002c800403400c100700341e0054000d008402801c074255045291211000300890043c0d200b03140305a404018100003003401440078541c910800c181c9441c61b1034031600410140c40c4080c42010005110301c00702a1103000c00d000c4100f26880071400303814581402c4001807207940000d40040c0c040003001a907420b4440c010b8002c80360100070210000c00034034100f20159111001848107030303440390400400941c00401023200f126201c0c1d058540c0701e92225054241f0106821000044441c0401c0c4e0201c9002060200f104c00c85440c03007565210b5482109180403180d80424101943c040ea0400006003d9500080240c500759003103842c0c01a150041400c0981c81c20803006441c003440d14100380d0382e41641c904200940160740090b13850f201503450b0301e08204d40a02c411600540080c0c500c0628 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 29727514 1250 29726264 29726273
    0xe030d05090d0218100905040b040b0a0f050a0b100305010e010b09030a08160c05190504050606070b040b0103060c080114060a05190908010b06120c030403030905030409060f0e010501020a 82
    0x162009581c090040104820580e010899421401e41c004500c0c1c40c80c00c3c01c00c4401c0c4030007001d18000d81084d0304140304504050742c580301500800360004116090f9400010124042c941c0300b80c0740d8a041503c1800070341402c100120082c0007a8004074001c03200c5c0030300003c64070302a00a0380c2c100c60010115110076031814002090903004100000c0e418000c280000011407558001f80c515400e425403140c0c0908200d01d420f008490789584154007800d03804000201e50b03101c4000341811aa416500414a0b949200c00251548203140c00141016809400e000a01c40c0c000d40041c166440b80000b000440304501c400c0c1d545000134800c0410a200482040506080020240c01c02201380d080907802d01507283c4040c10040440340c20400001c1c403090003000410400d028541105100352141071a04800d48000c04001200410034031303a103036000000c5400c040c0704e039204400c42da41180550380c0300c0740c031500340c44058003840c402c1a203400c114400c0818070115180f560ba04071241600100074611f020360b079 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 29728764 1250 29727514 29727517
    0x702010c0f03140a020303070e0a060804020904020f031209031204050d0807030c1703060102100507021b0a050405070210050906060d020108100506130626040b100801091109070e030d05 81
    0x20441c1042102800030f000260340e4000341141207029009140c40f480c10400c014420643d0081d0240300c2c241c400001c00910303401501854000d80c041d500244180e403280080356540c00c0c42100c4540510400101e00724164814000d840c1c1d030401101650280340388450030008a0040c2e0041e0380d03020007602000c800140800c4001c01c8000d1007800c0c008402a1b0719243c508508058185100034408000100111981d0600003107034103840540c401c0045040c6028020358500344041c41311a42200ea041e0302c0700c19034034520b00900400c00100180024500382000a45031044072115403003942c1082c000c1540300d900400c0e01d82c400c0300054214902d0907903640044403481d2002e446014000000100411651242001043d41010068400301c695203015001005030034800720400d04146036a0a4440c0d9124100c10542c01a8000d400304d0440d490703906480c04203c90f1988504115868100d6050421100c00007802c42454200c1d2042c0442c2c3e5200e4094035440030a60445606402040d0346d28181c034013440 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 29730014 1250 29728764 29728793
    0x30606030a090203061005130e030414010e03010f06061106040312090201050c01240611210c010c09090b040e12160f0501060e1303050d0c03090f0b0402030d050702010c 74
    0x34010030228010f07004a0f050140039102110388505040c0c00b4007440c00c11500c418011829400d04214000742851303e55185d02590290000d0701103a0f42100c400782e8400c11a0000403000200208940911070b400341000f4640340c442c18003c50002c0700d1010301c18401058462140380c15440d280d284001c081e00c2c40d0010407004e18203e040c41818891032040190034800c0b84030700039590343d505080e08811001c5840c4100309074420010803001c40c60845030386501050b0782c800303149418030610310000000441391003030207602c0041072035601e40b40d1056040d0303074011040380c2214042c2c0e030100710405000c410700059601101c610109540003020040107520f80c0001442611852150039211b04842e0b56408041200c0800c1035906a44410080c407070600701511154000d2410440160f00340e0716940c018007540682c209200007983d4a0100010850081d003000483c540d11a0303141d000d075191303407420803151942a6800d038007905c903e410301018980605c003103601e103940503101d01c1328050907580ca0040b0280270b903 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 29731264 1250 29730014 29730031
    0x3060103020705060a090b090a02030c0f03150703021c09030c020f120703050c10020f070608040c0e040807030f0305130f0c0510020706020d02060712020a200a06050c03040803060603 80
    0x2c22061011030002e02000c1e00840c2d0050f4003003000b40c1d441c00c1a080ca040083c02204907500702c681854010307500054480f14a62050313400002c045407a03c0000c0c141400f042030b10135002003c808002c800d5506a0043c0000d9044941350300389144028181c20480303081c868014045645001079801524000382181e4180400811400420000988032420003800d43e000300c5007507105001004452428040c00045e03c00c980c402041225480c01c0a01d85c2c40c45144a0030b801e0081140206042c0041031841c000034001300c0c0d401000f81e080518011110340d0040c181a00003030752303400143c4c01191103406403078002d8550740e88903204281d150f01e414412076041c2c80c0880c0e40c034414040004860302c80c00c19100c3c0d190041c1c0c000d070103007620300b04000c1e0a040c65a600e030b40c11034000508101c02c05800101c50b60603095400c000507102d0300307091000d6a114265034010b448044c01a9000305003084005a10002988204c40a0106446840c1040d21500058500810300c4000f40000749840c14500c001e0366004110 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 29732514 1250 29731264 29731267
    0x3040c0902030402041b09050f100207030807050709050708010603140f01060f0201180b041a04020d030507020f0a090606020d021908030c0d0501090504120c0b010e060307050a0806070206160909020306010302 91
    0x702d503041c07001d200c1211002e00c0400d02c07d0008100c40d1034498100600420f040c3c800c00c44019401c07000035180c504501008049020101c4d41109000e0100200c0024140a1034200401d08100b40d000e000d1030ac0910483e0002030902400310b0010b29205105070040300c64039401d80240c1d081c002c05503403850407104203004541d40c4d030420a5008101b040c2501e44c150058907024213500303050800083c0f0080b043c0059910f026440207010050300d4240c0724160381a01894860b81b514070781d10001d6043c9800a40b0b16071f100f502d010380420200f00644c4031900721045a000c450403030180007800c0c2e84a140341f510a6240fa0003010302d02003c00c200740002c5034803880d0160100c1c60100040c020384200c07482138108081d5640c1c0d8200308000c0204544007003a844d0802c0c1018445098207a541c0300d00708070140600e440011903c00400c440342c0381005001d01030b01000b0000c400c160b4071010519030b94030084030640c1c0148240e1012400d585c0c1d808034629444a01d9568081480d07003841345481c00382d403000c0d10700ca040603030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 29733764 1250 29732514 29732531
    0xb030d0f0224040201110303010305030304061a03030c16120309050d05070503070f03050709140a1d0d020a06110405100503090a06110c06010e0c070609290108060a0203040c090203040204 82
    0x200070b03403031240362290607040d405418940001842048100c400307110540c010001840494000425242d01550141c40851100d44890340070311492408078110b07400d48004911040c18040104800b40c026042c1c4000020441c0d481c8521140140c691754090081072003800c0922141c1001d48e950f500b800c2c065811100441e9a90300403c0ca0041650321915024010210510401a050080c54020100f000f81401128400b0205110001c0080c0c0f2840903943d0b00c40500c07824022001000303403420203072025214460410800a0345840d1024001c0721003a1508500200c50410700701035038140c0d00041c3c0f03000e00202d0040300c159100e610192690500d44611070410000942a00a14918800200009403a202e080c0d41491521106800c00100d0094907010440003214200907582015006840442c01c80d41d1824800304d0030162a41c0c1480c1c401410700d55112010106045074100c1e42d440c0111070380b030f545030065082240004d41c2c00a02541110508001c824600d40165410a00003000000c8109 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 29735014 1250 29733764 29733793
    0x1060e060d06050901030503120c040506180102010905100921020606091005090a02040e13020f0f010513090509071d0708041112100e010204120b040c0f03050a02040b03010b030d0f02 80
    0x13907003603204a40f580d0000510106c4010312015654101289190071406c05050000180d03050040c1d01a21000d0454a045040303241e01c02d4101c01d01c0341c0d400c1819038917107516000c08000500744656059030800031400003000090355241c2410513681c925809040d00da102c000400004500140803601802e10100c2c0204486d80c0d0038080c5400b860200800594580c540a00f0100120000b49007680c005580380104015803515070100110741000c40784106510560340c016982400fa8800d580c80d201c28429021072501425440300d40070741559030480d0119942c8078403601d03400035488001400348090002142809001d4650b036034205128108041140b000c0c9000f0846103600c103c1e00004940c0910610030700e170703962172003400140d0000300c0095152606003040d10b01588a038031401401d0b0310500307000a05120b00e20315280040c0282d01c02e0000003907500d04109a8460301010240e00c500c1c130340031048000c1d180c144284000d030280078015113011415407006031400e510f40707400e80c4c0944c05401d00102524 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 29736264 1250 29735014 29735029
    0x4030507060305060a05040c020604230109060905060127090303020c0307060f0e03090a181104140307090911040c0e0d1b05060a080c03060303090a0303030207170301060e060d0605 79
    0x521982e680040d2a01c0d000d010800c58001c1588942d001c0c03842c5c5103100003040e80c089141d5034090340255209038121043d50014040d01001c005c111403551034000c064040241980007440c0b100e0044040383e01a0b43c80c0c6000c140b0b4070041b69a8490802c1c800c50340c0741511009500003c03c0d89000b81001400c10046500090a40d40182c0d421603081d592214001d0342c02607c0d2203002c07402200c0800840c24032405501003409844180100401600401c00b05445104c1c0c9402000202e0302c40c103030581e101d40d40c480c5036481c04140551110712a014541011910079020f01c00c18500c6078000c0d4a0303e8440702d024042c00010212a18500c007040700810244240c1d407101040440d0151050b11209a01c031040c2c00d0081d0b2a07801c0b0b420040c490041002800e10082c1d1202404c0d07007207540c00400039681d403a64800071389184180711000e0b801c251094400070a040c1c25078098543d05004100070700d00742c10030094482d1036200c02d00400d400716200d181d8200c400d00340000a045480c411002c0010038548480028460 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 29737514 1250 29736264 29736269
    0x4090c050304052e0906060f030b01031104021c1505090c0a08010509060604030221060c030a05090f030d0c05070501020705030c150402030703030e0102031306050406180f03140304030507 82
    0x31900000502040100400c42807021408601a0803001502c400100401c151031824061203c2d84a00c0c03900107014007603100a00424818105011981c0e6a1401c512038410900c030542d203410112500c00c9060070f160088031405000741c200036100d00301e15025803005104481403035031f030140968008222620382c3c21800b8003900c070301100f071506e44003107090007081014160061030060903060180042c81d1180c0c400d580540e5411150102c58003020f400f01c24070500803250f801907501c5107070140320784192810300540c003902d00000148034681e200c40700c050351249008207014107940100000003542c030442d80280c642c82000e103480b030701c0d04c0c0060703c0f05803d9800440040e030b0309810006000520340300c10480030940b40c4402c05007880d42d1030a6000651078000611024003800b00c01c0702e000140360b109100319030070090b09401e8070a199441d400c009100b81c00c03a0043c1004101a500351000910a800d0184121112424022607007400c55540300c1d1203d10384191005688024400480002c000f480769101 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 29738764 1250 29737514 29737517
    0x906050a0818070b0d0b0f0a031412031510050903121b010f020306181603050406020f16110d0b011e0e0405010b041a030c09070207080717010c030c0504090903030204090c 75
    0x315070300c02403808003c40d0450304015208884903044640726231030300904501120b801c8811607021003c001e0381c050501c90f9405242400030780001c200141d904980b282d10344041c6003a03499000c5100d20381010b4031148614185560703d82d0140700040c2404120500904017450108010348a200c15440e400e801c0da520344d00d80c000060340110801c100703030502718280b04200d50340640c0c011143c14115514404511a080c0020805485800083c14040140c04965021034002c1200e42e07204000c3c200e10300741020100e0120303452001d180c54907009103489032144808503000f0000c0c034150f919000a100c0341c2e101c45120451969441000040c07540c0254903400e00c182c0c003400010401c015400100412aa01c0c03008998030301c0e042100d6410340b43c9001030b07130984600c0b00b540c0044041c0c4402c0c50030b0b0b00d46801540b2000d20b500c5245800b007030a000502d0320181d89003e920081c44141d24000e8154140c1d54016440c00000c2c106100030081c545a541100f180340780241401460281c40e801100180d5140b81003850 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 29740014 1250 29738764 29738767
    0xb030307060e0d051e090d0206160209011703090103090c08120c010e0307081804060f06030c02010515090601080403050d02130305190b0601030f0f0612030f0906050a0818070b 77
    0x42c1a0442440b981c2102c2043e4544149060510266140b280d030010144040a00000c28a0400d43e22250202d5500e603400400341031300c40c0f201da0440103001d40c81c0a81280119941c0c0e000042c0e001c50b90b02c20b1000d44404034091410210b00b0001100105107280c02a6a0b0ba80710740070001e0b00c0b442c1800f445a000c461050441d50305c4080364200760a44140040c0c0c001598410000c07080403130b00d00c00c140c2e404001c1c0714040720b130203098000002c2c010f401d0940000d9040d1620f4000086c1c2d80350164003004004950ba0000c0c0000da6550003030901d10021342082a401c94a001d00069207503103c0d0004a51251003030615030304009103416004200c0e04510592582c24507036207014000c3c40001c00c510309847d0804140c10444074a20398a03c01c0103c000b1741f0441c14103449001144040c0c205421071104000b1002c810041240d503840000001038840034150080303441004e00032040c1d03100b403a40800350340c4151165841c08441c60021180510001c1c5a42c0100308000340c460241c00c0248207042c0100820304c80c59 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 29741264 1250 29740014 29740031
    0x609140609070b0c070e2a04080d030203060f04020304080c070303080402120307051509030d090506060f09010f060c03030e01140703050c090a140a05130501081203040203060a0b040b03030706 84
    0x32450b00581d500041083c50050200c40c401c080e00040e41c0c415074000211115494440d5401e0000c49880e00f88480324420b0a81071841e00c808044000d0011120404110b401c01d4003640c40036812131209440c01da030061480d40c07145165003400d400440d04244908072241c07504130100a454240306440c0c008a0014202c0c0080c0700951800540d001c00000280001c2d526028031507030350a07510303030480032614440800440060500d441c20300c191101c5c81c4411409114618040c504243c0340c0500f26645842961030040c00c01543c1010b4a410307041e070703405c0301245100300c1c10480203450021910b1004c5080548661034030214030400e01600101a0b0b841c0d1b0003404c1c9091005002c0c05490f801440c1086105052000d06940d42d921010281101da110101da03481c0d04180011030b2040c0d1240c4c0000b9040844807103038201c000b41d140d1283c0d0403030340e49030291070640e15a040b541800e8402034501039419030142d4007184103140594400e0303982d40001480084e0f0070780000046030458011f035406481c1103682d610306 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 29742514 1250 29741264 29741281
    0x80c01090603050c070b060a080d12051005030a030c0f0f081206190b030901020706050c0301080c1c0303020904151d0a090209040b070203040b0403080a18050f0d06091406 75
    0x1118050407a908007840fa524082108039040d01940030b0140c9904c520101045541e11500c44000c0034041c200c0541e1101500b0ba1806003882c0301e002c55101105240c000040c404c500c081341c1030700688000801030302d511011a20704858151b03a024040c0d8410b450290048005100c449584207103e1188581e5521949040c1202d681d40d80b006102e031313024000e200351035220146424908019121160b035015100d0725070b483c0c1c00c0d0081c050594002c2400f03250405220100892101031412102480d0460b9002614002031180180b85038000326008100c043c5000700003400b07900505011400a4000111403041c0e60510301c1c00f4503a0f03480034544030000300c0c107106440c0c18881c10a50100e80040180480b918a40c0030881306400140080e2406180d0008281d185100388212001082d0018925071100d4403410002c44660092082201042c48140010703038280e1080e00034001c0300c00c010300c51042c4c60501001c0c420744816a11040f11019550380d66500000e80c4150034604251a107401046c442c68448038 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 29743764 1250 29742514 29742527
    0x102070b161107050d080705030705150108030f0d05071716030e01091101030203070c0501060e160f0c1104020c070f03050f03040e0a0b120d0309061b14070c0f080c01 73
    0x100c1400c10400500c400c01c20b6200003000411074200341c424401a00b124100510300c0d00035804001c00c2400b0018095042c001c00040106485440701d11700c10381030b661603107816a00d03c00e900e0304454154080c4000100c0405035400203510a207030341800f0880c4040d400521342d108004664a041601d2207125510100b40d0500c9203800d0152144000c2000e0140c1c2c0d1903490b01c20440b002500e04140e00000014041407191311105c2e901a07100000703000d4140c48801d18000d00004448841c410300b444c048800345540700b8011901c49070460740720785078050b030641c4819025003450800d054000d40c08001c012220b01d010841c4400601016a0b401c403420700f90300e0814144900310311412903590040c0424062211308210781a00b010092400080030035516001c90300d100111102c0c51107030301403034440c0ca50007030300341e0012040f851064800b00a5805841c41d0003007400c1c035214030000051401d10459400c0c0d02080028503190340200381c0381411a6a07201c00300c080c4030f00d5403ca0401504030000e9501d031542c1000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 29745014 1250 29743764 29743801
    0x10c03020901080f1b040303120b0d0f0b04062003060310020702010206010e2211030c01020118140c060c0a0b06040207110d030e040e030c0c09060603010e0a0204080102070b 76
    0x1505510744800180001c1c5202400b07401c001d016400100450102100c5418601d80140d9000703080f41c642e03590f03080181510700c510030205186820466000000d240c40604401c90507403042c03c0c0781c040442d6031500248a8002001103074001d0b03469142c16594580c0e10f2800c4103004041110990b64a054410305080c03040c907400054041e03005002c548010b03a004640c02e81519034940b08103085660310128824000e00d900008070795000981108002c1c40344443c00c520b0f46039800d03012901c0206006004900320b4002c0000e800d003480d00d0b050158000703080065100a01c0e0901c00032503105d2144100000c05607071060025175604c1d84041c2c0a9410455050f0f0b0090303228504031411802c203410f507122296446d4026880c148501d1100c0100c0040600030303c070030045600003500401c42c14591140455032544400080c40182c400c15103400c546291403000d6511400300903040c0c0e400c43e440d02007104000c040244c03000b0041c43e000e000c040703201d0038244050641d2a005440c400040d05003956681460380e41c05 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 29746264 1250 29745014 29745017
    0x6030901091401111b03070f03080402010e030703030503060613031a0108060f011512020d06180b031207020909120309060709080a05120a0e19051807080103020d020f0d05010608010c 80
    0x10b195042c50403640300c1070310780246038505440602052002d060741036101f1904000c00000058060005055102c401c03103104601c01c0c0c0300d1494290a280c109907440302c040c41b00500080c0c040000800c103061202c050413032128000504a0059101c0d0750310358038407500c0c2d610319020f94282c1c001001120001c01010b600413007001005c038002d50400050400804500f80039005010309000d101c4004c0c00c83d603048800c030406000b4204600c0f41c641003040100c152549484d11a03900745400400036240100d03d2002c4480001c0c03040341340c042140e007030203403ca0b0010503004690149c0c00300640028000303001548125405409490a8540044084d041210b150060062a4020301d0107900182001030b820000d800300034080da880307030840b440c1103408100280b0066000385000d4618030141560058a8007618011a00c034a00c4120190a40310b02c1c0d8000c0300c0000000308500010005806c0102d04100c101c0e00190000f161142900041000500041000c44980e995041c00b000740d14028803c00b40c0700f90ba207 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 29747514 1250 29746264 29746271
    0x10903020402120702010b0618010f05070b191104231c050307052424061605010605010201050c180d02061204140303100303050c0c120304081203040c030f1106030901091401 76
    0x102000c03450001c01c2701e414103000a0305102803505024405032849a80c2c899142485460b2140c464140801c4000f00c403108541070992081111008009840a603903e41a40c1c0078405c101946800c010400310101e16004610407050031412500748a0140501c0d00950080d60f40b039801c1e00d0080e261030800b0326490150400009564021441646016040f81800405002c1d480d05026801101c2042422040c1d011384001010b811140d1170001c540c0f80e280c02030000b040b006580f1001a404c2c0e8200325184100410100100d11890034990780741e06031040050401c0b524002c1660100e07440d0f82c007841404104614034010401003040c3c0034148091002c2a82c051411800c00c00030001010b46140401401e000000c168041c51110800c105044104003c208401c41010391100e40e40303a40c032031702629220b4011510303c0391241e44030a04403801158056221a800c0e807030f58a40881c075551115041318140b2030380c120000c150b076500c009540603100348000059441090f1500808441c3c6032001e08080340d04 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 29748764 1250 29747514 29747527
    0x206010e0f070c0f060f0e150f071e03060b0706020306090a0b031207020d0f230703020a0603020d0b0904050d0306091103060103110403080d06050901060507110f010903020402120702010b06 83
    0x2800350880320f4060340319040c1c2154141e5403500d00c0240540d2404050352070302e819014400c3e400c00207242c00034912006032840c010f8442116003420007401315403400100f06142881d01c021500c1401016282e900380c03600082244c2c481d2500c0c0219880a201910f4168002c4107105071450003040041d04020309100400060112201182c2c07620446005111110b0003c9051001d40d102c80f081a002c041d80040d15042d441d04510f42040c05001d003103d503074600c8010550700030421100245000c19079400901c0b800d107207482e141048001e0741c059202e030403c041c0c592502440b191100c1045034011445103002d0500740f08a10401803c503200c1d030744030344c0311281041a2070702c4505400d000c50b40c004100b0f00c1c2c0859407410b2800b0428007846a5803000b024401d00282e02d400c0d44400e03500000c00d4070f40807162104640d90fa81012551405600b5001d007001c0c41501d1348500500d0411070700c089114060510f02c2c4003a0341c0707400080403a042a400304854507806000c00000c2603082c4591001d07503804a600703904264 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 29750014 1250 29748764 29748767
    0x30303040b0117030c060f09010e060103030c081804020d0b01030f09080919080a03030606020d05040509151c0309090b0103230a0f0203160801050109080d03091509030206010e0f07 79
    0x70410701c155110412401c00031040781c401401220030100010007150403500b0721017086851500d0032103010000b5441e0114880d01e40b2004552a03040301d40541c0c80024900d02078030b50034025400003400003a02c1c0e4030301030900029200c074006060108962540098229410350000d070966001ca0300c1b001c801441d01c0203110010b62104291081d912059481c1606074000c03070ba12185c201c1c0f85810040003441140007400405a058101c5030a50b0300310740c00e80d140d00450050039915030103207014040d0301c59440c10010b520907150307811400a40c08002d0001c9240c1e8041c3c03841160764159101c042c4c000500090707050126140d0b500030301520781c8017882c08000342281c400f8084148a21442c42c010540f800c00301040100e0142d4210254041c1003402c110b58070300b04460550b00044d00c102403c40421a24000084d4960140f20810110703500b24014080442030307504220002c00c42604215007220054902043c01c5415100c0c4c0e95801e8400d8009181950400600c4500490010004445511910104100036 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 29751264 1250 29750014 29750033
    0xa0615060c030c060f0518071406030f040c0510030204030b010506070f03121401090c110c06030a1d0d080108120c0a02060d0e1506130b030c0609060d020406020a020a0503030304 78
    0x10760036143c001550245881c080c00900340b5132091071207071824078060220043e1382c0f0745114034114905080300c01e5541e5900300542144015044564409000d000107400100049600380c0c3c0a03202d036494822594886000460314401091904c00090380400c091080020200005000d0402220482d06101556440c10901240f0b81d00050800c520f0824402c1420210b4000803c00c1c98180b401c0340361982c444900100030308468425400151600c4e1400c01c500b00081b40590301d13100040c06042c27866991203c1c00380980541d1141c0c1030201c06c01704901c549004148450020017446540d00e1102c0d5140c5401a860041151556040c060302000050109640001e02d000c910394141e40b05501c85c624207490b02c00400118044200c0c40c020b1a804140001440302420701c1880200c550701494a0119440000c459281d41402d030560710820306108640707044005400740e0310f001000300b440d01c14800d6520081ea001540608056070003004604214586020b41c60f02034413003680213504502e13050701d580c00f10 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 29752514 1250 29751264 29751287
    0x11010605150a0216090b0a05091b09060903010905010b0114040803180406120311061b090418080c0105100b0c030910030608031303150905060a0b0613080a061506 71
    0x1220740011001e042030300a1003210500404804041d81807030741d80498101030044180050b11400c424540490b041ca84001000d000d0240e80300e055111201c540c201c0305a43d03111040140d4052400d005487c1d003642e09014820005100e08008581414481c0015104441d081020719070141d0602c014844801c0020a980303400d07c0350000c444585000300c001c1030061030990440001c0f14000107844041c1508410a5800c031008203044400d01d64401501c00040a01481624180c500400c1580040d20301500200c81030088500800e46d40302e082e940704000c6a104000921960b5100d00030401450034281e6058000e10341d941c019440c0c00014500f054032842402c1e245440380d1082840e44003040c1c401d921103c09400f80c141100d6071080c1c611584144943c0520049980d2942d5040d2820910024050b010340140d10000500d400d44580c514500030f00049001140c04c26020700405464072001d151841c001c111580203071a80310301c00c1c182075060320328840728841d44a180d030404000c582d0b4041c102680 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 29753764 1250 29752514 29752549
    0x703050a03050901090509040f030215060f01050f090d0b070305060f09010501030507090f09020d060b0c151e040c0602061302090711030f0f03090708011e02030901150902090111010605 81
    0x283c424600f00103032155109900902c0c0c0000240080104004400f400800100e000e50225011041c00c581c0c0b0981c1d40c582205da40350401c1f44002104441d5001302d02070680f891038042c81ca41030881e4140800c0360305201b00b80a03100f0345884402d111005405200b141e411000a4901852011113840455054803040c4100e9040641d2400000c000d140f060840790042c2c1a21050340031400d5940c2d840c0c8019401c400f1034031407110b03d070080004018010000f00d618003000d01d07014250408103400c905214441c000c2251001c8040c10403881e14030310038010042d00c03841c4940030301349426042002c024a4a80300404c1035000f00045001c28016035904144541d025526240c90010f4000c4040c9960445c052103040f0010040c010400c8154401c4045c0518481e900b50412a0561580d40603028240d509900e07401c10740c201400c201000440c0260001c1d54000d000000114281c2d00d410301e02c3d400c1030001c0d80200802540825030a840390f0380625015901c0c0720034402070003c1c0b41040001046100c07004507080c0b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 29755014 1250 29753764 29753767
    0x8060105090c0313020d05032203020d14030714010c080a1401091a060d0504030e062b0e0f011505040b0112020703020c0a060804030206010b182e030204170703050a0305 74
    0xc000c440440c44129204d6805454010910001d01d0a5030b81c2ea000301031815100c40c98101000716010468074031008480e001003c07401a8503043d150400d41c1c5064025615050004001310000b142e54070000241150502e000010703114a001001003503144058148686681000d0b85244810ba40b005181d06558070040e00090045045025211640c08a00561740003803010480c07880c1c1c0055944418855070103a1100321650707560000b0007901e4800c0f00702c01e0402c01e40c5100343d07024001d00d21448010001c0300160000ea02070344040664a80844201200c926039110605800d64901d10301c441002001c00360740501c41d80500a001800c101100000c802c44a5400320702101414800c000c0a060300c800601038014094803140c0c01081500304850070b40141c407e1000000300310080c50112427071050045100b85940d00c400042040d5000314a012203006075001da16035a145150030308423820303542c00341c50040ea00c525005090306501e509805440ca90740142070b0070404100c0111742d504400d689498403e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 29756264 1250 29755014 29755021
    0x40501020a112704020f03010e07030314040b0403060e010c030213050f060d090308070305090a030804030e0a0f1202150705030f070c080706080402031005040206090409150903090f08060105090c03 86
    0x103041d505030035201e00c808030350b6808074540401450201a004e80d00a4400706a100803207070a150981d10800101c02056011000820200e4810b0851201c0049103440c11481e25913282c3c2c0c481065045034006445090f9608604540e0034401d04c10810b0310300182c1000d50502c5201d4111250401881c07107054015170010045400c0c603501c07036045600101e400c136010800d45460341001000d12a08441b03150120740340c54081030200d800007600341a80c031303410303551980103640c2d540d005c4036140040d8014603000007041c5800302e00c1a0f08a00400d01401201c400e240c0694841d0041001c0e01c1c222602c1146845010840c1d00c1c08100040110380c00c03c1244050190742e12603510f484110b4800c0703a40001154090418041007466000c03002d11b01560084040350362101480400d0012244240c03070007075002108004440641c105904501442130080041040b0b016401944005840c03601c01c00301c0008881504c284480c1414203038030700280c107820000f40150360400020482000700907045090002d000b2000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 29757514 1250 29756264 29756269
    0x31603020702030706051908010b070609030e0405010320011107060503040f051002030a050f070807030b0303040906080c0a0e01080703060218100e10020a021305040c030b010611070b040501020a11 86
    0x119040103501500f2100500d68030b0303200600d99048880700080701d0108082070f490395441915234506841981c80b5440c80c200c0745503107070001000301d03000440c14055a4204145107907035503c5043c0c0254040c000c244102c078981e604540700c01a801c10014184904c2d60300c0e401004400040c10001d45060303090040d0b49460b14280718030645200d440050a42c0301e82003c900303039040035402a60181c1c41400c02840980c0301c5038104048400c04844c19000075400400041c450341c400d0f008007203540409070960385003507140e40214042d1546604034031000c0c0e102900d51611801c1000f1204010040012f079800f655040000d07882d03d64040d8440980f0444d00400d504042d00c0000240682c5840010079958a515640d00054055102d88013110310031405400d0300c0402c00d00120300518005d42c0100034030702c0180010003140003440b0141069130303800700f0301201100151900360132a000c0c200c5d039283c9440740c80001035212318180242e040013452986c03c1c0003c200e00e0b60001070112005030710411409094500310003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 29758764 1250 29757514 29757517
    0x1020a0516050307200109120203060604090321020301150203070b01031101020709020c0d030c0e010e0d050a06090b100807030c05011d03010501060e03010e161a040513060503190803160302 83
    0x180680301045102070a40d54002d058640e0f85d40820a884016103d55a89450382c0341e200c1c0964041d41507003100000a40340d107815406400058804c2c04c101c1082c00c00c854100079200c14600e003c0e00f045d82c0c004010305c40c20104940c0c0024070b17406403004600e040722644d190080c510040c880101108041302e80c0a100340c1c001d220000143c035520394210f40310351190002035683c00220102c1d00100740b500f0f40010101c0e104094540c0341240684400310508d1000080c803c0400650074181d40318001e0744240070002c1c200c0e020301000740f4012843c108060404040f4110040c0c0d1580c0041081e034080303001040040c00c81080c04044071401d003016600c4240480c41d8220441040b0213a41c3d05520348000810542e0f04243c103030a12107070580c000c200d2a904d10b02016500c108440c6200f011824001080081d054403003001c2c1c080d071200003402130401c1e9940e00420040c9101c254120942901c556050056040400c82e40c99a1491080300ea83e444002d0b8540c00401d00c0044d141d40d2120400310141c802c240d01940 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 29760014 1250 29758764 29758777
    0x402030733030507120903080c0d060317040303120501050306010e06010c0203121c02090906041107060903030b040e010903200f03160309051e130605060d1d01020a05160503 76
    0x1c0e034803111060940c40003801040101c80079804213142c240b010380061340c140700342200a681030b2683c803100c0d2205008203259402030140303403049949400c0088001038035100c0f48034401c1900442c41d5200d500350318000d011f00700c5801c3c0802200e864080100038559001514074110740685003840364070344131000100da00e00380c03080d4081d40501c15001074000030704602008054158007620098a81159186910217a10400000c3e030b912a4500d40400c80310b1070720780d01c545c2564016465103890000c0903034400054034002c507002d030b0100ba9a41d00240340c03810940500040d05c099003008010717a54207031307a01514240f03100450030601ba01d803503041d5240b104100b001031100c010328002c403a00c60340410420800c075901200d040340040c8403024000b4003802c01c9001c404511100c248108807580c5440c0074400b00120341e6003408038054483c200011a0388401e0014484406070100100785000d1307941000c035407200540140801e90b0b10400604040a07803010603a071010303008000701c0e01d0001a40c18454514040d58 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 29761264 1250 29760014 29760089
    0x60f180b2109060601020c01030b031c02070305120301030203100207032003040801090f060b0108060120120f0a030509071404020309033601050304080a18031202010c080f04020307 79
    0x110148400c40d040003c0240c4509401d03801c076480034030820300440c01d95880c03c0600da01580504c048000d414400c00014044104500c100c8031801e0b130381e840340e5242400483c01e04d003011000000520640c10240301d0aa007600d15203c003580340004554000b018030180e8840d0364803410a188034480c500b0710900c21200240400002408114114113051154090200044401d54900383d00b0303240e1540285a56481200142c5804c9003400c80500c024910a400341c0f00302c0102c0c00b48010f505111007900010b4000c0b80d02c00080c103a00c0b24584240034003141d5019001075071130380c4003000422034602115800344042a054402580325100c00c0b030fa8910358094904140a071403029080c1b200400031442e0b8050220f180000300c5915900340c100152094802503502800424080020542c41030090b4030081d0003440383d4540071504c035a80d488840142440000500060751194003141c42d03158019501900300d07403100c18010190070960700080e610955441401c2800109200c400320968000f502d4401001d0032 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 29762514 1250 29761264 29761327
    0x20313050d030b010306121e0503040515071a0609130302070506030103110a0f0b09010509010c0203070e0a11192f010b040507020a050c1203040302031006060f180b 72
    0x200350090090041041080c4c0024a040000904944580107a44066411101d41c0315003a09040c1108d041c540710354810303140d5202c20030002600780c4400c1c0e907600b01c1b03000349144261903141d1407500d21151400d500b032400c0d0355105842800615903039500800e8005960204c52280403070249016804d2481c90f501c001d500c608048000400c1c0041d190b0740d411505422500c9140d4587c88400c0412b800c0c0090041c05900d1100707212411181d40900010982c007401410420440d88859000a240c200a0b130040c2071102c40d014148000c400d024080c08520411038161181400b400030080d010201601d0541d0b010403110321410304621000a0b075007101d00700944149180c2428035503005000e000c441c80100d00031440c060000d42d40602c080f0f00b21005a501c0005060384a00e240b0030080f905110802c0f6424a001c10000000103940400040013801d22482d00031513081d1034900e01800803210b81102d40e040c0500004941101070181410105a52404030019102c0c42450705d01c000186c0307024040041e5101c0e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 29763764 1250 29762514 29762533
    0x180e090304030203010c020f030d050c160f02010201050106020706170c1905090901150e040504060b040c111507020a03080a0b0d080c070f080c0904060f020a080709060804080d02031305 81
    0x202100a100b540d00a4000b4000c3c06c20003001207030b445800a40040e12034009210800c2040c40f542c000720f400c4107030b00030102d00f007446202001c4400c03e81c0d0311045500342c02c1d040e040421942c0a00825006144500142071001e180c07000281880800228461842c160b40c07002501072074007001500c0c900307819030070281c6184822000c090100e0340240740c650301c604410000025a40b2442040c000341c0c0c00350ba0b4480c400c40e200f1800f88805458050411100c070740d111486c1d0362083e01c07688616280740030b044d0b40e600c044004070021642480c00d06403c2a454040a40400c0301240d000114291559450300d054940c540c2c413210366200400e01c1032503407680003032407002410074445c1c004050002008c2c030710181d9405030365951000005e41c10314801c2c454240c000a250015518292103101e502c140280340114003641040e100c1012070340024503032008039400c0e100b8807000c141d1107500760000d000703503080c5882c0c5401c00303490380e640f107004a10550094613000000900c00d40c14406548c0034031544103046800c41c20 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 29765014 1250 29763764 29763781
    0x60e0405030a080a06060c080705071e05120f030319060b0d020309063d0b070807120f08040609021309140c240f0f07030e1c030e01180e 60
    0x184882d415900045104020456030403982c440d107011500503403606e035086080c03641d800125800071b00081e24103000eaa00001441420001d070641410361090300350007094203110801941144105078820140c1c04007510b0351804030000704072030708800901c001082c2d10340509020760240406400c62021340b00c000c00c3c2000400d96980240d80141000b4083d25242d82d5901035a405140d03141c460041081881d543e88400c1c05042888080b03200c400c001106012910340c03400c450607510040048450b240700044c0d240620100260300010061189040103040c02c40100050102e4000303000600020b94442065045540c0c000c070428004c1da2450003031000b0f81c00c50a08a00c150585402c1c0d5915018100c03a0510300e25000004040390190000d12180d02c009003000d0902e25004521803c6500c0c004000e945a0542c2080107056004d2282c0e4031040c24003040c00504c45164100705d002c040410180c414100000e030480e00c0d6031015002840d0280c000c40030001c004040c8606913001032000c2c0d4506050102e0302 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 29766264 1250 29765014 29765017
    0x9030708070e0a06050d051c03060e04080c0706090e1b04031a0405070f05130c0c0f06050103030f030b1e01050d14040507050a06050a08070c080a02010c03110c0a060b0301060e040503 80
    0x3803d44803030400034583d90b8803c1c411450300b40700c0000c0030360b001040c40000440d141c000589130000709140004206072034007110f81e490101610306842504002c5464003502e541042a2000707030089260644915141540040d41000c0180601e00b00d44107508003001414551800d4400a64002407103201041c1d442401d03d44070760055a0036a22030141207004a403200143d405007080390400341280e10340004100e8100300070100790400004018083d80079402080e10b0403460302c80540034a82c001001c0d4503510b8058a00120640c0b10410b05003809094800c40e600c90411408038140b07603100d042d00d410f02c180102c81c180301d55030080c0b45076407400b20001550a215520207203c1e5110794202d2b542107464404216101c03036140300355000140b0030803101c10028412610184c022215040602c1031104d25614800942c20455060300142e661352400c00c01036901d0f01901000c0040d2003052468007400b92211901e43c0044a000b410090322403084007800c0e20f09601500c000c0400402042d40341c01c052811549030b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 29767514 1250 29766264 29766271
    0xf0303050a02101109030d0207180510030c06020303070201150b0901080a0609020408030a080a020c070501140d020304030e010e150a030b010512040c031b0e19021b010506011403010509060609030708070e 89
    0x28843c6000b07c0140c00d000090050555414031403200c5940c21501d00c80c805064024211680306106100000000305040e40c1c202c003034061034014645070b00c3d12000003400c4070300403003004240e040480d80400c4050418000c480034417400f0700e0061081d6891011100247c5401e500011001e44000b0780062107203404000b03012180712542d42c664075510f818103203106030b004202d80d1420701e4004040410070307907009140c100125913040881c141414503052200c0c1c1240c104071001d90100350f00558140b0303250b178004d21380741c451501200c0f500914051261060b0281c02081c580b00f0500d40e45100c000c030180e010310259010b54086c040024101c5c0742c00c0c5000280808184000c0f42c0c4845aa0b83c0b0340002c0610a09034000c0c1c3d40c0031510071220b5a41d012001c000901841c995034030440e402c20113640c4c4002c19901c2c0300c0701c64210500200349402d01e44001410030b4070303030094200036401c180300612040c0d46980350345801c001c0446400c4d0301d40380fa0f1000a030070104e0540c410107a9100703442e00002c00c003515a84d100d10 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 29768764 1250 29767514 29767519
    0x30406120203040c0506090d050a1a060913080904060308070c06020d110d0302071109070305090708030703050910030e070305061b070b0402040f020903070b07020310060f0303050a02101109 83
    0x200c4a00e0a42450140d010070780c1c0042c01c1c0403c402007031049091140250901c40e10040c14011900c0341501d80b5414044240003d07620b50343c000c111344507640903044074950407800507104103015142202e644180d4114181d0000c1640030001060842540e4a81043c03025540005409a8030b003000e2a0103044c0c56518032410300580240c5a000000a0149149000240c141c0010703000008403060120001d500c107200840b00300c101b00c507000000b92103040105114071070300e880c00900741c00c0007420340307103441c0251b0700c55800d503802000710074006a4031009451203034a06844124003008080c01c02d502031b01c100481c41a440c45880c0c4002706201c00010454013804051081c4000e40701401c840e2400d0740305092014101e000098041001806c050744000c3c2c00c2da002c400010305045020b000241454440c0c1d202c10900e210101c0c901041d0310b000d0000340c1c14005251000c000d50703071411540c1010703001184009814400e001c10070880c014003c1c000d000c078171301c205642004400b5a58508070080e41040b10080d0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 29770014 1250 29768764 29768777
    0x12100e070803040608070207230906040e0c0f060c0a0c090e0a0803061e1c060506100e1507080d051e09120c100e010e1504080409091a0702030406 64
    0x290412010880c0026140c07280302541ca400d080ca032050b05c110001410310411482030944c00507170001104201e02941c2504422448403040d40d008000561b803016001e039100350b1030002c813411361200001380c1d484110300a0316100018510640004d00d9400ba201c9905490b0150004002c10040d90700c000c0002c1e00c041c030000b0010000446109560f0b2241078074002e015800c100003140141c074003610449081032600d150460015a040041242107441070300509911991054110401c0010300400381d00080c1901d5020b0f06091942c2c00a100900800f41c940c001c60f0030b0141c24114980540807104101d4200c201d990742e442c07030b5040110060104440301f0310400000d102035640302c600510034601a960110041c107008480c01d4030705200c0e0b072201c00803c11350711900000d142000460f00441001b00c007004000035040441048a60038180701c400107400c2007601408000000c0e8441068a0584a0210300040c0002c01c5103044107c1e0000204002c3d21b400403142003261842d80000200196141951482d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 29771264 1250 29770014 29770031
    0x2b03020609060601120f0219090501021203040b04060b030322031a09060a050910060306060509060a030b0c0d0612140d0207080a06090f0b0a0207061b0e040c030b1210 73
    0x2d8403614140c1e0305500041c4003586102d4a00030a0300003032006460403000500d40b00b0f49110b003140007a447c14074440410005030301004550b80511440c1e440840c002e00b1b141c03440c134182d503418042c000024001007905964034139811041e1020400d550150340300308851034403025028451180e411881c4011207120000c003024074407640d211120030380a2409600100350710340700c044c5410054400201099418802c03605160f8200f0307080c0c00303400025030051500003502e50401c814003150440c0280400e0043c0b04504081000464146091b075100e0210407405850329040300c40d660140501d9446101082d04c44c0314031105000480811114003400202241c0300303d40c4141081e0f03100c506d00d103e140d820b43c115004400224500790440405a80b01d82c640741100025561280c3d0b1070302040d1410400c056000c581c0c01f00f0089a8400d000304448000460485103440c03201c020010381d00e04c20014055501c6030840902c003400782d000000c1d8030100a0035812040c0000128070f5030b4141d0b407186980c5c01401c14060 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 29772514 1250 29771264 29771281
    0x3010911070201080703050405030904020a030203090706020a05070303031802090405030903150601140d021201060f0306050103020922090203030301060c05060a0506030c011112031509090c0108060d022b030206 92
    0xca6480c02c1d810384813000d039561108411b40080900078030603a010f000400c40b05040d59210310081000032003a0f00c0040c2c6070b0074007001e441c2c40c041090b0801015903106164a401203a00040c81c401100d034580307008100e155040c0035122004004c0300c0c0c000d4011454200348020000040040c1ca0516416011100700c101e442c0005001c13250141e90503400300700c902154001d100035940040c104450742d07846c00351a01c000b40340b400761954001d07413144000802d190306810400d03915004d6040108024a41581055815000900c0302a124548540701c454002c540b160200b02c50341004842e25001400d898880da03403810090100036169100301e80e03c3c011100014003880907032160a0107000d0107001006120f00080c015160700c10a4003a60720f5621448070407d800d21480002103104460302c0e00401c03509101003041c000b2861001e00b0000a94200c28014030309d59a003c440942d01000841e00090010281d0020031600003d14404a000841e813580d0041481030150920031054403980c02c0310019035501e2074 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 29773764 1250 29772514 29772517
    0x30d09030b0f0103080405060901020c0307030b01081603050309060d09060912030608070b07020402161209061101021801050a0e030303130c0e04050d0c06060b0310030c09090201121505060408010203010911 90
    0x800b000d01c1440107001f00c0c00c10801030a50100180100c56822060b180000d01d0b00f01c445d031003103c3c503112070300c01400b0b078210a01a01c4400c800d4019003070a1241195210380d00d034050121114011000421850b8242d5110303000000b405410410811400d400c6040460819108070f41401c042400c00c200040c1c02000010b0840444141c1c4180c20306101d030603030800010f540003000042421001003205404102e9003c2d404d40445000d80351001c802389084005840c0002d0700801c80c00070b074814040040300302c03400400c00c8030742102460001d59030f080d22542910360409000e000fa0709440084100080d200a0050921020b809840b400c400c4940da007c4c042e10301e18017260010415000000300d10180c502440311006840d200318000300760b040d15488803081c140c0040758407040c1c60314000c0c400c000f4441c3c013103441000703070081e480140400700403900041c140c030a2000d4503412113982e8030001d0200f9a050403000e00503100061080381e48665441d0018040d40080c00344501081c60b020045c000c8138080390 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 29775014 1250 29773764 29773769
    0x3090503120c0a0204050604020702130621030e0907021c08100b0f0708031315020319060b0406120605101d030a020d08030601030f0c03021b1912050702030d09030b0f01 74
    0x401003e85103995424070000e802c000d030019401a4003405001c00681d81c82106071005a0b094000041d400d140240a50f03020070001e050401080c51050645c0129510107410746050100351501d901685621070100d00e4641404403e603400022141c0744412554014030b001d00030794036031130600c2c90a070322140200c0041c030644030081d03101001048000001520380000d10f9000300003400110410700d0540314600f02034050810b00c82840d500004000d5a0140e5010041418908110800c0710f54205a400c04051042d4000c030fa0174080710109448d040e00300c1d80c2084000c0c100c00350101440820454020f00540031400c5105051034540440e2641410006160f030600c1c0d4000708400280c60075a1122045984040e0110341013548440e2500030040301070080518002c00c0d542e0059030b80e0380c000c00c06110305030620000d84041d0015120003110711440c44130400520b40001514000f088040703015a101e10a00307500a415005003001c4000b842d4000f07011508580c01001c0c00026a61044406540d045090 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 29776264 1250 29775014 29775037
    0xf090b0108151315021303062004060c080405180403080106020c0d060c1206030c0906060206010506030703052707060f0203090102150c090904060504020103180c120c050402070309050312 82
    0x1000090f2140358240c00d41034100d000354030980d6000c40b1062038800307a9110000b000110106503408004020301e0780701d82d1a0390507000c0c0c500305c1c21032000080c0b050f251255100384000c008c240c00088091186005c00c1300c00a0100400c1d2403880b4242e06000d61b40c0400840d0150003180365035000184081c0081600261143c0080205050722041d030f132000020a10440c1017000c100150002e160080f401d44200300156014080000405180030840740032f9030002d41003203003190480001040f0342d486038003d40c0d400014604000c600d56a400c20301c15040b42e45030f000000384034240b0000141555001c075445050380d206a54000341c54841101c142d980b84039100305140141e1042141d0a4444c6001050300e80195441e0490b0b880c01409200142000409490603240749076140c06000456815100720b15041c101041440d000764065204e1121582c0d49100e48035548090300c2d85403003000b00a41d400400340c00010011500d6480e036080080040c0c2007030190300e000e846040e00c1c0d00c1e84061400107a501a0041 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 29777514 1250 29776264 29776303
    0x7020a020108250305100f0602060402090a02070b01030303050702070f06051c0e01020c030d0516080a02030703020d09030c030207290c0a05070305030309010612020f0105070f060f090b0108 83
    0x5500442e0418001440110041c40744030710341159040a4200d89510354680c0d07000b05403400d0660403c004110141d0001c2c0b5100c220480401a10780c01050440c0d101c0c0d01104e04203840d42d18104d105000e480f98810081c541d114070310021040503003542c4054000c203015400c4490b1562070f903154188141c410700030b8030013041c4280b081c0040d04040079102103440e000c1036804600004206600d60998000e007a21035190382000c600380c52226a40d00c9102c0d4441d100200d070400e042000c0c54054902000034044901040e00000007403500750181d01107a481c502c402a003001074541ca801e0090030340040d200100c00500407101c0010344c500143c8642c18842c2465100c1e1802481c0d40500d01c201d0754070404c81c2042d94014101c065020410a0000c0c00096000744099503907450044102402c49502d13400031701140c0c00d00b40303141c000758803a10404101c04000f070034107036540c8015080a8040c1c050061000b010f20f0700700041206c50102540180c1e09681c030980c036116030760340c031801d60310740f241e81d03440d11040350550 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 29778764 1250 29777514 29777533
    0x90103021c050f07060e12150c070501020c031626090f0a0503030c01020301080f0d0f0305071704051b060c0d0e0a2c09191101090e090607080601080702 67
    0x1e0351414a91601c220b0450b00101d003000440e03410040680c0c13102e070100b0344502d412451030800c0e0b4800004c00c503000b8040e111080295004408a101c0a4100d262840011540d0000c1000950440b01c8508003402100d888000b00c041540406004250440c1c207102c0301d511210210703200c500501707405a164003c207404d03d9040c5c0207200d03005c1c10700da40043e48500e401c54001188d8a09000620074000c9070400541d072503040500c401d00e0480c50f040e1a0805a105101c0502d49030b62040380301e60b2490b80c45c5404200d030703102d1040403035a0308000e82d14880348600c000144010081300081084c20359803609e806400084800e030801c02c0301d00074000c6206c6260800403480c1c2d00c4500c1801700c01c0195000800c000429500c2c0c56104a00100000000f01100e81160007110704c4d40e44e50544980c00702200d00107150410019800440301d026880c0000e02d0b0020b480612540caa026459030700c06020354140102040c9031400c01241d0710401504c04001141e80311001c42e90b82d51283c001c0920522180c1c008044e0f000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 29780014 1250 29778764 29778799
    0x801060b2a0c13020405040204030f060501051206011203120c030914010c080103020f060c0a0501051b09060a0806060c0118060506091e060402210402010905010f1403100b0f070303050609010302 85
    0x400b183c0400b0381d50130003001c225640d40b84040c00c0a14080d0390702551030456071510b04112001030700014403680d0080384000504500050a50540349040705000c040003d40c642503403141103616802800a081070110fa403503951660112a090307008a04103041401182c1080d800c840c11030102d500081c1e801b000500c09820020880240c05d03c02400d0145812103c20001d0f0501c10140d8046843ea51944103105070b00320b51242d04031810142d80c040c6890b10005034002501c2b0721820409900344060100043c213190360f80c0d030540d50601030000080c030148462441c2c148241404007411207600745084003007151070404c07100072031207032aa243c400380c803400504007140c644400082600394015000c12508040c1030541030394001d9200403105840d0141024800541003940702c3d00b1044c100041d0b0645000c800c0d5000f41e00003000c881010825a90391103000400b0b140314042d4000707180c203d60000c0d502c40e68082c0c02004020300c50103a6410000c0362600b60421180403028800070758032804024000340e104 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 29781264 1250 29780014 29780029
    0x150806040318181104031b1403010c0e120a0203060c04031506120b0901020f070b070f02010b0a051e040606110d020102040f0b030a02130f060210090b010608070203040801060b2a0c 79
    0x1494400711312420996203603215010b00b40019140b04803110030940410a400560a0058110781c04a00a0211a00c0c18a008003c405902d9007244074501090300380c0d041d40c00920141c3c000d590060250351043c80e006180000592040c4811030383d543e86580e13813841903040c910482c015600441440441c0704229203501220000240014095545c200b04509034810410018070004d40325420003850f0346800e0178042d080e1078031000d0600640e41094040320340740c0e5500d902d600c25154115996100c08000445507921700b01107403842c81c1c0040c9422004130f20150000103003955a1040e00440e07008060b000b90803400e070f00039407091541e0084980c0d4188070450500c00959440b9026110050400030303141e0720303d02850101c3d441000c168003200d00c14094241d052103100c410381120304050000106d155104100c01205205090402c05903002040d41300b4400e000700d900405240c402440340b030380c4440e41d44489610840712890342003e128100d92200080390015992501c1c200c0151a109107030302c1c00d00004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 29782514 1250 29781264 29781281
    0x10501030c020708100c030b090613020a03020d020309010504060b0a030f060203070c02040c08040c1208180f03070807050a060305090319050405030a050a060509030702060a0309020415080604031818 87
    0xd40c00f488102040340802040307104892140d50001240000101c03201a0443c0c2c20b90000c14010140d0342c04011140e200d40b6103003000ca500c0400010b80e10b804090703084009000d03013480c01d242c940c000024800410300540109010394000d04007001118890300810600382010b100041c105880310400d400406c1c12940a15801040c50510350401e0546a0014080b52040c0e4848000305034500c09000a200041082101a10b403011102e602d88006440d081e81d40e02504a0044800300d5041c4640102d840381d0107100221300c00038003150a01c40e12012807035243d40310350080a0044c104003e0000350184280540b50080c90010044c0d450709408042c1e010102050780769001c1401010000050591000c0240d20300040c0501d01810003003880307180040588101615220719a4010700c00b41d0701681c2d60078100e444030111803c001507400c02600c00f00d006488002440741269408200010b0104808140507105a229a8540b40c021500c09000701c80d1440900403800c4644001103008015000c950210f2003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 29783764 1250 29782514 29782517
    0x606080403020d0320040b030702010f02090102031606060302060301030b150103020702060412050718140603013c021602100c110d0804090c0c02030f060c03070c0602090d2315010501030c 82
    0x89220024080e645902a131f02c0b802c0c2c0c501d800000c002090b542803080724003200540f00c0652400800e100001e503a4022041460f0ba00001c080b107040810070070b940502c005603806400a503d03907a4a05101d822f0440c01c84081a420400c00d03c0c2d45000d40c1301e4421100d48a030700604240c01d00c1c4c03c0c8014181d41800f0740e41d007142c80d0700c110304012458050104030101407100b02c03540446d0103152410040100302e03000d840e03e800b0b681031006410b130403002800f000c01f880310490a074400301c124003e240e000130340990480005003440000d00700c00d20345c0c110070f40c018102d0007946c00e00ca400c48801d0f41161200030481029007804450520089031349003100c41ea555403030141d420642050f03204c40d8503c044841c118600c4001c5800d1121100c1142000d01102d501624100c02071f0032507142410424640307110091400f406c00070450611410042180e05549404201420041c0c03d46014984608045040700b9408115019182c40d130040c02130001d40e070f4000500d01154102c81d46d1921005401810341d8604910 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 29785014 1250 29783764 29783801
    0x2070605161a2406040f06210207050312060f031203191401080c01080f07030f09080304060506010306090603020a0b130509040302060a060902040b07150209041805010606080403020d03 81
    0x20b600018100c1454001e824044000c2c3c85070140c1001d00e40340c0c54545a0b044d025003001e01c000c0101581c40380e403040458440707050458900c00740402c0e0300080100001305410803840405c644003480b4000028190103c00441c5803142c54462074200440c8540d604441d580c194004404002401c00c6500919006412a82d041ca441901580007405036000c4140545a02c4412001048940e07000c01185204000c00c0c203041c0c00d0703400d0079400062089801402c1034281615015000f0304110288d0150040c540c021002c241c8a0402e454148040c00c0f042d40d01c50f000074200318010454903501d1043c03c049030740c01051888000e1134003138061003070707008440450300c0141070040004042d1107452009106034403d902130446071070122448003c5504c0f68011000c503901c1403105000d69000b8034200c9100070381201d011800b440d440f41505021307106507401203802600340b80e000740f0029846105041c0c8207200b14002d002c0c803615500308850600d02190080c0059002110302c1c811640280d208200e004286038161 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 29786264 1250 29785014 29785043
    0x1a0c0717190219080115060c1e0203030403060203010b120903040602030909100807060c060e06011a2a0c0102010b030303060d0818100807031d0c060a020c0301050a0209100207060516 80
    0x3000002980c4d00c8422240d45a19008482c400038840d0701000d080903040c10140384000d0b03100d070310340303055841060862148111121001d554042090300c00559104200b90f40d00d42c2c48407840411900080c00c440040d0550300302080700d82030003005940035200c0a81c019424021202c04008201101504441c6024078104c1c02040c088010302c618005494191940c94401190780307015012210142815030303540d0800c1d8018450303210f0400c040000b410f0940c528a485040d0340c030a040603203001048450b000390142100c1d012030740c0040386d65070200001f42c008000e9400c00c801810345034801260183d50014903002614000303000000909603903000d00c0e0801c10100034450210b451100030b03048120100b0136000400c0a2541d05004881200e402c2d00d403080340710924202c80559554914003c0d0380310358000304140c0c0241b8800c12111060010007402817050f410030117403140c005d6220943d91030145da8940c2082d0409400058401c2c1119416900d0f00d240ca40d501d40c182c151001d0b4030301c00703e40c5000031203a403 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 29787514 1250 29786264 29786299
    0x80f160309080c03070c12050618010b09010314070906030b0a05070909020c030715150506090d0501051602120a02061504091203141e040b101a0c07171902 68
    0x1030308003483c6000c001c40c1e55034818180303035641541030350081c1410391445458030001180810b8907500710141e0040242a03a4a18601c0ca0141c0500e960060b0080c02c0d98000009000c4a514920280765a01c402d480d062504c41c2c0c4030600f41e5070140009051244d001010130458100d690159610001500d00341811640381d501000690b8806000000760364400f003001424000450580300351994185070402a005404224548550b154030502d0720030034010400e1700ca80d1701c415268130b0110358004d00800c298a4070b6401c0c10f400c121610359030320051203108045030b5894450011104100ba00b40c005000555505074440c0154272501502b58105403994944c0d0005021030300c0d0044400c05685012801025440c002c0c4084d060040c90080302c0c400035040300d200d405440b604180c00c1500001c81d440a59100c120745441c1008503405002008160400c0200004003100581000700e004011385080e644d950311a42608070044031001081c3c1c00c0741070307150441d400506900030a03a1019003504d195224007441e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 29788764 1250 29787514 29787517
    0x50a0f030512064006091b0513030803060102010f060603020910020706050a0804050c060406020a150b010912050f01020406020304060305130b010509360d080f16030908 74
    0x1100415408500c0c2c00812080000b80759000e541900c0c294122501c2e4580c02c88041c41508421808415440b6400042c54640c003120801e0310601ca002d0200550f00c0f1285801005081c1c205101d010b580d50600c00d09034860301c11070340b40303480e60106080480e0554441032039a0303101030580c5040d5036035518040540300b0301c1d02400000f052951001030b2100c0c082000d00910310301000d9908115004030718244512500101950751203040ca2038448040d5507a40380c014a4400324030380c801d50041021a0000d005a4005130088003e4450091000c2c003d503010000001d503541c0a101c1070108607003500c02e00c40ba00301c1e003103406c1003c0d008a0445846030380000c1d1150881c0d00036000080107820000b810f001c0160140240760700a0145141030394128825100c964482d981801583d00c100f80d0100421410580c18091001140441c0b0306842e010003078888030403a08010003641c1c0700c41c0c0104980c42e80c01602442200784100818014050241e0b60b200c1002140e6109810031000e15130344020030710100c0c86100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 29790014 1250 29788764 29788793
    0x9011e060303020606010201051017010b03190c0b07050a0308060d020901060807031505030a02040902030f03030703060e070e010f081305031c0e120703030b150c150a020703020304030f050a 83
    0x800190103007181802828108020849415a8100418819607242d0455900308407940507a0008400248240050141c00070102c090740c90f204205a8035501c029a81d4241c02043c480c0341d99042e0355a8801e49080d850142c00006003180c0c01a0301080040b0b801955240d60010000342095000704442e030000d0007454081c0c1214000900090401506a4252150419105182d501c200c003080c90140040d98030ba5084c1002401242c545d8186021901d04120009030303022038000703aa0303d07454a068000d00815a034807070b19600501002c045400e080c001c52401e1145041a1354490103601481070580d00e540028115500f080e1f102c950110204400380003515101c1c800a001444030007200201c40e0541e042c0b09512510b03600900780f91120581c03028200c2d1000c1c0e07450304001c140485158006224016020342541d01c91200107050300c12900023150180d0701014541250280351a180c200b00100c0c02400c10040140c0c1c4200310510210358650103043e446032140c021140300c100e980e941c03110607100e001c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 29791264 1250 29790014 29790071
    0x1302090a0b0909010b0904020f04060f1202010905010c0809240403031e0801060203030a090305160f0308010801020a050403060905070519030309060503040c030b090715020703020102060a0e03070305030901 90
    0xc041da81d086141c01103190750044541c42c0244200d8101c000000d10740d50014000170310a4510310404201c1b601d86400c0107006003c499280d180b0300d030b540da0384080e008414420407400650a02d00210341c940c015440e2203900ca4000010900341071908040c07080c02010750651a0030101c100d5062100310704d03001d0007072003d14401d035a421854101500fa00071089181800d560070311030450010300400d54000196030f40305423003420102d40100c050070b0030b4a0901c1402100391054a1740090174007800750885c200102c0d07274882e0741c80c0050340ea80d40030b1310740c00c03401501a0a1f0015030200020800b040b0a90040504103000380c5c2030718a910f95903000156008407190810290303001d800300410915411442400051211782000b034650b180543e2810003245490100420f0446071001044201c2d100304100c001070a462205104480304a0f000a59102e000c0d10040740107105000014015500e54000d2040e0f8a448600850410746c17559030640d0103400051501d010f540d40d9140c032100980910303064070340300b1122 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 29792514 1250 29791264 29791271
    0x60c030b09090102040303020a23010507081602010c02060c130b04030c030c0b04030305190215040813091829010e011d090a0201030c0c0605010b0a030c020d020c01081302090a 77
    0x21024415841e2004002030441e910621081000c0390b000319080d214103900000f80207940c142020010761407110714002e80e1042d842c010801c034645420107036690058261200000032540080f00032401eaa4500380c086005030069800b040441040d000070700000001d28040071025620f1300d161592503001b541c0b0588011155042c01c00a100d00d13030300c1480141071542100307032401d82182c5001d060381c420380711000240b07a515071540c0c50691090142c00e0581c841000744060500742410007c20766040305040e1101d00ea8008000502058a841444444840c1640d0122980c9046d01c0b1050350203d013141601203000b025107240040d080301075601d40a0021011a80c020354100242c40c4000103190400e50001d04180050248650f000100103180e141e0903e00820380f41c00c4ca8204507175080070342c0e2004041604080001c11187d48031000303441c1030a800c0d60200450715604034100d965080c1c010000340941c100b1000111103521030b00031581d0010000d004100d60702c0c003a40c04950411411102a0b040d60394 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 29793764 1250 29792514 29792531
    0x601032403170403110609060706050a1a0a05010801170f1f05070f1e02190303050a2d05090712060b030606010e031506040f0c0903140106030b0a020703030603060c03 73
    0x1550341442c400020202c58a04050a5a64108800d017001c003109114040100d101c1c0015030711402200c0d94590311590a211900300021180f01a062944400c28030114008000e030060624030000011210165200e1701d0503441d2841c44182c03e2000c6c1d112407001d01803a00000c040e0072003082000c14510b01203400c0c05050040c2c0b1004011140050440c000b04080568030481e5103038845184405d980481c202d00000840394602a8580003181c07484019070310405802c90b051603015400700f4890f52100030709120821040850003900c401c1440e5040404a04000321140c1d04c10940c0461384c05000c140403151a25100c41075100041e450007000c0b201c2c5030f20b4422a092a08080c010150011005e0070925500001c0b80c0000351070f208280c0c80345d00a00d06040000f69242e81d150884842032008900420004100c108010b1044120740420703107040301810312070500c0003130510070700c01181c0e004801c1c03045548640d0301040c00380d0b10051040c1c040684982d004400b2850314414050a80c01030340f800680f021 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 29795014 1250 29793764 29793773
    0x203120108010501050a03020f030715170c04211e06050a0e060c0405120a02060f0304051207110409030c05010f020a030b031207030f050d020301180b06030405150601032403 76
    0x1005030001c80c01c0d64101001002075440303d4043e80b064981c100c0b49540c1407061350010924000080e4032548001d00c05010206580d5040740c010800f4848a80c106005607a8180311908c55214512440c45510a0140d11103601d044020034040c1d103e00c0303030b000c07004060f14155007015032020444083c5d0f13040781d0350b5007400002c0b01c41d8404d00c00301c00d00e003a0140510707280859a0b549180902c0c81003902231032440220072910801403006100082d030042c500b44c4c075860103c44502041c0c1044034216031358450012919903d269110507180384550218541500741c60017030a0002608402a0072401d101c03010702014001003083c0110b4007a80b00701d040051711903c000d0402000d0b2b40042000a0281c0c1000c0001c4103100c40c404101c50b5408e070582000e800c03580c10b6030400c136510f01c01c2014040e40c0c03500c013100114090b00d00707008050100c2c0c0207800a0020080c140304100300b40c40191001072180e8400303242c60ba007139262021003d03400801410f00045a0b54009459841e807002201d2000d00c50505da1024003c10 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 29796264 1250 29795014 29795047
    0x80c070606060f0305061009030b1506070501090b0c030421091706040210050f070b3403050a0b090403080705130f08070603060b0a1409040614040f0b06040504020d0f0c0203 76
    0x1c0101c9150244880d6100c0c0941081289e0201610000105000500807100c2c880d02501811000c1c02e401d80d914544e0a00d54020492003100310b880301c00c0c45000c21a020a118242c0c0d002d103401400c048615405141c800600e480c4082c4400241b1000340000074040740b0386a0484800ca180b030001e814a4079081c4100030004c1c0300010800284442401804062002041030300c8401d940a0324070740b0710b500d6010700380d407080f000b455030702e900c2d003204240d0440740c1402180010706450164070305100c0d0380c0762050903205076480e640880e5007007a00c0700b000a001c0303807054088503004010b9080036442e00c00c80d000941401240e0390003a0615011040f01040b50030003c108041c002c00c40303450304200060800c0001c0d4120300c9444c5062041004580310900c00c0a800d00444100c00d600600c2004110b0356048851402e80458400c83d202d540381211540105115024902c03d1070030083c8803516040c20102000020340000300d801000765590b12044030110300310b00c20700d40c0304a055002162a00c8a021b030b0309400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 29797514 1250 29796264 29796271
    0x41d0604060b090904050109080307050409060602121c0902090c070309080102090303030f1b030a0f0f150603021606090c03120e01021b010210061509060e09040201080c070606060f0305 81
    0xd5180c1102080070039020000d990b8035850840d500c52454a440c1030060242401c110094000b140000611281c660004d0043c8200c441940d814440c8650300c0b0400d0343c4035404c0c50103503098000708021a0310029030944002c1650396000000040c07842003500031440e101c000311404500d40000040301401c1c99001285540180000c0000b5441d060b01d95010a84a0001800c0200c6a040719800700b10820142800000c040c00b8a031107841d00d034a440c01803c0302810b68090b0800c48189012000d49080c0f03264003880640445084427100040d160580480c001d42c0310040290b404000c04816100240070744c0100c03150b20b40030344c4030444440e003142000717604007494031488028800d2111108003166004101442c01c00182600200c09004590050341441e01e01c0c00d003150400d242010100c0c0041d41c490b4540408903059490841a0391101026280080d40180e1164028450340c0004c1c01584100138a0f54001c0c5032111035410f208450761140d06403003440c1c01c00000700d240d084020301382c10303407501c01d880c3e0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 29798764 1250 29797514 29797519
    0xc13060216050d020a150c0605040c09050c19110c0a08030306030601050a180207080c0303070305090706020a211416170307170a15030c0302090c2703070902041d06 72
    0x98000f041c0c1d000400748200c503c2110205088165611030030340c042c0442034080c5030448828001441e0a24002208440c80d01994071710f54640004100400740d1541500e03a074130304144421038241d10108007911f0302c81d0806030425541c03144103480440c0342c403030502c0c0b040206503e6004503101e08102c070405040c10f80c160015405007103080c100700200881510044600c80203103600607602d100e6410005198821a074568806200c00000d00a801d0790503401948038651580070755180d162101803c03a104c8a4416014103020840722034400710321400c08600d04403542500b00051131070880941240d180d00181c00310300500f10300b20b00060078824442d140e0302d00740c0b10040d41c1c07510714a0030b0034001d03004404030504405041d2000c4d00060100c180e542c070039500828072101007a011030b0744c0d02d807103801031a080c04124000c01c581800b242840700800c00382c40301d411a440c09000d0000b82414048980405011840d505108031440040d041c0b92510041026000c852152144040381c3d0b40c40e1a4410702c0a001c8030f0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 29800014 1250 29798764 29798779
    0x201020403061a030a030302070501140405030325121d010903050d0f090b0705090f0406090b01021b0901050607062a02010b0d0308010501030b03010608030406030507080108070b120c1306021605 85
    0xc81c240d8002c25120b1060346e243c10300680340c241c28105035004107001c4a0200d813540300a4244001c0c84800809140b20307050000d442c85104510500c51062031207941c041502141501003c0d10481516820195480e00c030f8500d00d2030800d40200b046400c1d03a03031b002d4040c5e02080000075141503008042c041c91660070501c13642841404901d903a0a100d4450080c20035041000c04501c460040d528440343d86400e41d00280b003031002d0707600d4050080040c01490300c0c0740c0c054032070105070321200c0c0240c00080000b810b0040c00d80130710fa880c0c903007030001a03030101030101c0b04107566903002600000c0301810300c0c40d003110f09061210866010f810103400c480000e2001c601c20a651540b46002036800340340107054403000e00c1c02152403481d01c1c0c08240900309a4014407242d0002242c04240154168007440c803480495440404036640d07203260740e840c3c3d08617018543c50800c0c1001a00c507130041401076142c001e054101950b00d400f0203504480c2005140c3d410500040c3c1000c3d48230032100000d05151009020101c4215 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 29801264 1250 29800014 29800061
    0x60403050307050a020102090a090f0b010305010b04030b04050f03070b0105100305090607030b030708010204180b06130902070c03050a0b0609090114012102090c0304060615020d0815060406020102040306 89
    0x54401d000052406080110004216005174403e4042d0b44452901030f1411500c10740383c1b000c290107842f8100f810350b03c0c0762a20484103140d40c03080c0107180c101e403075820b0f0541c40c1030b0454450501521008005544c00c0c8200f40f69074100810030001814210f008640c04501541003070200644102d28200035010141070a0500c9140640440c0c626003081c4c4ca130500003a59441075020a0606030aa8000c404039440441e001403100034203d010248243c50980c00c011141e01c10040098030301510101c010581071070703403080c05248150360081c0301c110300500ea4140c4540d81c80c0d8401d4588213a00804944010343c81040c410766003409280e10390004500e0303000b40101c0e502c05240c000c104005100c0e903a03900030380d070340c22480039150780950f01201e90300035210f5459890040000401d070780c4103403001c80d2103d1074000002410304e60400d220050098650180c101280c0035881100d01c400c0c0a816000003802029080045565207401000203010359000981c540c3d2440c18010211121002c081e00715402d100480c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 29802514 1250 29801264 29801267
    0x150506010206070f11070305060f010501140403030e0a030c15030507110a020108060a0914150114090607020f0303030a0b0307050901050303090112060f03033b0609030a0204050a090b010602060403 86
    0x1688030030b03e85098100b041d40c40b50304861880558a0b5843c0310702900d0004001d00c000803d40c031303206215a111410450366600e004447c0060a0000001d503000700b40010300010703204030244000c40304000c107408402901e0f51a030001c490419485800384410220020b514281c00d40121523000d5164107200d00d40404c5c1007007281d100c0340f00c154002c0c10800c104d000100e05580b800c1544002c0c0107901d00c10000321800c10408032150805841d0000000090b011089a640c07194603c3c8102e107847c81030240c144204030302404115000070b0b03400c07a8003088001116559131400c0018501c601005c19001c40d030360205000349070034508940c1003d0301078980400140403585000007200e041d15001c0c68403600e0015900381c00c1c40104890380258a02101103a400424180d210301c5640c0f07501007442c103801020525105e03100544a24807504040c901c0007403041c04180c60804c001c0c1000241c09814ae58000070f156001070704480f012200822400c1d80e4681038020302c0010246280034289500040415040c2600d0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 29803764 1250 29802514 29802523
    0xe040c08060a1206020d050a090b0f01030c051002100e011d0a11010507020a030c060203030406110a0c030e0604050a0b0c060906090309130603140109050606010c0f110324041505060102 81
    0xb8094030780b1101680802000315545c11203003581316001040105040c544204000f501030300201b564240c0c1c2c40404140c41421024419041f681d0140b003503200149004148040110091031341c0c4154010380301403002121f014001c0c1c1240300700c03900000907440c0844c0007203c880d200e201024105940680d80384d00c0000e10440d071290a100f400d00f40251610345900c000b51013841c0c2504001d001c83d03070329940058850f0300000554001d921451007884a001c0c5424540b444d40104101c41002600044440010078080c0441c82184034002c0c240c6490251160702040041050368810402c110300001c1d90240c1000503c0001c2d009a200030182c812070a00644169072030252f004010311880131421001901c00355544504001c59010f203510f49142040020035008064010040e5076074000d003400199a0340c46140800000741d8007242da50550075113a02c454110300305801c80710360503110301801e035546400c5100310b074511500c2440301200c1614092030304042605405665401c01810507050011580e00401c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 29805014 1250 29803764 29803769
    0x204060c1b0308071a070c0b040210140a0c05010f060e1503030403120305090c040e120304050705090408041e050109150e061305010801050f01020a080a09090c0e040c08060a 76
    0x82a01851040400410000c0c803030030b500041c030003440098500c04001c00b21191050358011591001d160356502c44066a601c04407d100070201c1c001040001c0041c600807805050302e041e14501520b0030114602081165070240d09294041203800c100d400800c082401000000b0344070350400e02c505841c207404005000c8004d449078040c2c402d2184000d007907442c2001a0340c0159080180c2c0300c190144404007070001c15086c1e03444d01040c0500451f26100d424613015007501d0810100c01401041726080503d00c0e00c2d0000350049607203000d011400284c6903100e40704c00e80240d0280c0003c07940c4915214030b05003442c100c070300c101c80130110f90b420420040c1e1b0003402441c1100d200a44490b40f07100c00303850844814100f1115540c0c81800130905043c0e45004482c8041955420b0325104416626041000391000d0a0741516005034000c2c90800009140800540485612410601120341e21140c6080c2925005280c04001444041c48034859141c00c1c016280303159000d04140b440b90070140c000c98001c400c1030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 29806264 1250 29805014 29805023
    0x60301090b0129040f0e060409050c01030b0a090c080f070807020a08090d0f0320011107110312030406200a09050919020c06011403150a05070e03031305030d030204060c 74
    0x740f8551580d4a0105481101c95100c0302d526503903561103a48000c07151006000e0502441d0000e40000d40070700f05071003480305c6d032a0004018075412441c1c3c40110050680c3d0b00815801050f8840c0c00556814180100207000b0020703250741140b8680049a00100c1c60018011070400800c40c081c01100c5801280240220340c112102c0c0b1342e2090294086078148061080045c034a100c0e0940c5002450b03030013a0181d840f0041c00c2d20b860b0311480340c4400a42030f10b51054005c882d1080812050000614190101c044400050b05440c2c3c2e541090081100640040310140e5205071152071619100c0c030124082e22000e03000d81c0c54a42400f0505400810484450080301c1c02001001c020811007405802000c16287d2161000d5641790303c00017000f61111020311400b0040205200d24038030358500440c900b881d41010038259050b9540b200301130b102a00d0040c0404043c0080c00c00002e00c951001c0c0000c101e64051381492843d014038200a042c608501998510201841444181700107980165200f6005401 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 29807514 1250 29806264 29806289
    0xa11010503040c0305100b01020d02030a27180c0801050109140d03050903030c0309030c0301020304020d15110d021e040f0e090313300c0501031802060a0201090b060301090b01 77
    0x10b41c41c2c03071494030482da0400f404a00c00c1d44d8000400300e501d03030440ea090420a90036160368440d0100d0a983e280901c886000c08915003540120010780d10b1000c901381521140302daa00d840740d131106000d40028000e214951038540321031010301850b420488150043c202846d148a02624050204c0301c0c0c50490714250b88a145880d017041c2c20301d44110156000100e0040540369544100c0d0081c0d41d0326480b20021600a000e0390008070034a01d418404c0c0c900c2190003400318100304134642c2c0c03201742c2c24150350315900c40180d440c403d00d00c02002c070402a0030a600807001c0140e98640700703480b80d03689802155492010007810002403181000c40e81c211800c4650201000900d034032011003084c2035004034440b00741d0400203410006800c100440960300586000a103460008000f0030035005024094400603040549000c010004ca51082c0d101800110350b0f1000062030401550005404d54403048003040145e468032650018494148101074000e00124000c0100082d15512568840d00521500212182 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 29808764 1250 29807514 29807521
    0xe060a0c120e01120b01020a0f050a061505090a09031d0312030a0207030908010203011d060105070213020301170a050a020d03090e0c04060801090c0804110a050a0e010e090a11010503 80
    0xa000481012a446000040342800d14036000b441d40409500d154002a0300e4032103c01010708521680b1103025040c0d028000d548655180c01c4440b03070203ea1f04030340b01c0c403504c81c1c0200894a98810390040b240c2044202480074a0102003107030726a4042c1500b0880c2d803500c0350000001b03800c4107081e900000c84451588485c8900c0c00002c0c1045034150403075149041c004200410744200d9801070070418426151030220390b40b0b81c81d40c036080340024001c01d00070a0301c1108ca86194450403c102c1d034422814134000741f41402540c04a00c0500b041c40c28810403c2d00880144203403200108141e120700d01000092801d4042a01d50b00c4d0350305030003036003c0d026948507090002414404c2105802520020300180a01d0a040b643d050080d4010310075400080c4402c1c0c0042407496044c010742c0c00001550b580d02c041d984560326a0040e011507100c0c0d01d03601c124440400241c540f220801c050042040200aa01c07662400450610045004042800360b4000105001c0081e0b044020003940c08820318209480303a4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 29810014 1250 29808764 29808767
    0x20909030d020301080d0201051e0606030a060b070f050d0c080f180d03020c040b0901080d0806010e0a1d0f100b071a04050a0201020c03030309100f09080c030301091b0e060a 76
    0x810900c074811410300000003c98240d0000540081c4070300300742c2c000c01281d5600c4c000745100d01c08038050785800b10000e002240c140e14200c0043c3d42c0082e0303160000940180c3e140100142980244011210890915480002c0c40340900c1100000f160502b02003441c3c02865032a41658440d503c10800e00803000b051846a50080341c030030f08003010001d0040c1711801d805050107941d0343d40b07a0313032080c1c41107040000221503800c2c05004c0700c0c100e81910000302403540c0d40c403100342d0350000c00410950411158080003117040da5641790480003041040f442c2d1a9440300d90100d842a00c600425500c241c00e5001c09125005080918130300031030701003105160f01d803c3c0c90302e80200000e0301c504220fa142c01c3c0391800d1106000010803184c12181c0300342c084940c00000712081c96180d00040302c6000c0a07030003241424140740c00c42e80001c04031a502400020341e0f076091360f403505515081a1035016565101100506c6407014500c181d01d0381200600303044085203000c0c40c0051442e501c03100800c0c081d01c00030501e861101d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 29811264 1250 29810014 29810017
    0x5100e0c210a020306070816030209010e060a020a0813030c0504020301050a0303230301090c0e1008070c02010e060307170a02130306020d180302010b04110705120c07080d0302030103060c030b0d02090903 89
    0x50f0300406840701350520110050001c40165a0181b0000988401024040c0688203e4464500c10f0b110262141c0c1d56070208201a042001024103502407005510000703030902004100d100505600c8400d00c90460a00d0300c0300740c0c3e45800050040e84104018000d590b01c002e100030031079600d071a0125544c2030100c2c1c590603003040340d88030344088240070002082052a580080d141110260381c0e49074508103d034100b1000d160000c841e00c000c64a5030f00482c03c06d034070070f00c42003900714010f042c07001e0711206141c0824003c1c1c2c0b0441d4030741e0014000e4ae0750f000c2e0210600ca032180e044a903100081d400c1289110700201111120301c80145610307030014800d048a50107800002803a42a0002e1102180380e500f00079000c1c000280c001c80c4a107240c4650071054144000544504940003002480d140b840400c055200e540201d072516001d100d24040080d994078100006000d0113003598006d138a951640c50100141c1e20f071300c8040001d043c207119002c4041d0311120164040707650102c4d03108078039482781c0e80400c0c2503 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 29812514 1250 29811264 29811283
    0x2070807050603071e0521060f090903070f11010206010807030b070f09050409060b09060402041a0702191e0504020307120b040e0a060204051306030b0c032205100e0c21 74
    0x94090000640c01c017981c1250141000c0c4620009042c070540040020510107002100d1142c1d00c411502202a214140703060059804110b80c42164501901c13621220504510600d040320700030110400d20348a56414003500780144140802032408500b142d4421311000002000c040c10000c1103002000518812902d0358010500540108428541402e0103006000100101800b811444000c40e0160500c1c2c0300301c0341120400803880f6440c02800f105200c0702c5c1c1c0071540c180c2e446003403a00c5001041400000c14030081035050800f02e52445405481c41c0a480654800ea12941c814802c006125402403210601e54002c0c450001c0c404c50441c001800030260365000c0999803240c046414108522940180140e030b4048940442160900710020141d03507060100800100b10000131495035507c5802454000c043c42300c007814894030300e60101035a443c103143c054940394441006038962008078130a90400400d50702c00307007444030500d101081d014a081995070103004000070244464200c240b000d41078 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 29813764 1250 29812514 29812547
    0x507020613020f0a0b120c03010b040603020f040504060e18010b0901032a15021603020a0501050a090312120f14070e04060803030a0b1005030601080c0c010e0d0206090d0207080705060307 82
    0x207181752500a8402c1d190402082c0001c00380803140440c4c0014070030802c0e40d0407640180300b220302d40fa00b0301030110040d41110305015422002880041081e999030b02400001d420080c404d040302d498030740e4010b01c0381000e0b00502d01c2c5036407600301c0940792034454144860540380c0150304480c94134100368802d1904007107030180c08101c0d01400130209903110301c0c1c0c09845446441d9400ca449424228800800025941c44002c5d4031040c5c19030b0800c240d500410142520700c5542c00c004811366a00d49807a0502c03181080040e0000300464842403103081c540c4035510000502e541c0030000c0da011054035603034605015101a05200d040003c10307600b0340c0c4540010b400391901e041a02e81307900b40498400050944003282c0c41c42040207051001410f8419002d9a2203500142d44e0300b0610b455810703a1072401d5100e070f0030f0440c081d52124081070515800b0400144041030700e038018a05803604651030b6040408081c0305000b150844102000404000201e4100f900c0c8100d42e50740d81c90310743d441c1c1640c810a002801a9 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 29815014 1250 29813764 29813779
    0x506040507060e1f03110c0703030f030c0e030615030a02030115050114130e0c160c0e0114030601090c260702010f0506060d0e0705130e0c040507020613020f 69
    0x10030004041400011030b40e0b181c9642038000203100401100701e9829110040b100845421190200c3c404e8120fa8505401041a5403030f000a918a00f400c0c030132540c10540c0800c0d02c12000c5940c56905206600404003286400c907105156100025120350780900021070507003152000214503a02030000e070145c59801002040701c1d1405108030004185148546400314100710240140a4254411500e60401c62200440b40c1824010758280030307000504091503200d014890304560f40b01801c4080b44050003842c0d60401185000480d01500605800919907461201d500140c261000111141501c80f41c601c00314041201c11001c440a1400c0c5501d600c85410801081003c0c5400130002c43c0a1083c035030003803001035610380051050701d80c01c0d2449034004070b0410000e0310006442e070200e801ca90108045c0c4014507a1807000890030100000d00810140c1c2c0e0300c0c00031091050800c40c4600410060fa41480285481c40e006500c4000c0141324004010000e1010340840d91252840c0000700310041000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 29816264 1250 29815014 29815021
    0x905010303020d0c052a0405010603020a080103170403081209010b060c0d030914061003030e030c0f06030403120f0c0914010903080c0f1002220807181407020d020706030203010302090a09020303070506 88
    0x440c3c0003011b24001e008034600400800c4651090003143d51070040c54850034400d0b460750350381c018402e0258203200c80c50742044c040440040d41403002005200c0c10160802c405041c1031603843d013191400400b0381d20a0108000b007040d040c3c4041070b10225000c05050000e06074002d42420301c050421f480b204c0005001d03050400401c901c0c1018034409072170207527480c01c3c8400003a10a041d0b4178030003001c11319413060442241095501d003000c01154030601c60301c0e080d5032003451160a502540d0b409903e69041a4035040585480fa600288000c010000c0c4003100845040140018185641b58003000d426039030009403419122400300004807044854204a40c100d10341040d113900290401900c0501d90340c684500c1381d40480c101d004a00650b036500d80070701562450020740304040d1041e03030f80b00207a081e1140c001340a85440060010f115554940240c8203a12407010000d080044540111003814818401400540c840550780c6a018924000c000b50300e014500000c1c0ca5405007540c002d2152007600d081 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 29817514 1250 29816264 29816323
    0x5060a030504051002030f01050d020d0506100617042d0f2613050103020d060905040507030302070e0708011e2c01060c050c090703150611070905010303020d0c05 71
    0x620070750240701542e5413504600300c544168441038030344ea01520207050040c0207a00d040c0c0c500001f150700c01420703180c03e5013440d5a210309242c422160410348001c050310400c0341c190002202511880c045000f031816240c1035a8007100f464007481d80d07414044116544462240b0903001030790042d81c002d100100340e20b055207001502d800780b641415214a606180c0508403011034010707241d030000820052032582d424000110025040b400c140c655583e200c16000442d4111441018001c034010700150480b6400c40c20040d2901800340d000c11086034a500421a0311944800010f0541e2207d02d43d0000556840040f07004025071508001a400c00e0300368071140c082e602000751031500c4403081b01c1c28504e80e42c800c419a83d54521081c060300136001413040031420303d04142415031080403410001043d1000702d9500382126500e4000b800860030300a45096440000c00c1f400e002010b04503014009581544d40003500c40301c110f5115001d11588642c86c03000c02505104445500020352400f0080a089080 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 29818764 1250 29817514 29817521
    0x60e0312150310020403080910030f020c031206010503010609030b0703110408010b030f060c040303030518120c07050319060504111903020108060306011a03090c030d0503011707061409060405060a03 87
    0x10550310038443c200c50401030306018004c0e42c0c12290084101070811140d8424040c0e000041032041d0105591840d00c814001d449101501c203507080b2000654440a1400b03001c9000c2e6000f411050500105000400c24207501901d00415240d0102e0900d0f0f40d6100d1340c400790b010f00f00061003000e401c031000c00e0101d180103055022640540d022402c503449003481c44d080036100c2006444440c4c1c051000c110900209000390030082d04098540c000341c0400611014950414400c10303a080340300c000018000102117010003500c000703008110007410582c80354104000e00b40a14010041001da1203e0020b41400700071607042d101e203400070b4581041280c42c1c070307400d0b2004242404100c1c04a4050004a20507090010749a03058881c0007070401c2c007174201e020000303419800080052a951081220034002504e00380641c440c0a0303026160240c41c0e504091680d811707403a403500303900c0d01d82d0b011844c1000701c5d0b80c0c091802034000c1e680d1040303665142842c00c04200280b01c1c2d500115084200040e03102035841e8180d0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 29820014 1250 29818764 29818801
    0xa020312011716032109050303040b030403120b0112050c07060510050301060603110a0c080d060b070b0106051215030a050a0b10060207030c03020f0a030218010e010b0a050403060e0312 81
    0x41640c014042641030812a04458007000d017004814424100c1103071141c400c42c0414001a08011404a86e40c1d00060700d10391054009a07a840b4011080c4400c06401c01c0c805544488011010f10a000500000070050101a00d202e01d001c0e0300c41d00070409641034507088461494111400b403206150808180500d80702503c0f0b80c500030340c601000003818a00c40e10400e00c850a4007500d0071718080c1e0070801183d24050501040d140035000700054a0080314522660008220b01007a094580d550707414118400501603000d8010301000304805c0c0480000c88103190360140841c94010a02e007140b501207071400507400c1001b032807445025029018000b5410764144101c011311209104503886200880e160502444014220b00440006000500d0b0440e03410043e054041c0c840d00b0030301c2c1d41e600001c02e40d01c20f182d2800c01411a40d80103120425201111501500504844a1400040042c000c0880c821407201504d210b41c2c3e245c50360a4100240220790025007110319007461414003141d01c00401c50b81e007 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 29821264 1250 29820014 29820059
    0x501020d050106020624060d02130e010302040606030212060d0507050409050c040c0c030c03030e01020f03070f030b0f180903040b07030807110a030c080307090515040806100302030a080a02031201 86
    0xc000092844180c545c06415071b00200301005c442080c8041488500d4024100461310107400344035202c5000c9051420b2401000580745025103545140140412201c0a8002c00304042c01000303080d001640c83d170141e5411610584440a69003c07a00b0041d0502c1e0342a000a80d200c3e0600f00c00a040c4003000500d80308244080314200490104980d056542c4404100000c002c47c8000084034082801395203c01c0049404030005442c003043d45c10a80c0055104847c050040f5003140c500305241503251107100241c50050b5841c001d03281904001805290702c070b980d0b01035440e610b0f0300003503008001402079400800c0d020380c1640d251703421480e01411000c002c035007210004001d10940070011a0000310b1492054168961004428440d11411a260f00003001d5805121181c480040c0603103c6159800c594418000130649a50800d9a8141040c81c00741418001842405090015a85c0170500b8881241d001a61940e66103040400b41d00b1070140c08a0401503070811703000014100c0358001721421841c0d80c0c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 29822514 1250 29821264 29821273
    0x10c120e010203060108040b04140a03122306040207030908060112050d0206010e13030c0c2301020105092509060e06092203030e0c090405010f1503030e0105090d0501020d05010602 79
    0x121a09080b408110b804d14002030705034001c940401c0c2003141c1560028010328091296440141e100392501030070744030032400581c0700c11410708008020310a2032265403030020384000c0e8811445601d80040c402800c0c44e440355a000a441c1e0806020306400707801030917000d0640354a0340c0d451072210345240c80054140da50380251414204010310218009050320076240b0400000c0d00e50483c89a4000c580c1d4074128284005a1031321408180d260080c0f030b00030040003422000d1450000300c0758400032020004039042d60b04000a00c6605140400c07140b00c0017480c1d4032040549504901c066542500a510903410903103095804179141600c4031065119050a40f40d2401545940c0741d1080d021035200c1128030b141d548403000400283c442d40141c1c40c80d01c451412510101600c000240f820070703080d80e0480d1140c2d90b030400da600700142401491508009240c100098901d142c4000e0318030fa51800382c2c2410030600086040c1240d40e203003051002150008001c54a504480c01401d004200c00c2c0951800f6208 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 29823764 1250 29822514 29822531
    0xb030a0311070e3d030809040f0203041101350a1404050a03030b0f0105090d030e1203070204060506120106030f230402150c030d0207060e0613150204060504061b0203010c12 76
    0x40d42269611160295042400a440c2d51107000f06d0750001070741c0300e920a03200d04005141003040d0010b14040c030b0240f6041403900c01070600140c0030b1f056403d6500034200f03071a83d00903c194181c10940e500302488402c2000700f580d4078100200181030021041c200c0002107400d21090240020384003404c1c600c00d450401c40c410070b013010004000d03800403060703001800412402c1024200040340441080c80b90500c035000942042c005040d80c1c5d50912901000e0307202081003015460140214070003007500380c074070300d1070051040340404540805004240a00d40c80714622480b40b03615a002c5051200c10121000e55154180c01e0808040d00a450a07882441d01c11030100c0d01c64500001c5030421000040214504031180702668080d40080f1001d8480594800046403014000c1c48410b11407650b4a01000041c0b0f030601d03200741c0c14042500d01c100483c0c4140710134840260840110784c251011410b100c1072001c15040c42e81d1340030703189000080d095401d1001541825400c01041c4040071100c6009121450 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 29825014 1250 29823764 29823841
    0x307050f06010f0302010302071703070c0c09060605030c0705070305071805091209040b0102101506020d08041109060d020a06050301090c110a060b0d05030403030c03120b030a0311070e 81
    0x30300a0007042010143e50f03004000660180d4000c1460611903007003040070480006420919400031141a0045100410340700c00700485885243e02400c00c40108101046c1420303070041a901000302880a1a180040c0701400d0000030000000115031002c11144240d4644129840405480c91702c0c10b9514240000300d0000e4001058180c1c011050010543c10710710040100009042803c00d4141075029400903414820142e01504083d0380340410000704151929000920f00f201e984485010001030405202c0018118010003500c0329040b035504060b038442c00000307111154002c000a520103800f00300091712603000806181200c04d610810050201110410b450030304000010f00d02907040304c110400010140c1d40714480184010388001c80740012a6100352645d48641c105501294640b03202d0402c165004007045030184403d481880184404800b00c1d54a0b55603500082c02d100c4003c80010000c0000c101034001441e4440755181d01d0b080071806100703010b00703031141e0100301203042c040f2500d1030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 29826264 1250 29825014 29825023
    0x807030905060a0c0302040b13030b011a03040b0406060e0405060f010617180f0f01090c0906081c020c030a0c0e0603060c0a050304060209040606030f0605030d05090d0507080a050307050f 82
    0xa030000042d00c0c40b41e07221210030004000a503841410700d035007400b000c6101c00e00030019164180c1c41941381f24106003182051000c2d0801603105040c0740220300c00142d0040c00c44400d594000d54811030b11025a181ca01c1c1503070103043e481d040704e0705480591080005001000420074055007040507041500d07602c9040131641e9482c14540c6140014110b00407860b0980300c1c0d42e024603090301c02c1d0251b44082c28596041418408040303101c0c8803680d1504024014001030250240051450b840f08001c000d01c0c201003031391541d0f142c1d8048141c114045541030050346c000d1084402c7c010004080d9070580d400c5103072442414025000d61440484c28000148144c24006680c45c000c0340c0c0c0c146501c0c108240c01e2400c642940c4014012100287c00b404022030301c1e280c07800386202406036601e0204801700804460000c5401b29800248240e2041800b8950b840c0c01100316044040c050b900d01e2207801043c1840c62405099030300c03003035061048602045c1441408405802814441c6040c4c0700c2c80407100c250103548 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 29827514 1250 29826264 29826281
    0x702060c0702090406090b0f010906050f1003090501090605090d02010608030306011b050a020409120206070207030b15210d020d0503060108070f0309050f070609060302041505031321080703 83
    0x528040007610007614161509581c494400c40d00410801c0c0c840c1e450100d43c0405442048002500400500c4403240500520001d0402074404884a130001400151600d21000951041c10340c0c1d039200200b0300801390404c9411030341221080c8654206600c1c00e40e5a0f42d60784000800652801801240a00340801100e018040513542c541d60f902c04614030225040d00802e044613148101d48000006031070f580a03404100c0e00503402c0e5400383c40515000390500300018020030071508600801d00000e04a40c151a400c02c281c2200e03c01d90002800100302e91040074a614032034900191000108480c002441c41c500d001c240d420f07612030345a0343d00309032414002554180c0c0811201c0d80081c80580c8680c1d88808000c0e0185408240315089031a00ea00b0070314090500c01c51600700100038485c4581104402005140703d00d411450f15107808229103041d4800341a40b800c000c4004045000380e2001c030100e0f20110380100c00111030b16030010300c0e5403d80007540c20300d0020540c050000360380107001e0b2140250 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 29828764 1250 29827514 29827531
    0x50402070f080306011b0510050108150412210b04060b12150105160f02030708030c03040e04020f0306010f0504150b07060b0613030c230303040605090a030b040b0f070206 75
    0x100764410755403102103400c01030038607040207800d40b041c0310800c0f001d2800f003010380d00840241c088229400780c41000e65005820610980c2c2c440110758031004004151170b980103800041d41c804a005582c4c0840b1080000c2c45844216401c1c801d48241c42503041c0d2207400444800c60302002404c1d0741c0c03a03100d690707402007000617071503038401d003000540c1e00c804181422001c4505242c21403404680f04021041e04000f06001e0f21a090700303d81480c21410104422809040c4030380c000d46c01d0103903d4800c40d0780c0e44102e000301c1e142c0c0b10051000c14115140c1e226040e103801001800d4030410741c3c440e150700d00c16259911030b82d4440ca003072108800100b4120000c100607138158200d40783c0380507031a80340d01d0007a1041a504903003000c2c1c1005982d900107000501440914868200c04449a10b00300c54078004a07003010b0001e4507800031512603c242e542c0081210121010f0313047c0340c1e0b101d0020305c0002e044203489500c0138000c108588104010000084400c2e4032034811501c4140c0c070341d26030740401c980c0d0b40c00032105080b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 29830014 1250 29828764 29828783
    0xe0a060503030f03040c180b0f0108090705120a0215031501030603080a03050711030a020a0203010b040e0d1b1704080d1e050d020c0a050109031101050601050702010804060f0c051305040207 83
    0x3500ea0b0040d0011640b046c0076500e076080881e502c400044006138a400e120b040d081d0b850680322420b240000007031410039401d20340081c0d1401c001440c151204070394803e061080c22030040c144894001480304094058004200c1d00d082c2801c442c4114041d8030440e50189110340c5a01032560541c000d00c95007040d203400911050a010740907000b1350080c4000f8060405208400c1864440c2032010401048002c19a90241c04010b1491060600303407200040e42d24861f0f803c0c20202e0300b074010006042403501400745003d034464600e00744050a410040c074006004510b0503055a283c00920a00400454800b0750846922003485001160001101100c001900071404500304191f4461009021807180900c0014602440354089600d000c1200d0011100b99446099100515812a030300450a48a0000030301180c903041c0c0008185205540c0005e0502c400078000c941400f80d250300640b86005401010021200502d00c0070b0702c01d03040300e080c0c0c140b803601c50b01011800d81464001d071060140c0c09080c0c030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 29831264 1250 29830014 29830027
    0x6060206160f0806120f1c1704020609060708070308040b0106180603020d020903061611030703020c0d0303090b1315060605030a021810050405040f02040b220b0c06010e0a06050303 79
    0x11940b44502515184c3c1c081d101d441c0c5c07041c2054041c024034446a04079801420800d0720101c503014440c3c100d040e100140208650200100328a0b00c04d1598025411100325a8072100540011005e028030380000d410007102042c440304064025851138000d60003000659150380c5d98000440704181440c0300c5102859105804120343d174040c1d0080c0c0040390742c26a0242c00c0c0122500402c3c58400105c8110800c0c06842101884080d00181d900040700d0850000d54588041c40d24003940d41d20380d12010b00d00035080c11000c8000d240c480d03032105032882e070300034814291400c0803d02c004c612031f0b15807401c0d500c9052032070b801a0001028031900341124543e484040c2190340f202c40060082d04540698015080d80308505006a51400140811051141c440c0c54a0318100030610088070a2007807007183c6035204020600c40043e0070703400e079a994081a816005108080c55001c0c3c103501340c550040da20641b000c201a0709015001c14241d0607100300b0790340c804060756008010030603500c480c844c00390190400c1120 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 29832514 1250 29831264 29831267
    0xb04050718020f09041d0d0801050907021c050d0b06030a0c080c0301050a0e040218070807020c0906060304020d0501060f09020903061e042a0b1902010606080105040b040603080c0106060206160f 85
    0x16600f0340150811b5600c030401003100b4605000160240728005119000103016a01d007a071012a0094000d200a04a80784008281c484240b6011604e10a0040105a0315111a80c43d0804180920301a240c5922410001e804601604000c0c42d14002705203a403000031005248201524101d8400a18000c812441c1145041c61440081c2050b038004602c1c50000009c4254071207080c0c02000ea9076614811840c00806c001d09103a80c0040c1c26114281400921149986a009591704150129a02095204989411030041081e68004030891110160016421400e54068005040180c0c284e138000da07900c0c02c403104c0c3c2c140142065510b802e000320110380440d840701441401006806c440301d41d014005070700141100102e50240c8501e610010700610001c0040d070f65188880707801d0000b8803144e0304108004d050710405004483c0119540d42c81c50050741d4558010000442d080494165201d0111054a01030007035030203410050300c500804030b002c6a00c1080119081d0b440f0f1f070307984d12000460720b00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 29833764 1250 29832514 29832521
    0x903040b0a110303150a0608010303050d0b03030c070e06010e0904020604150504090608061803030f0105040c030f05040602031b1207081003080c07080105070504080a08160b04050718020f0904 84
    0x100c001c100000754210000205003040218018201c210b40c031074440240f502000702c401480c0e0803580820a0802c01080003981000a803041000011030100320800388102091442c02240882080d6114424000403900924400c490040c1002c3c0c2c0d440b80303094101000c0c41901744080d903009402180400003000f040490100408140301140380c420314003076607160860151101174100c0315454001d58107002c1414204050a45018648805103007140f506645244a0001c14070909004548403440c880c4828460b40c03001c98150001c071001c019500f0b081c101035000b5001103401c071600040c0a0720245584611005407401c900b5000070540090780c4040e07088032f05c100050141001e143c43d040d40400011249806410035040e00c1008116451425240a00b034500c0a0a002c040c050b041200740101c10022440d002c159800a040c44d54401c00b001d0082c030780002008002e041c50b446042400100100404d9074004c550703407509842a5a20020580402c0348200324501e0007211041182c0410740c00d2031740 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 29835014 1250 29833764 29833777
    0x6090402070204090b090c420d0606020703020a0501030b03070909110a12020f01140f031e07050417120403021e0402160204150302010c0b150d030302040302040b04050903040b 77
    0x43c0085490700c401e070356102110780181e490840f50740100c0400302c80350901240c8500b02e20b00c100201d0341d40341c40410340b401c1036421000c0c480e80155070f08005840a03000c034030129039821017204000c015840d51100000e4031134070140803c901c91a01c1080028496110340282c2100040040107801498a0092014024403035010212940e840703240e20754600323644500c1100300501403114001100c020318030401c400500782d40505414030261103014a191111001075581d5501d0214141e81e4948484618903240c0f03c1241c12101107080c0801007100041c1e01a0152044039603040c203a0b984609810281a107d00c0c0d15100c106500c042400100f015103000e212881e440326489848002d9450b100010800380d9225800e081e185140826000c011818540f06040c401e4004070448800b15080d41e00081c4010b207a1040030700614245030100e1000c0d010601003040c00303840204041c141507501c0c540038010b03420034407040c1e00c2145419104481400d00b405240e00c14621403010358502401c02503225503640004 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 29836264 1250 29835014 29835019
    0x507020613030c0b070c0212150c0708090405100f0801051b0711040504030305091504171b0f0a0c080105060a050108070207050402040b04050406120c0e070509031b010f02010b060904020702 83
    0x10180078040b42030031349407034068411659418100c100c2d50043c442992409040055140d024880148031001072040d42031300700100884655071150903043c6000340d801200c282d9607005241c2010303c0740810004106400312815030300829012a565541c4038200d400490702c61612401c41812420800082e2000b0480c0038420801c40c40395030503000200f001c0700c0d411241100403a032f80300c080c00b108501c00c000b419008040d244070340b00b681c90565540600c000010f410b1440d52200405d82c4841c8140c1001402d000399a40401c0702c5441603030120190786d400e00103034140c40210740c1740004108030a042c01494072440300584800e102c06d140c4801103070303d400001c2510341180034a0801041760795960005000034141501d48a807100e040000704002c8584507400100c2c1c03803071f40a0130035002604002042080f030740c2c42c0102c0407503a175902c070302500e8500c00c900e03559505000300d00340542003070202002d1088600f400e907103007194040d550f0b000303900b2511380664040d070100d018420321109203880e800038000b6031301c00f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 29837514 1250 29836264 29836277
    0x31308130b0c010501090b0d030e0918030a0507030318020d0b1803160606060206070804060c02010f020d09030201050f06030714150a0c030f05040308030105130b0a060201150504050702061303 84
    0x4030300c000e81c03454000184054403651524010001d0005038085c2904070314085818100150099402504020b44062958080c04032540098040001601061030710f89182c42540c2c0c2c0d074180e88000421039400b02c4011408245081050300c0c86103001c0085000c101d074040c01e0040c0b40f9220741c403000389800d8001c3c038990a03011042480b211900f800c2c03000d0400e80300041c295900395509403500c44182d819a422010440d4003000c00c0007200d5601c0000c160f007007604284001002d44403103201324098501200c4200c003850000400c461040c24680c440780e0301501a80c000c00141c0c4a41d02c41c4003c2d02c1c4181c0741c1941c1503100c44021310041080307491820150030020305110844501c0b4075400c496403c41032103103001c114081000e10034180c00600000c0c1b00700080ca007017881d00d811a80c807503405020601a16000d95100c0c044114150300c107500019040400811400341c00c0ea442600038003900c2c011110030440040b8920008480c00d26000d0745004041c02c0d000381c003465661080c00c0800406c401e07019005c0052 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 29838764 1250 29837514 29837519
    0x8040b07020d170a031406030303061c02090403080105041503020f060a03090506040503030f07020a0503070b07030f0509010b0a09091a090709050a05070801080f0a081305040e0109050c0603130813 86
    0x14002c004201040f8620065070316840c9000000c0c0440b100c0030a0180c141031000d00b004641da90100880f40e100b402103648500542130b408106031014035886000f900000d40905000515400c10350103812a80116000d2212501071012404588400d110003904503124551400079480c0800c040d081c5c60100c1d1400040c0c8440c01d45807503160450503a02500c0941002040c41148116849000e60001650004061102203070303484541d28850b02001900002801000c81c030810301c25000075009850541042c0028101100e5590003400c0102d01d80740706601c1c48000140341c00850151182c581d0b01312a0001c049580d0041146101200900c40c1c9694040c000d00491a01154482c49000340341c2c203000066070f0725009802400000040e0000303641640880d1078079000b07103030004104101c1070703202c00680d0f110084820003803450f51039030300680d41c80b5092080001500d4070550240361000d000f00c0c2283e40d46070b1580240b28481c03006442805401184044240200c0d18000081ca861401d54400340c403041d5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 29840014 1250 29838764 29838773
    0xa0c0e15041107020102010b030f25240305061503010b03150303030f101202100e0402090a03060509010c0c0507121505040b0609090d0e010c020a0803071b0e010308040b07020d 77
    0x42035034010b80d942c0e4002203400e40c00d5503030920030074040050030340040c04840b602d0100d9558581d81c010350a1b0550043c1070240d0805601e0b18280c41c0184205400c69400700a07506c01c1c1440c80402c6800c00002a01e41800a800c0b860134203145068000100d41451540e4241604600694030081150950300202070702552203031420030085208810102160807a41001c180c03646107000d485d4810b44440c3c400f400004c0150340c0c0c0740c610401514980c10f018900c00d0b10000468041d01440b420580c0c02000c00d0000014859942c003c10321030140389008000b86c0b00710f82425183c0c1507210b0b00180c49507000c2d80c0240403070b42218240300003043c00313803012041c0c00c5c004451003801c3c1c2e10115401c8403481100f070140103c501b003c0b030f0b43e03541200180000d8400310448100080c83c0b0784e0480d18060400c000d40d120441991100003201d00944010700c01d0f00d50300c1a540c104600320840c0d0000705424440603510000d4400c06245030075042e05d0340300c0700361850545000000078290300101e00a0b41d100d00030022030030008 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 29841264 1250 29840014 29840021
    0x3120905060f10050907080a0510030c062d091502120f1206010f050306011b0f0804150504050d06090204020c0d02010c1706090f0c22090e0a0c0e1504 66
    0x30002c000542141e807403e03044280d104407003640000d002d1801401404101900075503810b620070041600040c4550792308101078100c04680d40f0203042c440302180c001c99125440025504010001c1030801c0303298181c5003110092800740c666160008402c08401c0c40b81d91010b02c24406440d21300d20444000c0c14039100305600603805001c0343e0035604000103116030744228060301c440d40715400342003a0702e1020719048043e1561000400345410001520b02240080740782d200c0300200c481e044002140c160000345400b803160761141c005c40d8001340f03042c85213080710b034426421581901c4025100110030881c55603214040c003a50202244d0107070302480700d07805d51801001140c0104480780e0020451910681000c3c02c24200c0c029921800c402a5041007501d8a500c540c1940208081c0058500c9555002e00c09085000c2d090104030300d841c4d8406405842080f0302d44010a2f21403286041000420481c0c0d260f684220902000b0301c04104a80200f0411030340440d40c5620210140c1a824444c14482c0040c085 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 29842514 1250 29841264 29841271
    0x30c11010c170105010201020307080f1017030301050117010b04140a09020a1205071106150607080304110a05010c050606190909050105010e010509040201050f0306030304030f050c04050a05010b070312090506 91
    0x1d1064012a8481c0d0340b1a08403030051a0a000131031441c01c169070024803800380140178408640c80f40380400c0601070034500400c000c110002c040007152100484003520703070b031080c410035000494111401501c0820f00611354100c031148410245801d281000b8036602030189400607a014010b80b00c0055030450900080c00b0242c0c10380d40344048440c20700030101c01c90f20301400e28401c03c01000588101c109001900a4200c1240b0301c030710f903540d0501d1f4000388940c03054807070080c0044404800d11040141407074840590700021074a0007885500e4600440e404c80003054003a005600c0f00c400701e0414104500c2c030110000e1501440418140c80700890310540d060aa0100c07050781d900d0004001084411030164007601c802c0715194507600380741e00020b0150166900000d80d100000010441c160380402c1150011039000e5407500340700b030150900c5070b240d1500640300c6e8002ca05043c0050107064031449001c0c140d071043c0c0c0105003000d0094404071410402c5407401c030b10590b60350180001180c81001414032 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 29843764 1250 29842514 29842517
    0x10e060d021b0316060207082206090e06060a031805030301080c01090b0f090105031f030b04050606012a020102010e06010b030610050301030f021509090702010e010b0f10030c11010c 80
    0x250b07014080c10449645101c5007801249070028403a2404040c0094050010315401c1000540c403202941000b80051040b001002494042d40d0000b0a5600b0601700340301c2295056200e00300c0850755820307010b000c2c3c0744c103c1d11a80c0c4210f0401c20300c280300c2d0213030344819280d0201c822136000303007803403a41c1d001d103140d00c20f0f040071003d5444103d081e54250fa01940300b90203009100700312424010800c50341034041c01252001410300c1000300c001007a50700b1640040181841a20413800010780d82e003024698108161820b658130b02410000031102d5001da92110250501100740c3c44c1456903620450b512002c8100f0200e045548806031485403400801c00e807406840200101c80d507030306069040083c601c00d81407103201400390900040010400b4200800505501901d280c0380d48044484402c0300c038490b00030802e42c0104002c05101c0f04e103505500200d10700060400800528404004001c54042d405a02070b520050714024681c00c01c1c4a13421060148803113042048482e4000f40d0445e080d14201e0040c1070 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 29845014 1250 29843764 29843767
    0x11030105031e03030103030f110a03050703080f0603060a110c010501080c010f020708060c031504021801080105030304120f0204060305070e19021c0b030c0604090504060608010b0105031302010e060d02 88
    0x11038034091068501c0841040140503400e042c950b01c1a480740014030004c0c052002c01541c2552403401403c0802d8031005800035600548518900602075801a40f8190006180440003803803c031075405559000304001401000c0e15520030740303918042c003201b0890010310b1205100764440318100b405014040d11600018000104040b40010001031701a200c10f81150301c103013810804070b0008141d40f5000748001d075000b5602d41d1203a80c0e03016000314403034840c4c0e001032001911091070b01002240b1001503200740e0701d140e05139036100101541c1c1e01403402004000108508a5000078000e1000d080400f48041c00100d222503590b01c410382019155031095007440d03860400c1116840100308030a070303c88440380003107042908480100300b040e801c404c10007807056940c00036a141c99804000d01c592640d0002c0800c0c0c0d8564640b01e080010b8a010707075084071800d0404001052042042c010106801010f0751003605583d038505000304490b41c01f100985c1840514903c204003511402d00515640c0200354016 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 29846264 1250 29845014 29845019
    0xe030f0d02120c0f04150504170610081b0126070f030f0203040b180703060204090614060910050d0207060203161e02031e0417010e1603020d060207050a0204110301 72
    0x42c001d48030010268040040704002e5107100e401038209031000d40c1d1103806000b002a01d82041540e0f1407080c0d4020050000c8a8010b15801100c00102c91744510044411a03044c2a50340c0e9225660b155140b0304e6008441d50301d4002c0c4495485003a100c8100341441848000300645a0910002590141d601c8800102150090302080d50140a0141c0098441408501c2e40c6425218180040009011203258222820541810034010040c007030207150031504c02c554440d920002c14008004901c60128441c00c5440c0c2121185000b034140c0d0302148002c1d0030b101c0070701c4c9840c034225125800390b068400d03900e500340007520105a16201440c41040c000510b440c9a040c440c1d07000d020b100030403003221001d01035090040e40484e400310135031311410300c99070020400d0f0b80d100114520314000e0b03030020900440020034820b22007005401c4442c600202c0803d8400c0c02114546c40000d402c4180000b82d00300e044e5807007800c00112658000c0c400f0078010b00c241c030001003090f8005000e9a2400b01036400d2900c011006 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 29847514 1250 29846264 29846287
    0x501030b03060f011e05060a031506050f04051003092001020706030e03030f060a0f0602100f0c0c0b07020a050a0f0b070206070801050f0a0b070c030204060501020a050a06090201110a0b0a0506010813060e030f0d02 93
    0x1214041c18171814070cc1c2c100a520300c1790095612807409030314020000442c07008100781c0a82c00c040703d46503020301d8141116107880b010f0104001c880d80400d0052044490015255009100340d1030a880880d001e14515a92003c2009007144050640c51b04504900400608009220131042c040c1c02558060041c8014000445098907000c041c02a2203518020800c0d281d1a000340e81d80782c0303c80d4000910b4900e42c0d64a0f002b603081442803800907080c3e0140c1030262082240c403032030105507140304019001303150f2030320a4201d95275a0215500d00100f081701c00103214501d46108034880b040790007051281c100381c480c01400ba017508461340845070360b0540746060086141c40d0040d02d000c3d1200303100400d5141065111503641c4c2e002d01c02c014003541d80d100907020542e407003408288004409042101e418602c64500305001c50012070b44410710381e00c0c003c0891040e40c030030120780d80940c2c05080039a0454800792a0f0744000c101e440e0046100f4481000b1901c04882d10341d0140000d040e0030030b0010b0711021103c40 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 29848764 1250 29847514 29847551
    0x3120b060405090f0403030e1203010e0c030708012702040801020d1a0a140a0803040b03070201060504050402010801060f12051302030c03010203040b1609050303030f010501030b03060f011e05060a03 87
    0x1015124150601c010301c00c9468000720a507004050303180d410800d172154202a0003c200c02401c13601d95016801c035000c4610303c00c00045048483c8009101280d40e2070700410347c0c443c0815520303440003401c20303c010001000071340a00100280d86090070940c500308841c442040741d2295102003540d94002c85e214850103d02d120b5024030400315100b42c102c0742110400101c00303002034000c28556004204204226884000003200a40340400840703503a9616200c00c421103804c2103c0100c0151b013410804642c81c00c01c0e000e40340c0030f2981a11003070480d0342010420307242c03401c14954210400c0188491140101070500405008015240e0784041c3d44080e40103050034920403400307160081e8010420310001134244415558094540e1001e99511090300c1030845429002d036228940c944808028030070700800c07802901c1d0484009880422500c1050f2051640301c40e01141c071007000c18844801000101010000c10b2a81c00703000e010344004503103400003c1d50310f801c00d101250019a640c000c02501006489 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 29850014 1250 29848764 29848781
    0x6120105030f07060f030207110603040804050910060c0807020105090a03030e031509100c0c050106030c05040b030d08060609030106170a060e03070c05040f020d1404050d030e071418040312 83
    0x8003c1c0540605051001d032020080f40c010b6400c0641c0040c2d940300b0300400d500000000e0400500b2140e4a0505080070340607a0070500416200303800440108889161109224040360341c241c83c0c40039003119031388403803038580c00120041e414000108401d03030907942c94240002c00341d4403948801c000c2106c444241898a4030300000040e0128018007403084000000800000e804000b202c040350071030310b1190880d050110031344000c00d5507007008004010014611169001d079042681c0400250ba80001050369600344940c2c5900820444808600c075810890010a0581c2d00031300041159a5034043d00e94480c880185151100d8100c031000c002007041900440c004119844025410100d50f07889043c184450340c800c1d948a569907a81c6401c8942c10354040e6803e00d20358031010806582c0303a00360b101c0115411074045030325009140401d26018003905c00c078210340c074000008110803800c2c684007034a841410849240d21500492a070707050041c000c001c1c50321661103aa901c00c03070000c0b1544104140c402ca80c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 29851264 1250 29850014 29850043
    0xa1101020a0209060609030a05060711010f050103030c020103150b0a0203070c05010c0b0703022206050d06090c1b02030c03030c07031202060601050a0f030e0d0903020a090614090403030b0612010503 87
    0x40307525a000d030365829805604200c04494165a45800e2400249050190342d0010054080c4004110045400141d0b240c52001894024405400710103549030807034500f40402404524100011405544251b010341c809045040a480780d80d80c407101c0c11241c03500a00340080041e03100050380c20402c412081c44038002c000c00c8c00c0ca462004016641d4802840300240502c0805a01160310007250071602c1508403d001c41040c800c1d038690316014010503581c44103e50f038102d10300389040056900f5451103207494079100d030741e181400c1071408026942200115001a641032060030110389080e51b0038001030508800b818020100d0900c3c1d464085003a2007684030b18000c5d5081401000606e0340c2180856540d8010703450140c400c94035170007003030b80102825882c0d80f5140c421049100c81c00b85d00301103a0b4040d00d000f00d0f150500310703580e0b000c0c00040e50014000c0200c3c60904012003411820102000d540240c82414003151200380345000c0750075038000054000901c0d59000c0100b28a0a0a2191301c0c90903501 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 29852514 1250 29851264 29851273
    0x70b0412020f03070503030405060c0a0f0b0105101107050d03020c040c05040e010909050303180f060a0c0306080f0c190905040b01030c0801020c21130b040501020d021506010e0d0605090a110102 85
    0x11702c00046e07101d0043c3e109a0b4064200025050303480c030000c0c06035031205da90200e1041c4000041d410038001e038a409014103030283c8404c0300007005441c041c3d1400250801c0074001456000e0400061000c900c603032007000c405601c14510200c02c55643c5001e4440d1070086940c030341344c5881c5801102980c955040e0f01041880345818254400b00320040105d81c0d1041d41d401c038040c509010700c2c001919000c2c1b9800190701c680640014001482c009401408031100d442e80d05005a41d25019003036168100404074039900e600c101c2c482c500f282084c44014895140d42e00c0791640559035401c80c0425030f9021a07040380d8124550700140700f08030208010380b018200c90340085080c200c403401c95954030440d00103481901600000017140c141411012180160b80c84100d041c00d446d61015181000d4110b400f406001d40924102d10900e2403000800006018075901c0d0b03501551126001500c0b800c03c803c090a400141e015500c2c0041020b41c010103001d44042c4004015100081c208280218200301d42c07079045422 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 29853764 1250 29852514 29852519
    0x905041b030f03050f0d020307030f1a0a092004060306050103110304080706051819230a0602030c0d09050a050c0103020306030a020105090d060c08070e06070b01090e070b0412020f0307 81
    0x78120003000c9201e9250a0085d0f5031507024180d4103003802008126030780140000104441c1503896007000e4100340c00c1c224180035040018500752512442d44900d55040b09240d0400c02c51400070741c000c0e01c1c81041e0251100c1c005055050840e0381079020b50000004039841e0142044a568140f180c1301100300071100d0b0608606013a5199140d034412008040e00d03558580c004141c40030a241425a10403100710200c54850002c400c1d4245200d10044003a40c405070a0040c20300d0b00b0103280410340c03400d12000c0c00340070407880a071398220094002804d65182d1445c24401c00305809407d01c11481114015001403607070200c0e0f4500381c0d1501c00b40100450400d40103000740301c11518002180f03c12282d09091550300d40300a140890188040300c079014000d40c0c240650900e8064210820710b005501d507a5681d41120b1210040c42035910560030001c1c490012840104486d08250344070301c403090045420ba44d8140d6030340c1c1c45001160482c0d041003500d104590304080c214070f028510ba02501c0e41c1a00500405072 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 29855014 1250 29853764 29853773
    0x602010c0f0507150203240405070804020d0606080601060504030605060a0503071202060d0f02040e0f04020303040e0c07020901060f020d09080a0b060607050d0f030f0506030d050a050d05010905041b03 88
    0x125104003818484003043e82010400e40300446030f600441d0354811501e0b4030302500100910b2940403020300362010344241c003014505040c010940f2440d039544400c1c40580701e41e824000c4a40011b8001c0d200c880e61008086001e050074440300e030090091340c0d11a5210341c00c600f800f90440d280a00300510403941084204002e0710041211001c4410b100b00540c440b02e1240041205840792100c20302000741340c400304003900d500d541c1c0a4401c0e54401c0010306255510703070314248142c120a481c007035070503030040c0810000d50b055158035640c40a04104414140b56550b0b020954040003138001d50041480c000309043e22550400012040080038904030000d9440c1800c065210042c44c0009004440000c0000b00700c4e80312401114541e0358400c045889848520f01d0042ca40c01481c3d1416001a00b0405040c040c0480750055900510000b070141505020095081d90a0303400308051805220f002e010842c2d210900b841a0f034001c0c510341c03601040c0e03864545082204c6080e808444a00480540720600104 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 29856120 1106 29855014 29855027
    0xc150a140f0103080711010e0301020c0a05060606041a1e0a0302031b07080a08061201060303030b0901080a03051c0f020313020f04060b1c060801050708100602010c 72
    0x1501c81e210040c000c068203210180404406100000115116011000c00d84105041110380c484101001c00c2c04c4e03030496164401150400b44151003405020303c001580a80300729001840c2500341404034441c40e4021341b03d010206d40104040324024003003c03903e01c403032040c001c90030340303d209441004001e50300864188201c4048119400444002c40c0183c0b14410b42c0908050b0901440ea4001c6407268030041c603ca0b400741e0340c8040503180540078810a030196011756004692668800c0c1842001001a4491703102d81d032000105c140820f6000c13068654101214072000030202c403c61448014142c4003010310310440c80042030040400007001500348842c400d03903d400160210f4001c00c0200d5007a4400c410105404001400007400c0d07880a03904000c4c0358180001c0c1e45512441400e00f19502299501d0100750030805100000342400a06001405944001d0000c401c1c1d818008041 = true := by decide +kernel

theorem cover : BRFrame.Cov 29676264 29856120 := by
  have h0 := BRFrame.cov_init 29676264
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29676264 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 29676264 ≤ n) (h2 : n < 29856120) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
