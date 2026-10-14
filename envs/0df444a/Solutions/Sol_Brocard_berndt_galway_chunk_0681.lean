-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0681
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:07:13.316932+00:00
-- url     : https://prove2.me/submissions/9c21eb78-8a19-4813-bef7-507aef5b89a5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 122302158 ≤ n < 122482014 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 122303408 1250 122302158 122302171
    0x82a0f09070f030506060f1207020a080d0e060601030506130e07080609010b0307090b0618040212070f030b0d0b040210020a0c061d0d020d02060c01020c03030a050901050708010e04080d020d05 84
    0x400e4a0200b0309405801c071040a80403d10601e0f00b031002c01c2c062030740e207400c03a0b44113031000401d1442520760305002c1c0c1c5081c54180e0000c0c46400701051900b08a80264041ca04020090b01114a02e032240c400540458000f900c042350006001c46c0a41c1c680c10b0306401041c8102440c80c100c981455071100300c11304181c000d4558201130307511440903c1e50380c9801c000d03486c060060344101b0007443d9900400901c00b4452110010313010403513070300d40302050789e11a41076510308021001c0d981c00d80c0c64104401441d104a1014010200c1e00d03010404005080003108908556407000c158000e40d1a16001c100e481b6100740907100452045d00785810024900c511207c004040d0381e01c0d40c040002803210001e83d000b42101015000c0c1c11201c80031400f6a4510070490760094040e6a1603a55011051007180684114600001d1074807000091101c0c40b00340d648220f00c1140b00071b000f0486501c0f1068112440d000a1142958030152107000c0b8002c0b034500c4005041d002000580149040281c2c4031a0b81a51801c6540 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 122304658 1250 122303408 122303417
    0xa0e040213080616020d0f030906090309081902090114030f151009050f061e0406080304030c0b0a080712150e0405011a1c05100203011e082a0f0907 65
    0x4201c1030b142044503e403c0030345140d44400d22050654000d5903810501080d008002c40401c000b6a40e074020751000046680129007070104480c103003006001e2440b507120315a4244500040c91266540f02c80504031000d0340145212126440c100d0f19038290210003002d60341c98004d0300c3c00c4a1071000104805c5208403090f42c1c141c085444c000d4040c8514840c1340c0d01011005090400f003140042da000c0300340d54400310459454020350440340b000718000741c107100d40d580c00c0b41c40c02038041402c010000203031003101c2c454803a10408645446840d003103800b40c2c080c0138001c510402c4c0401c84450082001d94450700300150700184807020396504031706031801c543c0040d684005220600041c4102030041808010b0403081400840c03807004080b5220040c001c002d030203d407802141113000c210040c00040c500950b008015034595850b00c2e10a8503221500b40d005c250003d20301d04c0000c00c07640203c2c1030403110044150f14101a545110414002c041c0850885e601c0141c0c568860a103654085c6801d001710400c2e0f0341e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 122305908 1250 122304658 122304697
    0x4020909090715081e13060507121a2407080f0a03231501050408060c0a020d030b0f060702030a0204050c03151503041209080102030403020a02090f060d080a0e0402 72
    0x608220000520041c4020007840c0c00402c00c024050084e80c2040c0c03800d00c1c8188a00c0d075100240c81b8401c080d9480700404040c10001030041342584140c94a48842a01c0020080c04480030300801c0d0900003204803d03008014030020488030860034813000304400042e610305180c0041607486c681c450340945c00b081d194407404500703d0001c42c2d05104070503103c48a2514410881c1ea00082400000d000601c04003080f2204a01d803203469100350240c9000707020400455030141060521850203400100b988001445500c00d4544070383d100340504000e5a001401c1d00b202c5c00040c1007071040c5507000c617105982520a0134940c01c0180c40b244112485201c0141500c0c0c0c0740d051084810320204040c101941c030400502d40c604c0c020b4a4541c0851b0781050b4048a44018803484140680714003c15030301132113041d44040108003d040e00451510f2001e48211442095660340c112903440b8920191041600f21200d140f00ba000a030054008100074442c034140301d8604500e90700080c090b603025060784180c0c01100030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 122307158 1250 122305908 122305919
    0xb0703090617060f030a0b010909030e0306070909050c0f0d05011e0302210a020a150f090b0d0b0102030c19051905030d0504020d0f0b0f060103060b0a0e040209090907 73
    0x2544405404240362007507042c00307402d1074a420a4805400c2030300c07600701c140352403000e9a0b04020140c01c00d07a100740500c1480d070755001403000038040b400042e4003084051030445d010380b402050461003000e2075140d40d0b80d82801c3c01e0044008060080481880f448104003024840210300081c01e415243c0746e00214156052000003000c100420b00c6142591002c40001c0c0300694502010602c180760940c411052030300074800e018609031001802a4102402100210b01c1585a10007410b136a10b0751f485000c03100803805000c85c0c14072170a104808160100b4400d045e01021103410140c9a0b04e01481103030b0400601c0ca910310b0920344081c440000d03001c4400210000c201040c0901d103407410324030340390000681c130719200d43d03031079100e0744d000780c1e80740d40d6640009811075451800f20880340c2d4022495520400e003501d4a081c4141c41a510401c008104000040f842d41c4039010794000d071496408901d0810311842c009880d0460000d0300c3c998010303024041001a40c88256610f88034004a1009150b21807604 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 122308408 1250 122307158 122307167
    0x3060e101410090612030302031909030815060304020d020d05010f110901030e0d0206010e1305060c090414010302062a030c01090c1e0b0304030302070b07020607090503030304171c060b0703 83
    0x294001c0d03d0076420040100100003103501044260f03a014200907aa80d526401c601e04103040b1800002102490701450000b490b50140c081c40c0300c0c804404d841070030044c5100c100489030000710b44c000d40c04843e10783c800340142062418007440c640316100100c0c0210110f031617003098603015003051504820200e500302c0707190b0341030007044034503600d0390f01400b101174600c0002921400c05000c0d200c000303080d0748003240640c10b00720600200075401c20256107150510700d050310b003980d10620045100300c0c1440441035240d00014080c0b4104c0354010003451a15040f07610f80d00703201d0400052542504407052200d1080340c024002448004451400000c0d02081440d107914800304036004520880c403482c0700c0c0074000050401000560350801d80c495140d69603441c00304c01905c540840108002812804d11035800d400081041c0902800e44070140701d1a180c60a2540e21f0208640290440d107403100c406440101b01d07001403a542d1400c00c188440c05040140403030032307614a07074000081850002246024117030321 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 122309658 1250 122308408 122308441
    0x13091a01050c071401090e0903041d0f070e060c120a0306080d050901030b0f0d0c03020a0902070312020a020a0b0106050703030c0503040f1103100e030c0601080a020a03060e1014 78
    0x90030072038200301041000a6459800d401044640c0d0703880c81c0e0707501a6030300503c110703c02000c0e0502800c07100d103042240d0343c0d16604a4804c0107c00003180321003560340b906082040b03105d0a503003440818650394000d8100c4007280030841a0350410380030400c007200c1200c240240382c00020040360b507554074448840e0040c101c4a1a03030001c149604400a4000143d51003011100c40030401d20300410300b03060940021b49100d500950702d80e80158034120020402222058020489000b01e440140300e0b952240030f031013680300300800200041c2d286030b00c11170380e46495800782803611075a04c100c4103101c07400d039541c0030303071440a8101c400030543c0840c00d4010181e05000318410300b8103510b070080c01c504042d40c485140c0500c490b0020702c0040c401d21a0b0640c1e440030040003002641d40c60041c002040184015074481d44107891001c11400b8000020420100000d01d803030f081076024145840c0c940c5551208401002c15420383d20250141050500e4480c03003900034030710703d05090032146010b0b0604c4111008400300 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 122310908 1250 122309658 122309711
    0x20c220903020f1c0206070c1a090c040c0206010501090501050c150718050414132f0405060406030b0c0c0a02040207030f030b120304140103060305030a09030210030e0a0303020d021309 81
    0x3a0041103078130603070340801c0d031503000601030a00700592403035803420b82c1e05420f18a4140c03803118401030400ca0081000213030f803032610400351020006108617a0089880d24000d00942340405c406040c20401540300708024442046400b040c1d47d84006c0c04950200b04080a5035000001113442d00c0505850005209960050404550401c0491103450100466090041680d403e20343c56203002d81c2402441896024484404210740210000400400500d6041c614016000d5450b00e00002e5041c240380c0314801c181c0f504501c2152059980c814134960703640c03051700100c03864000c81d48400c1c016191400a0200d45120b85c5a02c4005030b24184014112030000100500c10301c808401010750400c007104981c10340390b01c40c1102902c000143e00603006084950310040040c4000207042ca611540324000c5015680b007200c805011425246046096130342d429940065034005c0319000c00002e0007a80103103000c104854000d401c044000110710000242c070340c0500398654070b610401e1003500c2540c01c01e40d013005 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 122312158 1250 122310908 122310943
    0x31107050108010311031603050706021005060303042106050a09021f0c060b010e030601030b0a20040b07031b060b0301050604020f121003020a0b0a0207050109030201020c220903020f 80
    0x52500d0002800e207a018131001c1c00700c03042400300030082d072000d10041500303149500040305e82596901d0314030b0b41c502e014401c0e04014010000c0102d60080c0c180191400303120300500841c101810480103141c5c0c020f140010301000d01100903044005034550003450f115945528001500307100300d0040c0040700352038000c01d90480c0040303000c1d80e2965070071003210000c080d004007000a0540340d410040e80c80524000c00c4603410301c40c1d280000100180d0341800340c45000000000d0000b0801807099485003c40111b070084551810310040c00f081070440c01520f107080c064900780728001c2a0314000c1c9441d40c0044019a00700b0348900340507689090034000c0325000130043e5401c500d400c007241544201401188500c651440134180803590f40e01da03d4100328040c40d0000d0020520030307580c40c1d40360802d905c800b143d4030260050700000501ca60082e100301c0e080381d8040e00900032030540402003003040180741062040f410741c0104810b2a0002500c40c0c080210711940051080c0201008000e01e8641e81070000303240003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 122313408 1250 122312158 122312173
    0x3130e0a18080a08060301110403060207050c0108090307030f02011e140601090f0b1b12040906080a02181003060c02160905040c0e04030c021008040210020d0206150d0609050601030311 81
    0x10030b09021601005460700e8035924070b49450b8000382c05040c1d6039003e924005404907000c0f09220065001f010402d02c0350f0120b5525031150401525603810444130304c40d440d0130a01580d008203001d1900e0100700030341c1d4400056480f011464214801014211030862560f5445080140c642400911a0401c0d07007420a040c403180f80c21110180c070003d80c000d9614100300810129100145c42000401100c20311080d143d01203499940b03460250401d1045170183d9003030400026400c1030101e5400c0c0301580160822256406856041d184100e01034002c4010305031045000000c160305104090003107800307501034040f15081ca0305006544c4015044144624038003001e000024108591410454100c00e002c0070503595242021b5a01014802d0040c0d0454122402481010751201c409881540b088402010b401c610750412651441d0329100b05002d40d01c21804a450b411211084100703021000701200400c03c1650744d204195003100c1002c0742c15901c000014001c258100b4814000c4074104030060852 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 122314658 1250 122313408 122313413
    0x160618030804290c1e0f09091b09010302090f0315010f0501030501080d140d0f020703030606110c091506070c05090606130612021620010201020c120c03130e0a18 71
    0x1210005400a200c078600085c4034000c5074160302c40080c502605c101c00f00c3e1901c448604c2c0391182da2000b03542502c5046020009109844150134448008140758034071400d041c103100054000b075001002241d403107600d410000119980030801324034a890400c0c4483d0955141450361008040103410180c145410180140319022002850114889072440d01c0c1381400d04241c0c200380d1a00c21401003100050400031000c40222050b001403500300d109680c00c100302d66842e0030407140f50b07102028084c1540c201c0c407921081d500d40181200d8006082405415840400500058041d403015200b00c0300b01404007001c10151403c204050b5110700c040c0c94103498450b00501d05411010700380612414440f203c04e40125a2040d031303040d6030544508149010aa40480c2001080c24203014490642c2c0e1401c0e00d0072030044d52060090390300035400701d002048012441c0185280941000b000c0c0310280c03006021074404001c001c202600180b400200a01c0141000f2000c60203440340d6010030700c421900303007100200 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 122315908 1250 122314658 122314733
    0x2030304080f160c030c09060e1801061d0f06010e0102100515040608061005010518060f070507031b060f1403040203010f020a030212090a020303160618030804 70
    0x40c000d900004240c0d40d40c5181c501c0740598000c403591402da0a02403000d100030091840d101209490180c08040e5545503500c509506070703240f40c0170310003440820b44040b4207500c070300c0c2403d00d2030544040000b054094807010f002098150000040e03088010101c14400c034480940d80345500f01900b031074941048441030700040d544a68040040c01c01743d030784e000000c19442003403481c8a51540020801d2001c01d41d50f041d105e81d0b800d000d441304026022220400962036006008560058403000301183d110000c182c1046442d4011002c01603c90300100040c800288080c030030f0201440c0b050040e8180380075004440502000b103500845e0a1060800d81c2070303007a942140074104c41c01c00c201161640c950311440440e024101c1820320b000090300206d16150700725050f8000c1e000f020041080050240d4924454941d41c0d035000c4d801075016002044945802680308a0340d0ac1418040c45001c544152144401c180c0a00740000950000301d6803401e1104014103a12052903080c980302d03840c0d00c0e0f40702d4845040c0303 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 122317158 1250 122315908 122315911
    0x1812071a0a090b12010810051603020c0a06020708030103051005060a12030509040c03020306030c010c0209010306092609041b0f0e0a09060e07021e070504091e051b010f020303 77
    0x610300c0300085412070745288034161001c050400741210a403100d54415001ea00e9003800c3c0511b18240c041c03a808417100e01d5007440b03050305c83e59580440c0d2035007201c244001d8009600c0b80701542c000340288039048000c141503000070701d1680d1242d040f00e0342e6503256007803140c24641d400c04c4649180d800d200a111069540c0b440000a0302c0895a45d4440d030891803405540750b11580300144e42140c10450907841842e0540d01540c4210301c1501600d240d1721101004483e1003290b100c000303501840020060010900c3c9610113039402c2d106801c0440f5600403040c005086c41050380c2c1c0360a00400c0080d0800c0603003010f0240c0c0c83c995007000b030b035020101c0320b001c409020100c82607110400c0120040ca024200e5645000c01002440502020446035403216002d426844088981802600c540010708011080f0122280901c501d484084c0c078031141090104009401181c0c010354171004425615164201800e22154103144108010070500c5a2266003034161056007a80e1411b1240d685010306070a5008030488c0d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 122318408 1250 122317158 122317199
    0x6032d0f0105090a06090509010f0606090e180307080f04050109090e0c1203090d0507050a1521060b0406030c110106060207050112060806070216081606050a14181207 73
    0x3e816900c4200030b40c020070103588100607030342c2000c050000300081076000020625509100380142d079100c890690b00c02e02903100e9068040360010008040701007120411544003054410740f441c252003074460300c1154100701e000854018001908218540c0c000301103070000d01d10381c0300902803030605126050301e80c0040140305000b60b901042240310b00d481071045030351025005102243c5410641002c0c0c0da55003950003401d010707074024007001c030715040250700041c5402029554803000590345818070300f200320344000b8190b80b1502d401001c10740b4020800684042c00321980d001486041d0702e0801424480035002c0c4450f1039150080c2400300590228581055031070a00f0141e441104c410481001002d143e800080c490089000f40046c241d4041b401a1170055045101c030405500c2d502240d4032020035404040f84e00815400401c03840d0700a802a0030603c60604051504a040001c4211150301a050704507001b880104000200e203441ca58509072405041c00400d8480d00301401c0e11611000d00914 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 122319658 1250 122318408 122318419
    0x100b0901081003170d05130203060123100e1c020a0521010603030507021e09041502120901020c10051006080405031b1501060305060108070809070506032d0f0105 71
    0x81d9104840c01290005503409502c22480c034050b420f80b042c0740d410581d03194217820305090106004000c2403203000c030301c20740040107400a40d00e011a8000e21141240051030030f45984070641400c3e1b1380d45400c2c2044001e01703440e002100ca003001d0800000b041d51406134120f072205000d214000d41c498001c41402d5070410340746801000e84003000265160801448400a582015808400c166010000c3c000d61440bd0300c07421031121006a0f00c0c03100e220002052134001908100160116002e01c0002c410489049001850044d15403500280c00318100e489106030f03034000880001d030385000c00c40d1a03842c5c0380090080001c0d00340b50000c09900c10445c460042000643c001141c10702c00c0c14030440710f000c41c2c504c841e0202d158055664030788954a03c02c19295007890000000342180c042c0c0951403081d48140d54200c4641d848a000307440606024098001610500c40045003d03200c02c0d00450281409811408545460240d41c0024100003a01e401b41c840f245024030117850700d00e44005040d240b04649 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 122320908 1250 122319658 122319661
    0xf08090d0f0507061508060601260a090807050706080a020a021b0402040503030d0902040501300809030706050409110c060114031218030f0d120203040f12080a05100b090108 76
    0x400b22000c0c09914000f500300c42c42c20400c801821042c0030300008407151031056460541d1460019150000d030308ca464082200c0c100001201c01d400696483d03400b0400b42c0002076030304180d8070740d060300b5001460215040c2d03001d12018010150815241c0744d2188019500354070302980020003c1d00d410204900d20700450900718503c00c00c0c0d4a83d010764014060103400c072034444000d41c2074840a8403820506074041c17480d010000c1114001a10380c030010604400000801c03609104800880485112003910300301420710490a8135507042c02030b04000d00c03442d5500c07902d95041503d83c0c4112883c20410f000c1260f420041c007180a807021680c03904540c00005415181c1110310013090800507821a643c032040000101c0c0241010a035005442400c0281c003100e01c1e20b071600c0c0c00703107640b100c010043c02e010801440442000300b20a0b0021035201e8400c00c001041e0800701c0c0d0340c020500d0700e0f01942d003011030807490410246041c02d1192a5102d040c051021444d03610341034041e04288220003115040080200 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 122322158 1250 122320908 122320937
    0x8030f070206160e010e0a05060316030507030c0518040e060907080118051203071e08190b0913020d05191407030f060e0c030f0f1b1c030c120309030f08090d 69
    0x2081e1f240180000b07001e40f0368901d0035803612800d070340412005402003031419004ca0040ca119104e000186185901c0d02440c0074540c15414880d00c894501d4a54001d03190000700b101c10703c0c103101c414007035400c0700e0040900c142008107041c259001024800b00d82c200000d0007802054001980082c1000212444c0d50342e0b854400c003c42d0000303040382e24420241e501000c0d9850041e40b094039184540520300009110110103071960040e111070b81c0803682d1001200010500b4003c070002e4541031184010500359002c03159648007410035112421500b91000810f500c0300600426400010004e00503170060000c0d5815980c84014005007503001904559981c52058425207041124080c0b085e8001d0882d00d40984042c078440c0d45100c0380ea2a0f2120340075120045042c4004180ca5264a500080100c0c407080c200740201c0940001c004401e604100c0190323074020204001c0e1800403514040303594003081d00304a6080c05802100c00ca2000c00030081c2c007004002c96610041861036510000c2d01e0806100c14985 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 122323408 1250 122322158 122322169
    0x9120b07030b1201090b06010e040c09260f0106030201170115050f09120f010e010c020a11061e040f140102060f0a110a180506070203030412080708030f070206160e010e 74
    0x1030b0350007150741c6003a16100a00421b442550710070402640c501c0712803009030f020320043e28601c80328000410051602440b01c25809a080600c880d41c001d050030709034105461340341c40c1c5283c02d00c0b5804165074500c414815560f02040d01501c505000d0b0216000c9d51501441111078944c8141c100104040400d0240014043c102154017954009001090800540300d0032902d848162032800c10729031801022058880d0103001d41c1ca4004a10340142c54100e0054035400e5840428021b915804103003082000084180b58505401045807850410f440340e0500c0c1005400842c05c1d00068801c170041100c2403116a07000811030740c0302c036000c5c05801c043d03218840658054611140100300c210301c085803a00f8281e502442c01c0030f120f101889583d02c03407035490092100314481d0300f501a402d0b4004020921011110b119003103074940c0b04c1d811072071070001e0310303100c1403442d400550f1081001d02031842409406581001825086140300010780315807208400040d1100004074580d0781440b48040d5540c2c0300f5640d0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 122324658 1250 122323408 122323429
    0xd08190209040e010e010f0b21010212010609030510050c0a180b0d0b090f0408030105010c0309080106091b0311090d1509050105180a0b04060506030c0307030605010609120b07030b 79
    0x20b4402d103c1c211102d65190b0203400c40f03080700c031005d600c1d1801800325408603024071904500080c20181010711105404000d42d421009034800359902002340b40680206100940d0003480d043c4c0e0398002d65411450b1450410605406060300c2c1070810707007400002c07a5508201c940303401050400c150010060054000400d0081e44510310400000c04c1c40c0c0000304154104c207880f041c0440d032040142e924841d1700311500d002070341c000e800f81c0020710061165501501e20102107500074200701007190750740d05602d82520090303008800110340700e44010b0325603810050070810744c0c11070342400d01024101c20103a11981c000c28107120303c80ca000080c2c80c1c040c441240c0903a26a011218014030000c081801c1660107454169404040d00400948074440d07410040f4000401c1030b80403003d00c00075203540d2200701c064079020700501c0e41401036800c60070b016a010040c0c0d0000710b11980c800300d460740c0b5050b009080070100c0e0f0f01c10180c07500c0701c0301e8000c00034a100c1e12260b80040d083c203000820102880c0881c044071103 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 122325908 1250 122324658 122324677
    0x30d17060f01120903020705040608070f0605160b0106120e0102121501030e0709020c1207120507230d020708030a2a1502030402040516020604030e01052109010e0d081902 75
    0x107400e4030b004c00d00d940441c2540c1941e2043d2400d00840769904035090365802584508000e000466805120b03480c8524010003900700c00d044071710102035880c1c6858052980070307484000800c0c601e2a03600000d410602800c003080d51900c00844c10103000120000d59480c000340540740a442110002c82540e0080d84000d4210780741d8012200f0103500d070325004000350f0002e0790158842c4100e0300ca01030415060401c44a0f82a4044e150381c1203c503a04400751415007000b00202d442d80300c2401844407010317400e0710205014071100001e24a110800b070b03000e4107140443e00454600c0c0c104200d01a070f03040e0072104403840c501e1907210111103003d2196001454105100e4001d000e0a8500c95111910050383c000c0d5002e203000303c40c200410385403424891003900084e560040560021400200401e0081041242912040c1006842c002c1c000146100001d6440060300c07101e40c8490600031101d034244101e481e40f880d65402800c0041e50208043e240d840001c0c41c0d640c01504805a8440001698060310102c04 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 122327158 1250 122325908 122325911
    0x9040230030d090512030c1b030405120102090906010315121a0405030a110c010c02041a09090322030203030f0c010905030a0f081302090c07050109020a0306050402030d17060f0112 79
    0xd00405600060180f402d402ea840303208280f40c0740e030652901300c102c0b40220900c1c1196890038020070411301e1507240d1400103804074007041c040011a07031100c2c2c9101310080c800d140016035a00350001000303102e50025045504052410b400501004408500d91041d01c2c203004542d868840d45140440c01000d00c4481501c05050303602c01c1c002084000030103441c01e03102c20703112105804c0031308c0e181d1540d43d1045101e0f01d0025061610080142c2402d50000c03a600400051041c0c61043c00804691030b181d080d1109843e035800001c0006c18080a64986a002c082c0c9d60842c070503007444c54002030b9880c06004000614030386c000500c030414850075480034090903805003d070f949400803104040c021004603480c1c400420f4059001600c08190102c03c201e256078001c103012025102c41c0345408894100a034111007665940c105c11004d6034611b6940b0303009520401010a0a140c144141420074055410b00400e2005400300e40030040c108283c140d502a2003035818101c0782c8401030040340c041000b500f4540ca041d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 122328408 1250 122327158 122327167
    0x90f090d0302090d21020601080303060102061b09030a1b0e060f061b070305160504020310090c0c0b09060702150405060a0c27060305070c020a0e06120706030b09060904023003 77
    0x3d045c9050100440c800c1e070f02607881c0c682e0790350740d01500c07407200b22034050060300624005964500100c2218011003d402c1c81c0a0400756110082490002000c0f0b040e104084583c0d80c040c00550030802d50006050422608a032901708000403408080342c540f00548103550100c1d6215a09285003c00d01410107442c04944c48603640c1e0400300d4032035a0206031a00701100114000c00c480c285802142d01922007462142c107481e16041c40c1100400d501c1d01300d4000c1048080c0034002040300e08076007074000c00401000c0c0846040c00400a450310807001038000003090a54200000720300d02254255204002d043d001c1400c2e86104421034030307170300321107043c2003040e2060300300310034861680c2144000e540341620100b201741c0701d034501512840845800290310060114042c0702c0c42c05159021a000350303024000ca10850301e44044981005880e400400c000313590f401003d0300c9440c002001c20741100054a08440e03a00b03241d0003050110f00311031070000707200382c4140205d0360030300d04501640c58200498003902d489 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 122329658 1250 122328408 122328443
    0x10e060306061213060c090806040314090406170106060c081801120203040b041407050607111201140a0f02041503051806011403060901050f0610020c03150105090f090d0302090d 78
    0x500c03c032a9400c0e11701c113290807180c0b00c141307004040300030030b6070320000003018541e41d6039070102ea003041d2072103100805040a001443c1c041d1243c1c0038840c041c1013501441005020800c071001c1c2101c40e1a841802000100500100820344c2c5404403203030001c1d40342c164001c9004000040e01c3e40658501600e100502c00030411050198202c0c41600462190b1041050528118a5190f0f141c0207400b5003940b08904000e1040000c81640800b0240b01010f0006c0312000200e2000c10308684024a1a414a9504d0700821000e85880d12414080d10000401141880d084c002c0d00d0081400c1410480c2c00c0c9603544000c01ca000240101703500320000e42c4001c4413560740e12980302c044030b811004000760081c030601d40030440c020010b008191048079100e510a80d0f9986410401c0300c1080c04041e12030a501408a01002588092180f540800c42500084145500d0070307040c00301c400c0d002402038080001180c140040201c003c80d8501208031680b5000da1120841c00c00038043e9418550010a0005401c3c402c43c103 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 122330908 1250 122329658 122329681
    0xf03110405090708190203011b020105040c08010207110d060b12010f0b0108131e0605090303060f18060613050418020111150408130e0a0b1c02010e0603060612 70
    0x188008195030900c1a911580b100a5941c1c0c0303240581c04aa41120422101d00201008581c42d401e000900100300c0d0300b81c600c1c4002d9000c80a45540e00107175180e208000c1031001c80560500148260002185000484d89681d520850307600340c0b861103503030048810000d11030242c104030340200d4001e201c0b8003034074100d4041500a024441401d104903042c83c070301e00c580751701820203070780306001c3c16003016241d403215502d01900420b0305524a012403003031107100010500038810203100ba500c90b002540d80f81010402c000c500803445014502c19001a01011502e516000200d50086801c1e640c8507181d1118039043c840e032990755001f480c2c00c1450302904800308500708854075240d41c000e8888081c4141c044100503200c1d00c0000314400d0000c070309008540010b40f08002041280207009180e040262243c42c0c680344158240e03083c0341d0460304c1c0c60350710b4518a881280340030801c01402020072041d03800d82c00030b401040621240c0348680c0c0c0100c0001c0760358503110210341c0c2e90755150580c2e4045240840c0f1240 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 122332158 1250 122330908 122330933
    0x30a030c11060a090b01140105040902070c0b030f0121030c031404151809020708030f0702100f0b010e010f09060e0a210c27020d0608070f17070b1605070f03 69
    0xba1204017000001840c144906541600000c041e584d1910f801e08100600340650701040302154680400400000e003211810091400703603413041c01e4400207514001c1001d02c02c080c10741ca040c02c01d413000300328140020340003c1d1034413003035500d0b00344507030300d00c02c0032800c010140600d6000c103251038905098000c00c03940c040d01c0600501c800350107806020741c55036a05022400b031101e00408550042010a41c0080000070190340141144112084003920941c44000c0e00e04040e00601020b0310f401c201c1a00f9030708140d5400a0010071311700810304012415008140032240d100d40030034016003020f02042c0d500c5d1892803001a04422588200b040d010580c01814100345034070980741884985004690031218039011031803e00b4509420181081066200d002988408480c1c041d06549100014006e034050003044014844092819001c510f4442c01c402e410205200c1402d407500112401e22034050888291440c10440303000c0d00030798080c0c614100b40784c842180c2140580c90714880d0700004025116000a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 122333408 1250 122332158 122332163
    0x2010903170411090a060302040f0501230102100911040507210903080f130b01180f02030609010339050103060b0307081b070c120c0501090305030a030c11060a09 71
    0x114041d210310211645801d80607180141411000e408031800b07441d1196140b42c00c10030380d035070001c1d200c0ea90380c0c005002c5458501408d011191a5001081340c1c119400e92044499402000c2c4c041c083c00703c000003501d40d801503441c070562a03a1038441000344401e0b103101d205068000b40080140e0300384204040e144a8203504d0340d82a240d442c41c081b00c8038511a0143e1010254562200d65903074951400c1d1100180707004000008140d0701580c004c0c04142810800c500a12602402d101d0b0301301021098026104174500c0c1400f000e00400600c00c0540b50240014112a0401e40481003443c0c400c8247c50008102c11108000350a64886186241480490b0800b2030300d00b41c90070000140d850200844d240411200e05011440105c000717900701d45203407031036a01c0e800b2450030076140405944d40e607902c42d426030b0030a10703901e81c85101801c10800c80c103040c0c401030002400d080c01c10f2850741e82d42a54034485d0115820816440d8000b01183e64040d9010b0070b006400303d410380d1001d00e841000c0100031b22008109 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 122334658 1250 122333408 122333417
    0x60509100e0714031e010b040308072613030b010b040503070504020705161512050f0711010f090501020301030204050f040507120c05090711010c030204050609040e0a020402031806070306060503060103050603071502010903 97
    0x50810055402c8600714ad6010f190f40d400c105440d01c03100048010640c5c0d40400c1880151030b10102c0011500a002120201c040c5400301811414028a07401c030580159501a00800081c821950000303020011190112009685d81110b03240103800c160092054111060030020049541810b10365900400302c25645c40131000c10b510500c0740c095600c26100c01441420010104a000388518000710412080c20001b1900c03906d07010245045514503141503400b4bd6021006104520700381c01025041050f0402c6012181815200c11340c540d512846044403103074040002e00d0070041c0001800c8010b107402040141107181146000d40f6030024007028207080c3d480c002024100500078800d480c1550400b400050811440d8814000102240e0640e080e031442035110380001030317845c3d000039407050484200b031301c50383c61000194a2601c94045c0001d000d040c18420144580c81e8441c050300d80c011003d10300454140c842c040401c0c00d018540c2c01c01c40c440300c407480c0c200a4a54054220950b403510a40d00d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 122335908 1250 122334658 122334661
    0x603050a031b08070b1b18091005010905013f0c020114130201030e1e240a09021f051b071a0705030c060118060509100e0714031e 57
    0x3040b940c80401410b000b06880d40503c2201d01080d25105032561201c0c10024070700e2089218403802103550002e2a000e00c600c124102c102c02c49007031240d80150003c0c10031034503c5071039003800c00113040f10300e8501a80b8100f0456034014400c07128141598582442680e9030118403e45600030259110b90300300300e0b0280c07581860041d40c0e22600c144a01c62103a2170001480140d51210110301e481c0e04450141a4100354540c1d49803980100240300342c800505035200e12a5001c4080305001d420000c040c20b14800003950a2200d030040705000004a41c003000903400080c1d0300883c2d00c001401c1000a443d9a5201d05c01001c0918030030303800000910800708400d080012000d604180380b41d8644250165000303060024100542101460004c3e1824522400c140ea0408100c0c4c045103140403000d074040302c0040003e2103580030035102441850003820054800c0300c02464103414003c00f6828070b224510146011000180e115845542c0c0c0d01d0101c0c1d8000c60b91641d03810860f456a010220111314010b42012140 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 122337158 1250 122335908 122335937
    0xf1a0d021201032009180a05030d0c0207050a060210020d0905030304030804020f0f0a0306090309150206100e01081b130f150501030203010509160e0901180b030714061305040603050a03 81
    0x3110b90304068001008800d00d6921044243c0b80340340044080100c6105c2c1181d10400032310184081c0200d01d40340840081c500000d072100901d025245d03408075009083c00641031002507400f044c00b24146041c10000b603030b207600880c2500000c2030480c1018096000c04401c2c0002c0580c004d8195004500840300503441d14540713002c000000d540c5034505a449580c0c0c0004200060590b0000d1817414000e003092079079203607100400c07990a00240b601c03000503000700c1c2c00c10100301c1c403202c158001390501804404082d0704021102da035801c000943c80c5034140000c003c058859582d0500e80078040708e070402c2407040b900080c1840b0040c110b000c81c2d4255000441034081481d5100c2e100f83c0b812204d0051034600280c65800320052034081031a40c46d4204042c085903202070f80c4034809010300070b0510140861504810703581e080f0403524181111407298014900c100036807150328403035090224040712003d035500c0008091410030b4801d40c0c0801e420034206000042070100100e188280b482c0070b0b4445990380e10000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 122338408 1250 122337158 122337203
    0x130b0102010e0309031506040b060f0a080f0402010e0118090f0e07230d0f02090c09040e060412211a03100c05030103060209011b0501240f1a0d02120103 67
    0x2c040075015400840349006002d1b00d00401500820042c00c0020a40b4405c00030070059030240c1c0340d0410713004000803009100340d8460b48247c0e03c10404421440f43e402c2c181d000070020f0800b0712415042241c1b50740190846460b80803044000c1ca00d03603504000c0c102250004102520b010584081a07005007403000441488004132030f280884490384c1c155944000b40c040001c0c010900209403440c1603900c0c200401a291040140e000341019803120b5100d6807110f040000352958501e803003003143c0040301440002102e030450501c08451606003482004800d14480090403400c14408001c1402c050001030781c04c60440b511070880388160107484815800706400001c0e618414503d20020320104010400700d01c06078054412038405241146455070b4a0600c8881854000f00a6400c1e954846031005c00b5110141c16000348030040260b140f0552600481d245030300054030403840740895080c115414201d86c1e01c100e6244a028134002c5459141c60354145030b014009001c22588410b00044120b42c840e401c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 122339658 1250 122338408 122338417
    0x8100603080306040216080301081e030c06070305060d020406180e1b0d0c0504020a1815050d0b04061701090303110301030203030910021608010b0406060807170405070302130b0102010e03 82
    0x2016801d4915101d4109000080d844409003500c0244040c009000280c1c1000041d0700900700800204132060006c0441c83d5001d400d20a04002a0700401900003105030102d0364641c400c040d0f090000d4079076a41004144001901d0000030f510524210021072916208014125a1041707020100803078803034803240940d250100480c0c0744410314007901d0200b00c4e203440b4a15922091060040048266441000c0760a90f040002c60710042403c441d42030004031031040d030b0080180700004030010301d02b4652001410701d2080c1250300d426503803101e10106054a03940c2006d8004c0044252428007035182c034800342d000b81503110048001a0130075911100020236807050346d042c0c1c0d130020080c614100c115002c0152503501c100044081d0f0140d000200c18201042e0604002400000700100b4190707180780c10802110340baa007144061148074018414015801058415407040601074029251140c0c00c3c41441c114440c3d00080d031100480b0300c3c0b2242d00c1c80a8114107140c1c0c03001c2c1c00030700c25203c1302c1903003645034000c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 122340908 1250 122339658 122339663
    0x4140f15061c0b0901020f03010608071d180606042610061d0403090503030d020c010f09081603020c091006020118050d0f03060b07080703080f0f011418040c08100603 73
    0x2d450390340780400d0282160a401141183c00140341c1000302524807040d8009a100d440455020390030003000c01d400000800550719880718203c0e0019a800019007080550500b40c0c80810140000440a0301d94008072000351190b650401350030f0450803800c00c1030080d201003081581c0100389581a9062840c0580b03000c1d20088205004071850210030400a218020419020403010a000081c2d5072000c0c0000c1000c2c00c0d2100f80540da0351000154cc0b4203560301030303500c3e81d007151074628901c000c5043c0ba000c0d01c8000002c20070241c01401141000c901c0e10400010b00740e40800090b0500c14050580b003201801c49107650002d0142d260380030311a0321101012440500103400c42c68012010b40c0c441e041658101c0440d080008465813640586105508460701c00c130f40c40400010440705154002680640c8540f1001c10003541e45058042c9021914040c840d86060320300102c2c00083e95a07400c0030801c800107040840c3c0690340380c5410150a0111395115541442c0906590404000d07407500036481502c2c0c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 122342158 1250 122340908 122340949
    0xc08060c030403080a0212091e120313031103040608010e0601050304031706010912060603031403070903020f0105070b130b0619030b180f060a1506020a020904140f1506 74
    0x50b21500c044e81c3c21007000f001d16601d542d08100d1752440d401d00f40c61103400386918100a00c0ca19031083e482a070003a8940501c040194010f815404854420004803503010910074034000204a45180a031220a4461480d201a00012401143d001d502a0081d41207524800c1ca842d81034031030400540b41d034802510050002100d01d02d01485001c600c00c10950070000600d0460030407030752448070540807600031901312450703030701c402c81001419445003004881000c039103521459030501c0500030700600c90310702c8000c2c012000b070401020968055800d8864580e00300300348200c41c4c07411040340d40b100100c0c0c010448012030584081202418000181004400484124a052800e60700c0f8104070000080409540c80766070004810086d100340f00e010b0108170008000c0c079075404c02000c00026603106042400709066101810010f40b9030025454100c282c045c0c417a8140d6845031b017030200c4040364000e12107005200d2100d1030000600c0c005541c035844500c001d03c9840300d48401040045100216100101d4034 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 122343408 1250 122342158 122342161
    0x507081f06030228090f02030405070e0c030a0f1d030a0807021207060209040204031b03061407080106110a020a0f0e06040216021302070b070c02010807021501090f06030602040b070c08060c03 84
    0x154800181c1404d140d4404040d4441d1950fa40c450001c0d21120240740c0040c603008000d20003007100400c88100601883c11156426240601c0c2ca1621f84c000203000300107007074541440c0441110310b5802040070728210315200c04100d04081066649a000c918034100254240000075036051002c070f840c5c0072002600540d2890b040c510340760f0f0000303904940595a4850f40c00c1000000080d4808610500f10281c40301c0102510303d50705207001150103100425800400ca50200030b491a403003c0444d0555059080500c030b01c015640301e8a24000041c00e00075008a81140082261102d100e0a40300300c44c41d8a5150001d0382e04d01c030030312007a8000c0f860740d180313500b058026071030040c6407030317100041d0400b02c202d001428008151a07010a46000b5648080403482c84031496055503403000302c07607a110000c0d00003010b08441c0000303040d0b88420148100340d255907480d00381080e03d036441d80007807005540048003503440b1901c1e4044100b01e40d020404c100c4401c405d200f0006940240469003e00c102c901c16840740c2035 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 122344658 1250 122343408 122343439
    0x6070306180207241b090501020d0507060902090a0509071202030d08070203210103020a050306070e01030c020708013e0f0304061b020d180f0506160507081f060302 72
    0x2e500401001c451500400700305040b50601c029800085a03e40340c00400c0440504142c2d588900c032006048040002e40c00d014401a60005542c81d00412149401c0f40e07500e000c0c0c1052070080c03580d00002580000440c00344900c100640d04000e005800d22010f0322495517541e555041040c400610082d096007000c43d80e03800150060400380c0d0f120040d40140d0b846d00c00c602d17107c46e41d08241c4026010800403a0401441035040044807000584001e07402021103040501005d8030300c0782c800461504064036000c008a41c28828410803000b0050328001388100311341d400000349510034040b422000140f000c20300803008501044491000c0c5464044680341c00c81d15a01000258030080003608c01c640c441c62682000e0f84142100d401c0c00b08260301501c044000310600600405503c5591144040341000a2000c6008947c80c001150f4046036100d9540441240700c02a40d10310a1014110707028011001550010120b05031800d500b941e0001840c0c1c040f85c81d2041c08a0f031050101a4211501442d031001 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 122345908 1250 122344658 122344661
    0x120c04051e060909120f0705010b06032e0b0a08010e160f0e03070f03060203040501150506040e0603010f0c020d1107060816020f01020c150109110307211103010501020607030618 78
    0x1048072003d01945d004070190300d08620a035005024548500c6000143d500c14000c00f846000b929100c00c4910525505200f00e0003010595910564401c01202c09079807170010b804500c6107401040714500c2c65032200e56490000d440d8060034824609004542c03800a906a011020200308202441d03d51a14944203280100c42c1101c040102c0ba401d40700300c05001c0344c40d42e00c0007010300055109400c05a07a0703150500d40306082d25010540c90b00074181d032010912a03580d13607009440036281c1d03031080c0d41000d943d03c1000034050401170b548100728914180c0400c1c8080d50114103a40001041c0e1254102040102e000c25555800c9100b51800503001d9008a4020740ca080c644500b520198411200b003c5418011030382203134001c1c0c0042d1003950140c00010303c54080c1e0703c0500d00409c0c88200030084039800d0740f0080c0311480000c0c004002c200300020004201070300741c002a10b1400e12640100483c84100040c2c0c8015031080c09802e026200780800034030300503c40d0140c0c1042d280698400015007842c18101030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 122347158 1250 122345908 122345911
    0x130b151603050c1609020304031209020307050d080403020a0803090111030a0f03110702090f0a11041404020a11070f03020906040e07061803050115170d020a02090402060702120c04051e0609 83
    0x40642c010480c40203d0f000c455084d083c083e040c4081c2c016582c0c1041e1a01410b400d84140345001c007103091081040250342c0c080382d90300403240c05485003c42661546446c1c0003511581e04000d602402011000c6640c0800101500c1485002c1c1c1718441c02040c0b040d40e00b992402586901000a4940303c000380200380310340c12070040644411a40c50070301c000c5500040b4010740032654403961400440410210342454003503508481c561180c45803419040140700e280300140352b400c00e40110b40000306000f04922645100c036084518409454072140c4a00700e18510b0300e610301c0140d1141041d100403440c4c5140c84e110328100e0704ac0f03000050085a140003010b54008442086028044c5542c03030000012403000e025002280215511480c604d47c02c15294215070008485654446d070301000e2241490b58000134010307009a011a0407075041d940e10b01c000352251003051802900401c0100240208a40000b10800c81c0c031411182402180d40c1e40d200c1d0b410550281e0f2215860014907000f1580074106855450b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 122348408 1250 122347158 122347177
    0x4020703031b08060301060518151c0506090c04020c0d0e040b06040801090c060212030a05130642030b0603010e0601030b1605090907030b0a05130b15160305 69
    0x850a001840b050003000580b032100c07500402d05650401003249030a12820010305011507001d5068800d144035000c10b00130003804031040d561415503c0c4147d641d02c0200d0f1420340316245160001201600e0701c10b45038401a40d41790014461b012070b05001d850680266026621100700030026100d5807a000c6503c1d00700c0704190b50700a0350300e102150340d98072104000d0000c3c003024400070a1084103481c4c6042030f2a0303990300010441d00090001c1240c40d04c3d10301100c2d00500004bc0210710346c0c40e072540c0c4038509010075070700034031031031815092903c00402c3c00c8a80301800a005080c5542e92541c1007500f86003241c1d0030060f100020208020300006044403081a01700c41d018000040e507101c41c0c00312034034000e0207820070f07a00c0c050356030100009200866015951910240303003441c2800840da000c6500040050138660905403661002d0543d511858a82801060014002a030325030291211a00510300c201026010b490b1100c441c000360115002100c08012603401407851045113a242120079400c4240e4a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 122349658 1250 122348408 122348411
    0x6070e0103050a06170c011416021e040c09081c020d050f0408060a0501080d18120609120906020c0108090c010c0c0e011401080112020d02060a03020d020c15060307030b04020402070303 81
    0x4240c241c144800d00482017070a200030102c20514000141100000070100d010a00c41000a07550381814800c2400c10703250b040d01c43d5050301d1020f406e210180303008002c015070400d02d4003403280000b907400344091007164500e40541d92480c4110309002c2c80807120313404100140e8001e940b540c03412403182008107031903680510880e042075200e18450b803d1050503141c3d0790046445e00b006100700c050038001100b1790401814408007075030344030341c400201c4010303403240e10410004049580b003404200e400c0014a90380c003d43c402070340444884080c0030980305016090041c031a00740c85501650080e5010790285d21100e0061450000003c01142e180c01216401c9514540c80c0b840081d69440896491b03011300004108241400c4602000601030041640804407508005404601503240c6180f000f940e9a01a00d00d03565078180780405401903c40c1800399508603100051700041361034081103004140a09100c42d0000740c80d24010180d503402e4601000c0e140100030008100107141035070003081d038540b103800c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 122350908 1250 122349658 122349671
    0x7080606091216120b07080a0b040905011407020d08161404090c030b060f0a14091e030d02011116170d0f060e0c07151d0a060c0206070e0103050a 64
    0xb20303000c005004410041ca90224440c0072601e048000c144003d4200c1c2d00c6041e0854803a03407116688010080e01d800280319907040498448055504900d40001001d4400c0c0400525403070458020316020103e071100805400100d21102d10108071620340948503600c44000f0b440e911030054503841d4201100c414021b4080b0301c01c2030b01c0390300c80140c8000c0003801c10005204007004800381c140d4009405040c4241001c0200b03903010b03445003003907440d047e106151080c0700d404400c0e8100b00714810b0440c596030080003081c0b9000083e000b40d11040900b4816815150b009504400990903981a0012071002c1201480f0071045a1400010a26a98045d0103110401c0d11411030072089070744003401254015031075034101c600040c000e00540004061101c82c0200d03501d05807004208600a5407402009219246d001c02045901c90300615041075542e03800c0242e540c451141d10750b49840841e4101c585d1420980190001400421550702c28065611327206038240c480b80044008040051007001c44994408 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 122352158 1250 122350908 122350927
    0x11e031d06070809010501050607030903060b0415080a060f051501080712061403010c11030a03020702180c03040201081008031e120a0b03150c1e0d0f0212071707080606 74
    0x80060b00415058540243e6414000d60403401c0d0b54050704110b0203540d0030012580043c1c1e014111100301d03a04100e0005035612840001030140020b6a0036103080b00104a01080001e80450100c0006e4880d1208100558101c50f80380190b41c0111383c00211003019010407000382d400303880130703c5d8042528075001510710300c3c80c0b500d8800c4500300c1e00031425403010789182c810035040034410341c0c000f6402da05168541241546219942e0301c540c0d261a0205500410310700308545411599030002c4004401090b20b0340741c0005104040e0300700305d500b6400102000e01040e0800c140f540c080d410b560f01d40d00650710f040304c24010140c03101c402d051182c50380d4a08100c4003000000c00514603005d9800140302080c000d140404040c500143c9075030342c1c1d5804010700b09001e00c929824080301e2100c0d500f1045103000312000e5403044618040d000144511600340024060b80310059030050102c103110802d110425142d40900306c84402a031501440b40840020215040e43d014100482e48000020203c03441d00d040d02 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 122353408 1250 122352158 122352163
    0xc06070515010f211101030c0905060f030406060e0c03041b03020d050a030f09050307030609050a1b031709010e0904060e030a030f0606020a020a180605060f030901050105011e031d 79
    0x9a01103810504590b105219054000100e01034100c100e500c403202c4884543c845170b81e10956100818107140d56180d850b04100d020705c0d400b074010f001c010000d40d1180a801e0103220144c0c03041314201e42c078510380b81000c13031078216400c0104d00448041e03022504640d215900d824540c1e071999103081048200120000050703a404400c2c070f250300c1c818400380050100034600602880c11922425092140c21541844140c40028106044a400c80780201d420705140c1810783c209290b01e40054441103092600c45c000481c107011240440307200702d0002503a01e0740072b0075000e0340307001c1c1001282c001940000544128070300a0400c80c2c0050040c200058003c0b0f40c0c4004610319441b54031510046612a0035450a041c3da500c21710006045d20f001801100104d9800101100a64014901da05007500140c4d0000740c12076001134041c16001c1c1025555208540d90361500740c004583d000d190390708000011403294810328003080c0b41d02c0c20a4524052203040c2006402401f200c101640d6004a10ba2000c820100304 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 122354658 1250 122353408 122353411
    0x171306020904292421090601060207080a080a051305090106020f071502030708030406060e04080702190303050306150904021602151c020c031b07090c110c06070515 72
    0x614690000e040c450420401c001e0010040c020b1181c40513021010041d0000c68504203540c55032101d15507034149800c20000c40381100450799150342414001c10076420400910207040e5000350b02200c983c0380d43c480d00340b03a4420300094000c00301c00090122849240c0188040d0003021401120401c416459001050b00c5c0d85099102d1001030b8040029104004420720007400503200300000d028203010142d4019580340310340740006100700800000079003480707aa5480200a03200146e40d43d080d03030510b030a00400c660030200b001d9100f1050201185042d003000c480d510101c1c5e60580356181075030f6800042240e0b4038001013542403140c0040040c088955079601c01090104103403030858918401c2c5e80140b000414001909140d400410007800c2c420078010a641c0201e88000131300503a85004d0191068114000c02e0a20003d81400060003494400d010500702c040e503003003c004000025140b0b0080301c04e10360208a00700b4941003100440d0b418280100284201e40c09602210b800b41100030310030400110 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 122355908 1250 122354658 122354681
    0x30d020309010311070519150504080405151e0d020403080708040314031c020307202514040506030304030803040501050105100e102724171306020904 66
    0x2000448000641c0c251180c48810364200035034074100a0705a407080e1fa100380d0304c5121512000381348800d400700b00f403000756800c5c010107100c000c0c007050821785800303030054206014041c400c031350000c03403040801e1b00c59040d00d44e03428031000c00007200004240416079a41c4102d1803280496000c00c40030010804040c010050944030b2424203079254a1803c00d012102041a840100c941041010b00c401303102c440c403c62450499803a00682e0b070f03214040d00707588190140429228035455020b25400c1c002022600307840c050704c10f14080c8000d5240c0032110000d90310a0103101ca4400ba0a00c1c50610350500e503004541c0041d0140c1102e1501d500ca8489d0300c40e58104560480d4103a464100500550031f0405000000c4051401c0542c80c0c2100e980004160741e4602042c00104100f0400380b4055002d5410300d008642c402108085041c0e880e240083c40d52410180c1d08000108074a0035802c00d148600d2803904405401c00c1058025251400401e015800b54641a511540c0a02c11a4103556680c403960070300c2c01 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 122357158 1250 122355908 122355913
    0x140f0f03040302040c08060105070318090509060403030605041b030509102a021204090b0102010609021306031406030604080a09080d0305040b0f091b011701090b090108060106020706050702040b030d02 88
    0x82c5544104800e031a00c0f04a00410003103602c00f030000d5a43c21805a8800d03036814180048043d1040101c110b6003000c69100d402414105002e2107030400c0003040582c00b40d07001343e030b080c40030a488000780025108140500c20440d07110641c4000803500c29070159420201d64010350322222210304075502615090140704c08460f00d8682c003103009040298000d42400c130030780040c00300100c81000150060060f8407450540680301d204100c681d070300c01c0d80007001910200704d04540f1041c00b20341508490400e03009010120349010303240349076000205443d40c82044010000d20641c0d072255600c0c400c0d42c0000756483d080c460030000106440f0f0703040c041d400404c03056030340006052070300c4d04140d00f0308000035094a22100c0040c0038054900d4011941038a00d550722584e01100d0315035100120b41c0004007503883c88542c0348400c0040b88486a0741c120f19405a402c0710681705607600d0700a40b9407142020b102d14005a80030000420a141c01f600c06400440e0005100168040300407003c80d00b4002c01002c07540068 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 122358408 1250 122357158 122357167
    0xd26010311010f02060f0a021c05010b030613050f0402060703020a0804060f08010e10031b0302060301030f050129091902121f1d0c1b0304031109060904140f0f03 71
    0x81d680508414043c15041c40204000d0500002e82256020302911070101140c00141a22490458900703000b8000c200d140104007a43e91011902c1480c0c1082e03410034403d0010800700c07081000700740140c50080350700f10072554040d02c03690f0800211b1783c40401c0c11002d600400e020480031a0b00300010b4001002d49403151140c60751444001800d00a05800045441504005100381c00c1035010014040e40e0303101034654114002c80150300c001da042c0360b2000398090000000803081010940b225848284075100a201c10300e80300c1d40401c603185031204c2004e125107211b4100c052600d0501f21041d007001c0910411a102e030950081141668080034200060403882028000e6054105038416000c4042c4003116000f181082440000100856a0088519124004208008606003c441061590f6854038120101a0003031540740c0c0c20910080c1c1d44001c004d001680c441c10410150351040c807000300610415030713590351000c020078500550111a03114400042404003010040294030760038500055844 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 122359658 1250 122358408 122358443
    0x50d060905060f0a0507090b0a141e0c0c030304180b060904180506090d12050c1303030c0b0601080c042d0602070e061203030117030d0501030606060e0d050d260103 72
    0x1942c4016005400f0080b160f54100f2910300c01005445403105030345424648140703442d0000c80c2c80d00030551542d290bd81030b0542ca0444071000b5000b8241c0d00040001ea6021402c0c201c02c16440c0d01441c40f450020007044c00391010000c6c202c0d40000c01c4c0010003425281020b10000105040f80c1d600560382810819800030301c1d091200c10003821b0740c0310100c08000c20351100c1241d402440820740300350301c00019440300d0105403642c00040c141c400030b000c00700352646480d0b620b04000703000240c100b0003500c6910480f40441c8142d44201d1001d842640e1070f42405240619082d4030400d01603040700c01c080e5142146590301c405072818281c103030062040780d0040c00c9043c14560703940192640503000601c00c15908040c0103510710080309481c11540240540030501001d43c002074154413809000340c4496190000106c208001c5500080c140c48031940d0302076899100c0005e000c100c1403a48400f51165210301035102085208150600040500030207084030171840c4c2c1c1c22000c8a443c00e030012500c009021980c100d0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 122360908 1250 122359658 122359661
    0x50319061121100302061b0111071a010f030203030403080703020c0a090614040203040b07081803070b070e0d0507090b0622060e030313060c1406071101060b0703020304050d060905060f0a 82
    0x2040450120b503e90302c9440c55000402d02d228001110503501c10500310a032507001c081d0f102e001014180119680d44a0151038840781c007025141825a500003c0c50000c00c40c0300d5000c4540c400c1e00d9002d002145020b00b107480d450f5440c1c00c105000c40c21807058001d0409542c80b00c005400041001204c042241c2d814a0b6800144007200d00c3c0b280d01480c4180200400b21381c40046ca075403c0006400d20984644810071442001c0110100035410341c0b00000d90202085501e24141d0b219074220ba079007041c1c2500036000c1008541440602074880e078070182d01401101e01c44d03842840d031580010015450700c102e461075200e080e00388252801140d194180104041500006a48060a8124041c51500c14070705400e9400704000e000712010010500c03041301c1082071500c883d150320a0b041301168010f00c3e1a9400800c054402190488039501700400086c03c2401c0c00281e45041f43e2540185d42064102003d0150794414000c0c10b40e07800d074440d0301c1a40441d206010071406140388400134582c61924566000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 122362158 1250 122360908 122360911
    0xd0c110609010b01080a0c051204030f091a03070e040b03160302040507090302061903020708070b19050108031206040605090c1e03010b0304120e03010c180e01050319061121 76
    0x50300b03905225885010fa030740081200d510003071038800000c04002842c000c6415001780c40c044403045182c14284000e243d0002e4981c55001a02d5444505075a21008003024043c030032589804440b50034004945c0580c050b450f0420f4200c4051700000f946403d800019141417100214a80500008103061082d41814014254040c425040181186181d076010031114406d00f111030400310480a98030020341d201e501110206030b00111083d032504491b0410b4440c682c4296155591101c000c2e80755888200140102030403504a107010b507081502400381560850801401c850b030050f41c030800400c441e620720320910301400305565559110341842c0092440d401c1103012462401d1024001000341d41135140880e87d005900c03464407140302901c217070180c810b0350042d61b04c1b44d89542080b1003c0e800304d43c0f00c00c40e55400342c00301031400b0885a468805031010882070081d1905a0400143c1204501c0030b0080f42d2802d038070500c0c00107101c981408008045421040e1524619952900b4100ca140d0b50300310b19a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 122363408 1250 122362158 122362171
    0x2703020708010209010905060a02012a080708041509050709020c030a09060509030c04090f02100228021809120f03010510050309070618050d060b03150108120f0d0c1106 74
    0x3c41c5800f009800290a00c1c1031480f4803031103844005075070711740140300390080f0740820401016420760010b00d092620080d501310007020001140080041c044a100d030000d14051904030a84001e22010701d0309034000b40c00c4000d0190380c0c070701c200100011040e00c00e100400c50030a4100c080c0d501d134000048010321200c6940e010340104001404900515035010425241d0400101c60018200b901440c00034000d0102240183d0b01420300d00070f500d403560300490b9080c1a880c2000c0d0350201840d00c0820b802100c40b45000103504103940b0300e0102c650182c0359440a8002000e1800c40300710814401403400c080e8000c107840030701c4560120040006003080c22044244038070500b0414210300d0060880e83c0d8401c0244203200c10403000c0b44a0b00107c0800d465800090240900704d4031032580981040005403102d4014079000703125400115940d500c1e0b1140050680320648003400014107910b240c0e503102e40000c083c00c201450100010001f000151107150701c103443e640c4417081c141042074100360030890000d102 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 122364658 1250 122363408 122363411
    0x7110a140c030a03050f0d0b03010c0e01080601031404060b040e0601030c031505220305041802030f01090507020604060c031d0a02010306080102030c0a12060302030a031e0f0c120201270302070801 86
    0x80000f178001d0143d5a25280191500f42c44034003803140c020260452411340341d00355113001c50b03901200b0303841804102070f03000a80f80d044040d03d94900442c11075500700c104601003070484010400140d0150066225400014004141800500300d2103062180c02e0303004450715500040b04008209141d00c01c2821055540400c021500c1d002c011104148551b03614820000d141600d068202750103142503801500000007142103c010050880d002903009684041440342d07801c000040704803050003510b1261940740d0140800f51182c4c4d860b00040c00000c0b1113001495120300b19119584205070201000340c0c2803000034190002d0500000d0121140358010310b801c4e90041041003aa041c50f1811201024440d107843c100c0d500c40c0b90130020041c001500002c0d4075003c0c0ca140a002c0c10340c0b044070810054074a40030385101007040756040e102c40130a441110040b0355075882d80c201055a41c1d8041d00100c0940c0004a0712206d9080910440004026100d80040e101c201520915504102080240450400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 122365908 1250 122364658 122364673
    0x8010c0201090c2d08010b030606040608120a05040305060703060e0603010504120e01021203010b130f150e03010b0310150f05030601120c080a030e1f1707110a140c03 73
    0x282e100424007a07000300d404c01c102c6280321402d502080c2e2008060004200d4456000303607124089903010340b1010816610910811010641170b241a00c544411208003500401e180c80d1492407008542e00f14811090074014188400004201c0038000d075885031182e40d400140003424070385d4112640304041c2c600d50107a80740404000004071a0405984500390360b051000904084400407440c100c2a80c2d8880541040400005400c0b40c6060281428801190680c54010f88a1881606e03450840c8a0103458004040d08215080d02814217a2040d003c082d0000c2040184180424038000c07907586005a00d030ba5a1806600404240054a02818007030351440506850300000a5680806000d0f40d0307003091418a107801005054007400c0020444201501c482d4112400c000d002c0d00c0b0460001030240d4400074802c003117015840044c07040b00c2a151552074440141001800001000904507420710002d22080c0f403000030104030104c0d080c1d100d101780c2c0c0525a800074000303003401c04d0040c155000b6880b110 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 122367158 1250 122365908 122365913
    0x100f05060d1104110c06070905060a0503010b030408072019080c0405070315120218060112090302010213030b06040b180a05100315020c01060e0c0717041d0108010c020109 75
    0x704050003140c1c00240b0824580c0c1076100240052000030f0f1080d4001800190b2514100400b1841030f2140d0000d85403e24256524000c4c403c1030300c107201400001480170001844000a000003130741d082805140c1031030500b034080c0c3d1042e000c00c1ca00103030240c0001810034042014500703800511000803540c40c00701e81d81442c01c24090350300e28140c14a103129035103880024004510a5000044070453303070340d80060060b5104640c0d01158243c0f2000d034014030400705074000c030900300903c0d28041c640c180d443d250200e203580c05550081c94640c02c110704554081103500ca91403581070240d806103004520028a03400c1013000c00c0115140346146a0091040032042410703a00c0000c00c00d680803240d011f0100340e69542520390b03585401560001044014014580c07050303e4065400b038090103c1c124020005541c951040065044007201c1070210514200307c13000c00a5140c1b41100c0031041140b410a05260b2100941442d95075544071401c145062000108084002400740d24611340341400200603138000c0340c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 122368408 1250 122367158 122367169
    0x201020c0a0602070f020604180f0c080f19050907050406090b01050a050d0f050103080a0f02120a0f1101020d02120f01050a120206071a0a0b1f080603031605100f0506 73
    0x98401424196011034403c050000050106030f404c0d0f4000d0003a696140c503410555284080c04907071141c292b26015105461078002e104416440019440b03c0c00c0c281d4916103079003030f10f00006081c203503040e2241c000d01060324401c2c016140140d42100140400c1c03800c001c00c0c0700490700c0f15440314101034101806a021641c20a0071141c0c030085074600f456440101d00b01c0200034041c501c08003c48185848000130500c8901c5018010402e86039650400900c04c0c084102c1c0d0300c007030000701c10720910313010082840150700804111103e150706090442079020781d1402d050032071b04000303da049055000075800848010201015a00000c240c9c080d0b841c55040001152070030b4107a0150b0382c803040054a400c02036565810a9600c0a035220000c008401400041640380351410740303080c0c8800e810300242c00102d20b444964034004c100414000da611500000c0200c0c0d6411001e000c95815010801c410741d040c1015001c07000b801c03400340004201d491400411541202c00d10314460255518007800d009869880c03 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 122369658 1250 122368408 122368423
    0x20d030908160f0e061804030207050f0618040b1311070c08030a0203030c0a0302040801050709150906020a0609020a08030c01090c0e040201020c092d061809030301150c0227070201020c 81
    0x20104e042e00e45566020105100d50307550001c00d001180204100000c0542c00203c203001e03030700107170381d441880141042806901d002d610031200821080070520180d9042980c045058103d004000081d65a00c45500c01d0840f0340481c0252410324002840d40103001e044a52140100b811000861070b1103403076030000792603000140802c8442d07140001c1a24070180b09070143c0c1c010340320f154001c12280c2042c110103024101584035040714400099200241c1e00e020314001002c0b920303e600545800d889070b40da003100804142c80120781c0244038000201d045101040a406513484007000007510961500f410741c19250306501c0201152b440b82c04010060764081400d4484000544510f00c0c140c03100c2503442071b030b0210104d01c00385c540321101c20712035070702e03030b011841400f600054610903840c1c8514501e000c640041140d05604580c001c0004209040c248014584000c00c94a007804220403194005140381d800442c1c484045558520b2400030750b5600e481c600d420000300d0000f1450031545001241d160440d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 122370908 1250 122369658 122369669
    0x4051209040f0606020d030b010302090604031112060403180e060f010f090b18010318021c06020408010c03230601141e0a030c18141c020d030908160f 66
    0x1004500003a55845a0b040031a002c0078604003408200c0d12810001e6507000405910710000341000d086103042c1d40a80300315141070381c1c050b040c3d516050031501d4000031114040f05a030b070851102c00040c814040e040c00700d94041d9210b6910f10000840084201c0c00c1074185400c1404c9640702507080c82856a03400a02e1030300c0349001c2c04e00034241041c0450030b4601d19000c0c4e02c00114940000340145941900c044c55100c8881c00b600e080090a04080080c0d42000010700002e4201854409000500c41d001c28040c0b0040d01c5903c02615060b01d40082508bd030714500c071140040303a01d0310500b518098040c41d445a0b400c8010005440500c2c00c60002001c840300001400500c80700081d01c84038a2031164000c5080c0d016800000703a5034a29420000c1c01040c070b11410000180b440449441c034a2000e550001c2200e051940f036078550030242080103aa0b04000c4010030140781d64030203810040e01c0c1ca504130441c240c000e443d0340440c42e103004030550512542c0c0b401c4041c1804243c4051054040180b0481c06588 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 122372158 1250 122370908 122370943
    0x4060207120201020a020405041202010f1e020f13060507120206060310151d0906090703030e060a0c02040e010c0f020a152309010f0b0a050f091506120612060405 71
    0x41e168001030f0f0529a4583c4080e4120742004200805c0c0405551811034141c00f80d802042180c8020410702c0440e26000044041c20003407a40c1101101e2040d00030748150a000e01120b8606520347c62500000c00e080d601110208030086024400d01500c4203040b00c50400f10f00140c240303807800400007034079080b50341204c5408654800e210b04a400f90302c92814003411300c0b8660000741c032403404c0c0d01001e20300f0211051400c511940c800a01114008110501101c0d4140c880d401e10005030385c01c01c42c0b69000102c400c01085580600840503a41c0c0d40121180e01200c0400064805503a4000821030450045807905543c80b200d58a800503403203451035034030b54003a114000350100d02c0200300342c0c042d90b0a00c4607001c2910810280a0030b0354065110b0204448007140400c0b258511405000d8485900d21907030380e07c44000000740f105400c042c01520f60209000c400040020740e2000042c006820040340d07603142981034810012641000300c0030711003001c6850000c015600e40b568031559200c0300c0c22021030040 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 122373408 1250 122372158 122372189
    0x4051306051009090f060e150109020f1620040510120203010f020309030406030c1e110f0330040503040b0d09050d1d04060608010b0c030408030304030e01080a0204060207 75
    0x185080d0b21600090481a1000e006800541c1411460303003112000595001e498411810b2030200300054404512100c0c40d005c0889030300c0c0c02d80e968000e4101406140c140841000b50841611040040c035003003038071400f000703242c48245401001d26480f4004480d03015034a448180117948901802c024222420064604010311030351000c80d014100d0038170765500c418004401d0003a400f20120240056a8050b5020018040032600c00c032100aa180c040003541860880f80000051041e0040d59114803c1e10448449481c113081440c51640841d5040d410442000705800080800803c85100c103130790711400c0842401e240e10340c540c80e44034610481c0300090340082c500c055451290001d0f01d410780c114003940c0c200a80b101000d03001138900440780c20030401000c1492820b20f0b00e80308040907180ea6541d00481d40c1c1c04c01d44002c5030fa60115206000600c8140400180c2d400300b00010343c41988269070f503088610181001500b0300d0000380c0420384050040c0024009144e0024000e412a4841001c0c000130 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 122374658 1250 122373408 122373421
    0xc020c091501030e01050c04030209090307080904050a140c190206160e2107090e0a110108070c020a0314060702030403050c010f030f0f05061f021b030f1c030b0405130605 75
    0x2050b80340740410b0b1319420a81000200c54208002c2c00c110fa000742c0320740304155904a1095140e04c21184010301d212400d0210910b1820180c1c85260710807021040010450340614107400c44041c100e48021500780c00103030784180220f542e0b5042415041ca40024075544c00e200f02601e41c420a408844410402880c40100d45507131552070080d00810823101001c5000701c8901c1c410348030007581c010071030395500f0450b580c050880d0000e00d0369400350b00400c400207564203240c011102401c01901c07d0042102101102c0007603950b018503400194407681c1400c0380041c0d03640340d144c00c0040080c00101950020712003080030840200c0c2443c0010b50919040c03101c032075445400da0080c81805002031180b40382c502e80100541a90340014050b0504035a80d102c1041c3e8416003580f001480601400141c0107521a200341d4600004151031404000b4140d819000c2c2d40c240091428466035903840400603c806001011074040c815810f0300d02050310144403d16016508805040130518002d141c0c5071780718002000d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 122375908 1250 122374658 122374661
    0x402030106091e230403030b03150c070b0a1b02010902100503040f0615030c08010507020129010804051c0c0b060409080f1308010e070f08030909040318090518010c020c09150103 78
    0x40040c001c0300400c0280c02c0c1707400d00030001c003203504105001c3d1103440740304110b2a240e007607a2841783d054000d02901d031895030354889800280281c405400d00e5103e404d11011100c0134403d040d854080d0341e000058000290041011003000d010303c42007849820000d01c004a02c192201031a603582103070004c20400c80002003010190303110742c0040c0c200c03903c0d002c002c60307608419007060340500110703402407142c1000001c0000c150440d41d400140c65141e005030115441d4012240c00f03038401e02960075682081c3d448903d8841c0031b849407419a0000c0c000702c826008106002c0715181d00400156010064000700740e0701ca445610403101c0c42c2c0069440840c98400300d034030141c1400e011f00310400081c403003c1140000d0310fa50748282c0c0504c9d5903101c0010b2002c6800c0e0000400d0750107a80008109c0100380c2c07110f881c00e4800054040d01c03020b4842c5a00340100d460000c0d0b0003200d00030b4110803010310300ea000e905091350031141201021030442d00600440d94442c2e03500304407603030003010402d40c43d002900700c0030060b030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 122377158 1250 122375908 122375951
    0x2010c1704030602071103010506060901030f0f1a010f17041e05070323190b100306060b09011e0f12021c020301080c01020607020a06270b0402030106091e 68
    0x14602040018044200410f9801800b103c80c8584000c54021483c03d0405090b180200c590b03d800403400d02c003e100c10b43c0303c1d4200143d8000b4501c800100e11081050f8003003510100a0003c400c8254029800d640356480704d0410a2020940f07003050032402d8205001c1c458210140002d05182071804840343e8201d0415801101103900108907444143d9a00c1c00d448042200c2c04011140756201e400001d4030380c008a5134542121111240040d2110170741d5a042840101a280020488495038084002006441460080c04415003019200c1c80742c01e000410340c100d0355044402083d0040003140a06030814010586e10341c15040042844440081c0030000307015000c001540c119600001d0600c018039a401103069410f0307102074803080200380700160f903240b0b001d0f600400141d000c504400082241503001c5125814003802040541054210382c40e40038001100594100c0c03170300420f120451070244904401410680001d01156041e9000e4a004410701d0070880e0805480c0c0c214101c07480001e08150 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 122378408 1250 122377158 122377193
    0x1806070c05061b0606010903020a0e07210509010b1c12021c031401081203070503040807080309011d01050702030403080d020c010c0c05010507020606060f0a18060c110d02090402010c 80
    0x2103443d100300300f001c083c100c0368885807410f05019190200c0c0d203551084003e6070640e50041c200320700c0141740c02c030945200c034402000403003007100704100a400010095047c0280b206c1c0300c28040b074182081c00c00706007181c44061a0520407080e98540e681952280750300e17070703c070260844616000180c01000990030402c518005240c102c00c45125180c0864040d8032040d844d00c0501c1480c071290381c94242142d51040302e58500d40b81c00000f0300c00125150300c40e900640d0f02c548950100741c00e0185595403c4140d40081c1d8a910141e519944603118061242101108000c3c0c3d01000b4007142c1000c9201940324440d500000c0c3c12b000f4000b5a00b10200c100703404641c06031942c08000c1002c0e600002000305441070351310b01242c2d103508003c0030400141c80014428003522008010600c1c4c550b800b00310b903040c0d0b0702c01c013201c805002d200070149415801104e6000018130640d00e48800c8004686000300c0000029031121380b117811421008005601d400103490b0b80568203003040c004000c0c103400c00d1040b140c60b95030340 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 122379658 1250 122378408 122378419
    0x1f030209040638030f060d170304080901030e120f130320090907030c1206090c08070f050402030f010e040507150e011b0b070305070e0306091608031806070c05 70
    0x41c28001120203025032490b85903d40030246000b40b103030340d00e0030780c1c4010781d65480b80c051a031000c07800c5864040950342005100300001c0d850441541a446525001114240c0c0c000f180821b403d41e00356014010307400e04266220180061681900c404540740c020490400c030008000300b4194020640803504a018503000030100440001503250400f056006540b4203000b200000301183c8100000111403041d00c0e44204804843c03818079002030700c0c0040742d050035650661940c140310007103000c6047e841c0240c0b80300c0010700303480c5013001e0660024100a6000b00c0c0218410020422900c40c40d0404ea415149001507003415510707141003481c40e04010f50800030702009450400b440d00ca400010540c0100000e07241c0e103441c0a485032025040c1c1d1a4010003620407082e00c000034400601c0f80e403200751b100d451820940191407100001c40e18080040755103000603441b02c414085440301c080409001031086000a61034120700e000e64410799002c51125902584020800b0403c00041c6d2020030b000d402e01402c07 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 122380908 1250 122379658 122379689
    0x21230717060f031c020d05030108060a05131a040c05060f12040201140d02030613060e0609090313030c0306050c040b04140d0b0703050a0615050f090a0806090601030506061f0302090406 81
    0x1c06911111201e200c0707000d0b1240031610413416011f00305881c101d411240145c8960340d2000e44070700107050020140f030300201040d03072503400240c04079054500e0340900105003561803400d4580031700004a07607080144681c0d8113000d1142c05910100444030341e0130003007001a0040d01c0da07200503126400905040b0040403000b140308000b160065010314801c0b6030460b00e814001141070950f00844d20f550042c0c00f1040d040800043e914140244215005102c0c401224a80302e09003401c6031945045401c12a050100d0050810521400d070003031035044900c180c0c03881d01e02458400100b0b080c0c4154450b0201043d0040b48200301a550802d41d0000c1580041908110b403500c0c48000740204400c491030b001c442c3c6031030004a140d10700840824880300841d260345141c0303012410000c000d900301c640300030740c003003060800440c1e1950180310aa000d442468024030041d4103610b0258100700d00102002c0c0a081072035032941d510310620f80310380c0c441010350070010b0307035001180007050290810341c1005c102402807a0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 122382158 1250 122380908 122380933
    0x30f0408030a0912030e011b12020a0b0f10050d050708031303050f0604020f01031503200306090c0105041206020c070807090c080402061921230717060f03 68
    0x100401d44030b42240c1d00e18a4041e2600c10840200d0410100540003480080c101030349940900c0011101800c6070103c000004134681d034640c403400144c0e440000580003080d503d020003c0740200907811070f030300300d8154070700b840c02c041e203220307406c2c80d902ca410320980d1209007910a021f010701800c1d0151080e941502d035900d0341940c04c20303003d1005200c120380d2031040003100f808000000c14414002d0398001d29012560404000442c06492801e025158036251024000b000032080079106003003000c009a10889540304008050800d6402007190703550750850310265010340c1c1d214044406455264086143c40c00c40341c2000d10007805600c1c0c1c61000c03882403510110f496640062950100c400d00d803020312407020303640021034020384c003520020740050301405100c1c11101c80450580034140039140220070200162014000b49507101d0030b03180803d0b0b440d0a8034006102803044c0820b4078841c200305028034100030100a000c48000000f40c010091000081040d40e5220780b000f007010390000b01126451b21094 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 122383408 1250 122382158 122382163
    0x50c0f04140a08010917030603030904050a0b19060f120605030d11060108121b2a0901050d020906101b08031006030c0f050d110c03030a0507050315040b03030f0408 72
    0x1da10345481407044140004241105028280e9429442103044a03503803000c429008540d00017400c043d80c9400140b00c90300d00390301c0f98401c0c3ca10960381264082021820001072202c2060410b120141c0b40b604000144001178020504c40581643d510340180c42865042e45040280803503000039038517008800908072034a90100e103030f0881019281c1541c1d0143d98a146813580c0c0d420100c4422030019082c04036034901420032006000310100403003a0794901b010000e11280d0725003801000d4a09080c0c001401d45207040440e15140544020384a4180c450f4044e000600c240d000200b04e43c3c0f00d031002c0c13120251614810004200021034401064001e00e07410310b480c440c01e4004a51010b6900d842120005440c0d2084c051302c0000f8010761500055841c08030403c0703519a000c0022640c91a4407061120280c4511034018001134401d41c02440e100d041c0a1003050940320050401c100b040414004d21200f100302405022001408039400681070380d1480201c0d06502035081d41042402e001301f000580002c01 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 122384658 1250 122383408 122383439
    0x360809150a050306030f0f15040510060f1d0103020a050f240a020c0406030b010b030c1309060e09010606081f0e0a050108150c040303030b0609040914010606031b03050c0f04 76
    0x807000c3e1b0710010350690176079607160110074402040b0760080040405c109071485505401500840c10b542541001d0404002038441c158010711007008c04580030855441d245003802c250048404200b00c49500d940c0008000d00064001c0603c03501040d0202d81269480150101c00301813100b984041d02c400400c0c10324581d8000d51a00d0016000381048007007e46454402c5109a07948420650306690820059616030742006140b0100380310100b22110b40c0c0c0d0303803209d4200002e25280c1d401007802ca043c0a11052081005000a05030742c4c10440240405030300a0807407544a4070650f0b24581c218403074403840b02007640d640d0122051500c00310500080214580000c1d060301e490104490705a1f070701d0704a1b800307603039000c491009404006100c24000203210380c000e6100007000602080c20310004100280442e0111401141c4031444020741034600f210070b01492000305643c2c00d0401c100b4200ca0103041d81c984000760b440b002c0540e1800091144400300d030640d410000343d40b0304903031900e8a812500500451 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 122385908 1250 122384658 122384671
    0xf0c1210090b12030a141608030117010e0a020f010e06030a0e0f0a0b0703090204061503050a05010b0c1b030a0f050304050301060b0c0d030917070501360809150a0503 73
    0x10318403202e446082c02550407903080c1c070540007140752001e04142111a2166448040e060280801040745082c030642d0b111a1864012481650380b5450040010b8500842c05403450499042006108000e071000c9079002e2615010344040d0101c07400000126101c01000c040940e00c03a42c0413090283c00e0034980d201c1c155150342c45048880074201094071070b40d20210110000c01040041e000601030742d22a4004140c100d101800210740c09032640403802804e5030300c00c000000241d45904009283c16180a002d00404200a80b6072504603840d6840782c0301c0000c2d51543d580740c20103040079001610100300c8000c03803941000e01e1840a000b58075010391664020701c5241c2c480c1d801c00001103a1441401c0440741d8150303284008004e1300702e110405802802240740c069942c51000f0301d1000410001d02c00405603503109200010384804d184001040803820b90311044400d03110305029003203183ca1640d002c48203d4003c0001515400104001131520741210f03000c1c445013a0110342c0c81103e0f03800202a602924 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 122387158 1250 122385908 122385911
    0x303190507021003061512091202010911100f180503030c0708010c050a0c021309120203041a04080304171207060e0c0d0804090b060c0d081614030f0c121009 69
    0x110f00004600741c40c0e09005595810607110340d9400118001c0003451032080341c0310008200c2e041c19840d09440b440038801d00c0c80142c0d44801140c020429001840c0d4480c1030116002003141006c5580100b012941803409418006001d01000c5810200d0b1595401403034000d0843e40d9920360441080c2d00c035409803240b08003941c00c201640c120301d40207070306a805134503641d40d503002d400d4403d80030440c0a0424171400d2030b1580e81d4034500004101840c942107083c5286400540c2d0300c82c581504c4d040d160805203007050041c6001c1c40280b207140404000c881c101c400000b18183e64904101446003030800080e616002c07001c001500604015040c0c110001c0840407409450483c11b035107050104d40c582c902d00040c501a400c100c1070040c00b80c030340c0c00300003000b1018000e00e040a1401d401030b40b516026402c08400320f6040002c20482400405914850b04080d14000135a001c01c0e4130b1141c3c2502001e004105104601d40006400b84c8051f0182d4440048216220b911800c0010f06400441d074103001c1c0510b42c0b0b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 122388408 1250 122387158 122387179
    0x5010b030a050d121a0f18040305130501050403021c030207080708100b030c0112111605010605090105031605040c12090b010807090c08150105040f080304060f0903020102060f06030319050702 84
    0x402d00c030720840c01010000400241428491170411100410444201d80d00c450305040201280000314820791049120fa1500750340c03103110100c18081c100540c1d20060400c50104014801170315400e240100303a0001d045400d4107240189020303818060142c014000700d119203100007038008000144c44400554041003003180240d01428151a000084000c41c042550a10b8000342801035078000118000b01d44038107400c0800c28044882585403007031080c0e07660b039101d810031712203454102e020f10300400d022030003000075049140d18440815a079100303143c803a40d83c4400c0ea909150145220703980a4000d62001c100740c03c03a07841d100c401050203000d41d0a01d0701c030f0070801045006a034468280c40c038010703454100e1550399400005003005221202c040c10000284800500703885004021000382a180015544550601c0b100401c0010196007402c1003040d602009c20160b40c000c030740e0b2504251803110210090340c418010070301d58802c0c0140e0f0540b0102000385512101d500c81d01402c1c2491003110250048c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 122389658 1250 122388408 122388437
    0x140a0303022101320a060207170a020108130f0b16230d02090a0f060906020d080f011403010b0603070c0308011e05010c0512040b0406030b090106120905010b030a050d 73
    0x1240e003400b0301c081c0c4c0c4c19030380c0210f00aa44186400280703411450b1140c0340e000c1c90100440e00d45040e0381c0c8500f000d68844a01401100f030b103468a4505807240714010100510300d90002004a60003829030b04a2020107991002807000400c04182c1103500b01e00b0403070160500540141c000004072001000007a05504282428013104002e42c1c0758400c010031260030203c5249568000350b10040342d06600650300e034070000303030b1305910406080144040d450f015200e510b0258068100f0b500d2189080c10400c035038042000200d00c004415040d60100d408002c804000300c408a4014002c041c80700e640408040304100c0c607564040e0300300c1c0380c5270710aa5682c440da9981d100d1842a2820001e01440c489034000028400c07035101d4004640c03c43d00503c11a9000d642c0e400030142c481d805900041d18668000030184462174060180c01211041543d00010303541c54020020003121185465443d540e45a8440600b4410250040724035501c0090581d0000800703131410a50343c400010206005c1082e000001b40c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 122390908 1250 122389658 122389717
    0x41a060102060402091f030b07050a02120703020a030f200606130b0612040318090b040501050d0b040605100e01080106050301050f01080a020f0a0e07120e030f09060304140a030302 79
    0x1d16130140111450382c88446446181e48001c90010958108011000001c51690b4441c42d000b01c41a8075119900c4002910003400e02000c210402085c4004100c2c00c00040e03400105c11a085815242100407130210a400303d450b0910099010440704400007140d1901d240490703000d0042c8804c50b1400781c02901805600d05231030070240f01c1603200d101403114840400030160001e0740705100b49080e0700000c003a5104445585070360b07040242034540c0c44010010500b082c4c404c0902414003200d01440d03403105640d034012034500c020802402140c4a1001c20603004113070500d130028061401d0655015a11600414000c100350f10496100350f0a00b004285c100070411511030594070745c0130240090000f55000d00c400c00850084050b045031803040001640c91161190341e004404075a0740c035425981e241c001009550a10002d460181c00c1044a040c3d41c9034a041140c08005041d9280c685030b50769400c01c580e480e45110b00d00d13000d030b0045c46807410800d036040d4014000312030189041c89030905d201c25500ac = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 122392158 1250 122390908 122390911
    0x10050a090c17060105070203060403030504020108060904050a030f09080a110a060c0c090b01120911010215151c0804080d0801090b15030402030a02150d142a12041a06010206 76
    0xc02007001440d07107110714803040000b03642c00f81041c188a40752007001d501183c6440c00866064002a81c0ca0080c042190380c84448160000c1040b0ba0300300f60350500d03450301500e079404643c0050512040c2790f40c0d0070145001c0c0c004107000309219001d8440c0f038a010708140384034000501d40a44107240c1e21102040c018000e2185201494000f503c00c00c1c05824210080f00400b110109941072091840c007550f003c514901800c61524482c540c2005c4119020001a180102030700b213010703441c0c1c94102000340440c0100200d810105044880b050f203044041910b6200c807180a4020301700b4100020013099801d4002040c03503084078030396201807007681e941207010201c4118402855001140790420b091520380381000d550030030300080550f07101c01c2c1ca032360004400c2c00c201048145800c07400f0940350382c201001d1250f00d00303a24810b080324500c2c0c5480281c0c81c89444061030b4400c0c080070b1804608a041006405483c103c40c0031082141e01030516041c50903c901e2000480740380210200005850b552005c03510300d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 122393408 1250 122392158 122392181
    0x114061807140a030c11070803070b0c13030f060c080601120c0905040203070207060915020a0210031d071511060103022101141603090b0402040b0d0206181002160b0f040e10050a09 79
    0x110708100650f6151800c000001d4070713389014009002010080174100c1c50140103500c903960002e240001890094281c0d11450000c60500801904120f004c0e42c0040007007045400c490300c00a00c1c41d422100554060038150000c40d0000c0c1301204008101c0d800080c4d000680352151611101c8981d940071082c181c1462588010044e000244042e0042c200071100088811a504010400b00c444030b81001c11071030340c014140340e260300902041110844404070514038031698500001d00b00180010385542c0c0034184002405024100d034910240c08000300c100141c81c3c0346400138420f0b281008602c18550707a056038484e800501c0b030200d210101d4040d118281026501802d405096a1503408000003008030401d0250001c9c0791600840040c1e032407074010441c3e00f000820700a04030390004c0601100c46001840a0103542c00382d1804070740a4103000d0703c04200c5a200161554a11222292b00064000d1354841c050a000040500c81c920701e1082c40c0f90301307941054800d00c1d015599006080250b51941d00b04 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 122394658 1250 122393408 122393413
    0x501090e01080a110d0f15200403080d110a020109021003020705060720070b130909020303070b07030b0a0e091002040b04120c0308030c0c0114061807140a030c110708 73
    0x601000a044019041904400500b1002100a11b0b280c000010503801001c13a0011505c2a1580300f42da5a44102c103104078601c0340d108140281d45201c29420301c1a4003001d0040f0341c020030566142c03107050b00400c01c01c00b40500280d40303400c5c0303186010b800707020f03d005e0880c4a00f1160f40600241c44c0b00f8801d41e414140c106004010340d46411a0698617174502d0311034650200d00010400707070b01020400690f0010b1880201c800da956400707500018032482c032600800001400d000d400d078056a4008251030885c2d81003d00c0c0522502c071071318182c000f0700c00c007920baa40100103440300050104960b00224403030a0f100c4c4c15504808040703600070040703218500486584060a020905c401d100800d030303c0007003610031054200344030b44a844080080e081124600070304040020a0008030100b03020b480d5143e148440c0d4404907007407490003d01d40c110800801c03852070200b203000a208512584215900010040c00e81d6610342c2c80980090150584090100c045141e03001c0044040d01c00080810032a0740f440c0c00f = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 122395908 1250 122394658 122394673
    0x708060f060a0e01090e07021e010e0303040305160f0b060111011b0e1201021b1002040305070e0606120703050a06051806040207051507020718090309050f060d02070c0501090e0108 79
    0x7603e10314440300d21641000700411010400103000c1840c1802405d840c0c004190880d200807184800e00484540300b20b003a410f080e580103419100000b40d90304a54903051240c0c81e02460540200f14080340301001c0e01d01003802d4603100074040e00106141c080c4400303998800039000016861401d0b00d218808e800414420700036480545445690143e00c169001450b01c03c0e40805030700c3d443c3c2642c110200f1824804428000c050305440e0800004036080b10080040d07050614548500e602d8800e0745c418202c1409034000040e20650b2000c08032011408140f61504080c01c01200040082208884540e170039817825001065524252001015a014442581903540e403104248406500501c1c0d0864192060404030281200341c03034012840350400303500500c41503180c00300e0609508031400019200c203140141e00030201b03512580610580740e040c0c07410cda948420700041516032040350101c54a9520204421040156026465040303035400d80c1d0b10740255454214810840ba0f0a10601541d07a01c001d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 122397158 1250 122395908 122395927
    0x81e0103021e0315070e010807210f05130213091e030203040e07050c0d0806030c0d0c05030307080306040b0901081009051507030c0807030606091a1b060708060f06 72
    0x2045241c102e0112940391214800304010900d4440080003070212403480500304441c8a9000c0b002c00000c210074600101641010328014150070480000b000b04c800354007440ca238568a10b07812a00b1003e442c514100040d14181d010b43c1400319080c00101c0c410b42c0c035002202c2c104002030040c064003030b0700241007200d00c000020b480c02c0b00d00805901141507000620000030a40350118003948030b072080ea15020359409411035105c0c1003103d0300c0400020b101c041404e001c0161400201200c204c00240c5800c0e0605c80141070500000446030310150b814400082c5080c2000706c940080c40c042e090940c9c003403043c0c3c1c291030100b03e940300027405004002c0e03101518200c0000101c0e041070034200d01031300640e03c2c0884a8040100721076002c4584034003094a03101c2c82a1020ba02c05485544074174180307400c101941c100311006240240754854803540c0d003500305170302d504c5250101c12070318a0040ca4009246c050031f02a00103491300c40841d1398402080840b0300003001410a003003404045030b07005000d0ba14007018070 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 122398408 1250 122397158 122397169
    0x106030c1805011403180a08030103050105060418020603040c080f010209130b1014090402030406020c10060b1902030c03030720070f0509090109020d060b040c050c0d0509010507060f020307081e010302 88
    0xd041d5105004c500000b0400392030184100407c0c54000e08000b6030740d6065040c60b42c00d445014040d0b83c0038500c1c02d00258902e5810b440110702403641240c2580d07482c0c4503420802040a44c0e5017108030345020301c00b001e1b928a04150300406a218007903a12035883c040490305a0212140a0b20150b000100511502a003e126803501100751900002c040e0030104c85030045405c0360411541210340caa40010448070701c010400040001d80720051050014070b0801322001c80500400c0340311a10f0f0004030343c00c611142c2c02482aa481c0b480240d040304e480c0c0c600385074000d14001842201051042c403111206401d04400301e03d1400b518200c0702003016442c40c1506100c50038034005d0060000355600c000c10801642e45040822025004901c049078003004030b02000101e40500140b9424447c0c02c0040c554003180c0821409003001c800d051036500c6945540040c0c0319841103c400a01d0213107420f0f0500036140070f940c06507015144581c2d4481299030344d030380640c1500c824840d00014540c2000700410061501 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 122399658 1250 122398408 122398411
    0x1706010e0601090b07030206010611060402031c02030412050c010908120319091208041205071a040507030203070603021201050907022505040e07080d05030708040b090c090106030c1805011403 84
    0x42c941000c0c00340d1341d000101d1468020342c1c0c2c01c40041c0c00c10340042284607800480417013001d10800180c5807a041a03030009548490b1360a40148150300c600341402a5030090094a0081c40344a607008500d2481d8500251503c420365100c0340130649aa034081240300d40000d0401007482164030507861a00c07080c10b541d95241c0c00340311014907180c5441050f00000c01c4680c000c0c0e034002507610381090f903003401e1500810802c4122107130000c2003400d020680100b80020b648401500304000074000b95116405d2503424140751b500040d400d0301c180c250004440b0391581c002c1c0201032001d0200341081e40c0700c43c2000881703135007580e24400590050a060f500b2545c09114442071030403c40c03500032071540d41e4021034181c1d1007001c11a28aa00440c5041006030024040d5a4581805280075481e5140c111400781442d00060000752940d0611400038502c01c0c010003103c1c00c1d04100418582c155a95120010041d041314890a03002a81c10a8040b507038040c29000c802c1500c40584030f81106d0000c111000e03166410 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 122400908 1250 122399658 122399671
    0x30b10050903070b0c120a020c0102100e1207060f020f070605060d080324102a03080f07030603050102030c091207240c060615172701020903160f1706010e 68
    0xb49140880400d400da06c028448155036401401c40d8501040019051817040328840c00f505080c001000f20049021410707680c02400c1d251059141c18050810710014042500301d42100c52000450103900070801c4003408405104034810f01150b0389181c20700c64007692122005141c0c0806102043c42d4036908081039170f000c003075070034a0a500500d120005a03d01481c00b03841012400402d0405504d042000460005225801842c2d41030141035900400021006041103004d20314240491003043c402c1e00650000d580100080d5200c5c201b1140b100501c1d4418800b4030710502e000b488910961202003070351000c507500000400f214549500c4c80c814102048003c4a0410180b091604000f401900c11032010f00342c450b1601d039000520120241484d040400e10b0303440326096100b0030a11070840e0341258166060620a0780c00d12030541a518060701a12400c80c2d03050041502100103502c007a02204210b50b07540c40556200c0d640c8140c4584840c2d03400c00c50a00d0354015a0050120008005031581c1000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 122402158 1250 122400908 122400913
    0xb040e0a09140106060e04150506070f020a0b0f0310060c031d0f0a120b060603040c0902090f061c0f0903080114030a05030d0e07050f0d02040b04060803040303030b10050903070b0c 79
    0x40080034041c3c00c54005420003804901c1400d00351005d030610b4442d49a00307101d031001c11100320341070000041107400750071801812140d03591022411174550800540040c1102144a91204001624922241c000701c40885400882800009000d40700c0c0099604c120f80586644000c48843c0b81011449602c07440d2498000c2d2047c0c0c480009900c803840d007000103220388021454a582d56203800300038514060411481410180203100200700442505001c440900100694601c00e42012408620716609003950107640401c45203a000500300e202d0350a040d140404100b40035004095000312030740100041d002502210060104401c1185181c03040d2000404807030340c7d10300c90740c2c07040e2941c0c4c054001e40d0005c584030300d11021501800c211400241c8421501c101c904000302000c01c6143d6680d50010b4408d0b5100c2969003511f40360343e800030b4090410001665074454481c18042c0c0904141c20015002e02d48009403001410b1181e000c0da0740c84480100540001c0e0300e81a950401034201010100190 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 122403408 1250 122402158 122402183
    0x1204031101110c03190c080a210f0207060606090f0e09031b0a031e080c031008030406020706080a0b090609150603100e0a050103080d020f040b160c0b040e0a09 70
    0x440b044041c2580510035030081d5034400d2450104021107652415003018406049484800180c94205984070000c01d440c111895910080d10f03c11000341d00c2c80001c160a00c3c000c1c0e0300b846202150005d1007101d024410034825641d0f42c0e08200c2c1c0c4c40c2414850034550707010513101400a8001541c1154112902c041103d09000c0d644100c1c204803011520030100c0c0e640304907010b10070150490003811380400d1303600219400c01101d840240144100034080408880d000002402408041c90880050901d400860303440302d466100c0a0b50341d684c54086c68011a030f0150000750110843e0198102100d0064100d215a89844081c0046080040e0440341c1d13400b0700f04000e0801c0e4139181d020758031600c840d4070500d4000d89040403d0344c6991020b0001c2070203504040060000c0f41044040320369090000b20b00681d07614404108000c0340c06142c0002c6901840043c0c581d80110000c1d410803907031070040b080d80198569883c01e044a0380706a1013005500381113640010744030b40c1203503c0700c00d500c0d006012501d0711 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 122404658 1250 122403408 122403431
    0x2030319090602130807060806180901090f030206100e1b0913180b1305280507032d051f020d090302060a0b04180b0703090804090506151204031101 65
    0x1030b41c1107584c0d0f0110301c6090070320400c8030440421561000704241c2c00c1c01485802c095001c100d01007080150003803282200c1c000301b8030800007540010f00c40c0e5040500c042e045080c3d4a0025115441070718880d51004200f100481e400e400d410f0041c0c081d01c172500400702d20220040185000b500b0201d20590f0098580301c008074010381502841d06580342503142c03195202054038200c0801030010340034204401802018000041001460002080e161030401d101c0c42c4800380d00b20666020000014124000c02000000f00445151943d80b0003074a9150240c3d5440c0f20340d1580001c40e44503a02410035406003075004503885e45403480e0300b8210b200001c051b1409022000c0341c000c0c0c840003807003100164002001c000454140e031140c00d002000c1280e00303024004090390071603004070300d841001d00713450420000303e64468007d41c400700d19a80d0002c119512030b42d86141010085c40b045503410b00410b240000e0030303070314040034003150a40d0104a401c00d040e900c8a85007201c0300d507407858815801d50740e41d109171446d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 122405908 1250 122404658 122404661
    0x1c110102241e040f03021c0c15020c0a030203030405120304020a031407091b030c0503090a0605150a03050a030e09010303141602060319230412030603120c02031c020303190906 77
    0xc90f50060584da1080e407414034000b480d14049441c0d0400190850800314000c60380030180e600c0c003e0f001103d0108204030200e500f402807180031302c01c41032803017001005810160080040c41c03203980a9030607140348070344180c0b924a8501c0103c50013036000085200500c002840b150600b61003c0e100811a00403544401131481290a007100081418202c02c20031010f035581406408100d2505182142c11070401d0440c45a981d03a00030b0700140f10350344400000c2c595280b10b410502c1e011710b000f0300080380a692801d00585030002140300b0f0740010f8482c200d112103406c0800c00541203039819940c41c1e90028015010000503004406121600d02400d4014005a542c14001e14020901b005d80d4242c49a0640c0000c4111000381302c40c1207108085100105052010680c41580541c22284103000414040d10480042540c1d800090029050182c603046041e440302030b544405100390f00712606000c5015101880f8440503d2420059004100251010f0345180e000303c503050303800c000441c5101e06991401c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 122407158 1250 122405908 122405911
    0xc150a09030c03060207120c1104020901050d02030c0406090e04030f0309141204080d030902100806010c05030a0f1713031103041d06010f050f0412111c110102241e 72
    0xc0e84c0d2500407031390380103004408000821500c0e440c10300724039280e6141e548001c4c11214050143c4595800301b85c0708000d074018130881d4240d11141700119640e01d03003402c00c032007160050300070302002400008020130442041580c05015036051b40311201c2d44240a0700481c0517040c0c0790030031904100091450800190100040043c1484035035442d500c650074504210320f400320b4034417028101420b000030400540c0302c0303804050071500c0f07034585541641d072802d00681d0b01e00c1103454010214440040c490500713a82c41a0703200f80760b070800e66944003d1f00c0781c41041100302c001620001303e0070307101845000c00a0f000d005440010780c0010280d80c2002d03640c00000013103031444503040078a4000c1808003c000d6901a050700f00e40d001340d003441c03400c055000e480c104441c02203000c1c2e00e03807481000c2801c00600044074202c03041c02c4401440303003000341c0c01e07106450303602d2042110403110807180940181c2c0320360010030342c0103c140010000107005190040880148503014026010020b1454a5a00d807004040c040c2c6 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 122408408 1250 122407158 122407163
    0x40504020a2d0f0906120203060a0f030b04020f060c0d03051b040f081509060c090a180b010909051e130203010e030a020d021507030f0b04050112050f0c150a09030c03 73
    0x4040c441d07a001c003d44050303e055240070801a04102c10302820380c2042020707814400316180181c0701d0fa110404a580d940d19070300030000c00303400004000704000e80550580d00c40e500c00e490700303441041c0880900020b40540004203400350000080051107078801d502c40c030303807150b450f0031342c01c07403400032032061000980c4260130120520480220078407035200100b01d201c0000c030807490200442d18049001c2c941381c10000c2c041000d5004005503c10040e40d40c01880401703403551042980f85500c031300003a00300400c00e111031940492151040041e80002d03d200c0d1901c20f485045405d1904516000c008400d004001c0417040c0c5041c6515000015840c02d03c50f5042d840101ca00030355403084c166001030b14005c0c8450901f81150b100c1c202c110845048110740c80c1d0400c22904002c20030590001c40c0001a20400356159001340c40c241c000500340584054001c861401101076580752000303400e00c01d4031140022021600060700000c880d4202d1180d500400403003130545040d104054483ea51703091070001d50b9105 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 122409658 1250 122408408 122408477
    0x20f0613080c0f010f081513050105120c0906061c0501030b0702060c030105010c0201080c071403090f030304080303071b0605070f0806010c0f030503340206010b0f040504020a 77
    0x1d00c00390100700107440c00d5480c112594599034614000007010140c0701941c980030046841e010900418008494a08134000100103280c40b0749648a2000100700911130386102d035480c0a4007640c1e4400100e9240e0f103850000e0000d44d49640c80d10103002c0d1961040c1c4031402c030380041d6a00a54005c2036486041c2c040c40c0701d0300480440e414a290028545880600741140c86071041004003c50ba800860400382c5940c20b0074246025a610801000d10380a81d200240c180c0d03a200307561503402740011000b08100300080340c150f0703005040030b0b05060b0340340520300a4003400d074802c0010648050048500e8085169401d5031402c150005a89401c00d980c002d59441010034044115159034a0700440d989034030503004c3c0b800060150403512209080ca900d48000340c01d0060000102c0d81c1c03020805071060310b04225000e00e100c0441d210745200319040e480c01c82c2d08011300428001140342d8075414101c407400c400440d103030b5082a0a05d01000300a50100e007040c001d01c100b60200c141c9900149203400050b04400030b4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 122410908 1250 122409658 122409697
    0x18010e0303070e090f040303090812150108010618051201090c12151b03090303020415080f01080114071103120a0b0a0501030b0102030708070609140706030c0201020a0903030c020f06 80
    0x14091034081540144604c10240820201c5a9480711955020760946004600b94140c0c2c100318569118090f02060700d03004041c10001c2d00d24850100c1141c8020a0ba034405950707907206000c40303c1c2050400022040540050308015901c0c0c4000200c07161034004c000040ea18800d5034950300ea040042d0705c80702d280712495003000280030304c00e00a103107489440c00342440400120340e003403030600782d680a080c41407550340c04400c801c5c92311030383c1550040c000745000840c20405d0650041c003d04c00449480a5480e20038001143c9a0018055016184ad51100042240d10303195420b81d44401007a008034118030081c401d10f0340c2e503100d0081c0719008080c00d0f000003410b031940380203002c802000c0c0e8008505240c2041050616039078008120303400c85800485040d01d446541c03400c03401601118001414002d0300d1582e1186403070000c1030300380c100c403210f40701041b100c404440180d00341d002e00010702000c5030104da000c00220340103040000c8010300c01004044070701d07440740c0062800d400448180310142044503 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 122412158 1250 122410908 122410921
    0x10110c0d0b0f07020313031b17030c1e120a050f03010e0108100e031606110f12010e090c010c030e030f0124030804140604030b07020102190c0c0e18010e0303 69
    0x40e501c40d00101c240c40918900304900c0b000040c400c03803e00c802018880c0102a4005040c00d480c13105000d40550200e000c0c0027403020201c250b807038004400c800180e010790b40c2d00011004207280d8070001c01d1001c1010345030850210041c3c068581000c0310240030311004000d110ba240400800460203014a00010081d6505041e20705150045c102d41d0046854648403444080000000948080c03802144100d0401d402d02c3c9403d101a14130524500407120340400c9200c4403e0041c00549000c415206014800760303070b111011180101c096460080d10b030803410580750786502c919a6425410700a06003403401428000100313192120000400545940d03c1c014551801090402007644401002c403901c0094116203612506102c0c61255101c540380c030841d113001a0f10b0300800e840003917400003000f56107072410940180c040e500221a5900c8040501c890805041c084c204445040703402494400040c1d0620f407660403081d030701174043d2034071446801c08044161400d0003110b58070600c50010b1612802d210 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 122413408 1250 122412158 122412181
    0x9180b10031434030605100915060e06070201030e1606030606050c0601090e0c030a0c030506010f0b19090f0b120903030405031215040609140903030610110c0d0b 71
    0x40d440e421070b5400034080c1d01c00715441e140202695200802e9403031260b40c1d80201e0398444600390303800108010309000c10000c1c441c040340120000c40350505018003006a88000c2c08101c20964060000820340003140b150044c1000b17400f03094200e106046c0002d17404144404545812120702c0709a0f561201e8007020b110f0a6418081c203001486d950404c28108844d0803142610351205004501580d0350352642011494410400210000e1021b8192540745601c1d062440c0b0b40391031800305540074814440009a122071800c2480101c412058140f400c140c03504000380c1c0d01514003c2e40c3c1d400c1201c2c00b000452808550308201c0000d000d110521396503200c1400040350190350041841c00541c00a104100c0440d20200407203004602d035100c090340c156103101408650a2050403443d41103468003d002c110541154042300300f5141d289190503403070743d4040710300d5901e1100300e4000b500600001c00c0c0444490007004103050b02c00040301580c05551802c40800c3c003075511040299540d200f00300038070110a004c3d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 122414658 1250 122413408 122413433
    0x6022d07120908151f0e0103110108010501051606060b03010b46120f0c0e030a110f01020102090d12080705030408310303051e0306030709180b1003 65
    0x50600a203180c0c9441910360300c07000d4204c80b8107118110030001a40403661034540850450448500f03242c01071300c596041c001d2840900044401d8190000b1b40611507000b05825070484005030350780b40c5844d00700341e0450301c05185000211100ea864420225a40c0d00c000040c6000c1d08089116507103d0032610b03c1020082c446450580d4a00341c4426901101905000da02c170941c1044454101004560101180c100c585c081e03088012515210421018054070380005a00c44100d41c0c0c0e11600d85400801c05442d07194101d030003040783d08044080e54442c10304030360400c1600c505000050410040d01c004c1810041c084e04101c030494484881c43c140203030024000c079001122450091f00b1460160340704007861041d84010511408411460508402c840b01c855040c10a1300419000d00c41d520f15000e02290000b204115104200b90080c4031948000401c1e03e1244500400600540b85040e041d100240440c22031100350440302c0301d0b21408103281c5003405000340d1190140804540c6542808a4100d02 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 122415908 1250 122414658 122414693
    0x30b06040b092709100e030901080412090e0406051e01030b0f041e140d0c1a070219080d06061403060f0109081b030607091206022d07 59
    0x414482402014010002e071000b2480903500040341140c01c1c4645500b0301071004a00241143c890308204901c080442d980c1070190700442c080c41315003c044191a100d0080c1c01065000031410350005010500ba650f420404210341d082c03c028070f0741c0f51524038032005400c0b80d0a5450644907070170b200c0490601c1d4000303941d690f2082d01e03041c999411941d40c030402e038070041c019a01e0406051f000c14140501c01070700a030001810380c058600e042d4140750650340d0303200c4c1811400031070149072030589550b4080ca081e40307400b581c1702d020b1108989151040361036544000c0c09440840c4070b03410070a0641e9203030b4075040356540d0142c1c07032300d82d21802100340203c15210580c0203442009031400d82c0d95808101c0d10709581c0c009100700c5415107444824030040305d640700203900c15840e0b40b10319148030341c441069042c80c00108c1801c0d010340c3c4207076684000c182d410907031030301c01c0469004e02c00c0c1d980c5010a4880c1c0c003402c80015200ba10f1581c1c050b0984003a035030a000c150084403080c100180000400c04c4510380c0b4145c03520b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 122417158 1250 122415908 122415919
    0x415090305071e1e171b030d0c060f0b0d0312050a0603030e0f0310110a020601080303310206040e060301050609010509070311070f030e010f030e0304060507050a0203010507030c030b 80
    0x1100541611a203007001d1250200708131580c881c8024110040405002400805d00c0781006003101d10742d055954090106021040101d03034196100f90f05010524041e8007040742c44d000d04200103541d078417004051082070aa0302d80e6481515000c1a510b0707110341044613009584045440c0f43c907151074800c64a0113032100030b009250940400000340c200d42002c541d10021540c0d41c9034104a40007190401c4020303004203503424603003084000620075190103807880b1a103c0d42140c41c41e80e02c40829554030300c8140c85a10300c13000082d1101c180724003110104030003558403a15041198100d03501103001500260004581c49185a0811801e41402d115496008104032005011075240002003007400b0000b8040c030040540320350304001500b010a08441c00b0507881a401c050748605814006e0182c80400700080c001740c4502c00c1d000b65030384a8002e04100d20394500255141c145014020754055008802c115442c0c022507120801695083c890b8a2060005890200c3d08000034030b00201120b803030806083c80303003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 122418408 1250 122417158 122417189
    0x2150f060109090213090f0b090414070b0f12180f060a18020d030f05040506070b01030204061d06010c0c031a01140402040b2502060c01061a070b0609040206041509030507 75
    0x200c032002c0c5c5c00e021101400030028000e94607500120107080103c0310940c1145510b4144801c0040c043da04c6074820040341e0650301415114255485548203880484821480a000d40804245884102504003022041440201d04800e41050628000001c40744094212174200100d200f054003904000c4000000c40d201c0700b102aa0008504013071005014040100e041c5540c90400e0040d01164060300b0001c140715124202460280804282400105d000b507007402c000041c888040380d00c0802d84151074050220315524980111140c00100005981407101880c000002c40e801030381c1e0003d5018540782c030303010030f60510104c060040c080d424140e020b00c1c410002080080c2400b402c3e10030140c0c5441343c072403020510040c000c400703041c2e41c1e001a41c4800001a03202c04030070154441011a100c7c034503082c48a100384401e408030790081000c0500440407010010342c181c540b12450540c424402030009080644030f5059842542440100d400031401c08042070040c0a41044102c0091100b00340d4610038 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 122419658 1250 122418408 122418427
    0x702040b01080c1e0c011812020a0209041407090504050102070203010614030709020904021921090210081b03011e05040c090501050c0309060712031b0f0f02150f0601090902 76
    0x152007840403c000c4c11891800c00065118854203c44600c0361040003032100f12541c0b182e440c40003004410846a5080d1500588001400411000d4801f5001016210295155220780c0c6840c02c0300c480ea45d082d0b0043e03800c0450400d005200301c0f40902d0040c80016100c041ca03105040c21145150071141011142010000c2c65076000106c034829140f20030070260700c130500700001c1800782c024440031a8880601140584400381c1c4400d103a40032100b05410b4503400c1c1c4c5800d14039002c0700c00485001e50031a480282240e800b41c015513038681c0000c4141c5005039020404044046560401e800010501d828000800d401c4902403010341c0c0079001c00c480030000d8a2100201812404440c402ca038103108010030480d94110040c019202d01c1400501499511060b619180036100860349080001c41c1c40c1490310b43c00032691440f108008804c2d52940c00d2a18900c04043c0e801d404001c180b402107104490f05c5120300c4200c20320640c05900c0081d007080d1b00d42030020000d0505103280c0c00400e1034500c1071040000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 122420908 1250 122419658 122419681
    0x918060e06121c031b05040b120402190f060201060e09060f0601020304080a03050307120207050a06110c0118050c18040b040201170702060a0e070e01090e010204080a06020702040b0108 81
    0x8100e481100d90340d601801c000c0c1c0b8507040901c40b4050168140800b481207403580e80540121030b0107a031510200501080c40007040d10319010300d0085115000090251a14140346030000341c0d0443c0c00200801c6840400305034401ba8402180c03c000340507812500204a080c0c2c090103044043d2141a04c004601c0c90030a07900756032410001c001e0100031120001040c1a03900038804c58010303010301419540c2540d2142000703003240d40241c480f01e0009020240c03111000029109440e261a400f001600e41c0305401e4403080090051101204a004001c10400750100000d1049100305905d035240030b580400c1e9030600750708005410210381d016620300c80d091981c0803048009198880d43c0008144003540340e5000407074001d10210440b094909883d0217002d4400d40000d803181c803e0050a40c03d1002e42c410f4180c06443c0d128510a51942105210062180101c3d41d00f05102840704840010304240d034a454072468820451000d13608240d001403020250700705030240c1040d001013070030115210b0421507900704 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 122422158 1250 122420908 122420911
    0x3070911030c031503030a030b030714010c12090506040905010f09020f0301120f0b0106020a0210021c050d0f02070b070806030a0201050901030906140106020f0f0d020c1302040b0a0918060e 83
    0x112030b240020015400560900700142c90f0b0f180901100e4440104000c0600100003903030801d8031901c01d02400207071040140d01c422101a0301a52820000b44060f40d480124008225500092080030200071445480f81340250000f0040e0440c003140c503501d05003020101c21443d030032840c0003038010081c880c004a49e40045a044415140d900d132100401d40c00d101d0381250400200400d00041000001882e40c0c1c0040c02207009402196005600c4074000001e0307903203420422801c2e0700140c0703041140e000c80740510040c201c0d00b010000c000c030b203002c112001441240d0104000f140d280900c40144401e040c1d02428055000d04190001c1c80089c00c1500040d00c01d0080c41c424a04068030341d19400100503a039040354000c41411b00200d456544c688102075121030410749400d00c2031107030307644a40700c00c00300050500500010381c001e8071000d0b4088042c00704451040300d441d000705408000c0040c035400074100605c0803060030b54903600040d04248a4a95030040f00080140060810200340300c80108541e065 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 122423408 1250 122422158 122422171
    0x1203091206090606120510090b07030b010210060801050910060317030a200406120204030b0c030915091c08060a090f0f02030906270d03090303110703020c0307091103 73
    0x39484003480c54800c02401a14000801040c1030110028022140c050070082c0d1520032415a8090102951000304449040d000604203074142004540b44601a50051f0616a010300c141c81c4d070340c1d01402d051001c0e01c0050744240161780d0b41e2000c00011450510000006030845202072144910b5915010440303200c20843c150310b02c0c8000f0102d00c0247c3c1584c00184491102c00c252040c40c80d480c078400205810a105020108a0075a11060540c44502c02c4a00f6640c1c000d108511075114512000388542009114400078801c0b503803200008903880003c2d42c80360b4411002084015480c0007250440c80105800b81c0c14010702c20203200c01035032591007030b070b0a4481c28000041d0942203009528050803031003140068080c40001400b121308401b086151041c01d4030001c55603503214440c0c580c51002103e141d1410540c022560064003d4802e40003e00b1507400ba10300450015076044c040d40980d03000041c01c6004d83e0180b45036503c80d00b0148041c030010310b2691000c02c51490b03003a581084901c40280308 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 122424658 1250 122423408 122423429
    0xb01080f04060b0607140a0201030b1206040f02010507050f2b17150d0c0e1506030c0703020705040507050a08090f030a030f060906030305070c050906010f050d0b030f030a0306120309 80
    0x40c43c9446540a451080c2c1d00000c8100d034050700056100e403681c000040a038002400e01500714407904001301d5924a0258003002003402d60b0761a00c55109072070103080100d0410400300080c03c0411020400036000d1542c1074042c00c200c00d02d1203001d02e111800d010b00e2046d0314804014409035990000541c03c5180a0844900c9035569041c42c480b40b5802001c4d01d2075440081e0a144505206c0001402c50949403c008280d829031108202e441e135180c910845503034040c1e0100009020710034a000644203e51090046035189912a40013030280c0700100c415070001403010902c400c046a02406080c3c0180c0740c01d01810282c10500c80031344e26840740c0701c1b5840078991102500e66616189034459401440b0112003002503d403286401840355000c00d0043d42c1850a40070301013040d141144205000758070585800e8076078030080c40706603907540248503a80700302540c82d540300c0c1c05030306c09000420102c507000020b15550b01d03104101901315003c581000540e00b80320342c09040000e41004c2e1a00a56020110 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 122425908 1250 122424658 122424671
    0x901180501120f0326100905090102070c121401050c03040b07030c1e050f0a0e030d050306012a05120d1406030309010c0c0807090c0e0906090604020a030f021204060b01080f0406 78
    0x308008a800d6440c01a1720f00142c500421200d8101c012201065804510307080c045501c40070602403d03401400300191501e400c0030010860741d0700310021000e004e0700c610044100d40010080460031900101c038491006074001007000100200391038003551217551404c0070040c90b519010003c100c1d121300c140d01240404200e01d848280b900541c2650302020480502c190b880c181e82ca0000e02d05000f11031400d020b4852880d01070b00041c06001a42e00c0341c541030b5140c50700301134848d8209886802c9220200f1301e200b9244062030102d801030101b500c89120b050280d130303920b20711003040c0000c9980c103840d00c00b03202c0e40d048107015031aa408800c9401e642c009181040c08040303281003008601c401644018a43c1c07250010002d503015440e00003041d07100150700c81e0401710100d44184800740e8004c59060350300003810360020394241744c90b40c0a080002024a0001210102460300000301d80c842e81100023a14180f0041100300090b9010704410010286400c003120300704510072103000b060107040208030648505 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 122427158 1250 122425908 122425937
    0x408031819150c0b0103050c01021c0f0806011b030807080105040603030203040e0402120607020f010507050a0807140d060303050d0c020c03150702160308031e0105060409020c0c0901180501120f03 86
    0x3c101050754100000607a00d59407840c03d9592110070014080c00360240c0d4040325504013480e01c40b4982c8400030b890700038104a81d20001c41d21035070000d041c541403050926865504110020307420507102e01c01c0e1101c0ca0a070414039006415080140e2141d4452814201c062000a6020090742d083b200c0d030300e10441c016101c6200052003181940e540c80c000340b14003402c0000c850307070000314464820094002001903407900701c012140c6218401c0c040000c20046004601c200307100c1d41c0b01e00c5030710340c50952140c00d040000c20707060165041e0354010707800a840031507940c2082c4071520500c12942403030700040402d18038040100b610350551101c01c4a07041d4000c0c0c00038592600038032007680300c2d02c06445000c1c0e940341ca030301c1d18900c02c0e0406c0e0b40d003909000f41c202e100c6074201860ba00560607288000e1105080600c0d01c1c244101a500c264206410703405145012425a00d4a40c0383e540030303050010364441000c040701000740483d00c0503441001d081481c0040d03000821030040c5400c1e02642c02d031a0080f100305409 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 122428408 1250 122427158 122427167
    0x60b04180f06050612010e060105040311010f02150a020414030a0c0b16120f03050907080601150306120302010903080903030415110c060a150b03041a060114040803181915 75
    0x154080e542111380068882d0046640e0407450781030360b1050502d42e02c00c0e00d80302c00449a82c0a07500006040040070003810441d58083c0e404181d40aa00d88100c956100048403085c008a0b01a0340020038140c0116052101e03d84c8490295540c400540090802d40c0503a11400040d20b0310f80b1440d034401000240d43e04880001c022030410958011112803031107004450000e00300c2c100c104882000030701e010003007040050b020403050120340d030000080410384d080c03141103960050089504400e050382e45e000007c017403014410500905010740c000041000c01070902801d0814000c001701d24035081001008005406140c038644080c0c102c24000a032030701c2c06010003500b0b100c0c40b94450714920941d0108120301001e03403c028a01b02d0f8030130040740c4040d034602044849000907030340144048840120128140c2c490300300e2a80c460014586a40003c01440412810fa070040d00700401a030400240c800c494500844140045030b810386100c3c1d13600c040798410700c0c04410710740a21074403211300c0c0c5510b24490340706 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 122429658 1250 122428408 122428421
    0x210050411120f0303070c230703080f090306090c030f1204060c0f0602120411010c020f1e060703050c010b060c0309013905010b010311070f0807060e0c04060b04180f 73
    0xc1c83c101c03aa80e0400e0031000e4298071080900711141b00c1c00c2c002e009141c10001c900003009200d280c004001c42030075035460b50b5440d00103000222034031009014259003590204511405080c0f10000307001c1640307010b0b09141c202903414481080680c07168044036804861442141d040b1401032502083c085424a400c0780e881514041c06401c02d400031034685020700b68039408600032489103501180503c00300005454006601c44043d40c06091180c6800c03141c1003094010344004501c00020078604036820001d044d0750099542a000618003164100315004244501081d090049400a042040034681d10b0383d00d02c00e0900a5040081d0105a0030140200c550071400b0386007982d00e038941448142d0013030300b1040841901610b213503003031001540c404cdd40a885009000d28002001515113100d54582605120b10004212000141040030002040640c030a2035070050702c0c000541420624001003005842c0a0303004641c04403006c04c010441e400b545070b2000c040f48540718010900c50340c04141a00182003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 122430908 1250 122429658 122429683
    0x303050a02011d0c0a06020c030c0f030109080307020d020606030a11010c0302100e03071506030f0807050a02031f0509120a030b21030307080a0b0d0b09010f0f0c021005041112 77
    0x10743e10900e4020321004101526081c02c1079030340c80942d69540d981281e503046017441151f0903030004240007155045c08844902d4205001c1c0c000308400f6401e90311088150b004803081d10040e0080035500c102154103102c403d0300080c0c120004c000d01c01c2241c503016811400c1100b014103003c0b402d103074082014000d00414202c2e0243c824100001c4031b16103606a242d52001c44201ea110703050106a007400705442c400c101c2542c0c3c1240b14180c28084030b80d5100179943c0603150a6a03076124400d03040b001650208640d0381041001042403904101d6840300318151b500180c008501c07600001c0310b0980801290046d51014011807074081080c602a002185602e03030541c0e40c00d160102c00e01076204255030000000c40c000ca1242e516011580c2e1030080d01ca04490344401c0340c0758840c00081c070311804a2080c01c030468010341c0c100c0000a4081c800f03030b80b401c21100303042003d9040648600001d807900340c05101043c440380c400c2400384603503c1c103903407403030003411003401100d00c9000383c40000000c0100801c4001c41800 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 122432158 1250 122430908 122430941
    0x20606040e190b060411041a070206040b030a090b15030d030b0114121b030c0702010f03140a060510050a0c2306090c040b0409030215070e2110150303050a0201 70
    0x2890b030b061041d16200c0450b0282c2c003e0703013000c1a5210070a9994121743c119a54000002044090344905045942c0420002d99110a050002140400250f0b00440c020880c0380c170005681c001510307090f00351200c000d0a00c00030002442c1201e055031404181070000b820301d443d0005020700c00b000140c94001d640e030307110410317054085071144100d00c84500141c010b0010110b202d65007110200c1404592104031150203030b0300c4040c0100001540217642c0d8044181c0ca50401290700c2030601c036650b81122080b01c80150103511641c0c108068107144060780c0220000b0302d022031030440d1226000e8a0181d103500002d19054143c8106c841141941c12604000032a0400b900c1840c18680c0b5665a0751400600d0203201318640244260507107030600c07451050301d80c07540152142c908a4a02c074035546200a00b14004c0c4485640000e5003651411140c01c80a450440120780c0191007040305031420421075209410700d407a01101c3c0f540c0504c1c8403e9002229458542a0350b80c04060301c1c101d0142145e0b40312020f041c2d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 122433408 1250 122432158 122432203
    0xc06210b03030c0a0506060906120703060504150920010807050f18031f32101502010c1202090a050603041502030412021006060504091503020604030c06081501020606040e 75
    0x1107004203019000304170850704055261210020003000340a40c054440d100c0d40035140c2000002c50174ec002c1c90344140203510040742150300840000a84400d40d40031140b01c0c000b000d0707204078005d420f054040c41000a00e0000058684000b0140080c800d0441c1c810203800e021801c200079140a504410300b00354060196100704820040c03041205a0280080c9030090921010408604a14103042c200e82c0034880b104281c40c40c500301881e0158400340503481c070700c4d000580200f1420148001c0340d01c00e0341c0e154000240e210b10310fa801410600f10030701c42e5003564010030543c2059035480c1c440c00282c8d4012202a9030f203888a00c1d010800030310340c400002c000381c0044100410702c20050620243c40e1913035000d55000c00012004601202c581e070143c5404510244401e02100c1c01c10750107024080000004442240d4890300094100e400540c021a424142c030181809190b0b4403028032900704400d4092381124103d110700103501c0c0c1000614a50040d03588007a6224104400c00011102c00704011420710365 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 122434658 1250 122433408 122433413
    0xc050a030b0d06021b07080316110f090702030307141801050a1716030e06130b180102040e15010c0308150d0f0303061a07050a080706090b070c0c06210b03030c0a 71
    0x20b034004250030170080c0105000055006400b000312000c1d43c03440100c0504500321607036035160700100d0085981c0c00002043c41900c260f103643c404d050285071507400458481ca41480c004140414111202c00c103054103100c0824400340320288181c49840900745942c881544900490340b14001181c3c4080c286d1041d01807051643e8104409a4048040c0c0d400740048102a020117980b00800c0d5080320100d0844c0d06008046008505003540114a605551030201d0110f042c1500b0798010fa0081744030402503000f400b00c9a854048002c031104030a00300400340d280580c83c05040c2e20f0004007031415481d072100c0500d025aa558039046280c40d0b001c0d0146100d5801c03410f000f40204901c0c0a4662805c565003803403420500c800341038403002980040200a45202503496907841d4110410894201340c0f0b421031040054484d042580c13207508640c0c0c030b032460b0890070b042008880e0013030713800107060000d170510304d041100d6803044065021034008004240030716024017080c0385100e403899504460044c00903041c00c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 122435908 1250 122434658 122434687
    0x911160c05041103040f1103100f06050406080f0a03050a0e0418152702131407090f1503021606050114040b0406050d120207030f0b06010f030c050a030b0d0602 70
    0x10307100182e8080000803518800c895540c84191409803a080e84800005c002034000c00800c00c10003805000d6400000c0d1840f078020580e241084000d0040303450344000c0c021420148101c800a00452006000c40c60440241513260b801080020301045800940200a14082d410218910714081c008102e980049120300c264004e0180040b02c41c004001102003d440090140710700304203c120000e01c0b10403a000301c0001c0401200c80403030f004500d40100f044104000d04c81d011107800400da41c4030007890700d541c000705000002d804ca882044030b000320511882c14000c01000b8001d846040c0166603104003024045c004591440050145081034000f00d1804105c41c0450000d050588091007840110740400081c0c130114000c1d1600600503802d0074001c07e40c1c815282c810f0880a006172007403907440351a040586140380700141c4042d407589040c0040c03543e2000100c02c8866051500304603000324510010521b1041c2030b0b00d0310405449404441742c69896141c200c002652003403003190b655104899444 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 122437158 1250 122435908 122435933
    0x3032001061e032109180f0e011d0f1b030a0501090606080705010509030a1217070512070c02010c0206030a060f0e0601020106060c05070302040f02091c060c02070501050301091116 79
    0xba0046107034800c8800040808032229100c4d1900e403244c1c03111604048103191101e90708029801200c3e1100d203c60800c411600c504002c0200b04800401d0006900f84540c080b0f002c0f040542507294086070600e00380c2c40010500004a41410848496000803840002d2030004200e10103031140d40b909010400b005402c0c3d0000c0d0485603c034003550131007551440156010b0158104064058000d2038044000549006564010b00202e007403525056101030040103c032902141c0110201e100022003800c2d0058106916500c240d1500e0401090801540001c00d49160404020301031000480812918041c82d0880c4000d40801d0b070300c0c0c250095455071100102031041d15030b94050752900c40086012449040d00d441c0590b0001c000381050743c6181d09000040c0300d401c000c034004a509010300345507a07a07802c00984e40c400c0c9007054424020303420309104048500d405241000c2d54401c0d00c0800c01c0340d03048015241100d10450000900c2c0f10482a19070291040c80418501031001504c0740c02081518403040 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 122438408 1250 122437158 122437163
    0x20310060f05030c01020a0803072703020103050604050c070312020c1b09070c05150406110d0203040606050402031308070804030c0e010e0106030213031101020c03071211060403032001061e03 84
    0x200500d5030b41c1d81410345690b20065940e0050300808152808034403075100868000c90175142669440d00a03400400c9071400c60041407800343ca1481c0100103540e850700400d03400041c110390400c40d03404e0444280d001c0d445220002030900600030b0301c0500d415a5503040c1c0d103171010f01c0c0f016507414042004504074581c07003140030944140100000b040c0c0c2c1520a19664030341070b50002c018415811003072b55007452282d000f041218035548a41028883c03107500c1c00640341c0542541c00150300d030b080ca840c100c020380341c4c0c0740c2295010f00d06c18400c01011042641074007100f10f0704012410745e11981e90034200d038544119080600070300303040080014412076100a0354129512003040641690700e80004806900c1800c407940d41e55525243e050021889480800d255400c050049504000c410404203041c1609640803400090f240c560a60900c4014040198542c10480d1014501404d40d074000c1c20303460304100301c0440001d6030700c8400486d000952110001c1c200c2003103602e400002c4408441c00c00003150004 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 122439658 1250 122438408 122438429
    0x618270a0f1d0606150c01022b1406010c020a05090f01050108070903023d0305070909060509010306051902070f1a0609040204050a0204050603090a0b06011404031101050702031006 79
    0x59003a4900c125401ca240381e40340b00c0901000e0701e904c01081110803c05a88408104040001000086092004003c2030400101308521241c6201d280385a07401d031100c034092a182480c10709a017444003001d11030790180007400c000707500303016900218807003d2a581080c0d40040241003486080c03404451030a04940c001d0340c0f02401275683d180100ca1a8140c1e20000750410b1013550f402c084e200c0f07803282c08a81c5862980600d011010380c040511030641c240d940c9500401d503100d00b80405551f01040d100081c040e069800c0c01030501d080c000c1880260144005840f095440000c04d040280040c802e06083c2901d0200390f4580c00242016606218107420807580070540400e019640501c0394100c0b84180c0d00284500010f035101e400b40009050f0040c90070080da0741c00c00001c12640d0b00c1c00082c50103400c0500003820030a85a00d407542000c10064001ba060050504080903820391120444c0c007036940c091401d815801e040801606c1901803148004d42c54041c04559840c2d40416910880c1200c0d9080003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 122440908 1250 122439658 122439671
    0x1808101b05130b0315130e0c1203040b030606040b12060910080c19050409051f020301051311040504020a120515030a110307030803010608150618270a0f 67
    0x241a81c241c85900310740301544020b00020000d8803481009944e00c001040c000c080d002d00341c840080e081c07a844075540c030a42580c6041031a81d5540800c409506850162000800502050002652400f176481a84400b00c07000002801030344600d000d40d0f00070110340351030070b4451100706144801010100c9149001d0b41c1e000380000c100c0c60110219004079031004000e0b216840340c14040c451081003003030b040503041140030360026903034403644a01000540140083d0800c07c0c010741801801d04c01003030301c01d2800d600500050101c0d6481d175104c00444c044424000401c54152a4800300310b0107540d0081d40d0213440030420301c0c88c41e9001410b88002000e0f1000400c03941d0307200420103654020a200c080e0301503114944040000380e004180c401b82d00348c002c084845407a50b07562580c5960703000360819400035001000348284000d2643c01c0d10000d5000f125010700b03010000c2080c89403c0c1c8440c180310b01c5102918800c160301c088441e00c4245809047d00074065070700e0040380c00c202070304441602103101303031500d003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 122442158 1250 122440908 122440961
    0x50706022506030b0a03080c0706030e0d02151902030703060302010e0a060912060e0601030602070203061006120c030b130b01120605090103060b01120e01061d07020607180810 77
    0x4840003404101c0d010700100700d82051011402004c1107100c640c0c1000c0780e810007001103420741014081c0c183d102002001800d00b000c1000302a02e8074261070b0032203075002400c80103403690081169218006446d44004241d52180e85044012200d4000000300c280b0002c14481599415048035040d0390003a201c080d1206c0d0702c941446a00c01051251000003028600207200c10ba81c0c98094410807400b80402140c1c6e40300c07082401d0b04200c0d00b80d00841e03c0355400142007045040c14480c840d40300189102c00410a0300e40030010741428030106034003102969400d100b484650103a80002140c0c10040e050462503a480203070100105052564640841c05107401600003038200c0c0208016a800540318070042c1e441e555441c00a0004078a1443c184804a211884244400c1c411940c0d5072215000105405143c03500d1141e50035948090081034200c0d140400c65620740001e005ea82280c501d14001c010300304030406c407200c2c8803010b80100003103005101201c2d49c00308081d0031120301b922040036014083c21042 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 122443408 1250 122442158 122442193
    0x1804030f0f11060604020a030207020a09020d0e07060906050f04080a03080609010b0f160203010e06040b1605030903070f051c17010e10090b03010b0405041a311b0305070602 76
    0x8441c8040e030ba07072103000000c0c500d04080c2c015040003a45400e02508040d02d40d400281d9160540d04440c0300c99034089200000211a80160145041c0725400703064044e08100c80280544014020a000d0000020f06002d111040d5022240104840416540040c1c0140340092901d08140c480134454041640042040f800e484200e44c440f400c0d0f60059483c2401c1c01030a01c00042c1e0880d403e991656840d2001c034074007003007884603a201d070b0712840310001d007450030000b003480c959540e8a00740100702042c0200b00441d88000121000346400a1030640d512030f0600d4464030700b01307009104000400101d80c0030b14120350003608000600c41e40391009201c0781e07240c00c3c15076183d01c02107a90040030350f1250380c1000b508403079920a080540d0054008500720160b0030201d0251002503a045607440810350481c1140c48401c00d485410640c0c204002d07407a01c4102001720250041119080d003450708083d0460204968840b0001c034510551090701500d581d81d041098035401c0911401b405802b9400144001181c003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 122444658 1250 122443408 122443427
    0x105030a0902012f0c1009060c0218070207080d020114010e04060617010c0801120b0606031012030f1d130c05070f0b091209010906120e070b090102070605090f0603061804030f0f 78
    0x1a6031368002e143c030706442110610270b060b00a9821299a412030161014030503019172044a5940040c60000e2030802d04916040001000c40300f103914000b0174038046200c4140050441c1d0703a9081c1c0014070380700d03418800010070307039540b00d0303680404240340c4403180040641000703c651142d5220800b1580c0d0b6109a5400d1107890035005041c168041d002920385e2034080c02a580060078010a03101154580c43d05905140c10500c050b408510445188d0001943c0803071150b102e003100780c00c0100381680080210341804800c0c684e070f50303415444101a61a0a2040c41030358803d0750070000b00c0c0100025401c041d0b0500c282524041600c0c042d80300c08030501c2061400300c07811140c041c0c0d11640007914200c030458410006480340071815407140c060301d07500c5504200000103800840380c0c090b5030fa02201c0c00a86801c0840d4048030070f10009211480181d503e010000c1404c0c142600c4081d90380d59440009030701645d80740304906a446546040c0070516600441101080d0042c1c0c0300d0021800301c0790000d84090b120b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 122445908 1250 122444658 122444689
    0x612150601030509100c0905040c022b03150e060a06020a0512160f030906030e0c0604030b07021f06030605070503090a020f03031603020609070b090105030a0902012f0c 74
    0x26000100311954860b0348400d80c0f010010040c0d07041000207021102c2580d19001c5440d0001c0c039486820311452410784900d903903e081e607000920782203041103144540c00780c1c4a9440a880800c40703603244e48040c06074015410413052a403003d41019200d10340c1034135025058482c9030040840900105401d070000842140540d04580100b080e0042c02410356216440b0315104548032085505801c0007d12456110a00714400d403601940c45040200050403680c0317501d8401500d0307005060341d01c9151110004c860591b0b40109400c080c640c6e03080001c5e403a0603106424294541520b45110021044551104055a220728418001070725160303411540ca0006580b0f8210942044062200500c3c01c2403294046c0714015068a003851109004480a05403500d401e4000d030300700808000f8070300410b02601018010b03ca80542c10b155030b01000030f106010062458410300e582c0c00000082d0381c000c0c01c0e01c150080a110020366400c0b05011082501080702000d4190341c0709542580750300b46426038011703181a2 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 122447158 1250 122445908 122445943
    0x7080111040b030a060504090308060910120206032a0a0e03030f040b0c1507121d031903091b0501030c0c050606100507050601091b050309070510051b060612 69
    0x7402c10940e4801c903840a8882100c1c6566811300188940300c0e4003405c46254000e450305525803a0000500c8040c500081003200382d008420700a00a0001c0c8588030420583c042c1c036140e44a98424080808003142e0004200704e4464005035483d41c2d48122004160104040e9607031004c1040100602d603981c0a01d03031545075103480901041c0511888800900f920824103401c46148001d01d40b07400101c14015181f160000d0b000707410000207641140600501260701c2060101042c91142483d41c5a0040044501d14240c0107841055024401c1c0c101d014042d40180702041114660402c0c4200000702c0e1080c540070034241200070030114014080c0c0301d40796420002030203890740c55800300b08480071499010403d00005100c0c00c004510200314144c041d0040d00c3e800030b00445840072180c0c0f00c0181d45e8150003001801c104115225001040f1002120001e0b900031415000c00e0405a66501035228200d88085082e580f902201c100001c03d280500e00a071403103c10105010301e202c1e01d6400c0d60030b0038042070 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 122448408 1250 122447158 122447167
    0x60904170a203708090105220816080604020409020a030c060906030b0405040510051306020408030301050f150711011205040501050f06010c0c1505041d0118020301050102060f09032a07080111 84
    0x13400b400c0c0201807035181450614030306410b0810350703401c9215541403546802c461003400c0c8402401001a022110035000b594050031789014100f0f60307a9500104005d0203107444802c0304046494280e5044061a404618a18001d45403d0000c0c8041040e21900002070304103058400c4034103091003498011340c0c103e8060220b00303200300c48640c05840301500340080c2015940c1a10003160151010700040c1c507043d0040c41d035030b500d072a0822044090b40c0781d1052245c18182040b0818088580803900d16990141c0e441941a0300b40b00160303070b0216942d040640302c6041404010030000306511032485501e0414401a91342c8070f040045800c0014a030000b0300c200003009050000e001040088081c070034580c075106251540303130500c1c0b04104c0440d024000620084000601403848500300900c2e00c651044011401c41d890500000c0d540d9001500c841000c038454400b14012110900c103c2d40107616204a513040f807504000c0407581902c80000011090180590105003041e0601030020072000707110516091 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 122449658 1250 122448408 122448413
    0xa0e0a03031b032307020a0501080c040e0a02250501050702061e0c040312080108011808031501121506020c0306010f1e091112060904170a2037 63
    0x1240c0048140d01303100f0590f007034458020000c065514600f484d0401c035600ca49051050000040940e0409414003c89900300b05013000c45005840403070306880c0c40d240e0aa210050000c0080c4209900000150341d901041e80e00c00c2072042692132030a00c518001c001c56650311000f281c94510a6864200c0192404041050700003d4401d513a042034142e00082c0c645966a80c811030820340c2c100180000c10b90180c01080001002e2048010400030790b01c240b1301c010802d030b035800301901c0000d10583c0e0038482c0010100040e4816440c03a40e2450420004201501051f8090381a41810b441418010703c5000c0c0c20401d0760401080c4181298080b5403819040c41c1040402c420040e028105100070181c8440700080142d00c1d40600300c3c0703200c0075a003000c0e40d40948a80c10705200c04014a01070080381d211042c0000582c15010884041003500b01d01d6403035405800084460103c04980081078544100912400301000300e0201180c1041244401c1c041036144c40da80803c4a844503d03c03204011003011002 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 122450908 1250 122449658 122449697
    0xb010605120615160c0807030506071209110603150d060b03011d07122406050103111306050f04050a08060f070207080c0d08040306241d0c0c070b030703020a0e0a0303 73
    0x40840c8211104845c4a0f2034001c0c003894055260b200342c45a40c00203041c0559960800c22000300f0540500c01880481c0c040e4403000c04104440c0e4034940a0038000000500f414010250307042e00030f50003401000c060b002c81c14410701811842c1e904920a528068041019140301e100000070300c3d4205020740300b260b10b40300d040361503440c00d1901919644a070310002040b0030380d080c41c404103119100500050341800d0400060450300d06040154403030300c1c204185000c41c07502c0034101d002c80d0654508540c0e50f690800315900ba9008560041340c0008030b03080080b820726000301e4803c0c0f040d50540340051441e035500c07034202d0b910511171080c41d405030032411500005e03041c03a24130305003010302420541d483c0640d2030751343c08110340384a0743c481c09114606106a602c07403a40c40300c500c000c00540b07201040803040f640800800c806e0242620480800000301000b20800501c0f190004001041043d034030b03441e0900d8003402039400103040100268952211520718581850310781c0c1070700c0c0c066945035030204d034400c600e50 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 122452158 1250 122450908 122450947
    0x10e070807053a08130e0402060d0e0c0d050106030510090b0a0207020f0a0806150102030f04060305040c030b010303090918080a0e0a0f0f0303020f0f0c060708070b010605120615 78
    0x520400008840d2183c050503541daa494440c1d440d10741e132075684e010039042106068000801b501e124800340005603841d841582c10320323200c0c250000b483c0c0d19002c2605180c8924400b43e982c2000c98881030314280141035002d2000c490250054504950701d04800400711640c4030070081c090708110f4042815181c0590242101c144058201c0250900e010006191400f10b41e0289180c0e52044041200840b508501307a90070340401e0006605140620802516500450203510101556080000c0500502c0f4160800454010700310016070358480c10010b0001d8801c0c0269000d041c28441561010410f0401a2300341c281c2140c41c95081c80070815044030444180c0311850b40c0051440e03c0800c802101e940c40400404a40000159551440c500070341450840321480d90340c1d03040100c0320203000b01c01007000c2003400400c03250995150260f240c4102640200b0102914103c981d02c0041500d5401100501c010f800c0448101d41940c2c5540810030415100e010204c00d0420610060302e440d902c180d13820 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 122453408 1250 122452158 122452219
    0xa030f03090618120e1c1113062309130204020d0e0309120114070f090305030a0801051807020a0602030604020d1a010e090705040315020912010e07080705 68
    0x10a90203078640b0303014141c1d41020030121880302e500b46601d0800134002d00c0034201c0320f040d062200b440a06a8000745c44005120340500741080c0d95810b0740308001d903d141c00601c18100410194010090001070002082940100d24500c82d00ca04172560404044004188040740108004010344d50349240328890040c030042280c1090302800103030b45000301c600447c01851800c0e030017961507500200402004412100301d1400b1645080002e22000c6607038940750341e21200030b0400c410640e003036035001c0301c044c1856800644140804601c455610740e000419504880c0c00315860b048079240100c0d622890341b030a484006c0907920100103000060f10351f130059540410300610050403e00000d988805980444001109019001600a145680000800010440c10784418641e4503010030094030602c0f640c000030f03003808081408440c1d840324a40480f1000380c805000814030701c10462100e03019194104a01e080ca014880740456001e0002680d0012508000c100c1009940208460010001d895069 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 122454658 1250 122453408 122453411
    0x2031609120303110913090c090902030c0d0305090901060305060114040b0307080403030b06040e0406050a06030503040311040b150304020406151b0503040e100801050c0a080c0c011410090501050406080a030f03 92
    0xf00b44a5071b9240845100614441000c1690700b918542140d802845170400c0c0c0e6641e291007100805a100094080c0e0f40420940c0d01e543d007030402d400c003500c1078003404040d294001c1a401c00070403190ba058011130300841c02030702c6101b0440c0c80a901c044280c021805201c003488000d00004506a100e482e08540060003810001500103203000440c445900c00d402c140d8200117600d0034042007103001d2080b036a20072029541002441d0070b69440310340302e10aa200c0506140d11003000c540c4165125032000c3e030540801031512000155240e10360358507030800c440c1a8812441d00c5800521060450b07081d041e4039a06940b901000800c407001d030400b03500070340c0e0140d038640700500020606007100800382d07004540d6111800f884610b000700103401d48000820104400000b4030440301b40310382008000c2d8010803c100c0c06502c07004c4020f48540103040b00641500c1180d080001d000540e00000301c1c5e1402d482640c03006201c5070382c81c0e105000607114075200300300140d4003400e020804684218440304000085160 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 122455908 1250 122454658 122454667
    0xe0904080d1515050a020c12060103150f0606080106030f0504030f050a050c0102040f0315150303031805100e10060506030c1c0e16121a060102070305100203160912030311 75
    0x540209200d200b40b440b400300380d000488000054040100d907c040c5000c60741d071400c1e15072507102c581e1143c1041c4802004e0b200559074010216030160001880b20482480801c101580d07030300c00034000305082c4200c00c042868401019020130040c0370f070511039a0103031504074203e401c482c01241d16a010150241c00c2041c14000d8112000c2d00f0b00081c8004c0c12120b001052580c1182424100d4070b250441c030120252030b08030341604d024654007000040340d4150070000386a091010700800bc0c5031402000508500a03214045244001c5900012200400c0700840310704140614171082200e8903400741c2d03a8013420510005241059210040150062100c944d258001c522000c070029999070712500c0714950814940e80b19072401030040c00c0010042c0c490410880c000307948a400580006040c0da01034134160b0300001d10340740d0082280d08005d60340320048400421020070808000d400969643c10258000c0940c0500e00d0720820016050f107414141d0150304001540e401c1d801805e64101d1419201414070 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 122457158 1250 122455908 122455919
    0x20f040216050120040f090f0e0607030903030e010e03090f030c090412230910020708030403030c0b010503060c031909081207020105060306100b0309010b04060b0a0e0904080d15 78
    0x10280e507410b07206400100718008201c0901c43c0d16070290400380d030210804d0004101030b90701d11007034a08803588180300040703410740d00c1c000d04098404003110303020314800c40701070000c6168183c0c04010b409001e40d404001b81201100d0503404e0304c0c0c00c0025402d0301d0780107001a41041c680750711442c02e0340e800101103d0214005c0b0b0301041c1c00040468050711141c01c00c4118040706500400740c4806000003000c1d41c030a03038044030100e040724050409494050700c0ca6161207901e8a00030800400680080402c0301d45460707581c83c00820840c2101e5080b140d0101d0100009024200000c1880c003804a540c0b01e2400c40e5110417400351485035107131183c2d0b10a0303115154070300412020340c01070810107200c80145a40b840d186c207010f0301351640507103c24020791015082004031644124094140c03040040f80d41d40d030351104001075000d801c040385110791152600c500000c0b66507041d0010144400c06480d5118049407610400c45030840031140a0011102000340e0901802943d2146111000c404d010381c40054665 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 122458408 1250 122457158 122457187
    0x60504060e060d051e0f2e0b03010f0f0518040201052b05090d020703170c071a0a08070203040b03040206030415050c1b07180c050d1505210604020f0402 67
    0x107845e0138204c0c841e000e13a0904072035980c4134200c0e4040301c02500d144082c100481c0445100110141902841010142d481940141d915004004081640c2069101c3d42c40c0c00c00e10045599504c00c0021018820743d000503941803003e0740e4404440810b0808015680707031b400560b07841e4807004444040b5070740c44c8451388241c0804140b027407060528a00000700c5142503503015103810800c1c1d00820541d44200360410024000d0300c00c030100e68401450450b2500c5405880a140132031a801c40002c1d022480002d44013494984054414000e02d0f0fa925205a140c50b502a41c9900c40c0303005210b816101000068050308240b001140c002d80b0403401201c0402603040b46404546040e101d00c01d003c0800600007122828280d81c80b00038840b80307006001864981f0703010103880103c030780722140140e440311000d041e10b5000e081a0f650b6658604000d000c00e0800040c0d105440c0c5081c007030740340704e080d0500030064400c03071905904600c0e0741c242c1c00030030940d01e46800f040030f40b0b10070108095200d9001c218640046401 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 122459658 1250 122458408 122458411
    0x120302070c0807090b1c0c03060209040e0a0503190f0e011b1a01031401140f04060e0f0d0810150e031e070e0703020a1205130b09030c070f060504060e060d05 69
    0x103920005200d02c11000f0000d0b40391440c80d05201241c0ea0241b90070100d1300306a81041100c3c0d1290006994101704800315015000f580b080440340d0044036040402d112000c0001c0c03800120110707135981e4039000c10200f995080c2540384801d001a1001403009000e5000d006615104003020f0340d6066910540d0f611403c1110100050380701c01c0300c948004001b013007003e062400b00c0b0417030306009000035041d00e00c1c081130300540100700d01080d141043c04201408010f600071242d001c00070b81510810044203220700d1b40c0710003031518100003904820025901c0422100900192680303e549901c0c410603440d02100d4070150541c005a15020348244004801100030004200401c100c02034940d0925000403003000d0710300140031506140c0104031380d01e94540e0000755240806141000000c59880d881400b462155078004024041c0104105001c1c03000300000161699a02201c00c8401d05501e9542c0d4121560031441040c0c040340c410f00040c00514000d82041030380c10341c080e00c0c0074104100d980754070781907800 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 122460908 1250 122459658 122459669
    0xd03300606050a0f0e01051c0906110307170105010e1201061509060801140105070f080405060a0302031f0e07110a05010c0e09010f0803070807020d12110f0604120302070c0807 77
    0x2c2c00520792030129000741c0c003150100b02c00c0c101500042c4642c0c0000e4414800c0c00710360f40040400c41e40c81c3e03011065641c0300258240d0000020000c001018010b031120f58020f644c5100459840f1314030742c41841c01160002d043c2d41041c1e50b02c0c0a500c44000600104210040002000e9520350201103000401d20381c48041c201c071650b580700c89007840d000c0d024040c560180c00107461078a1000d00c02c4090390700081200e4070243d002c81c40c00303181202410520b04074000c1d500714039072201c4000750707400d84294142c0255000b0f66002200300d8150782100c07500006640b0310320a4043d813204030f0000801c564051030501000c68440c40c00d540500c00182d40e041e0031a07101185000100d86040801505410600d840c1c502506054605800680c00e005402d42e80c0e014101c0020844140061142c0c110b4440f1190f020440d5030200100e51840d080d444054200e041e88600b502180c03091f11601c3d0000e11000440034062600b00003403a101100419084020358803007002550000c4803e100014801e900300416001001e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 122462158 1250 122460908 122460917
    0x7092309100606020f030f0c100c03050105130902090a0c1434030215130206030f0108010e010b0105190c0b0a0e0d0908030d05060a05121b0d03300606 66
    0x1900340e0300002c03100583c0203441190300c40079005101c0400003040b43d64020022404030703281d4200403582840c020305a144c1040050403d05000c22160301900f100d8140c0328110346050b00054000341e0001224200400658006220070101d4800711850307110640d06500d516000030b140e03d103081c461000354003424078407003a00d1f0402c14442d200115181840500d84c507440c0705004038441c6840080d655440c0c540e944c54402d030800086207180d007211615002055020700070035107a1400f50303110348200c9024429010343d542400030100301908103105542e443d102c1615214140940002400c1d03800490201040511490b920070101103241d824010780724a51f800c201141c2180030004541c02c1c441a500c104d0144040c2c507000f84001900441941c180c40f10340a40000c03180d0700c410000d00e4503032407940f0043d000b2065114050f8040008603e044078890b0005584a05403603203011f12030003175080c04000e400600204c0b0908103120018481c88075070104280b20790407402c0b07100c0340e41080310269803004000c01d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 122463408 1250 122462158 122462173
    0x40e0a0501090e060103080a021603150c020106050105040e06210a06240b0306031011070b01050d0807021507051b0f0d0b060d080c0a06020703120504030207092309 72
    0x221200e004860142c0030b078060a005000c00380d81441d54070b5106010050240502152880480c3e208004401050196421909011360780781003217021404900702548202e400e211150401c5401401200211031069403058134143c6010050040e00c480500f9451748003420454048040d01ca02c203031643c01e01d17031020107446883d41c149046021a01006540c1305541d80701c41c0d44007425141035454104030351980d441282e9a0f501d580000303080403e003038150168285801c1030030460038030400141401b10321581d1a611643d88807001c00c004801c80c0f8200900f110002c001c5c620060505030007914203a00d50151030b1341060700941c7e5071403c0504500d85021500a500007803206031900c9501e0198a242c10f84042c1c0b01310242e6190210350200061090340185840b0400030100103800080300c02000580d000d640309030b0b03c90f24200e030103940020010b1303000400ca040080380d0140f00c1d11500d8002c680c190001c00b202c518044d04c80c000307030030141d00607105045141c1d001503c2410440c8001d1007201c6200c041d0440 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 122464658 1250 122463408 122463421
    0x1207170d0b1903111c052b020a021f02030403081207080c03090705040e0c1305090105060a0f0e0705071e031b020a03110301023a0c02060a0b06040506040e 68
    0x207042d1100b8072102140b005400400110b01c031070442c81c4d44500191104601c42c413951801246005081500422034450201d15010522400c0000981c500407013051070982c40c04264100d903540344403c00a0b40c000100e503200c060501d1810760040607501c00380141d0b414a640d0b92600c0000381c0005004000d404a02d0342040f06881c0d01602050748086420b46075811401d00320003a681c0ca96241c02a07070300481d903410f02c1d0140e088042040c03504044005000114290003099440c0203068190703041d054a600745000300341c052510b0448982918146011b0035802441e2901301070060801400600078000c0811048e00845d50000521441802c0c0c1480c0303401409503481e0040900382824401c420f80e5181108800c01640c440b065001160b400401d003010b08030300c14000900a02c51044064034011001c42502000d0078110403a19a80c03080e946000c0044e0340541108056948903907001006030490740c00650100c1065102242d0303680c0180840e414541c81d0703408141035038008c0c1c010700349500f900c4041145 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 122465908 1250 122464658 122464669
    0x705100e040b1c02040905030d11071e030f0e0d0606030305180103050c1804020c06010609030b0a05041e11040c0504090501150203030f07111f0e07081207170d0b 71
    0x803c0d92012034605004041090b00040b8200003441551a4a0403000307005c010015503c00c0301a02900300300b05002c42038841c1441d40003c4040b0f81c62580311080d18940304130a10307158459030301a00e91a00d02e402c910411562101881060741e80102b0504564011940c07911420000c1c610a8541c1d59807044140110814120180c000c14101401d00e0200700c0c09005107815120742e008104800c070f203030f4050440018040d000c0c041000d0030f0362045400002343d1a03071080061003168010300220031355031582e150400c1680d40480d4081c1c504825044104a060311500310908040d000d80030710140d105c0b60500141c160b42200c044000000c1c00424244007400c194800d45005140301001040c400600207000b07034480c040201108030044002001443c407070302a0002000b59331444040c1d07040c40e00d42c1c401d820203da03c41c06100644601d44200c0203d15000000c600042e42c04000c024180c1c4a102c000031515a403150781c0c1100c2088034400000d0b644c01018014003034001210f04007280606e201801e015 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 122467158 1250 122465908 122465921
    0x11103180c0f010504060309020a03020d0b040b07021501031403090a0b0405010f0207120206030c0c0304030c061b03020a0212030d2f120601051312030c050106050315060d050705100e04 81
    0x10b21801901e490081607a801c00d00311012070b00a400c0204141486000203a1948030366840650003156140c840c0f0104903804d0390079032140d4440c80d40d900e1107445a0310200d0380e50342c44a0703040d11400140001170000c03803610011f0915003030f118000c0300d00d8a070312100030469581d49940200c04804022909211a6811180d0703045449407030302c02051818901000000701903422031000e40140740010100381e16008031003c941349400c604044035945c543d24500b031145514944544000200c0803521a103042155480c40d20b140781c0c0550007806948019002c116080b164981031551500c41000203120a90303079801616940d910021688519054010002c1500c07a104800495003040070050f40400c1c605001500fa084071080c68800e4a0b14440588030540c0e0030244c1107a02c50303005c0c0c3c040b030108165000404a280c40d12440080c0704030340d5640245030391120303e026490200981180010003d0918040c9113114501440845151341c0e500c2001c1103c6980204003000000e04a040c01170240c01c180c01902d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 122468408 1250 122467158 122467183
    0xa03470c0a0804230f0f010515090a05060d08040806091e1c030e07030f1211060f0601020307080c030d060b0c0c010509040f0e0303010603060b0a080103060b01091a04080618030708030901110318 85
    0x80500704114000500c060302c0007040f114081d80d4070cc01045490311190384000c6c00e154000200c65a5030344800c0302c2a55440708540380301251003900e440c0782000440d800d140268811410003495400e0b501000411500e118210000c00c041c0d850004401d0003000700280c10095010744d01d00c00a401c481d00741202800310b4a10b5036400d0055841ca81140c02f000000e0756980001d042498003e5130701c0d52030040b03055100300413010b468080041124a01540301100402c09680203030005c019856840780314814038001c001110200744c20000880001e540500c00400e81e0030300c02440051046081035240c0c1c210b17600d03064186820341c0003000620000350144901c2020300403500c80e0358201034000800511032581404011314241e115441c412080e405084902d01814503006605407907000c402c1001d1682e0014402e520707882c85100c0100d2440d20001303411084075103070000a1031802005172038400d110782c00501085810765803426001c20b000d0655000d18040c2240144129610000001d807914140141c01d04 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 122469658 1250 122468408 122468431
    0x14040b0702011707080121020a090608010510050f0415030b01030b161d130207050105093702010e030a08070609200a03470c0a0804230f0f0105 63
    0x4d1102c000d802a00d420304452440365003580e84000540a502101b0b801070340250800020003010640010356000902503d0490f0020042e070b5035640c6080901c1d0505208070b031b40002c588903002c03600307082a400141e01d100b5409040d14071541c1d00d942d01850702401740e0043c2c0b0450189002d000d01c0c2d5500b45800440800185001080480d402c0d5000022204245000d481441007403504d20172280e568042e500c2c04d42e080b500810642c5402600e40307848070340d28484540c8220720800d54854841550324020002d45400d0401000c4c02040d500659924003c0300c83c0e50703454804c0e121601d00082206004100c254880c5002081400d02d074581300b149c1c0c50701e080410607120340e100d5a010050f22840310080413039406c80c0f02001100507400d080a044841500102036102450405660004000c41c40669a01107814010340c0380c2d5030b402c103030301e524060b62501a0000c0c00007008138000c91094024000b00880c2e045091403403000f2181c7c65480d02100d00c0c000003403074000300d0714072b400444c080c03107520745c481e00b00841c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 122470908 1250 122469658 122469661
    0x1a07080f01090b011e02011a06040602100b030102090303070303060f150507030804032604150605060a050a09320303030118020309010b1008040506100303051914040b07020117 77
    0x1802039002005001d01c0825039501ca4044a107a03104605900110300b1002e038880185140e404001d021b02005004011840483c3d034a0400d641843d5086800b01c4030309034090500b6400010030078002d49420041654590b40034801e0390311320358080c401000c449210361070000d10310f803820024002802d032a40c0507490020040f141c040005030058121000b1f542e140c034110400e507990b40303803d5a03801c41c004000c030180e0540484a0121620303080d0450301580c01451a20b0038254014510410b0760b6450041c59040b48040c88500260390046014011506281c01c0c81550640c130b038040e03d51013030040703024045041c1401810100c444445200b0f140e043c5000d802462456040014080898a4400a0851860780080012041e800c01c0d805294010001801030910183c2401e006200007415281541c1703e0040c1c0d004210741000108410b81100d0341600e50f241400c1c800e4116410720f4181590382824000b0b480a02c24409402000902c041c0221003651510380f4500d0000500c00b00d6940411122014601c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 122472158 1250 122470908 122470921
    0xe101113080706210f0618050a0501080a0f0f0501020a0302031906051c080c010204060e09150102100507030b15040915030206040909020a08031306030b0d0210030f0b0d1a0708 77
    0x2902142e448004041501c5215141102c1c0140b20005c1c450702d40c5450310101103582d01c202d28441c1505a15801b042c0880d40b00d0155400403900203205022155106616210000c0c20181a404040f80140c8c180034131201e00342c031000d003a0ba000c2149100026400800c00107041c0c1042c65401c01c10101100402410b81000d0100300c0541c01c0c000c4640203030385440700c01010401131034122500a00d205000f90345455a6007009010101d10700c8507648180c50030400100c40b880400c6100b03095100c160b00400b40c20038400e41d0b28000700800392000007096140c90380c0500c079441b034400f0803601c1009030040c40d80d1285800001e00840b8024020803039001000101040540d44d00e6050b00d0aa5001c1a000038600c0420320004010030b22562003150503020105c4c4d101031454082000d0006c958043e10107112901c04030017009040c404035074000f5031080c6602860006035119500c210a6500c00320f000040120140000030134000c034024084948880d021800810b074202070b60742c940c01c0300705410000d04605180 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 122473408 1250 122472158 122472167
    0xd12200a030f180b040f06030b060a05040603051003050a0308163b0a0f05190b07030e0111030f071e031202030403051b03090306010605030c040302040e101113080706 73
    0xc0000301d04010f40c2260164204101c1240340d001014042006941d4940c2c1d0580d5007425a214800e00700480d282900c90151410321034100c2e00c2c1c0380820780d200c0c2d20b81820070200342c0080001030541501d08000701c1d404000250100400e038078643c081d44400441d8503040c0c0d40c12000c940c54891714020007100e604070710500c680d40ca403000303001d01d040c00c1c02e00c0d40f090b00c2004d2181078841083c2d910b944800741c100c0c0001d4034001440c0301c0c010350740300b641c800200504106101100c40750600c545080c2d40400c2201001280c46410b03604114a0f05241072422515020020b07459908a95140341002c100041c4041c1000044250030803070505042400007124483d44014201c0a001460301840036000400242058491011183d0492100400c4091180701409583d640d41080e05001c1c064410f030130020500e540901c0a83e44520f0014428610382821036080c0005011484155030542c400c41d0000c0d940c0c10b0107400740680c144140b00d25141c4502803d54251090383c50744d4440c00054000c240148000d5511 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 122474658 1250 122473408 122473427
    0xb030f090f070317070b070f02120405131e061503050f0609010b0a0302040b03010f0602010b0d0b1302030309090f100e041a1906080706030b0604140f0d12200a03 71
    0x8110104c4010709085008042403250282c0100921446401c12110b143c1001001000341000d50841d2a5640341d002301504034400e81c09205e51003c0988240b0000d641160030540c2004069802c00c920501c01e44006426500e2540003000c024030004415910142d2521400d80c2c0f15402d1240d4000905044020403c4000d060045020a0400141c1541600d000350100d0700181400c490041c1d0301d6079100504031400240d4000c0d80010350070101014018540b048180c1d9440c0e0300404c03c0c040b2610f880000f04c00e030b2924028101d815000501011089a4400302180d10841c1701d40c0e0304c462240382c10707441c6204000550308064022105002440701082c003501d05444182c0305445e003c0d082d510f40419100041e5401e0001511306820020f0103c0c0306080418a0b00886110b502c0500c0032030790170300c2000ba99002e0780c094010000a0010554a5403508075546031385c3c0e06001d81441c044c2c001584401e151851050503040100e6403c080001202c820020740300140c01100010340000700060b600181780150 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 122475908 1250 122474658 122474663
    0x3082d010b0304020607051c030e030a0f0518030a060504020405090a0b060d060603050f1c03020a02030906030c071403030403080604090201170705090a0306050604060f1505160c0b030f090f0703 85
    0x80200c000f40442d120441161410740d000000c5804558102e00e82c5a83c14868044200001341420020030010000009844008880b602c07420400ca80f200c03000c4038590050301d4040391107900d8940e101d540d61010f03c04d03402000d002d07081c0400e4526082c018001501c6001e0102540e42c3d015a038442e0106140741c848a07000007007110303000346607511800c145c0701801c000d0308050064043c0810ac00c02c90b400020314420a624503104c0402c107024074200c140d08031f002d222401000340e082080200000d2030010000c60344504141c00c1d0904040c45912003400d04a1540141280703a400081840103260300120314a9211504507424400d0031012740c0000c15400c00d2100e100120740c12800800c10b03031405202070b10318001c0060702520041e81c1c1d07030500502600017994101d000303c0c80c0410129113100070305081420340303410481a00700400580e004840c103902100824413520158110380c0000380110b15624000c0802402054807410102c05043d66140080e0280801d0303400140c40403c02403000c24034800700e94 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 122477158 1250 122475908 122475929
    0x12120403030207050a0204050117011b0c0201030e1207080403030201060504020f0403330902090606030403090605130b0f0903010c0e030c040e010e1005010810140604050603011803082d01 82
    0x20072a141c105d00d40344000b10005c1d0310506120000c1240842c4010405041114000038001078601c202c500c0284143c203145c031000948000040e01c05940650003510032000e8150480e12990755800c030240c030a070001c19040310401c100140c00c0090650901032a00906000c6908611300f04800508420b0703481140f00081a142d4000e4003a081c5904800b0002c50040e13002c1c0104240c0311043d65030100801c60500101e202d06030301c01c04a600c5081010943e445250b140e00d03855903150900c20242c47c5908020940703086d54140690110b0300c815a50040d082c50300c039038500140c550707041908241c00e4030030000c4200304028030040d1201e815030700090f03180c0050400b500c00003010400007201034003520001300584402c0c41440c2d135400c41d89005a1041e0704988155007520300701d0320003050b4901982c454440846212071082c0c080b89640c5020703400150402002800081d02c01101d1a00a4044010510a0b0301164000003002031140261828281950000c0e10780324400c0800f40402045400c1070240d04d0345c01c2c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 122478408 1250 122477158 122477167
    0x30210050a0f120e013204020f2b0503072d030305060402040306050c0405030715170601052b0501080118120302070b0411030c0906010c020f0109090606080603121204030302 76
    0xb2a80103c00c25500040207103da00003040c1c149020361158500c80a58801241c03004965036030700803036a030007164000d020801243d49e200400c11800ca200320106054a400a5203c5030f0840d0240801d03034482c4140040c6840d0b50003410100340141111801210b07100c07055180c1e0035010072401d150501e40764181000281a1150000304c0c00901031034100a00301841e0405111440c2c4160004e04220303030086007150342d442d44400708109040340c03103030b00800070440350030f0b001103200c8400c0c40b003550002c41850824104100e06c41781000c2803021007105c00c0e44018185a43c4811500790007244d0250101500900480300d422007244802d10014201404006542003440310741072082c1c04644d000343e00034480000360b0500d0b04107020310312000318182c0d1107803081003800b080718245200080d110307050584440c1090702643d0240030b080e4044c440c0203410040d0000c0d001c24940c00500c2a40d020300902c0da544c944500e801028549440f514503034020b0f402c0740521100002110031040203a100b82e2500d000350301c8 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 122479658 1250 122478408 122478437
    0xe0a0303021e0f011a040501060e090c030a02090d060213320a03230c0415180e0106091d031305060a0203040b070b0618160c0228030210050a0f 63
    0x400ea0b002054404079420714501580e43d03511003000b0140c5c150219000c00030b590f42d45805a4071048003c980e1500547c2031000902c00600210213503a012480c140f026182c02003107000200c03030300d10101048844035408501103100d940200c26400140001c0c84a500520018424403000700c9081145541d46200517403c0354410348031145424000e55002c01040164400b4450303126440104c07400200383c0d4818040407819902d040d0080d6000210000000f0f015a820841d9100701900c90221a46226840342c4681d58542c00912542c0300800031802c00140c111910721486019441c3c2500c4003030558401d001d0814881000c0643d04221001140c006a40701d05098090b402d5011700e0340700075420440032030041c0a21004c1100207204010803900740c0d1200ca4400b560021441044d07419103100705450301d0b949460341c040c2d00035068031400244001c00d00c400d010195204182071401001d900c8021325030400842c200b440001152540030b06000b0309140c003404c80113205110316100c5a04002c07803810120715 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 122480908 1250 122479658 122479663
    0x4081903061802071703010f0302010c06141501030b04050f0105010305131202060709090e12090a17010b01031b0c020607020a030629010306080703060213080307030f0e0a0303021e 79
    0x2450032680b00c450000d07405035110001d401c01041a95803640b4403007004403102c2c1140c1101c2c1030351a281c030740280380307421600115040b40e28203108449150f84c07001c5040700fa0303502040c07003445810016424161018103100050948200c0c04c02039001d582010240403813a40801c9070541512000c0c07800144036135035540c1100e403d20007134401801c000480f014201c50070b45e001c01d10328856052600d40f049220750310140d050440d4014031407503a85404c5007072500354541c00c1c0002008010001020056010f07181c0c0c01d09652861703504402c5103269580c820010715542c041c05001004601d551404070440001c01d0041c0882d80c00000080c440d0400082a80031542e070070b4100e401640e0041c10401503c04058802c40d812400c0f4040d8441014480740031001a40c402e0160340c1c152204c00000e424400d10f956180ea010350440007005803401c4501c44041030240c010405408001d00a03501d0f0701510640343c101910740d02c110400140640045a0103102007a000140c8800011401c4564040b418a14805e02d0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 122482014 1106 122480908 122480921
    0x1606050a06140607031202040f0612050106032703050f0d09030e0312120907120302160f060507030818060108070302011d010c0f050102040305031204060c0804081903 73
    0x40024130038400d1201c03501c0d0760f0760b0150603d81c0300e00d26100c1503d03d03038101c0700000c0d92f00500519500500c1c0103e5004100c03c0c1070412058011541c00d21103a62409800d14010104100031760401d88510300703c948102d050784203a0344414000c107400c00500401c5e2403c1d00000c9050007644120f04e00070410300c503004405003d151a01c40d4100003074410580c01001a181402140300001c0d1841c908916801828400e5028040c0101d869000090030081da8200b00d40c202d5040300c05014040c2c004085806564140c01d00d8401c954401404800610480345030038241c0c020100000383d1841c000a88001740d03403003600c6107100d0b444c0007640240c04440e80305070940066401c6d03c0d0365001c10a0903228502940c0258000b515240c0c9a40700c5601d107034019010510135003034a10811060100d940b04000e0800c00d1361a00041c203041c981c4035207903a4050004d400740d50b94441d8941e50807441c001e90102 = true := by decide +kernel

theorem cover : BRFrame.Cov 122302158 122482014 := by
  have h0 := BRFrame.cov_init 122302158
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122302158 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 122302158 ≤ n) (h2 : n < 122482014) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
