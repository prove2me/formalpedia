-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0785
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:46:42.04631+00:00
-- url     : https://prove2.me/submissions/31455205-ec99-4c56-90f1-20990f206246

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 141007194 ≤ n < 141187050 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 141008444 1250 141007194 141007199
    0x6041503080318012304020108010923280204030b130b04120e0d0303090b070908100e010608030406020706020d18050d050c0301051512070303170a1e05150307 70
    0x8007002560703407188482d240740075640f2502807094090141407286520a0346001c608440b821040c124940c440c0d4000c1c0c840c240b5030390f43c44c1008001c46040080820080307401841400c40c89a40004850304403240c83d1315400c24030310031942c980d40b166030150340028080d4002010401c2200c03100708241c1c4500f181100b81044041d0361650090041e00510040144900082c4100e2460007243ea11440030b4010b000e60000744000d00e03018004002090301611000c2507000090813840c0b2910640d816144000c0c0980a0380013a074600e14054802100010455500d6040c00319500004001910040c19158010417034941791036800713070520428480c0c21041181071040c00c000054110184422641d0503180c405101c68181001ca0401c0784550420703a140d420441400340310301d8030b000450900c250458540104001c1c180c00181c0c0c55a1511000b004582151013079201034600180050b8088000000414961001e01c203000440001c00103219403030742e4800510007000351202100180600550080c9900c0c3e0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 141009694 1250 141008444 141008453
    0xa0e01050d0f0503160606090b0f060d0b0a120b071101020406050711010513090c02011d06010603110c070801020307110a02010801140105160b010302100f08010509060a03140606041503 81
    0x84005901501024402c2c0c4000e0412a040045844205440100c1d006a28043c601079010703080324480c440505042c40480f00d29450019003010b00003100600103440c080000c100400a088085032095202c841c20400042c007511002c400c1080c81d11401c55982941740020014101162101a5602e90380c81484103000c4160040121800c2c01d80106c100683c50740d000d40100c50383c1c4100e4034024810420040005625400303600400321540098000380050013042d45c1d400030308031045c007100c0c0841c4e110f400100007442c0240c1c005210003180c41d80c4c0c03524140c4a20301040ca0480c3c00d9011307100d581e5001040040b130f55400715a0b055404480c01c064034040b00e5940000f8110403043c0075500c0c0200c0c000e10241311070303070054049420340180444814501061820848604142480148c2c02034445070160910107104440351410321450303441d11429039023450144100509c000702000e41003e1512808408107880e41c000c2850412480002c0c806480c01e4014001030f943c00000c598006c00700c0010500001c0e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 141010944 1250 141009694 141009709
    0x3061b0c110603190207391206110a020709050f07120b2101060f1d04030e030a02060d0c27050103050a0f0e0a0605010b03010b09040203060f04060b090a0e0105 70
    0x58002c50b1103c0e102d07200d82c4001040c3c1c14000c201008114030001d1000c01f0014185084484e017031403611410740c41a5501d40380031103002c2c2c041501d109000c10703820604c61061340d0a04000814011000000e00b215296001d409030b07030282071100c0c007681c840c50b400c005020a902030b859015800318880380b01403d0208014103401c01c0d02800c455a0b44e260380700b4403810345406030150925440c00e240441000c40707400d5228000c19180c021211540c009801c0841c214042640c00310141510741c0c003030400c5503100c0d2421134400300d00c0e100f1582c6c0b5001c1e20380e803400582e0b100c03405020030003010a8002160429008042c059a4105c2d80300707684e2900840001c8c3c504c010f8003042e202152402c3c01c3c045100c1c0d41d0b40844500910801600c41403003454251030500707480780010741140d8103214405c208416601c1c0c88103442507010074401d00c210224100808801e0382055000355400000c0030b054202101c09820006040c5d9407150400d0300c00850110360042181390101e071070f0700100040c5060b143c45505180129401 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 141012194 1250 141010944 141010973
    0x703020a0c080c0c0a0605210405070303080a0b060f0418092604030807061508160603020901050702030f0606040b010804050606060f07060606031b021603021207030b0103061b0c 78
    0x80b020b0104084160b050280022110154010302240c0c031240c440b00054042e4001c2200828402e90303041040c0c001c21900d025260107160814010242031b442c542c3d088a601200400100005480e04190141900c0d900058001442d074003d501307894509201c40300ca02c900b020415196030300d0130000c880300441c200803000544511103000c19591001d01c400e0101c001d01c5280c1c0001c1c56102d001480704284550307540801a030102480441c6004d0f9030b10744010b56171f00d0503a1031042c41c010031003904025160007030340202805c0c14181030107030403e034890700000e06025a00d84003100981243c0100896483d00d481224a4a802402c10307050074100313603e81c82e56a80c0c0c0201441e0007050009941d2110031002801c2c3e90720207500180500c002a11058020080c003144c40d4050004109482200380250020030321030070402082e80c2c0188510702d15020888003014008004c22140507442000c000301c1d5038210088c0c040d5020b142e000c00c4810100d50855076080d8121250f00c20402029150303030010302c241562041 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 141013444 1250 141012194 141012203
    0xa14031308030603031c020705071d01090209010e0607110420040308030c07080301060903031206150305040618060203010e090d080703020f19080402030636010207050d05120703020a0c 81
    0xb1203544510202e441c51040b42074142560300c03000c40040c40911140c00503c00144500103461200340d86400c0110040c0320f4200014081c8803000040c0421505076014040c9144145081e4620340e0501340801c0c920b074040c000558405140070100060360805000384100c1000281340307140c401c016062201402e0089000040010030001f000c01c0740d4504120030349a180e6042082550349503520b40001d040c1409030300c002c502094041d800e600c001d0942d07104d144e0403550790340419005009506001c900600c001041141c1c084d941f0390640007071410840038890f12510401005075139506080100c04005401424441f00d40e00030901d044c03241e540b00028503046092400c015031102300c41d07100f1400754000c1e5085054501d401c1d10702540000c0c0c0c401500741c000c60080c1c054418a07106d084240c003080c00c1101a140c0254852035902da1900000c0c0401c018003010030b400141040866950b107070918804911000000e2400300345000780c0d042d010384442c0c10203040c0c14210f00d88000502c000d0001113443d4400741 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 141014694 1250 141013444 141013447
    0x20c15070204060905130b2202100c06110405010210060b04150e060304080304061d0d050a090b1216020307050601050409050c150d0e0601030f23060c0a14031308 71
    0x80440d201c5400c0b680c0031303004c080c20034841440c02038620440c0a418140139a1004124008114000300401e600c462000d40b0300303814011808580c003441450300c052903820003049400c8070780c50003040040c4034001c81340c8070100040e07986901d4800028a041000c9480b180c81c149030400401038080450115800c95510100c040303040494480151342d81510030604da60000c00000800003000ba02d00000e5118074400d01d410007440e0300760400b03880d43e516990300000c0c1907842000c822a5082c0204064601d00da285d1424103801c6450f02580c50f2283c200f15201040d03046401c040c048460103802c0c1d40c0c04003139134a01c002c40c00d00c4090f855441c2d80c1d07001845014000ea03982c4510b0f405000d818042c1300e4461002a00c9006a1030407001c16484a910401c0b640700007515102c1c1040c08610040780c058100ca422004940d0881c2898407400070b20003d420710b1004001030101585080c080c14410306104581072010340b40c80e245070b118090320260580181554025081040120500301d143d1410350702d540100049 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 141015944 1250 141014694 141014707
    0x405181e251a0705010204080616030504050a03031d160501081e0a05060402041508060405060a030201050702060906070b01080309010801090608030712050f1b0c010503010303020a080d090b0421020c15 88
    0x402c1203106000d005400740d4000200801c181c00700084c80b0b40214400348684205143c10300045044032025100140580c001020307110100e40301e42c100c00440e0080d000040140d41d03003402440d10303160602d0b81170701d1400001c1e071042240e984c1007907645038800ca0700445880201cac1300790300d10400140d006164001c540e6503940414050b499660698000c1c0c01c00300406080da0910b00005040c41008581d02482642000c0024691b4207215070f0341c030300b220f6060b11601d00b414599420402d6640003101d2041c2c0042042c040c50006c518103030155030081c0582e00240d82d982d08808001407152405070084002c02d4203041c010000610000110380e140d5070445104c18480c054034904855a1240450800540380040b601560611740300d078001c0008548841103480c0903101c00c00546441c082444041c001d40c106808403408120000300402e04560300c035400281401003982c880a54803030540301554074502d2811031150b544412106a2140d00003400144902250b0354000f6550501404512030003010201e0361 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 141017194 1250 141015944 141015989
    0xd06092007030f0c051e34030b04110303070812070302040501140d06260c040e0706110708011d0d03090809010f122f090d020405181e25 60
    0xc43c82d14503006048a806c0c3c0706032452280d69000c0e040d00b41d2503c8081d0410354001c102880007459a02d0003c000e1600c0030714515140c4408684008005555003036030080c40070b50705d0307070140020041c01d0b00c907901d0103480389500d902183c120741004152100b410310400c01802940e0b04111845001c005140007135a90310b222140c560060f01c2c46900c00700403044001e5141d5059400300002c480c1c5130303030080304a41344210080c00b040291026a0200b01140d0890082404010b10801565490b00000c50072200102e03a910412401c4550502c0170030170403030b4032542090400b8001d2100030310f04800c610781881000a5a21904414494070305401d0500c070151851010017030080107058014504500104100c008400c1ca01c2445001101c490124205040104c94000c660301d090303038405500030300480181942d503801d0000a05020703107800106640c501c6091020a41040021900b4081a85d800b09001a805a5915020711113200101c2c91004201140d0080c0c801d040309000c03584010462001490516413 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 141018444 1250 141017194 141017203
    0xe0a0b04090209043e061e070501020307030f0b0306010e070309050a120306170606100509030d09080d170604050601180f060801050402070203031b030d06092007030f0c05 75
    0x2002500102883d04100602610036050860043c09040e4070014070901907844220b07409004418180145440c1c03c004a800e0040c0540b204520200704a061300500724070b203004640245404a500c0e80d000010000c401d585801401d0241e4803018052241c0c80e20703500000e4644105005581c0c01214070030005400a210360081c2c4003450300036007034608848180c203283d081b160102e0341c42804a81004000a9001e0b4808000302400700c2d11400340c18a40c5400080200042c82c48501c0c0301004030900281e0500e0354217220350508075100341c0341c0c10b4009240108140c1456074030b03002031061052002d042d120103486010350719480399088400041d180d8070071005845407586c0d5440c5480c9001c00c600d000c5114a0008440f1042e11000d89449d5410380c1d07100100b100b68402c0c00c000079016001030040f4441c0d100600302003181d00c0f080c0300607242040e4003161040115445544600703650340d100c03600d01401d107080040100f9481d600b20019442c00700540c8010b0030200014651504012600c85040140b110a10 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 141019694 1250 141018444 141018461
    0x30606050702030a0f1e0c050906030c0d080d09080f07030f11030a0c05030d05190b100c0b04111207050f040902010c0b0901090b04030e0108060f1e2101020c070e010e0a0b04 76
    0x101b4080a0801428210080903a5005250048101c10007040d2180380000b10036500110052a1402c01e0311666a0310300d460308540f08010b407580e02d500105c0d0004141d000541081c074001202d2580700d5146040040010950942a80a0010790270b003640c0c0b04803012080362613440780742c207081c3c4880d107061422618520030400c0494882c1c3c606418000e040e8040900416030b443c1c1600103101c000028810408a1000315451f070002c102d221a02e500011442c41d071055006d405117660014065403603010440314484040c038880c45030000310060246203089800a0a07a100958040101380850b0340040e03d10000c0001c090301d0012848001030b1181c03400d400200c0c01545c003100700112400c0c04c0c9409041c07010040c00084c04501280005800790600400407040b41500903e04a4001840c1c86510740d0010854072244e00a01c40e08101c5210b030040040c042d40722510100016960450084041e0420656401103a507c1c07061b070004000b100f040070701441d0401002c0c50002020300020002400419090 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 141020944 1250 141019694 141019733
    0x606060901170f100f0b0406081504050f0a1a03120c03041203030b0a0506160b100f120308060d050c04050a02070f0f03020705100207032d0c0501030606050702030a0f 73
    0x4000f0003000d03110b0320f03c0c4a4024012021356880c0300d80c9503400703060740d60341500034000d03100e00520003001000d21600585811803c0324a0100c4500080d002203429200115910340780100c404060150b904038601c01c0b00c3c500381401c0013669a0741000c10001c0d07103031100480340d6200b01c500881d00c1d080502080c0b040b01d000b070841c404031854a201914002d0003030702a00346540c0c13142c40310240008031400d00e4401c0300c0701034051201c80301e0f500b4065507174540b4030000900009101c030314810f000320320303a8500721007603014040b0b410001c21810f0652070000e02c94240201094040c000d541014070000b500080c000c807008204542c08620341d515107604200a0158040103801164070101040a00c1700300361051309400e00990a0f42e00554407981070100704580c0590380001603011780004c1000c23501601561038900080540b101000032850380c2490713001000310381664a001c800308100295a014840c8800405031424902d040c40842c0d0006070b192420001d002c0c0030003000a95101c10802d01d1100c011070034009 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 141022194 1250 141020944 141020987
    0x30d020601031118070305090d0306030f170c0312160906050304140c0607030e01110c010905040f060306110417060c030a0513050706020a0c142409041a09060904050606060901 77
    0xc171750042c0640016036000550b0f000d19446021a00d120380200c0084d6a00001440a504001d91714144a042914007403940c248051016180c002c90030300003403045e01100301d0f01e603400341840700d03100000d810041402001d10207080d004220403070b003150680354043c2c2c005d85840401c004038aa094144546c881401da800400040d045d020140c101c8146800301d0030a17a2002c1d10070110641c9965150001d60099001c921581e00c208402d00d055044109540092180411060b56039a0b5540a440100c40e03400e00304880480d00780b020501c0c1ca1903034145091103800415060038161580016440042d0480d8142d6845400042c1c1803a0a4045000c1081c0c4c041c045480c09951004000d4132101410b00407285881c8404c80004c41c40d020710f1508030700d2071000303014007460021003090801081c0001c03a0305811010501c03020b01c142da41c43c4546250003551028107600c01c0100c404000c401c0030000c011900c00e00c20321042c00046100090030a6005109880090f51103e07004010380f0355041d100e9151180220 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 141023444 1250 141022194 141022201
    0x30c120a0302040f0e0702010507021f0905031905030f0c030411060703200f010f0207080904051009060e04060e1b010e0d0f06020c010b060703080703180609051b030d020601031118 79
    0xd0580d03054806d000550080080c1d0b11940b05c100d03210140e8409640003050034603490110b015580e0b0014000343d2143c8226442e1819800340708d1000032069581c040800d0011080111a000d080100c030361280492049178650318084c3d84100b900c0d4101c851242c081c0a000c40c01e042014018034030078080110300742e0018207103200c1401d201c0c4e0360040450f15616650802c2c030384c5d0207110020b0003a280d43c00c4e80141124200580d40d42844001c02005281c00110741c105100007406941344e01c5414058040c1c000d6040c0c1a02d030900300300081e04e04200d0010325030380c080b20155035458014422918a000246413501c4517841e000006007031035181500161010b4007240c0c8000030842d0303550049c0892074448001b4440e00d00d03500100140350103408405400f00f014003000a0205209601c071010a0545c2c100740040220300e0745070700040740d102c0c0500b2209540002410300c400d0310811700c04442038000300c00400070801d82c080025100d84061000038594405013109113981d40d540080c1c600109144075001c011481c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 141024694 1250 141023444 141023459
    0x60209041b030e0a0c050621130b0106210b0307090c03091208011503021e040602030d050a0203331c12020a1703090f0607050a030b03030c120a0302040f 67
    0x21024103a00c40481c2c5031900600300c00d90045664a030045e00024601c1d80e251928061011551043c2c00b00902d5038002001e089039500c10b0b00541d80640c0340c1c0c0302c0c0c00c1c040321201c0c0352660b103041781038000c101401f0348000b03c4801c080b9281c8030390354049140c0c82c0104d5815040004240303080c91680007021f00604000040002d10381c140d010380b0b80e503070060351a104248040e070404d07145642c0a009886038148a10104580140641c0040007001c1003400316820561700000d000000c0d8005402c0100103802c0040c1201c1d01855038040e664006c1c01103101149141404415101944100d2442424190b50340081020080d044c000d010044240541400690f541100078520171060060341110b0034006802c0c01850907200180d80d548640d807003104501400c400400d40c0e00240c000031708403080fa04c14102802c108090500c05107018015540320b1039111005d03802c3c00b6080e21b044003900781c020b038410b02011816010008098900e14030180125a0b03450f142d03501200a17125a07001030309580c00010002450a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 141025944 1250 141024694 141024731
    0x10908041e05090105010203030c031803120f180705041808040e0f090f030301030f0f0609060e010e0307080702040c050c070e07121b260f010f06020a08030408030406020904 76
    0x34a00a44001c0e507580c86408010071580c0a000b00e6005910602c000707008208044000e42d0002c3c0410041d900c40d108101101e851035102c100d505040c0c418010500c404618a10442a00841140f011014032602d2031031003940c4510ba0f100e070f640b086031180000174500704005014003401d0740100c0c000d562640c03100d2900515220030303518450b404040d080080d04c0d21b540403034245a1529003202031451070f482c64840025039030740040b0554070383c215203800000245c024030411400314410741c00443c4400c607208540f030071220341c11140d2501c0d8004003c0c003c00907032584100c0300a03542c1280c0000d405080700004403941d0080d03000d0706480e8482c3d580085100461401e1440c070908180d03440c1c41450490121100c16941c202c80050890068050b0bc4603007039006049040c0d4a820311100c80840020351712a10103121015a01c03201011200c0d03006100a61550780c0c40c101610207400180701d960711560383e0340b90611004201400101000c000f1030b0802007035404a4945031002481485100d041003000c20340c1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 141027194 1250 141025944 141025979
    0x60d020903070803040605090d030509090907050f030304060207090c02030c03070f0203101a011d04020a03140106052a0a020a080c1816080402041b0c121706040b010201090804 77
    0x9210340070b0001101c0c8800002c0350f0a65009a0320399003460503803001c0c001d0f000e4040ea0300310240102440462071540352040824130420045008003465031400060008800003102002c1c0660805c20040c00b805400041d01c208031850b00c40e0004210f841503608a086000380e07403e0201500001802c5020300c5403082514520900031010346030060b04090400007260420222002c4900754510840d0a960090b014441140700100d82d0b070050508400001c3d080341d00c840b1205010070b90740c6000455442e4220811030140c60582810b0345005d118000f129140c2110310b130340c2c5c5240781c00c1141e20903c0d40c00a010380c3c0401a800380000d0b055580752302c6401c0d120041900941e000390010b40c070002c400800e41415601444680c400c012072030003648001c40c0d80b0a0024000c1e80c21070345a66150b10000034042c04071020700c10542e9140000015842c1c00e25600c402c914000b020442d00020081200c10041c10264204030101d500003840e4a1000042c1e015040454001d4603401010800003280c041520000c0007 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 141028444 1250 141027194 141027199
    0x6080411060412020f0a03020402030109151d01050d050a05070b190306030809010c080c0a030504030201080906100b2a030a030e0105090706030b220b0f1c0303051005060d0209 77
    0x120440c02424841240194411001d11000085a01025042000c00c00b40b99820140540140a84170f07000720f03003030364000e9002e0300c1c1c0e00303985040100740100480c50007070240000606418061101c1c1d00f0484086030103028541c0325171f01d244000740800c00204081034002d548042680c0c059030f0b807400e0000311500000c41000030910203006d940f0795680700744950401d507a0310540b064101f5043c0c500454004c010031108403204030040199105040c810091146000d00c01d5450650b680c0c03e520004040e00350144c1404281c2d8002028401501464901c00064035074110f1500d40b81c0c47c5440c00040c01d88000c4000b58540280c0711907000c280b500110007400c5804560b20140100000c1c80c48240c201d0f4001c40300402c1681103031106000d018420740020b1407203240148045500485404070a0900c034201154610041d650044807105041c00d2040950000003100d02060442c0d1414500b1181c4a860034003d08069994002881194591090310042c1c04e001d4401e60f101e0000394184402513014000151 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 141029694 1250 141028444 141028463
    0x51903060f02041412060c0a020102130f141c030806010c0807030309110a0f05150903070f06080a020306030a0308220305030603100b011e030209041812141c15060804 73
    0x7042c1007019040c02c00042c10b10052500e683c5510201f40303540c000d020b28000b1075408120301000216461b5a13680a00110a243e1210510f4940314444242850040030b020724001c410504001c101c3d20300960b40982c060420071566a0340c0350049401c203d03250002403245a0220303140d403c0c90343c142e0004850b90710803c04011100b8a110070404101c94502c150316031303135010701d0080c012410440402c07603136881c806030201d080180c00d50000e41460b520760441340e11899914020064544e2107541c180d048505c0d03110440c40c5007054804280c40e43c82c241805070612800c400460030b0040c00c1292681c0310707a85045501000b4038180341c014480d82c000c0d5107291091080b0310041031050785a114031000154140c40303400d82006003001e50710341000341c901506d05155080c0850a415100c5004050302c04100300b610030070344401482c081c010a04100d01460800851070061b00e0501c03e44011036004204258405140c10070401082014242900015600800c065000150340b6044407426004512480304803 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 141030944 1250 141029694 141029729
    0x6030c0801090c0602061005120f010c0f020105060118050d020114040b0c06151c080d02030f061e01080105040b03070305030a080f0a090302060402010323250216051903060f0204 78
    0x1203071b80e5001035400503a00c4c0a080000c2040303281204100e000f5101c07510588400350402c0c002c0500712a940705005c40868021018802016070a2040e69800a42406c02c40c88225181080c20018401406000d01a008600d140403c0d6030049905c1c203825550b42c260103554544400c203c94068100141700083e40c41365101041120740d40c071203608003428010b01100450860f2a4122000d41c038004004c1d03401000810040c202903005000a40c85104030b501d0190083c01e2001c2030281d41e00e40022036888690310052801d4a60307a0191105045032030803200400d214411600003410400c140d800208580300004090780c2858000d0421886030740b050103942c4460395000000000d8514464006005810202c0001c2c01503010707510900d0174001030844004e2104410f246a640e070b540c250394100c03c840c0c69284020802e91001e2000501070341910141800f101e44200075a090321203800f415100d0284501140c0c650403041c29040025900f041d8240882c0422036001c2d0000e5110b07021312680358600302c844 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 141032194 1250 141030944 141030947
    0x130803130512030a05160602040f0e060d2114040f0e01080304060504050d031707020a05010510050d0212010e06070306091406060d05040302070b0a02070e010906081f06030c0801090c06 81
    0xc240b0319040091441d040d0300c2c40c4112043c0d0701c100c4040b0341c80c1d806025240003040c1c9a1010300701805200000d210040d0800c520b50b030341d0400040c16544248403c20f10070001807405021102c4d80304203810881040c43c0058010384000d0b0f40000c402c600c0da080800e0000743e50743d007440308504440064100c1201c998031200c00741d031a8170541c0192008a042008104414100385800072041e80c000d14014405a82d400d0540100d50300540381100142c0c480c003502400d0000030300c100d54220803507442c603000c8540b03000040703010080010342c068403900d48030617000401c10080d04201010f4256009640d580c0c43c3c40f190140c018401c2c1e0050701402072410312030100c564002c151050164000400d00c90919105444800180000801c11011800b812000080240c04940a400c8000c00b503005131940500344659030041a00590014948a08111040017660004101440e02c24101901c800c4600c16032071504d40a00150b610003400c04600c080c1c000fa8100c010f501031440d03d071080321a040c6941d43c4400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 141033444 1250 141032194 141032209
    0x111072001112d0307020604030b150405090607020609010e1f0608030307020307050d0f090e040c170a1e020123040b040b0d0e0111030c0a020106030203190302060f0103080403060b061308031305 85
    0xa40020007004240700ac08c0190704001d0380604c1c03508040414450000124003901c0b0280c0c2c0c04a00d5500101c2840403481d0103000d100d0780140020020825a42c0e60b091850380c13165451005964141942003900074590140c00c64070103402c4000c21a680d900300904000d51301d600c811410b070b90a0040303038a04e044c5d40348100101c2c0f064400b103688011807181442c54004651300301500448128000310400100078030014030203c2d001d10244007400405d519414066624080c2c9039107540024204102200141c0e004003601780e030414141d10305048120b0004004103544210b030801c2c20071100c0428001070701e0344507000130910840340710310600c11001100304041c00c1c4e51034440d0071880d409d410f100145890403864041d1132110098400820000d9503600400c1c1829400009240020405440b040515804009050300002c4000c1601450741c5180c071060041e003da400000c00041c5c441d5882c840b10350f1070701d05070303058440b00c012007030303020741e81d030081300b03039a036100760008040381e01500d000141500d0203e6 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 141034694 1250 141033444 141033457
    0x312020706020303340801140d0f0b040c030501090b1006021606050c01111204050610060f0503270706020c0d150207031b140111072001112d03 63
    0xb002181140c0300da05c00814101c0803035000602003240e0182d0030180c4001001110b095030030399241c8143c00e50511440c40d9a000034015068012070803068558002500039034500d4a881d0001040c03882a00d880c0f51a1000c202c503a40042c00941c02c150000e4240030100c00b443e40980d4560003406c0c00d0b160f403a0f01c16038130344407030350522070802c000c8007000c0100314066401444510142000047c40899442d25102c0a821a10a11a040d50100704000c1000002c114036500200c0e000c81d42e20324076281000080c100040d00100e503080040c088085176002080d071000d0f02d02a904642c10840f10f511400c50f442d610081032040c0300040c81440c031070480508000f0f120b00805070b00480304e000c0002c604041040658000503046041110131540d034201c02c9000040c3e000c0091140d07042d0110110014010b0f420f58192502103035061b0130400c03201d0005841036404281001031682c2c0341111601c0800141c9520160800240450158100c0701300485048008070981950000030002c85181044a4070340d41d00500 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 141035944 1250 141034694 141034697
    0x403050a020c040e0c150f0f032d1803040e070203030f06010e0d06110c06130308070311090f280306050f01030803040b1503010207031e030b0a060e01020f160312020706 74
    0x88081e40a5090404001b1801a0001e4140d8600300b108090b030003d0ba804281d404803070748004400d0007451b88840801e071980000c2c4c0041c914400b200d8840e8800d04180241c1090050b42d4406926506120306009440c002e04541b06500c07010320703116002030f40701e40c402c841419082025000040c020b40c0901080b4440e444040c0c0b405901c54450340d81d580090912200002c0001c005020011900004020040c80340f0030030004000100c03118603001e01801405441c5d2428141010080340c1d8195000040c2c2d024150122544004c00b04e0640203e01141d01251340d44c5002e40844001800d891041504182100d210307600403c013a0b1f64a903000e0282640c02e020091040c9001c00128010402a416490b042217500610320000118880000d0072070707104c8070781180031606080b07030300c405201c1801002c0d00203402400c003403015405000014445e18514007603041405503080c2c000c0c000d64420445c4a0501030200100c41130003014001400b440e8086200860306040d20303800f40d010b414030206a08080742d003030307 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 141037194 1250 141035944 141035953
    0x1110a050c040c050405030a030203040608070318060216060f021b0c03060f100e040c030b01090b0102070501050d0b090901020304020a1d01050f0f030319020d0306230a05090403050a020c040e 84
    0x81c0c00c02025100201142d0304000c03045c000411182d40504c070300e500c901d10a800469449142520180520100030201810f00d841c08030002e01d44c20b5800707070038521603511800060742d84002c61078004507101e010340050300366441c054060500140960007491101d0a60240c0611089840c2e852503803161501c2d00740c2d03007541144000c070302482550450150001112080d9245907500c40e20085020380085405407056405a101082409000318030030380035190a00090110b4000400041d5461440b8803509042003c002209120503580340d0040c11080e170024581886800e081e410b650103500240e40c2684a10022030300061845684000034a018030038a110790740681c40c100400c5620740380174045a800001c07803054104155400d0004080d18075180e1029903071051b20304030081c5482c148104640a03d03141000030f00440580e1040c140b00072008001034031880b0a5500882c0340e04500ea0300480e0010703540c3e01400100f58016000c0c156003a4158201c0d07a00300e03000000c0000741c42d1116900440380e040b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 141038444 1250 141037194 141037213
    0x70509070c0519030e031b091305030304120e0109050607261809010603050403230f030f0a06080c03031b010608011407171512120a0c0b10030c0e0907080304030c0501110a05 76
    0x600399003882d031251289c17440f03280c0c400c80703611043e007568004c880460301d40d038190050805075604100301034001602864001c074002e091902083c400d101c1c2d54005092000448a04a4200c3c4012600c0c0c4403e0b0f01081d10640362152448038464071403080407118401c0c0b8910002180e590f1092064901c6181c25946544603481920700764010489200025841d41e0000c0201200e4102e503a00158042c0404c1c4410b5680380c600150303007001704c0300180c00082280d08000108001c540c0c001080e502068283c440044244020f071a0b224010101c5501c10303003440d400c1000c01012115103050580c4601032603144e9040300042c2d80b00c82c10a04204459485054181586401c50b605101e1004843d2111440840d030f17049500c84044815a081003000e0700006614034500b0040022100c0841d40089941c840b00790781c1d5040d0b59030403a407441075003c0e4400810080300043d41d0035004118500082190b00240ca136520385038103150b507180d0b0a034092507000c40c8000d0105102081c00240300c0b441a500072000c0e100f1a0b8 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 141039694 1250 141038444 141038449
    0x31309140c1b03120406140103021516021305090f0d12020304110d050304050310090506040f02150409050a06050d0210120908030f1f08070509070c0519030e031b 71
    0x20400c1c6101c0c114892a1004402c0d00356080009042c02c4031000da07852410710345407911130244e8459440074441d5100c000c00400040e00d414004c2c0c0341e1508442d803a07079150401c0c10085c0940f03104506010b075110722846e00b9141a40d41d5a885540109803800648528070b9145800aa0b1001c032940d2180000b43c94100d0032590b861158091354119101350003210300445044c0020307414000510003503031a42c10024041049103010003180140f403103813280c18098110943c6400ba1600300081c00600380e50403013198101155980e00000c0e5803100800101c54130b0750b884440d00b0000304811121420708528100020880b440c00f603680c800c0c90b542c003c080c884064100d00f03046a0200c40c3c25281603205868506610000d41c8220103580700e122160800e10461401862000ca40e540b100d1210301000111b0741c0501003d04003241e04000da5500b610003413200d03103800c401129803106582c8007801c0f50141c60b42a0841c0a10281c0460440d40a55201000018040201901d0b2002741c0000d1110090601c0c98005a0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 141040944 1250 141039694 141039697
    0x503150406020f160c0504150b040302060306011b0f020f06040305030a0e0301020d18020307060318060209030a230d140a21020f0d061e06110c030f031309140c 70
    0x24000fa51003038100740304c0e40030a10180100c1202265080149041807115003090712428400d49104d851030010240380030800040d43c0720701e00001e4021880000041e4241e40660a5080080070340818408490001c3c10425003220035950304911075008102d41d20001c0c80c040307003030f50141da8100020703500c1c251800c142501c00206102109415540a205020448440f44a545c3c06c1111440c403002d60103290b80304060910507160480e02c189403034600700d1a8140c00640d00c046c0c000e0341c041070041e620b0801c0c0300000c4c034048060500402103c09000b0041250500d90403140d40c100c2d2072401c0b00c0ca031125040055520702105a00500641c00602155003000c0c4200fa03030300c002800c540380d4280d048c61010344c000d084c0c0e030240160380120b030000100b42051031074a21171440104403174500d51900c00b02c0f0204606942e040c0d8802c400030401110b0101c0c001d0340b001d100142d68131307000800f141c19009506d05400e4030790300004d000d0b42e2a09000350000400031028090041d40c6044008174444a0755009410f0015 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 141042194 1250 141040944 141040957
    0x10608070804060e0f0f0106090e0a020105030a0906020315100e031b01090b0a1709030901080103030804060b10080117030304210504080609011512020f1215011509050315040602 78
    0x3140d85030307035010360042c1c01401039010103046140a007a94206c0d090145003907a5090340500d0070b00d85005410440c0c0c81000c2010f04000c0d509103404c541d6521982841005464002c4000c0c00c4d05200109101c174042e1105a01d07500c04009851948190201e1a404e4540e1784100d10344680503041400642c0034180c01c8903c42803c0f403414101005919110004a500c0390020400500070455500c040003158403d2031282d030b40b103040c500040d454002d042c00000c004003410b00c4010f00340141d400c04941045044d41101d100c02c0d102919942c444104404010f20b841000c2c42a81340000c0e411103030326464680402101e204542001883c120260031511041d1058a6520144d08003c0107200200c0e403141c017445880c0c0610613280c004501c6048000b60054038101c0c2d5813202031880c4c000301c80000140c03908201e200315a0402c80d0b0350032010303454880305810099030500c40340c001140c04001191142d9000e1084ea029480c956426403202e4440007810754464000110b111030451280000700051802e80040c0388 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 141043444 1250 141042194 141042203
    0x5150711090c07051204060206090703120806150c0105061504030507030209060f060a081006090311040507140a080a200f091314040615050a0302060d02070206030f040501060608010608070804 84
    0x3d0301d01c82d80c130f5241c202441c00740404210b9400041c2000000c0e410031107203030401c815101500307002e882d551b00c00c01042e1b0159003134400d0240d9000000e0705540c0300c213103041310f008081030700780e0f500d12440424600a20b01141d14500c075101e01e84088001d02091000c1d1401c0c1ca500c03800a1059504507000c1142c049001061164030106940309400e0701d072940000b0301030b41c441c20303180d046080c103155650a5030045a42c00c82c40411a00040410124003000120010b4807401c0c1c1b070000351a2600b1504030b03000d4404c8101c5c0c4402d281c000a000d10584d500070001803013141c0b40f4004004880308841e00c005c410038100039038001c201d0144000d814a220101c010100c220005100c0d2541070b09450007081501d8501c07000103030700d41d8030900304014000c4030f018840c0c0d2407001a161104440c2031000066540c02c3c2400080d0140101084012a0f8802d0790f0444581c03a400138405903d038078003c01104840202110221141d509241001560500459040703041e01c3e460b841e40d00c0c3c01d80e035615045032071040042003134a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 141044694 1250 141043444 141043447
    0x503150604030803090601090209100f0207051f02060a0c05092707030501030b09070807270f0c0f03060308090f0402160b1f12030c081b01020405150711090c 69
    0x2a1a684034002040158407589500d622440c1940d4207a040100580c040504180100718180080d564650207109102c91070812003002014150201c1ca0020036811840d00542c2d101c1c0d0000c0e0f005102d861010a01a469080390181c2c6d48410001c1c054031883e40421000c40c3d4140301d8480300380342c18402604003c01885042444000c031030241e202c0c0000580d144000310741c2d940b00600c2402400c90743c40c0d50226124000700842481d14030850365408940c1301d1503604c085074156003001a07030001041c00f0100c1e10402c0034000021145070f410001c0100d10070000104290075011307a4802c1c082e000b1034048940181c00103052030204814419030741484c6211035800b66003000300031407109110040301587c600a0503e1202c9240c0001c4100e02a03d0701d0410381c0a485050748100300030624110240511903041c500b08801c29000d140c07000c0036014810000324110115405409800c20544c0034108440d800c0310800240f0015500840d002e10820201528401150756200c44506040c544980c0083c0c081002e203 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 141045944 1250 141044694 141044731
    0xe100e0d1a01090612020904120302070f050c0a0e090607120603021f0e12031909030b04050c0a170c0409020f03030a08160305060607030f090509040305070b070e0d030503 75
    0x3802148044044040710340c0701d080040c030206441d40718071400340007108100e1403228903d4000480c140401040105030701d1a0b101c940742240d200c1d806664a69911030160030700e4450707610b405910381024620300c5004060b15540015841d00c00c00c1c1c0180108400e0002d0b01803034a429500311072062028401400721500c9010000044c3c81d01e5480c0c400707103a50b43c1001e2180742d80d641c034024401507280e900741d80b150b2032085040c040c1100100484019000400001c071b0307815000c1c5000e9400004542c0080d0208401c101000140000892010b1101c1000c50700320880d95210800c1c0c0383c125011400b0b42c441c50f13000c0100c1100c90706050f400240320500090500c14003401702d800180c5540c0c0468001b80001ea105000e0060118150945941d031030801c3c00c05104030f2900401044a600501c04080c0411070b40384804090a400f804c400b02c00b40c480074124110034030300b80c10080e2450740211411200c1d12100000030b466148a040c5103008100f00505200c03580d000780e181202d10f500060301210591032100350b01c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 141047194 1250 141045944 141045953
    0xd060806061e010813020627030c1002032502060f030f0702012c010f021c0b030a0206070f080403050607081e0903030a020a05040504060f0303090603110d020711030615100e100e0d 79
    0x1110408c100f11009080321729582000e250410000c088524003900061404207051900401074524062286008120000d440c010681c200c6560080c041c1d005400016484070178440e046c000c41c402e001851070381f070140c1c4421400b00d00322105050548101c03801c000c1012445220620f40c0c0078040106400419201c04540300017040342c1c040702d9810904e003903881e080c06041001e80525180b244040703001d031079076205daa00414664402e81c88003e0080e0500843c040c2007203161415240610340044c1202c1051038400301c098440e980556601e88001c1d075500364100000101400d0354400c4014070040c0d410340c1c64100c030b40c001a4001a4004050100034000410700b612144102c01c020601006039030340442c41c0d4100500012002e420400c1094180f03403c2c00014140d04040715191145030100590740c0070a414100200800e02c10400c0d0b05000341418800001000c080088041404848022208120850584103d9141c1060f00e41260020b0312013000c0e5409103282072500c51014140004200301640d9 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 141048444 1250 141047194 141047227
    0x1d390306040e010e06160c1509080c01020c0109140a03172a0904050108030a05030412110d0305010e090c0315090106030218040309091e0b01050d060806061e0108130206 74
    0x2041d9071741e02c00030802504915000089895191609040304041d820b80c03111241d506104003203104c900d84509a0104000c0460308880110f420200215101c1c007503222164082c1444880c156074007134420030794000b00c1001007132418480b581a10340c1801d40c00200541c40303d02200a00d4040d050000c24200380420241c1c000c00f075403036481045080d659144200c1080f080b140103800845450b44240300941006e9084000c494019802004503c00b0303181d03510044139544890310a0b518035000d000b0180740683d405400150603940011034580e1959500e01410f0740c0d88032038802c03043e0303d61b00001041d019541c0c034418040e004a03030000007080894580d00410000001c006600d84060000c0c0e0800050642c4814110007500c0b01c4030062045000020b194103510003031103400c8032015511045100d560303004e9002c8444412243ca4144085c9984071a030076191441103c115024140740c0311030440040088070100c1d06400140c45111480d140c540021601000681003207800110402026070580071034a07 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 141049694 1250 141048444 141048461
    0x908101b05030601211b030903030c1103120606040b07050a06061202060a031a09090d02010b06251103030304060b01030c0806090a0b0102071d390306040e01 69
    0x500105003285220910300300c00ca40840e40c40c04000040c400d12455a034032000758008444003032083c881076403031044003d000340602c0060054040100d00004409501604401030031030090710200706000c1200f005030354075640c11505000300d810820081700004c0760340303100e5600490701030300050805481c3e40c6401d00d20f5002c2c00095800741d003c141c42000300245400f9000182014041d030b800525055800710f071a82c0074a120000500d92141d61014000700a0004ca150041000703000d00702c217080050446455402880c102e030015424002c40031a1810303c2002c440301511030243d00460325040d42c0e411015203050b00b00031202000c46440392100e81d6010405180194015000010400201000502161580d4041c0e00c20711078000b04002c11640d070300020f42c0d80415402004641500502c2c0101e042100f2a04900d1102281920301841a100c05180c1407041056030411b4040380e03002181c06175185024516034a0b40d00350490511898220341001e15000b50001d0408141401c0300d840b01c90135910400c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 141050944 1250 141049694 141049723
    0x36030605010315091104050903090a030c0504110f0a050c070801050a0f1b020a1b0b0d0207050c01090f090c0c0f120905040c090504091a010b0301050a140117070908 72
    0x540c0103205000001e418a140d81445240402c407011403940e40c010741c200c034100040d1003203a1f0f0f440059034511080c42104c1d02850300a0200c0881c5440c1c0c5095800036010740900703401586008080304030064440c080b07405140820a0b45400e103400640c046175103611041c18412140149c2c0b00005455800340107590058008450103e545003081d8602c80c1160210740c00090042a40c4526447c02a00880c00040140d0040404582c02c00f00500703000d602078495010708410000040d8810b0700403601d81c064100720b442007040e01c0f1810b0181004407603400090080c1e0201c03020860042085000503404028091501c0c2032046040140303480e21003a006060f00c065400700140c02020001503405100d5401a04d01111f0800000d40000801081400503000340e5008640d10328010090104130002d2201c080750403010122150f858910080d01c40e0005e01c900c41c01001c100001190f00b40400e032440c00784070410380d558451152a940380840d41c2c4005845542400001c4001060400d0144141c8540c00e907030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 141052194 1250 141050944 141050951
    0xf0506010b04060f050a0e09040615060e0a0f050a2c0108150a0203010b2703030a1805010903080703031e110711040501082e05040c150c03360306 64
    0x800324084c00740082c410041c02000010060111030310f802c840d1300340c082007081e104c04109a407240b401c000100091401e0a04020110f0000150694031101c039004010f016660b510b1103907605c422070b403000462400b03055880b100d10365081c400070289d44000900c510300060303800300000d1072041c2407044540a0f00f1041c84c1e034100001480c0740c26006025140c001c4503000085107907615104100401b0b0048150301403507140f010001c0000000c08903883e41e040d120041c04d4954071810f448002d4400c400040b034070820315040010000d02c2d58002e0905404881d088240355180c86090390b011001003403005032110015004042e20b0001011520540008900100100356909518101702d0070707250b024524984141e003040014058030b1404030f8008145040d0454241012105c00c00300541c0900031401c4030001413521082006205800c012001203802d1200001581d10080900300c51f5900000e802801155161004030101034495428644001c11880605221081008000e213800c4a43c0c3c0141c601c1303030700d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 141053444 1250 141052194 141052199
    0x6050c03060306100e0a020901020f0601090209190302031009060e0f031b0f03160317040b0403030e03070b010509090a140304081608060c0706091e05010b060a09050603040f0506010b04 81
    0x2e00300081038114000001001c482c3d4a48031114181c03c60040c40503c50750340120f46040240d008102c482e0501000ba000e850302903840707040007c000c0d04000300c4284a00d480320030041442004141c2c603002d0307039000f81c040c040d1380d0b41c8402e040c00500500300301268520ba548a8003103003c50107205c0b000c42000707070001542d43c032001d500300810303001d80520204c3d03601d4104810420801800004481d1a60402e8107000d5a0410700e0906a44e00c0e0500e5a180c150040301e0340420042080709003001c1e00c00c40c440d44041001d000d00c0e00882d540c03030180c0c200003422030105c2e90041c0700341d142c403204850b40100003004070798070305d80b141d03030384401040c1c00103080d841780d038004141404080818004125500910004c021040780380401c102d5560601070005c03243c44800240e114244265074120385851900b15405880d50703400e102d1320740409e04154070180c40c55441c0c00c18601d02c1d4504030741100c40042039a9a44001036050404001c103a5002400032200340c0c0c04410f0483c0042ca040c0304040c000c0007070b108503603140d52 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 141054694 1250 141053444 141053449
    0x30209090114060a271103040503070b07080103020120030d0e0313170d051e07030206070f050405060a081e04031107050301060b030f060103150b18040b010915050706050c0306 77
    0x810160101d0704c145a00141800584651817a00400c246448800d41d10058641070010080107a01c0740030340740034000001c000522100200806600d48942c12869481c0c2d1901011140f88800f8003000b40010020801d418661103140c1c001d000182d551019207240152000229048407448003c103480758001169a152141030254241c005080c0034881d50034400303000c1e41403620b60402d481d01c0e4040c0000071643c5c0241c20070340c01003030b21881c0300c00b08170564900303080c18065601d8508580503000074140900c0ec00c00170348540280c80c00c507000603150714246240301030290751800005015206030f210303c07005403c054400149980c02680292604a000d404040c0454149605a000640680e0402c0e1042043d101f001088030b034811004001c00b5101c0d1210b200480160503100c0c40e000064204010104025510000800118244e07111415400050030b0031311058680c01c00b026800b040c60010b003040f0810310a084040001d525103019887d04016648101c00c80d40c05540721140f6550200400a960 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 141055944 1250 141054694 141054731
    0x180b03010e07170c0f0105270306040f120e0102030a0507080f0403060e0d080411120a170d15050f09130f0c06080604050f060f12060a020d0c05030403020a0305130302090901 76
    0x30829140e80c96072444950000e0031a1007035a0354940423103500007a1221b01003240c0b205806102004081d1000350901d0700700801c008000042c25581240368030078451303142e0701030f074401e110040068018508110409000f40e5958000c80d1013528002c1382084100c942811740802000507501c6030b5400500000c80720101031910200030148800d1041c0c00c0144130114110801c020a6000102e40025a41c5a18a60740b03040c600303e00402024400314a4624561142c180050081483c04090800002200e0f028000004042e481001c1c0c224a010054405509000406a6002040314103403003080c4504c3d66048001510031000750b941580b00036080c00440e0b800150701c2e800081c1101c0902c0a41007402048100c0440689001c0c402c0408082d2003156491b021001c0aa02a000060b40c19619119004801039880b040b002d411041c5413003c640c1102c0d01960070713640290341650040c540c1a103590303400e49903540040311800b1220034214000005907030380c244213445400d01400204500480300ca600140 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 141057194 1250 141055944 141055963
    0x504050a0603170304030e061e070b0105010e15030a0c050c03070c1806030b06040e010e011d0601080708060109050c040513091a130206070206190c030f09180b03010e0717 75
    0xc80e50130014440441d034080301c43d0304601c0040b22815540d801d1442d10108141e010f0300d52070040e08011826400344a10820a00e04a130001c1c2c07111000c81040600300544482c181d004015520414400b0408500a0340d00c001c6099401d800d0040c60610000310700380c036640140b9403c9500040c1544240301c000c00f0301003040b80b019000501072209506594502005560041415025594070b034071400c40b0a5003500282100758081c0000c1001412042c2c10002214040c0002d020511408000046400d40020300307000700c0d241c00c1d020344178036428000c0e80409010003409010b2050002d02000c2810383d10403049604a844001001410400c0e80c0703820142c4141854080301810180c0781040310781041c2c0d128038902d660341101e15940e140c440c0c0c400240140a8001c2c4841e942000080700d503000c0741c1080310400c0c200e009448824105580140031282100070b40240007080d00e0141c1e00803180e201513049140a1000200003184101c81c10100c0d40c0b4198550703102d254408550207441d00020000d000ba00c10 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 141058444 1250 141057194 141057233
    0x9030a020d0e0d14100e0132041e06111c0c02030306040c05130602060105090a0507022d150712093201020a030207020a08010e060a020a090504050a0603 67
    0xb0700070300c1c2000103000b0070070f109010b003080c01c1d440c440103442c4800380078034112680c0c00e12041081020043c4624001d2081000541d840d1800303040340c0a20316040003003d0710401e12503201d48515602d542d0f40d43c040c000a5141d801200c007014000f10b0000d4024012184030b10300c0c540d01280c45202c02d5078006a00310511108812041c903040343c5e01d900d582d010044035800442170314003181203004000121114420041400d44441c60032401140c001e601140791412074204071404c02c05519a081c181c0100c1d00181d40141c0540e0101e40300c41120002121440307165548076003114075000640100718100368001c00200c0c0304031450302c10804e407150000b40900007081c1d290410080190f0a98030049924610141b1100c0000312a4020b4800c140990483c820000400b0083d074a800000324040e000e5003100908a00c6058812030100d200c0ca4144100101c004c00b1000620040c0c841340000c41c02948110386500402080303501c0490795407598001c950082d00710010000342e061440c00c1c101038104021440e01e9 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 141059694 1250 141058444 141058457
    0x1805090601080115020a0f06050403020105070512010302040504031202030a0b031608030d0207061104120c050603071706031905060417030709030809010513060e0f10020d030203180609030a020d 85
    0x8030503684010814151441c01c54008440b400e072040503803074500424002001e030082069260100110354120300d000b548250001d111070340315210309441d54011285a91051454400100302510b4942c001a070014001d081120040c00e00300b040c075042c1c1e841190440d016640350b407555000390400304400d2072040c031030002c80c0c0c2030241000c1800e5168494585604203180c1c02044000174404039030b1101c107840c1c0b012081350750340307640d0b850084100d516200d40c00e40700816011400103550030903108403403045a480d602d5115141c60101401d0503500b01030184d5030144141242c3d14180511681c0c02c03181380d40510300400c01d82c540391604810012a140c84000c50302d800f80180210150003448480c1038a034865096a2a021607100407510750041c0c40b00039100c0300c030100c070018240d80c100c20312440203032013503800055541c0f20b90144266423481100d0302c0010f034010700043c0207141c0b0130f5001d140c11201e8441c8c03c42c2c985548250b8030303240c81000d860810440d000058030b00314a81d010841c683c5582000d0804c01e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 141060944 1250 141059694 141059701
    0x507050720040509071e05010e01080a060317180f0315070c061e0b0405010f0b130b0a02010203102723070207060e0301020f1b120703180509 62
    0x40950260100c02007107012485444520004007890104034500d014004000ea0f10b040090607545200c10b1051860308644a145c00450111552000080d2041a19082800c02e40300c001104c5000000f041c1c03210403030382c440010001542960440b10800b84001407103441f00e0701450501c0c1c5003621040214820a0801c0c80380129071000b0035899012000710322440041d0707580100130354085501010040250389011410782c0580b40c20410004681280c0d001004405004c03028041103400c2130007400ca00c00c04140081110402a00090101800c900d40c20344103195100d480250b04c1d005070701c6407409030350048204100980c154200d40000c00d482502003950503d08400390207a0000d0020b403034000c41d1240204480e100c0d00b011841c080000e100388424162401910003912141c0764007409001602c01031490301185014001c1c1c13a807089041e20f00740c1ca0a4002c101106014021441554980c0a400682ca4050f0203000240504c18003e40700d28000318016a07c162401242e40c004030b105007102d81c1031 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 141062194 1250 141060944 141060947
    0xa030b060301140f0d0b090d0e04050f06060c1204030c050f0a0b0747010f0503060c13050919050109020406021518031b01050a050105100e0a05090a05070e040507 71
    0x6205185050351480c50b001d1301c0401081d040702200b400581210b90413014040c0300000062095090001c544e00ca2609241c0d0004220684406941f2601e0b2800c41c800468410b01d0304034000c0c030300440554201c41d800e0003061168500d03904540e200760f50344401c1840421042c03c0c10615604400e01c1128a01d00090902e01c1080d072500aa102c05454050b40035075040c10a41c1d102175a856007082c400b107111041001510301c2c8805500c041c0c5c0d1600c05151440002558681d0700c0b18641a900c00030007030065943d50100115a0360081c1202a221040512002580f074590300b035618041c10340d000401c414003407100501d00640f072041e884010036510410040004c140d0100351700c10b241090020284603500c407641c0c1001211113009140840c1d004c0025802510001041c424002000c648020f11581e521301e020082100d1303091042c44d4000600030b1030140683e02c03409082c214a1402010055415281c5010907454401120b01041003540d40c814030800507040041070360203000442e000c2c090762600050 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 141063444 1250 141062194 141062219
    0x8030304120c20040f05091b0402040e07110106051813330608010516050a030e030a0309140a020f121c08041b0f06050328020a030b060301 61
    0x64203001c1c0725041d04005900c66822503020070380008081e100340022929200b410074003000744038443c0c0e10f400900300c01c1c859203020303c9200b1041c10001e00011001c6102421000b511583c8041e40198208400708199440e0204613008295540c2c51058114080142030f0854a0b0358012030b104500c070703407542286d00c070356446d11541c41400d0440740c020520040c90071101c90300030410020125011000b00e04105594408818a006642031040c0625039407440800d003216416141c840d040c000c83c041822100c0d010748010144500c0a14000900c6502603800324119080002032400181c0c589a01c0001d1008140c50881e0300361480c00a00300031031070f0b80e00141c0c81004920040b806081c807030500405030b00c000c2c4008000c20540d4001106041882c600040031440111000c5519019000007070400000000f074101c1504c02200300380840c60b0415006950b2038100030190140240d4084003509408510200603040220503040542c40f130b4030104010b001c2d203800f803201310300500301800108280c1c0e0340941e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 141064694 1250 141063444 141063451
    0x9051305160f0c0501050903250803010e221209090c0f031a0d0807020312040b070b0a06050319030305090127050c062205040b0904061a1801050a0906080303 69
    0x14006501403909100b070f1070006114101401e154680350400c1a00356010004002c001d2580d01020a0072036a0702054211140020018210f0394013440103020000e41400080c2e040041601b504c039444000c0304910003881c44900e801c403103206485185514554200e41074002070f2000090a000c094900d0303000070201801e61005100301a1030300001c00c1544507451200da10080007800c201c02001460902d07500c0303941701c581c08034001c1c49a4100c916001c0416400d0700c0507200d020309810f18081e8940c84000001d01c0103044c0e00c1f1101c0d950348001419503001c1244c0c54803030a220b21004c4042210b400c0c00703030450300024900b00c1d842c0d040c80a0720540d5048402400d003488140c0c2c9407070301c404500c1e091a9207003140d00203603140c2220300002d88a511b210201210740b001415410001c1419441d0800e0106441324403002e25003107240c44011900043e01c0350450100d20981d03100410807540031000288685404050141c91500540014480340c1000ca200c00301401d00c50034103000d814903007401ca5980c1d22009 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 141065944 1250 141064694 141064697
    0x30f04020d03050c0139080109020705100609050610030c1709160f1e0501050301030605061311040806060306040305030c0a030b0d030509040c0c020f0d06020c0d0905130516 76
    0x16a0301c901010700800c16100f10800b984000c0200c41403098484000703840e0300e04103610301d2090030f00244d2024407940200b00c1e0200300307a0303404009900c1c0180d114040e42002e402241d090080504403001c0070080d204210042c04441d401040e0390811000f030050507600d00304040b00301424070300540034080c1c100c828000c0741031802118410a5456406c5c0504203080c1103410045c48540100c002054220718501000f91031030080542c51451240154840700c0700c0130300c2000c0c0400c00500040000c03922561242e548904040c100035400d481c4207071240102c07080001c1405d01c11101080602400310100300310340e0b20400030b6000f0007441c2000d49002e04140402031912078812000600035007034511a80240175841401f409548141070345281c0540143c002c2c0c00071a00a07494403088017030451040d02032024184e0060142c1c0c04a500f1142030160201120078180e071b443e2740810200c404244100480c00b00d2000e00c0d0754001442d4180740030000743c61942d9104140049c1080203000302924800340c1020380316800d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 141067194 1250 141065944 141065959
    0x501020613032003030115050c0a03050708090405010303032301121b030c060f0806090402280f0306020a0e0105070c140114130807051c02131b0201060501080a02030f0402 75
    0x6901d0121034200c042d03549102d0f03985040c4150004040e002010314142d91584081808095070b090088a0341e0203011005842c581c031200025001c00d0040c4004d010b15401030783d820341390805407400325003a20800ea1046000a9440492a0f203c0b120581b280341100c0c0114280780f055454140040c41b0344c20320480c003602e240c48140d4011400c0c0310703c100c15002103901002c84220345a5600000d0010a1900c10350030200b00c00b100000c11902d014640117114580c001c0600010207000540b40c021074120300d000480f46510320102051500b040c0e121100254030035a000741e65040400e20050107108400c40f035a060000611800740050000401d50056030224003007400000344060040301c0310802c00d4506c419800c000944440b142042c0640402612107842c00c03210100d50328003d101c02c440c1c4e0205030f0b0030300030040711080e4010710788241610b920010b41d02c000304100d446d91501c030002244210603000940c1d9141008c0220b5600661000e61000d66410300718151704e00400003408500d40188000e202d50301 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 141068444 1250 141067194 141067231
    0x161a120c040509010303030506010215040b19270203070501020304050a030b06040b04020a0c21053c0304120905090a05040303090c08070509060a151805030316031805010206 76
    0x49034000d032801000024480d01c055650380c18042e009100a658140c0180905400740509441c4000030502803075011510070130b40e5540b40400213a0381ea000c0424411030f92601c0000c040300e011170f14a110003a000144100b6004898410146413a02035408079040d504280010419565000d49401c112a049808004141d5980000074020891110a15445031001c59030325802c0c1d900c00810760845204484240c5002004400a4241c0c00c05d2145000040c0c42000540c41c0303100025480c83c03041d0b2134200d8000b80b45100c1501e4170381c84040048100b0084038044200014049000c400b080c503020b2900b803001c54903003404045000d40d800103104004607504e030404501098071a600c07032545103400001e105070498541c80d149448003040d1140d107220f03d00101c0131031070174500100c904048641302414003804000c8c028040d2502006003d024500c0c8054440009440d02d050009081101360010310000c0d1380031528001d406003180104554201a4030344040c882660000381d4507070008124280207103040ca = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 141069694 1250 141068444 141068461
    0xa0216050a17030c010c0806040f0605100c030c021807180803040e0c090a081e0f0a03111c02030d0e03090f041104180e0d0c050c0607060608030309161a12 68
    0x460301c00540f13000c1d841c1a41c809030702d41d400800940900c0e400c69050215840c00a03030304040d40c000340589540400e41350b0f07012900d036010301d50844e0350920034102003040c8203a40c0c000403440d580328035007070034902d00001c10802c400f41d210042081c0c4800018803803800c942005680c1d07a0b80d001e03070302480d90740f80c4503040032a00c040110400d8500c00d0000814202c040364407180c110383c440c144004804c0325800204d88a4980000c04100e86022a803601c00900e0b484400791821603403400302c3c00d4100024002c40c2c003860308207041440105003008031500107555411025100c030b401c8a200102008041e002031006c60003540d01c0044101601744220380204400500c0701400300a84116402003d00200600c2c0c04541d6140035004202c050307555078244c0c1d1506080700c40c2503e0204c078201c801010303a04031030380d41c030010f00d00300029020311805914009212500c0780d01161075070740103507a2009503600040315803040c40440c040701c41c00b0f071990380c07050400282d00d8512541c090041d0300107030080104c0d500009113080c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 141070944 1250 141069694 141069697
    0x130c0537050415090606020d0512060d050d03060305060f060d06050a0e010905010f1a03100504050a0c0602010518010219030203060d02060a0c0c05040209180402011e02030a0216050a1703 82
    0x61000030003c2100028110100c202c4810b28810102d500e402c11200041c59400403134810400070458036078518140c00c2d003600d4500100c00074805a4014071003c0303801c001c9a0100180c15140e09943c4000a00e83e0031800d06518160000b1301d0f001070042100108030154582c2e0001c207060035030100300403030246c40e2100900d01030140005174545940ca008482001d01c10150010082421856402c100b5100c24001020700030b54040f00300303509a88200d181c100400c007942e0140d81e20900880a40d08030200e15550305c006200383d0307071180300140c2d190000c0c0103681000015181c51020284c00844c64841240101401c68031505190002e056000c00002c1903a201d1247d400301c016802411716682d00c0c10014083c107501000842601c460300285004181410302d80708031550000c00506e005000d104032100c00900c0c90005204a0420503041841c148010310b0040c040c1c0d040516401554686a20204c000d141c440c40094943c0c0582940310100156103030071000c0002c1d103003d2021006a805080040c1740b65 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 141072194 1250 141070944 141070949
    0x5010b0a0c02041d07030c050604140d060212010311030f0604120c050c0402030406020a140705060402060a030213030b07030b0108010302090c0a0203130806040c060c03080c1e03130c0537 82
    0x203105440c0440c0c1d04d50741000c9040800d0b030388510b510b08001c584660074080d01c0d0089004444d9021900407482c0070514100d011404020300c01c0b01c0143c0317025581c01c5502200b03003007030f40111900181c41c0c01405180c40c060101050549512000b0081440e168940c2d0681c020b02180c3c040c02d03c03c1d80881d010a0100c00d01100101c0301d40030f00259035a05140c64600d0095105507469030002d1015801144500c404070308540000d6000402800309844540820480d81d000030a000149a42007001c40302110030003900f100114090f402240540c0750a0300050300f80c032260b501003810405200300500050340d4803c4081d80107007100507203d46941d03101c1c005920b107128514180c14526440c410020380712400042c0300d486642b1445c0714590484c0d548000741c60011803100c0041c081003910000841c1500300c10040c00306860b141c0d100408001c02001541119030080d1001d00c0a511541203110503c80399481d081c00400007503840d1002000d400e040900080c1042c8891b5101181020146140b0104169035802 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 141073444 1250 141072194 141072221
    0x1709010609090c0611060f0f1302030d020601080606040908030a0902150403060c0e100f030504111008010302150a1b02030109210206160f0e0a0801050705070507080105010b0a0c0204 80
    0x30411900f040c06416445100da400098100032081a9804c800b06540b4000c0d064000c2d4410341762030b01c1c803040710540002840925283d4181000c4809640e0400180c8240c0105070041d210350b50401805d1401c0c48401040c141c0190b00340416000000c400030f0840c0e51200701100001303500501741c070001e401c90b00100c845083c0c5070b0000c20040140685030740708660200050322017400700000720341031001280e07400140c400410000c0900c00d00c2140a41c101940c481e219481040014054100041c40001401c84c0b035800035050400501c110704110740300101400d5590300c2a07041c40d020020041068600f880203903c104441106e90003191425000201103a80c007a025046018811303442c003592000135031190005100d0386001c62807052422080808200d129070b940760003445000020b0b200c482d51080e00d03d4021629940c001000c00f401e00c100741c011381460b502c85943d420720b03040c00c928111281c1c00900d07107649410700401a80c031490003100c5014403141800b51540055000050007440314024500 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 141074694 1250 141073444 141073451
    0x6090a050a0f1503110703030b0d0803190e19021003060e160e040509070b0a020a120504080d031104030b0618041b0e100306090507180b0406090209011709010609 71
    0x2040e45441c841c0e00e068075500346020340500c050b842c04405603002000300300c04d0700001b0000701d40800e00c03135044280b80b00c40190a58034280010f686035200307507008540f100311148905517103071004803d50080110601d2004000d0000c0204048024130122030000001d00c95a41400b1101e89140a508100e00414079401440124941108141c000c03c6201c160907000503003a446a218900d0144140760180300101d00500340d850504800309042d5010b001d03402d040d44141101180000d4805064041c444401d50f84d00340c44a00c1d2006951400340c0011101d0249170a040031102200702c158180c400f180d811070360b01c0501c0e440305e40c01f041d1141548202021403814140810040c0b09404030b40038504101c1180c17602296a40d203a85c0c110012040d134100c410424440c5d42000412080d030440b62045005d0420b80d15480e990311040c0504040b41600742e034005440e14005c242c3c038601485080020700745d4400030740c80d003260440001c00d0f100d10313400404000b01a4402181c10b401013507101c540030b00030810040 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 141075944 1250 141074694 141074699
    0x60106110709090501060501091205370606031b0305060a020307030204080f0d0809030903120c150115031505220b1011012a050c0111030403110f1b06090a050a 70
    0x442c01b90456004090104a107410005020000d926012a0450300034024044141d08140e1540840c80c4400d80b64002804900110b48008404043c40a105200f0381c00061010302d1840c003144c40b203802c1d910400e040c2085010130808a0000302c0e03102d41c4810403050060f81d80c1e0f10402c00350000d00694008089600c0b0701d100d41d60000d08001020840e00c0f2031911900300070b503605c00c3c0c04c0e56a4452400c4468240d00030b08803007004100c2c0307039019002c007c1c1080e01381e40c0f42c82c100d00b200980c0e0180980c0310140d0f46900884010f1125018807c1445081100000c80d00b01e904002c003082150318000580b442c9a9503241188468a44a90091a002c00300400d0190220015103000b0f20b144d040c0e5030440302c55460041e104005a444558132030643c0a02804d800e9441c215100a460b03581190003c00d2541d529416175a071000c1d2a1001144218030a45580c4030b2a03031102109840e000141c0d0313034180c5950280724030320400142d85060b06031b0180202c2e1590b40c0d9441280100707100050b10b5000da900400404c002 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 141077194 1250 141075944 141075953
    0xc170406080a11040b09040b04020d09080d0e0d09050603040204090506090a0c0801020a0c020d1e060c0e150316050c0106030f05060c120103080f0910110c06090306010611070909 78
    0x20070b000e004080e81c01d001e4816142040e012600c82d5106500081c0c01c1001400e0482c10150401141698010001030402e0091070ba8002620100c150448540030001034030300f842180740c41180300b01c0030064001e204828001d43d01800302119809062304c03da4004c000a402c641d1203411038410940e0003c10303a142c5091018100c0d83d12000c0c050221a1403000100c041103c0300c0500c2900c1601442d0b55034640030600300e03000e2000003100c0360410b4481004d00da40c1000d103c00550480c5180700d101c0c00002031800c5a840c4020800366090480078412542c0102c24100e4100792000e403508070065240c25441c4061a0324103890311b104440c00c04001d07500b44031001050119104104c0030842c0501c054a1407903480c0c0300c104806209250002100494140051001c512200c02520032880b9039154140f41c000c0c03800001c2c4a500c0c0c440c00203000181c5d92810580840d40501071b0404440f070a4407450f09090f00c101c006074075048140145010800c0c40540b00e904120304200c200018081580d0230881c5903401e080 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 141078444 1250 141077194 141077207
    0xb0318070e18030f0307030b060d05010b0d0b0907090312030e0f03030405060c0a09060c020105121503010c1106040f0309150207080601170a0f0302070f0e0402040c0e0a060c170406 79
    0x1468440401c007a2a1621002ca010048810350505002c0e2585960f485120541c0200328401425400442c14449000800741a100d5203010344900b03106541c8403200c03406000c1c01c0e1500500d56500408100052100032a0000000030690354801c020901103c00c0c06400c500070504c2490300880c6205e01380b10180900400310007907001e01e0041c000d80728aa56110031031041441002c210b5400104020310800c202c0d8442c40c06001100e07c14074050745881a50440c05079a1f9070107940720044d1411842e80403070300d40760910a0a8600c1060300b0490f0a1200c104102908c0d64001031025040001c0248810300f01846042c190000d030400c80e0582340d05103032100f402944c03a0740728010000948501d10001c1080b50007003d03d030911581c180000c1c41e0030300c40c943d00e211044a8654040b4290320030307150041a002001d49840e00900110755260701c0600d050300403c02640c4544080600340500c0b1078102d4001c0e254564444c0035900f050410180a50007031412440a4107034404d041c020900102d4041600c0e0b0744180e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 141079694 1250 141078444 141078451
    0x411070803060f0a030203060f090a0c080606010e09090c09040510020c030304120c020d06200a030e010629180607080702090f0907180b1002071d0108070b0318070e 72
    0x1502810643d00307030400e0000900d92030001a5141d48101c3c0043c03581c8004e400025844501003050b80d03402402c0d940c600580c84059007103041c2c07070b401034410015596882040c0f9000084100c91000c10307403e1402a130754440c0c8010b4602030290a1180000701071040802c184181106140350455454101e4100c0940701e800c1680c04480510349a42c20446e010311032048032002c039400030410b004502c21070b9540c5006204007450400b0b000300001c805c220f0a44000c025185458403030b100070030b80303041e10319403142120013582080f405c0e44003500c8041d40340c1852032510b810054503049115603a20790600008841c02a4030300c0a540800c0000340c42c0104074040300540309503442900c0d21203468130b88081c16050f11004031680300709580003041c1081100e42d140040d07000c03800c00b03c500140100c0340502140180140036000005a0f1001e20100415403d4092128041d040e0440143c11541003900c85074440180e8411841100000320100d43e40c101c9000d6035804540102e012118082c1e40c40300b000e102044100c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 141080944 1250 141079694 141079699
    0x9030c03030a181410050a180b2a0a0f020a0b0403060218060a140912070801020a090503190201030207022b110303180d050a020901080708010b040b01050a0e041107080306 75
    0x16400143c41c4e4007446054441d020014142c0362280e105c0103080740c00c0d4110b150000104a0704d9922002501103424a580181141d150407030b50340c0c0ac000c1e1803083c0c0c010000c5442007030ba9005490241d61142c000c02c0458090740e1004c0802d14400041c0002a407428a9820500c20000d0000b40041081551390044c20b00c03402d90f18220580141c031001704800c0e17025010b0ba07140406c440b01103a030144100c2c4401403e421500505496400000982462525660350088c5003182c0d0f0028061801030340080302040100380480c02080382611400302d0032035841110100905042c0c01040d00360840d0396240d803070040c2c00c4510a440d4081006002c441c06060000e9000360368090300b4043c0e034486410007104445402c1c0554040c10384c1108418140b0841851440060712a400f0b00c0d48040b00603515220f07024000c114100003840013a084c540c5050031151030b914201c0c403031031800d80c2ca00e005036041002d90341e4150705402e015540e142c4080109001e045001e072854101d600c006184420031001802860113031034207 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 141082194 1250 141080944 141080987
    0x50303130302150610030e120a02030309010b04090807080309030f0f0d0b030c0109140406240f092421020a0228080a0c020405010303030618050f01060509030c03030a 73
    0x9030904042042e0084d075038150401d41456180480a010b90040010019103a00f2902104004010341920382c01040d050790050304004280310402e502406a5629114112030410a84c0070580d03411030248500704004102110200004203e2401481500c0140420321a1039940b0345000500340032692100020980d241d01e0b10300100b1041c1000549000803a41c103840d40c03040c290500920410362406103545030742c807a4880c10301260314004200e1410ba0030401c40c1a102201c07800940103404540421581020055001c40c10040e003000384140c0420718010702203440140607141011500180d074803503400c8400300340300340750b800700e1407079178002c4c1040341d40c81d03007030700c50081000124008014602c881e8030312030080020b8000224072801c000b000c640070682000c072070315500e07036000c00d064440c242c0c0183c0c0825a64a4100601c1d08114103041613448001e80402080c98228204c24140e034060040038108040403840075030941b000c010b03080300c201004040382e03201c507101c21340107001c0c1d01d50a4020021505 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 141083444 1250 141082194 141082213
    0xc0d1e02060c09040902030705040f050103020a12080d05270f0d020a050c100207210b0a0b100806150414030d05040303050304032118030807090305070b0702010309050303130302 78
    0x10106019000d00402c0c1d425070700d050303003400800c0b015140d045d5040c3e0b458003e1030000503c95880c0e1180226400600c40d02052a40c0b541c01041380d420f01540c8014260b5041c90104000070308064202c400303c48007000700181b5511082a210220326600141e480445144c0131601c1440000044181c03444620300115180500c600700208e0b150810050024255881000041424039140e011917091580610480e000d0b07660325081c070505450340d0409454003810203113140080c0001d243d03800742d000500040a0069002c140040ba0025510404d510100101c150114070b880c0c1d40c3c035641c070400b03d140300f080c00d454a8440b02d41e04140140868910b2192050212001929000d401648d08403600b5480301811a52292002c1d90300b01c0c1c140310088100d4080b2081038100078614401d0b109143c11000c05154262150b14000d0034020003c0d010300c0501180103002c1002800010f1118207648450315003e403500014070050b00a425110b00042c050b00000c410400c09290b0603803000c0205009600b146e82e000c4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 141084694 1250 141083444 141083447
    0x6090c1701090b06030a020307051204140c1005031303030608010c0e040605010c12080a0209100e0901050901050d020418020301061e0902130e0405120d06030605060a08030417030c0d1e 81
    0x114842c0303c1c240c110000b4000542440c0444d806140d000d40f203404c200c0e241c01e1540381c8640c0c084004480883c3d60801000d505001036004100303030410500c0640301c03c00a440c3c0400082c0c507600000346402c0e001d800e4903400c00100342c841c1d00b01d070009051300802445125400c50001d8101c50810080c24040c3e840d000c0e000032158401c40c004800300e50000c5420300740d0000f0000c22a1602070040c600c040451702008208040c1d00c81016411100800b0b90f076a081c8903a85600b0801001c1d410f0340000c0c0308000610040c0550303a143c4003d2000d00c1d6040f280003601034400c21000817904048003000e5455480c29400046680581c5012000076032100c0044280c180c881c1c8030312081303014000c03064045040c040d01c207101c242074080388290414010811155100501c41d5000100d0384294040310070740792212410010040c660260b5508004100e448500e1941000c604545d80d01451090040608000c006100010024400c58103812200d00a0b10085584103201400d003481e0704c294011a404000480e1200c0c6 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 141085944 1250 141084694 141084701
    0x6090f15181c0f080703110d0f030e0705030316060603060905030c0f010507080609070203090910181404030e1206010f06120507020c10030609020c0c0301180503041806090c170109 79
    0xda8407188140500070f10351910403140c0c0101c3e41c210b09120207421511525401001454013000c040c1d5200c110000e28040e00500f50303040440a80415408400184955030f0b02000b40c0d03198a9001280c1000b0b00030604003180588134941c0045d004074644001034003132020204c010490031031517104072025401c001105500b21402150741c4000101c1820105802e850312918254000d640c5104032403c0c50b580c20001f030220b0300c0a91f00c3e10850b01c11840100041640300d1200d11707405000c04c60070031003840c242805c1c0d0207160009000078200701d0140c0010030307180d4074104060180caa50340c085076074640e10754508000d00c0c01640510741c00300d1001000a108601c203806003500c503915550240468107038020600c05e003081c108078444c050689602c0301191a102d80c0c40070341400280040103144109080c818142142c842803c01a11504100860710110300004121801c488901044a1000d0203d000c007000034821030304003c10306401c2004001d0b00c1d9a0044c10500601d240c5034005220303076038400c0f03154100e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 141087194 1250 141085944 141085999
    0x9060102150c0310090e0105090d020a0f14070b04060302030405071403030703080c251505010e0f06041e02030f010f05010c0201030e0c0a06050417030906090f1518 72
    0x710039084001600400994003a40c2c210800d01d11102a02da101c016000c2501c3e5203080303c580c0390b99104104041800c00304449090314849001500c15103142d500c644502e01054280034000500021000207103a80802095000303081942a5548598aa000c010302039801681c06403940d2040300e00204100700f04074110170f22410000e00852503d030081e9002c2c0d500000007400e4801c1c80390305000c16442980a40141401d50200a00800d01030b03056103858880342c2c20581061207103034070740001840310244401c1810303044003002a110040380c1e60800098054501181c42124a25010401030050700c040c1d009103010310160f1804940c160307201c0600e81c1540c0070b01d20605001070782c018034203000f55000b03a2004000c0102d8400340c480110b10103020606d41c40503940854006040040c04004141c128003590351500100c0d40503602e07000601d40041c09030b000ba070700c042c0d00c60f03403805200c11b10540c0c0301c107400c90085e45220251074441202d00d001241c3c00c00300ca804c440c0118440303010b446e10140510300420780c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 141088444 1250 141087194 141087223
    0x50f07050613060f12050c0a030e01052a1306030501060806030f06010504151e0501020d0e01020a030807020f010c03050a0606090807120503160602070212150c030705130801060509060102 82
    0x30551403c0c40031100440305204050a0011020300500400645d0096030b21030a800780c0201d0f41c510070410024200c0f02103403514a078030b03490441030004018900312940c0b1454480c15079810480e4404ca0120403510030350310303c440030104029001039201d41541150b030481c0c056841d00d1915071360f040145921001e801d140454160805c900501032450240d0240400200400300341e10059100c6201d20b15007010407a42c6220a4074070751040150350f81c10059050f0280541c03501c5440c80d0801c4001035540d0514060040c241300c000800204035038420090085c8100b4040001d02544403080300c0900285030a59100b81780ca8188600450100e0290070100304540c8820010901c240c5400c01d1030039054142c540498160200b0070003181d01040c2000403400070f84c09410010b0355030760148108031200304004041c1d2802c0d0806100103034000880310005607c03914401d01e0310fa0f01c0d5501041100c05100b40f8580d00c04a505000021507148070540c00901642d1080c2d8401d200b51715030348e0042ea80d038803c00f01080c1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 141089694 1250 141088444 141088477
    0x60c030c30032e080f0f07050109120b04030c051516140d150e0903030f0a0501080d1808070e04060c030b0d0609030c0206030a020d0507050c0d08061c050f070506 71
    0x103c03494250582c240222201098009405841e9124941440342c2d022000e54107174070030440c00b40050b106000d0b02004040c2400c103940c060340707060340b0301e1031850f0346c817101500031000e0400140c24103005210319180d0342e60100030fa03941e10a2890400d00025016180d200461500014904145000e0440c2c41103c0b00d090211a0030000c0058915025008030301840f01c804154260010302d072401103c03414025052800134688a2800103420350559200800b140b5003e0b050000401800b04040703000c82c5400c03220318080748150050744c08000c444d0860ba02a42151103a00000a41004400c010710b00952050307605002e03003d0350076421801d070f6818500c402c2e8401a90805000003542d60760080000c14400d0800c108c40d503401742c00040d100e40003118141d500d550006451503a0158601c40d4a5000e10103041c91800c0c0700c04501802d0b130361000040300d9030a1210034004246190384040d1481403070840490341a100220b00d1038a552140804d00c040080e610a074540410355181220590780419144a100e1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 141090944 1250 141089694 141089731
    0x50a03090e0c1e07080a081603090c150e091003110f0f09040501060b0d0903030b03070602030409180501020c0109140d0f030c0e0d11181302060c030c3003 68
    0x11000000300d00c40e610f5895008011039400610144041c0c41c2941503621050581e240031401280d06942c00703a6840e04061400c1c111100240ca2102080c0030303211000303c5468040c1201d2803e41e02d442e2141001a40002c0040402105641e28540801603074400d406d8901341c080e424091010300740c10004110341c40406e20041c1c040c94204207003c00e0303020b401000003141540e61070150a8240e845002d12002061315542800706054060250960340002900280001480c10000035101d00441c0a0401d42d40e44410f0100201c0c982e5803081000c1c0c079040f9008554500d0454105070003021000001c40f03d107607960310400080d8401150544000305980c80340d0120750b00d1a0000c500501c4c2c00e51158051280c0144000e91a486040038100c1507485448100c500303d4851040184866400100d2060040740c030040251a00291407612015541902c06640b42d0324401285421405004c0242005201c0c144071000c01d141c0c2c0c0e907440c0025130080401040d40c0d40c80c03070480d07464600c000c8440980d00d81101440 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 141092194 1250 141090944 141090967
    0x15030b06090604051017070804030f080f01060e040b030304081005010b030106050301091d06040f020a0b180613030807080712030504020f0d03030b060c0304140f01140c030702060304050a03090e0c 86
    0x2440d800031300c0c06d00d40a001043c600d004111041d2080300005040b5000c00007010382001014511001c981403c0c0d02c60310340414411301da80d0050190404116110640002c01e4445403c1006110300003001d8030746803511814600d42d10b040344112540e06505101c0001029120390f01200d040c0d40c40b9580b181c1c0303541e092600d180041c0140108080b00700509642c151410030040c4041030246204016400c07061031980100990648641c100f421401030402c4903a4182121f90007415803000141c40e00c5840e08194181c0b80001d4845610141403164001600b404000003400140348803403042440c508040800e450480072503a0454009420420682805540b441d1540d0b450a043e8407034034022075183c0300a0f02145041d006a04480c0c142c2d80041810b01141698002820903c901500c041c659201310f9400244aa804e80e804492203002c00078805101d00010b108485a9903006840150380e41803910b40700b503844c52801c9094001030401c0d400410a04458110203004000c113688050400c1a0004d4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 141093444 1250 141092194 141092209
    0x7090902092212081f061713080307020a030207090c2c0406081b0405090606060714010603030f0201050f01030b0a1e0e03070b090304230d060615030b0609060405 71
    0xb54510440036641807000010b1003061520384000c01c0d0740c4c50742c9140c100821100c004084100310001441c0d02c0003024000c00e0b5000709543c0303004000800d81c0400b5210708006001e40ca5040c0d0700a05514800810400c0403600004d9074a250f078401e60888000e26980c03507811084800d81800743c0d0005812001d0000c07c5407484941c2004d541d080542d9540c00c40550780080c0854a00341c0c41202690402c880f060080701251100098146c400d1314207101c00d142085c0619285d1400400240c45060b0100d820b4041c0000050280c1d604e4400302c000300109500da04015103100400001c91006608000026405800311a64641200d501402e51207403921441c0945015041459103c8030031400d046040c03400410718041c1411b09840e072009903903603551509082d881160010a600242d6000300403c03c20400f0104109141c030010f903500120862080c030000f10704402c0d016010b461135003002c09c081000b42520141160011841d1030400204504109002c000e01404058039031004080c0f004125901300040c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 141094694 1250 141093444 141093481
    0x7030210020c01020903010608060a0e060105091f0306090c0e250e19090203010521030a0503040f0f030809070f03020a0e0912040f030309051c0f02060405040207050f0709090209 78
    0x8005400c0603945c10100742114003a034041d0600368811828081030800078401c003041050141c001e40015170420010810070301c00a001c030702220030301001d481818005c120107030001d15031010082c000d508407410040e032100254043c6020742050304001c540070424904400039040c50300e4003007141c8942e60180c1074a48003400c034080c1e030b040080c842031503030504406c4000384041c2003031080041e00c035410034003030000e80328120b075080d40c0280d80509602d00446000058446150a40c9045d0380d5036a0395140002141c042e21030010400708042403050105a04240480d103d16008001c0310712031a82c1d0100d800e8031185030700c4041d41201c004002407096400d4440402c3c1e00425100844564074803401c6844466842941300c174405d00c0b04e5841c00c0c8105984900094000e001c01c541160300c0e0f0981e051305000c2031142ca10f00070064203d0401d0740c01113445034020b840040c24000e1085482d1051410f146440d4005606914958024981c0110f014489442483c1c180ca40192840301d0580e25001003003210035030384 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 141095944 1250 141094694 141094717
    0xe03010204080f032a03030112080f0706050a240501030207111f031112012303060703090204050609040f1e020a2d1a0702060c0610080d050703021002 66
    0x30000402d248204000b84040c8100034030085030744000c8012000e003282010040121a0b82151041700003240002041e02d06490400524400100c02803030131206622a003111000340640204e03c840510403180d001c944140904c40060014101d1000450880500c03146d9041d5100c0b1445014021940700381d0141942da403080a0109900b220304000920204000166000200b42c1045084840794540105500d10122040b0746040096641065074050300c14012801c01c038100c0c80301c440341905200c099400106018040d584da03800c110800030302402044405a0095041c10081441e03414000741141c0714503003000000c0618103451341c61070f40d40781c04c041c511070050301c2520a4a01680d5010200c40080c0801454202e07145030b1a003980725000c080b0fa031200901140120100a05016400c03ca540380091840d0541e4421480c80052001d0195041c003400c188034000400030302c2080803020710281c0310b0b442c085400343c2e144c521045a107882001d0b00140160001d4000050300c0c9141d402900106102 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 141097194 1250 141095944 141095947
    0x30911040e1011040306050405072c04030c05010213030803180309181e09100c02060601020a06050a060e040b0907270c050403022e030c050f030403030207020916120902030a030e030102 81
    0x42e1b0f220310040d00c10030742d420740f5250403295041040700100101c0211130402d00840c0005140f14aa00344c008400003000a000c0c41081080541000820360486225140ea000d4420b0101e0b107a060210042c0c00807910302c075458000c034848040c9004c00100343c4100080042c240700c014104842d480e000f8450213825281c0081c00c0003212404404003d449510a9902170024911030a108142000707441c20040c0c41f10a540280c0b06000d041c0c1d03400b180c44000650403081c0480d0984034441c14100606540d440b49c0124186202840200701300110614007800040003224180e075183c13044c100e414510322411021a00b44070b6983c1840a2aa400c1030304c082c0014240942801d540350003090001820b80c010302100c01c0d4460101000840d49880c02800319070030318041104c000b460b40b014103a0321400d5003280140001000040405200c0d070100d61200354050845003403400d207501c00c074484092004420303000c10340c80300c0250300d01d0046120f0051841c0e0007d00074500c10350076480c180c484030305400303505406540 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 141098444 1250 141097194 141097199
    0x9030304171f050403020d09060c030309050c03010905010609061505040e06030a120c030816050a050f07140f0d08040209010b071104020c0c030f0a05060601050f0415030911040e101104 81
    0x70391151103030541c0b00c00c0300d02040c203240ca8940281000b020080140c1441011041440502e50000d0700c030000d9a0301d03060000b05002035003401807404a17100200c560543c2403070710b441d041001c10341081c400c41d0705140d03062000c0744d150fa0b4643c10308144082d1041c0041c0c82808100700c031407400100300b5007110010302941e005006503214005861034448a038008038200c03403024810590701004090b4014001c2150f0614400605001051441081c034400d04212001c98500749441d9201e088031042030b0300910203c40074a1100c4165191404401c24180c24054448030001c4180a17508103032090380e0041105601d6800c09040002d0768002047c00d5600c1184170320b0825a603111840103000c41ca1684000301210700c0070038100342c9000482450351402c2d400004604000400c002112900400d0900307240c1d0f143da00303d000558507406150311145646151503884100541c0690155007064041c0c40094a400d1942c003d21090700d501c1021540154451840152606481d03440b0034450488a80c21510b0180d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 141099694 1250 141098444 141098473
    0x9050c070f0611030a06170601051302071a0709170309060a081504050a0b040605041a0d020102030d02030103061409010c0804031b0c0e06030d11071503090b0a050403020f030903030417 81
    0x10011034041d510550741d041c0600c90310070307c3c000524182d502d0600401c880d40c100000304020424500d09540510303000318840c2c00304100c01e40054085194810900d1441c075103100028041030183c45801000081400510404000442103a20045014020b07070f20703040c4d0a540480d40b925000313003e00d841050841c00f015040c0e40340c1c0101801034208201c0840ca400b0541e00308412601c036a0b020a1040d483d121800600714078920a01c1e00c10b0004458202c030489003800180e04608c03465000340e0b040b5100100100c100006640310b4220820804d08410340d5944404800b4200c600d40c8502e00e020601c0d210002d00000d102d10500c0c4082c0ca1842c080d80c1425001e907455132070b003001039000092040003203000c224950808011564104c0c0340e902d04441407803907070310700303103450f10410301030600322503a035114040d0958020b4001407070455002d5a00c1800d4549480d08000415080d2021401800390004180c55000004181da40b04c0f02c1c01008ac615291401980039521550000d05100344c0c05901c0c8480100b2 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 141100944 1250 141099694 141099697
    0x1804022101051e070c0201080402041104030b0c03010906060503090604061d030403050c03010f090c0b09010309020901143105041a07080411030102070803010509151009050a09050c070f0611 83
    0xc0c807010401c4031007640b0f155507900d0710010040c0b03403008003c004a104005170ba40a0b003401c1c1c0094040d1000501e5800ba500103101b0f61040ea000504103c0e068002d20524003041c00003103049400240e4100320300c5440e003c08640c030740301c15214040381e0741c80701d40403d01285c4960f024400d9602410761181c0a20b5600140d04d0464005510039144c0303412101c0f41e48800d05082c054075a40f10803200d4100481030150751769814481681c0218002c3d900301241c1401e20f64002c1c1d1040014540060202d28a503a40e50340107404422081101402141d229880400104050468400e1031681200c54030880c0000c000d90f60051900070800d0b07641c000031030086e440704000c40002d03034003e00103599400851310b01801c24180861205101c0e9001c0c6c3e20400403038002c25000025281500d0044030190001d03181c1c01c41010b08014030380d16171030388110304d9140304400c160464900e40c1260410364503100219910040c10040b10382c1103d49071a01e0504210303240002d0740500c2008040b510401c40015035040708140034845 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 141102194 1250 141100944 141100951
    0x30c0207051f02070e0105031c030b04050c0301050f0906010813020303070c060e15070b0c031513050619140906120627030307120b03030d020c0307030e180402210105 73
    0x70720003250314002c41d06030b0500240018101ea015803078540d51410300401d80d1110407224101c1a501420075880c01036200e43c02c9607881c0040140180050704255820f40c0e10b13540203100301c1d482004038208840007070078003c03a51441384205850703481c6150303684141450b9030700100c07601303c1e40b50004118410028114003c3c91001d4041980d5200070052214184050020001e08100b10f1000c10302011b800155180d600b164006900e2180c5501d0b40c83c4c9062a80309080705855840e801701c00c6948095120115600840c4548000c9903552020038408010108228960040684082c40704051400500f017003401190441d40c05482c014885550f003020a0403e40c3c20354025081b0400f4810042c1c2c1c114605070042e080c8000c1001561543c1020000501400e010303100c0b508240ea1a030414a403966024000e0310070107020710f00c0a41d80d50b000003003659200e501480302280411b0001061240c2d50030805000d010040d81048001c140361030b1038082140c040d0400d0141d0b00340c1810b80409900ed0f01702805000e02 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 141103444 1250 141102194 141102229
    0x200a021e0306010b1603050f272706040c17010617010b030c180a0b0f07021206160e03010204090903111e1e0304051908150403080403030c020705 64
    0x84900d280c40406060040680c405050200d042c0044611240d6030b6051003441e661509280c0e41c0e405511f10b010120f4007550588000c2c102c44240122618003180340d00034480b48080383c0388098846070100c1600a4450003201c545401d40110004406080c9544905408040343c01d1001c000070f4802c0e900300030300c20260401000254112401e0807071188000a69024100d0381c000b0034114600112542d14600440c080d64040b0711090703140107242d45804103048050024110060703540d8514043c2132400e44c5c89840200c1c06815020584548084045401d034007514203480d03071860020400c1e8080319080c5004400c2a4155400c0000141500c2d5078030900142d68031a8032513030007481c000d03220141001e003013455480d0018030b248098a161440840c020884106426044c0a5118040d0020b840e5004941060b5048100340103c0081c0d240c000340c014088610b00d00440f0076828041d071410180c15000c0c0c3c0d004010460010114000a0082c1c00000c561074185c4100e64900360348400003403001e60800c0301d01c0c6 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 141104694 1250 141103444 141103489
    0xf0305030c01110f030708192c0106060e06070309080604111003090201090b0703020a0c0f05130209010801170115033e09180304080c0f10200a02 64
    0x288104080c0100000c0881031107500381001204401e04c4000d01c0028245420003a000e00051010003044101d00900c00d40310700c04000b107010807206200c950414585805880d903025220b108072820500179807054030132543d40c0b12082281081404110f0b001600200d040c4035030000040f440200402c1058400c900a2801103040c503986402d021050000459110030541040c00a00160740c00c030041a0848842e4040680d443c15141000c0b03007088013540000b40312680028001864540f1540c04078161a0122020141801c151950300201d125400c803182c045002c6500400c2506a900c50364500074803684004150400c1140303020302261700c240c008031101d00c8171408a4500107001242d0070b1058005064034518584010101c44000044050152094034001d0004100c0c01481c0301e0703505000d03908403c484e01c4544444d07890340c4410840e08064095000c1e803104510380e1501b4021284501c00ba03840700c086805841580001240450381031031918425215011b00680b100c4109031407082981c100700 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 141105944 1250 141104694 141104707
    0x1e0601060305070318021302250317100b13050d05070e090309030a02060a0e100503060423070e01020c06070305040302040501092009030c1809010f2906040f030503 72
    0x5800c882c4040c20030010149000d05036074040000001035421640c04507035000b60640c070450000701a00c501c0d00c8000040000341c0b402480c0405110455540e140702c2e84450f101455000000c20a4020450700d000800040942c200711140302c6c0801482d03160640c941c0426075a0b00c90011030511b4503140402c07a941e62145c0010048004200201600886000d020718a02a0a0000640d8481700b44101174442d000000f807401c801401038484111202001c1c0413140174103074140000e01103800481d072040c0500c0c2452a2001c0c091040c140c00c540754451081042c1140c3c03103010f0100e4a0b410010b8429065200712106c141003036035004058003503a8400e03034a041d41c540c00c620500c400c0c2c400692241e0500c40c00c1c01a901204c08036080c0ca01003a40700c00b18000e44880040001a207070108032841150003006c050b1500c0400c54401220398480e89240f8000c4c00b45407c01c45074003085400501c05200d00312a868402d20880d4001004804581d0008010a05154840ea160004004c09610803241c1e54000180c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 141107194 1250 141105944 141105947
    0x10e15130501111002160c2702070b1807080f01060f0503030a090303120209211501030b070f050408011d060f01030b010302090403020f0d02070501090f05030d03020a021e060106 78
    0x281406041c003032a04142d88000305121a6962460301180c140c03068001c6a0b000300c64000e0000c400d2503681003641107103001c0d40c0380120712407410141202121384450040703450040d0954002c0b1608164411310500070303a55020070000d2038981d540200c5945002c1c4410024400d0410072885010503290400003e20615105e20740c1180b5001d980641e010307400c02d205541d0141e13000203c0c807003140c0d01400d000c600c241280c0c580600a1054a01d005da010007038201c45802141142c82c0c160107080c80c001100c2d4980f24a054059092000744030041081c0c2044000414179071288902c890001c01e24242182800c0d00d44030401c1c25502901607a14440c8818040d40d450250704028040d00110540c01c042c1b584c0d41141c8030480031841c14040640141c41a0012804161082081c0d04d606061442540c01a12842c80c2c001c0d00c44203e031040500040301500c0100701911403000d40000c440004004055240031038106034041d4004c400c50000794012014011014202d8010803540b00c1c1c51400582620340c1004030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 141108444 1250 141107194 141107227
    0xf0b060f1503010608060a1802030403110a0f03050901020f070e340e0d06090f150c0509040507020109020312120708040203030702090a1e021308030309060411010e15 73
    0x103041e108004090460350340e03100010071207040d502203180c40d0a480c1c1d100340208418144942c044880e40111101c8080541c00341e40c081d6001c0c43c07080e961881c10310300342003000d0740d200701880010300b400c244140c81800281c051001080d00c1d58060060365040881a80600d0502c81181d2090305034010b00c0007001851041c0d68011403108102e15119400076113595130403c11000e001d400032051005494006800d0b540704d504803141035074840824042d2048500d4106280c142d01d40046400c1120781b0110b85107030459005021f0b50404c2540c5440c01d0007084010000070704800380c03012095540e141c0300300b80561028800428210404000203960701c89518811002110003441d80302000f64030400d2100681d4040120361010b44c045504079440e44820303041e8070003884800f601103420010a40b1043d0700d884a600540186124901d05201d2580d48440950b2284000c850181268000c88001800078140f202000040e040616168544c40c80c00f1000c40c01303000895205100415010031700141441e224030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 141109694 1250 141108444 141108469
    0x4180c0503150709030809010c20030d0206070c080702060c06040b0f100b070305031503010c02010906110406140d0219110606030c010f20010609020309070603060807060309050a0f0b06 81
    0x580c030790b405240120004103501000e01004150341d00014031100707180c1c8038884003a04940c2000c0303040d03100840c03400d0080006d01d910343c9060290184113940515103001282d00da00c6000d0303c0c1c41d04022401c2913900d0340b41e039030700110003207a10080611044d16903120412001e880f0724480c044004e11070400800c5002c0c0004014a8003e52044807035091141c00d1001c025102d95a44c181003598072610703401c0d51190740012102c003694266181c514060f05aa0307054101c2c00e100da011729000c04c02441610000c9130144164015500452296002003c1c55915140200700c058180c40c001800c2859419180050303201c803041b20b42c000f441011045400e44810310015410100890081007521158030010300088544596642400810a4800304101c222403061060a032018000c03c45940c58428640c020340003611181c240e8800d02d500840c030203011340316103015a20030a000b069020302e01881100548210803045a090052400f0400091050347c000031b02c1e90310992145207d0b1400350188888481d948 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 141110944 1250 141109694 141109723
    0x160519090f0312090902040812030a20040f06020c0a1e0e04030c1203020c0a080a090b0c060a060509070c0807300f0e0f0904050c09070503060405010501031b0e04180c0503 75
    0x420041010410015000410001c8140c2c9a91030f58bc40710321500091002240380c140c0e0705086401135030760400c03070710040050f1810b031003c092400b519450206c1c0ea400c2811080d580008600406102e045040c1001d1140901680c681445160700c032a03041e040c0e8001a201103000c40c100084400400c1360780311032800503610601c0d0450801c810062816520220020b0141145034002007030304699114001d014045e08040e42703d40d0b944d2500040840c0c3e58041101c10141491404070b020075246800401c0c68024080e9030307980b594101d440c2d00c82e003001c0d0740241c00c1111541e2080705812038401c0203001911004002d109203030703034410394040041c03d1040948007400402c420b10406441c1c507039507091041d0030900142e540c1200323a903c0d85000c502e81400450070721342c41000c103803c028189a00c0780086100d040b094409200a99070343c001503060b02c21402045543c0c4111182d40680030303200390342c001da2500004101041d00d12080410a9041d180c1c44001e0b0b80d440c420520501c8542030401000001c80d154 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 141112194 1250 141110944 141110947
    0x31b0102032a0306010305040c050a03050f1509070b0d0b0409030e030c01020304181808030903190206040b0406050a060b161b0e010303051810080105010206160519090f0312090902 79
    0x55400c80b00007440020007103814140e40e100494188100d440748000507244c05802c800a1036101c1c10310365520100440b51011a1003490280307a1000385890103680100c2020700103240d19401c100325004990460f0301c21010659442d40c110041d55280d01480404500030b0302c0c0c58984c40003550505003007100800085056500c200b004004000e9805109142c0003a110310006111150241c1111030061141000d03104520100c103101600740080010802140e50301c040a0068242c0b200c181d03207940c01100c0140078102442c000801140742604040d0340f000e5900310010f0f0b10364580c941c17907c1c60380110316034030000c4540e180d0300d1040104141c401c110144107076201450b01490b00d451007119a1b01408000c08000f004a05802131f14940c5180c5040520000d001208040408000030001c420034804c0900500c00c0c100840c40994100c0407009009080c1d907617075494135004006010268090120344410002d0032103001030104810040350028600c5500304500424507950005c00b007000d15003014205620 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 141113444 1250 141112194 141112261
    0x503061207081207020105090915030f0c090a0c021903030f0e03030402060702100203130b090a09050421050405060f040602070f1211060c01050a0c080a0606090b0705031b010203 78
    0x1000418050041503070b1000f5540d05045e100480d464006d20b9103560708030f4100021701c41500b003581121000420140d08131001900e40c0f05500d903036642207041190308890090045010304015812542040c8124011038a0315104088440941210b0080641c0001c2c0d407040d07041041043d600507200e000b86a0700045045042540005e00c2c9480784000003813203130904400704000540244295104020001c1c000500c0654030310060034184d21134a0454402c2126440100f11442d00f8410039000301c0e00440003c0c0c20380e07854007050f4520701c06c80e00c41c0c006000041c0000181a643c510003017517a454625651900d0b05d19003403000c4c1c5010071340d8008030300c0d030304084505000c00314000784401c091540220ba10800011018007051242c45800c400040e154249010089440c2035508110100c1070103540d0001107a0341c2d404030004465050251074005400b01908005010403940503118941c022030a80c3e15010000d0101c0c0b00410800c402601282d402008008040040c105142d05a51000502192100 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 141114694 1250 141113444 141113459
    0xc030c0f10060f15180314060709031109070509030f10150b2b0603080a09060302030c1204050c0402070b0f01240c0c030605070504030605160905091909030503061207 73
    0x43c41402402a00c41e8040c40000c01c1600c680140c17070109002c03102d6420f02d15228105180d500c66880140f002ca841050085070416108400d5a8100c0b60043e0092104203100350070400c42081c0030307080301d0810100780000044e0707980500c10461000d035000c00030300c205100e00c81c54006907074618a00d0840044070503020070070840008122480c0320750010700403110b1440720180742c01142c0070300d02d4000218500303c0c0100411090100910000100341c48051145039505e07801c40603440100e503020540132090000088a620030881141c1091045096415070348194010030203d030031101065130301d84241018800d44405804145e03025044c0e00c0c440300405111140c0580c210780c10500100200420403600c0320604c44148120805154484410302c09400d1181c40140150020300081c0c43c010b15000101e01d101a080c10101c0341c00707440c0d80720411500d1908080110000300101402280c189140c45040e140b0014443c2e1013810784292034941c5c0300d0400006111008080c284411510741c40707030b00c2c01e00410 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 141115944 1250 141114694 141114719
    0x2106070c0b013006060b0406090306140403050405040b030a1a0402090a0c0903020d301404050901060e060c013b1e01060b04090e12070f03080604020c030c0f1006 71
    0xa80039459a8680c6000c81c4c61300c031004000c00d80c02051a0103000c6000300b02c06070300040103030803280141c0c001d2100d05000145c10300150006c0c0c8000700032580402042040c0d04158005201d500c81c01406d9415801c4251641d1020a00d49c1c40002051456041040210724062151a030411409003003005020302c0340d00301500911141c000648600020503441042021300654004910782c264240d0088402d00010800c540403443c95200110780c5100c1c0d4002400740d103009407011140000c0c400709469103007a1040c0c40c0403104d000c0143d004a010806c1d620302d51001d0003100100404c803141c1903069442c140e400400342c540c0442662040a6103420100c5091001600c50764072005101180310005981d0552401440300303520080d11500082000109000e03e98001d0314504607120540e2145005044916402d03c6010f0008150345000d80c404004070744245620b071350021000c0c00041c0740c035a40304161883d40e084100c0540441d81b20078007400e0240c10034047e10750107c008600c28002281400b03603207240d2 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 141117194 1250 141115944 141116009
    0x30115112a0607050313030203010b0303070807060e16080703020f2d01182402030f0a11030d0f09020111071a0702061e030403080c040e01052106070c0b01 68
    0x50100d803080101581e031007004840f9002c0d44002101d541d1804544030310350351801848180e04c82d52170034070713090018100442207485141d484625549403043c60350b5000700030b0141d405091101d100f00c84110014460803500700010b0300b248402421224610b104104d211400740d0012070086140309030718554400c0354a616154543e2485040204031065030040301c0c0488400f0548841d00000c442c0020004160050686134590084440e18060300603001642d5074480c11400300070320103040000181041c0708542c1b03601140210000e807850722020040d0241500c180c1d5515039006503031449001e045607001703460705080c03a400c080a4002c4a00c1e000341d800102c046103c120190000001d4540704540c0c5000c110307151800004400034441164400c585065007040340e0072404a0f007000b021071003042c002000d880c11501812980c80c603503070070202404807102080c0780e40000031400040d0205c95100500a50344151466622040d090480c1c1c00c0082c0030790340c1a84500784842d102c1c0800c640301c1c2a21090700701c1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 141118444 1250 141117194 141117253
    0x14060604091109090a080d0c17040b180709090b09011506020c0609040f0504032102071e0f0c06050306030709050103020306060613030510020a0801051f1d0603011511 73
    0xc1c3c0799607100d040c0342803178034450006145050001e05860724981c198040101c0404596512101d481c506007504400b84040ea0003420403002e03000020a00c800c120790245080402200391148143d035507402d20292000c2040485501444c2d03010000c41038403d10850301c2103030002d480d030b5986514004020352904c0020441502a05000800060548031604491003102c00620100a03030700e0107081c000c100da0700c4c020610000d4404007216194594050007541c1c002908414000e2403401c0081084940f01d01d080380c1150000c24041d01680402c3e14407210700000e01c0c407512001c0da20b191140030981000c140b9001654924500300c018000750320000740003648144191229a560460545131f8290680c1c280d00042181c80b8a00c08408080c0c000c1c0c0151565024645400f1040d980b58000c22450385414a961850074400301d5080443c1c0e1f1054001d0843c42e0201780300009c0b110304e0714001c111503900c01d0708a40c600d11024546032151990000d801c5040b004400301030079000e240401c262083c00e40203002e482c07 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 141119694 1250 141118444 141118459
    0x30903030e011b110f150f0315061201030209240d03020307050f1b090403020307060504150e0610060201020a0203190519080411041107080c0a02090103140606040911 73
    0xd002e0340110890865580e42c506086980c100618214aa00748815030503402080110074001d043e05015015070302c41c120045c100d40c28841c00e10000e240f29000205041c1c0c00d0013100c511a030491700c2c0c44000f00910550070540c0700c800e41c10b43c01840503451002e051a50040d043d011003035151001f0b0046030980318030844401c10109000e050881c614007605001425500580c0b90840030044005031520401600360038003c00c140b19a8208051040c04660180c00760f00f00b008182c0005025034409940184512205110350541d100c441c8122a400c01c100d054540c0180d05004001d0394502882c80203040601c02580341c00c10a080080d00d900400300442d00e5030030703601030b50f4040600802c01d590030345540c405880200484d2241c000c0825000342e400750380340940c4031500c440a0406004606010345200c804500d00b00b05580c45034082d44c400d00c030496603409803802c0d840042c3d807102040f44c02117006c1d11804240c42a5242e4190070700c2d20140415106502e0700c103044000404030003010b16070000c2140e000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 141120944 1250 141119694 141119717
    0x30411060a0c1410020a080a1109060a0e011e0903050610051f030e03130302011d0102120705190f050609061b0309010f0f020c07050603010308070209040203070b0d060509090a03090303 81
    0x25450410500d041e000704d2800890555030b910b51014000e445404807420901c54000720854201080c8a081d0641e0b03000700041060340c210f5805030080d00310485061409084251405035551000d400941c51000000c0c02101c0c100103000c1c040104941001214261407080c40c50030001494560201d00d550040049560308042154040c1c0e04c020020b51401c400e8030b540e02c2c51220041100c0b921808201c0c081010f030a07207480400565544130021030380c180c00034040d010002d600d03c982034002401c2250103108001103216a030010046003420340b0b20564840d00080c278280341c0a401c01074000c00c002c8041c0d00101c1040148032100d00500c4054094115141d900d40700c840305140034000e6000d0b1680174071705110b030340b0400e904154010f02400e2030f004196041c140d2640c0030055188400e110181408806106050141c64803220075034003d440101114007043d520101000c29401922011b00c8856440320104400e00340408503d0344a1020005481c1c00d80c0c040e50090102c43d031070300019003000401401e4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 141122194 1250 141120944 141120983
    0x90f060e100e2205190509070501030203090c04020c030a080c0309030306061605010504050d081f09020a05070c0e06040615020d030515190f05010f0f0807021e03030411060a0c 77
    0xc2d060043c5200c0c4020310191200643c10026202c140c80c01849080c804d420081c6081141c810540070b2502140507000d51407900f801140a9040030740482ca41e800360710700c26441d41d80c0d5440200b070700c1080c00c1d0103151200c1c5221005498070400804080508008004000c4042400f108880c4c2c403500071501c0581b144102c00d60569002d08441c0300425543c6000c1c14030050080000303161400781c032550340c1e401e400c0e81d070007030030710041021303a4251400070b01240c0d82030010407066000f40c004c5144901d46242802d44588034210303018800c0c0e0150f5119400002406001d04003030040344042c046040e00c0c01586480b41000964602c0240114000c0681d07410110300c0415402000d0340c45100001c0080720948415040494450260b11580395040c206000c00141540504a004c0300c401382c6884004000d4895901035419032001801c00c4114001c401d101005030f072117001048da04100c034800454a921749480d0403040d4624500c40716100d13000030b220b50784026520000c418000c80d4880c01c406525a240401e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 141123444 1250 141122194 141122209
    0x100203100b0a08060f030708070308160506010e04030306080a020913060603080d1a030601080c060f0c0d050408060603211309050403020109020108130507090b01021903090f060e100e 80
    0x518168003000819082460b44040f10038094039044409200704c120902c01c250355081284601042500411b07010408110403030301520072080c170031201c540229290798516090541c2600080d90062009040c0301c01d0562510601001d0a0300e00c009040d0002e1f0307500002c4110741d0080c03030f640c45c529200781c401c8100003054010400556010a04a40f20015034803198050113845080c940c4810045554010610300001c04504a4024001601d403c14155040c0015a0700855030900021010051130360f00da8420001001142c4441c2e46030758a403410040d8403400c00b5000761900d840380c1c0c40010260300f80442d00c0e90307405081d880c0c1141140d9580b40c1400300201300c18690b02050f03885141404110600d50107404c1a00b62a2003603860054075511402102002c950405c00589030780d0103800b09000d225400c0d400080408014011a252a50002c5d040070a0009000c412000542c28110401c14041c2020350781005e068a401e140040800c0715020800c0300079080c3c640d0040005011322055284c98005 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 141124694 1250 141123444 141123449
    0x60209090c040512060c19051e03012c01050f03010e01050a0f051e0606070c1e0e09120d02030a0908030103050a02130b0102030703030b0621060a0603090510020310 72
    0x8010401078640415419081d070082d22900c1d0140901540d111035160000c9a01440b03030302440e00c09030030700c84419a491044030300381e8644011f201d07007049004d080c08004c10888000111088801d5607079030500c0c0f050741c00030807000104510304002419000c0c0300081c1c00606419158180c8142c1d0170031a00100190140114800140741075181006103d0128410340081101d020607100600c90f617106d441204250581c4030505078100d00c4140003245083c40c001d00140050ba000740740340002c488c2c5a503203500b02c2c540450429030716030b400840100440c2030414000e903803041c0b0240240a1441510a0405542c4a0301210682c2c41d58000300080c2811001ea01040c80c0a1f0800440c980b00e41e1240340c42540c605025030b017603102c1e40103808401c03443c0c040c074010308501c0c200690141d03040444981d81900900513180748250710003810f11101b180000b80c1d07170905000c042c6000710b09103241014002c0c083c181890b42c02c100d0800d0b090510000c04103030001391084101c1124000180c0c1c2c2d90700c1140000d8040d0444c0c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 141125944 1250 141124694 141124699
    0xe03100e0102030402030c0d02031902061312061d0a0213021e041e0609140f0303030703141b270d060902012c0103020a12090b0915071b060209 63
    0x16520003911038055026611882c82a4111800442154104200d9010714900258554410f03e042000394124842c02444148003502c1a82445c1c0791105010042e20079400449054024940f0401404000e0103107802e03260101c00401c401c0d2001c5030b811503c650107913001038010035205180301010703a0903038100d4042c2017681402941121044004219940c0140b140e00011807050000b603500341303080e9043c1381c1100d001d525584a21403510304290b0700352846440081c1e01a4089a854002c0d0704d0520095120740032643e0000b600c0005000c00c0e08003120040c0114071941c10003140b0ba0001403100007100c204000104919100e011090342500142050710040707500008449151001c11960350481e0140600c01d8a400c04030354400c40d04541c00c01e140a400e00c024004000c000481d550190340142005405860403c40f0024081450419600301403012100c0c508003000300300d218002803148441e514500341c140e4040c2d0914400045c071400c4103201013801043c10b281e015082103844d0b4111104102e01 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 141127194 1250 141125944 141125951
    0x303090609060702100807020f011107060c3011041409041b0602070e0901021c0203060102070f14040c021203010303081017010c021c0203040902030604060f080c010e0414070e0310 79
    0x44182c01086c1400540300b0b28090f00ca02105041c0e8242e042c050700c01103d040c000b4250410007141c4170203003d002c01c001040c1c01d010b5544d10081d0081c0300000720a030318103010802144090903074000d4404a422160301750741790710070601c010311001c54401c0380b1017003901c070440d406802d07501d6908000080b03152a442c0e603001d0440c0840001001078012603901c0c21122803800e5190310380d407401da0850a03071140c0f582e4500c940d0007203030311036040141a1f4050768000c10184100d0760700984a454000c0c106505401041541c402d00b243c40a580c40e15001d1450010b50b136201400c04600c480301d040c541c1e0300060000030144194071001429a00c2001d00c03140040c40701010039000e031256510814002e03d280308000f80103005551003588441954400980040c00c10740c01145444c1c90220300000a4101030305160703026032600c0c170004401b441d0310701c40c0014081980240c2110b000401c0017400c034180313081215000f142041103403403404000540c2590b105500341012101d00030405d0000b8100240400081c880ca0b18 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 141128444 1250 141127194 141127219
    0x50909070803041203080a090222020912030d1802130c030f020f0c0706050901051c0e030c030c07050a050d11030f070f0501090506040803031308040509040303050403120b0303090609060702 83
    0x10959001c03130b0f20b4081d4a400a1580703c400c02c800c155000090041c0d0012543d1002007080340146091003aa640e1040e00103003070001d4640010b5000e12203900d510300942c00880c030726100603164490b030030184265020b6014004059030114154520044069481c1d940e100241d0b403029003c0d8100340c0703a0b044071810841d40c03804e1903c1c03013195980059081d00714511403403101194403400b64044500ea11816103480342810079043c0d0303a4500050380fa4003442c0d41919105001d41e01102040a02050f01c0280061902c80884141d000d1400b88944d00443c4580320f214030802c00b507142e80e02845e601e075410200c44200c2e601880046840e28118070015895407041100c006103580c0084c0c455001e0f641c00340c0c0c4601d806c55030b42d010400c1a000718041c0a006400801c045488060071209030701465105426040c00c02c0e07900c6000812448044805801103a03c440401007003642c80f129401c02e07038920700020010400280d010035030f01e015841d800703401410b00040c40001941c1e01310a550b2136550041401182d0750 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 141129694 1250 141128444 141128459
    0x120f0804030305031602010e030315010c05030a0915031509050903090d0b06040b0105121f0305030a020601050922080a11070b0d0b03031611040219030b1306030305030105090907080304 81
    0x84c011968140c45081440083c1000d83c03041c042c881c100b00f0001c0041d421500d40d07010340c464200c40e98542c9810300511180c6c010000f0414000742c0000080da0b25551b882503d0700d00f684640700405e0040300101803601d5003040468031840b024009132000e2050002d141d036158034103940340d4400c0a0b9140d5110601c0e41420040014441c6807521502055409010f1000038900540d620b009034102240c0c1d01c45c98000051503001c44540c810500c00d511121240e0035a80d0707842da141140e01484c00500160401001401181000086542c0004007040c601c08101c1d020311003407000001840c2c0040c80c4081c0080d483c03079440c0c072440c5480c4c00000b0302c009480c12181e035511440142ea00c9820048050780c00e000030001d1071300e400700603a01c0303008040c0d0f00d51118032015581c5525001203144141c0d4820350902200070414841080206402480e8030001403c00e1010200710080e40c82c405a0268039041c00c0051000a0b030040940307044800603220a4043d4551100280c00c24803a40c00c06010741c80003040005002 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 141130944 1250 141129694 141129697
    0x30f0c12131401180807050102211005011b120905040f0f1103130303050402010302070803070c0507081b090408070f080414040203100302010507050708061503100e07120f0804030305 80
    0xa02c915000d03030750082036120700d9099648000c1c2103611034001d0f400d410007050700b600c001c00480f44103000040c94001c1c03414403045281110000c404100004108000c152800c080c9400007424003403d09140d40000e403c0c000f02c040c0700341b0710028204a2a40000780c07080340100c0c20f0f44081e1000070414818800d83c0580d01c00102078220301c110340c00e07041c01d020803001241d64048900a50a0410418408106480a5000c6c200103002281090380c200000d101080da5000510301030301160785d84070f9075241c06090542c600481500444500c0e00b0902c2d05091310a40440b4a18103440c080d10f0408595560f41441c001c14000d0342c10141c051600300d4440c404002d9200024020b450031317500c001500c0e034001000e00c0b00303c1c007045450801c00d500300c0a06201541c00f4070003400e4904e109a080321442c42c0c8464115003898070980e4003608008014174544008d140a2040c0022812082c0c020001400101484c690b81d90f4517210301040318404801620500c0080c080c134951310f640200e0300030350b900d55900d13004045 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 141132194 1250 141130944 141130981
    0xb0d0b041b0f0e040902010e0907090504050c0901020c09070813051002030103110a0b04080604030c02130c08190504050c010c0f17181804020103020c030d0f0b04140c030f0c12 77
    0x31480b841e40e084030320f82407180282c0d43d46c069503000700e0001c1000c1070100441d406005081848010a0000f030150f0310f42c040c080c42060b03c00291501c0e04044d4001a00d4901a0350b0414030412900c0300304002c0c40e5022400030342c04880f542d0361015020b10750504074146000c3c0004505124000400070062203210300030f011071200259110110183c0e9810007407a240543e00603c41300c1e0304454081030100c1d1060740b4510b203250000300200600100049400c04a641b200c080340081610a0100030950b220350800040c0295104c005100714038103a920030391104403001c112418003402600036014440352400d02160f0350b921100da41d081003050054284150042c41100036502000c1d104058076040c1881200c2c80e040800103a5640368540381e0055020f0740080340b518038244030901c0640311480c068002c0140c1007800140014440e0486024002901c610501d4062412515828800012258812240d100414000c0300c0713142c1d110004000e450740b0038111941074040042090020046584074001c41 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 141133444 1250 141132194 141132197
    0x4060b010e0d0828020d35150f03060f07021504030819090b180f121e030c0a030203061908030a02010f05010b0f07020a121a01050a0b0d0b041b0f 64
    0x8074080d04202410341513010f4103120058100b603e4075243c03540281841100e50130341444000c1d0b91050f000c81004010550040200c5585000043c401003480c0d030b11940b071012038140e030b54113001002900820f41c0c0e66805403100048090000c0042c0809100307103c1c0d18022030605021850310b04007418004c12414042e1030a58a4001525046500968521070382810a611445005295aa0000601c40e03043d000d0740e208400e000f280051602d40d030040c86200030440381113800d50f0b11100c8030400322074030b0449c0c00d401c0004040300f04240805454000143d445a40d118500983d69650301c4000c01d00000040d0200303a08402c40882c0810b911001001070318034005d46500801c200b03c0000d1003402a101c00384601d1840c003208224141d0807a00c0c0380e008010050001e004032291a596510003180a10b6080051341d41c9400f008140c0312045010691900402c41102d5450303a45051240004192044000300b40324242d071496400d02c1901d490308011030328200814034204005865070040c0800b0149580d400 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 141134694 1250 141133444 141133477
    0x21b0601080c011e090e091005090c03070b07060902030d08010e07020c010905060f040803030c0a022401120204090b04030323011a0a14041206060504021204060b010e0d08 75
    0x100860005a82c03808400160b42c0c800011a082e440c1e104034441d601581410484e42c14004140078040360441809000200d004103407460400000300201c400c0078103030a40e10b07000710112480741d5500007425403c0e030341f42139440c03503407801d02d403034444002e12400c00020f4041c0104200c8080d22500701c50054100c1c0c030882006402c6075900744080740c0303810603030b8482c0d0302041d102c0b41e0078403490500c08060030310104e410500c2407815485000c4c184c6950011240f2202501000801e0b880342c550500c0761466411640306903480091100e10891080401405000945507500501e601950750780c0c1c201c1a4400d4001d03030a01e405003003505005015003403036560270b034040c10302020000c050450000c02a049070200001c22485e4103644034205551760200a0110410090000c002c2000310241300400003400d610500501c0384045107004030030b640f80f43c3d100b640b240d40f0601140c80d2188c4201404c9034080d40c0305030005101c07134040c030068680c00c0c40d4000154026001640d080204240c1030002c1424030290148403 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 141135944 1250 141134694 141134699
    0x12050a0906033602030f0f0706020708030d0f1b020d18060e0907090305070e011d09190206040803220f0b0a0c050718050a050609092e021b0601 63
    0x950541d410030702c510400d01001c10303140b00c42812601c945400f00010041c8140b610780d4507000a8542151107605e80902d41000300701d42c00039201089441b0050175180081e040c8540b8000090341c03039005250404002c230742c82d40c455a610725003c1d070101d0200c00820768800c4500640c1c01c0025920458032a4032008945041d5075001150b60310103071041114416914a24a0031504041c84543c62000d007615080c4034503108040300040c0c09004950250a81e030145080c01e40c5401034120703001c0c1d480081da01d00d404005c414031030700b5200400d0382c000300301840318410080d4090388086031607032240354004840750001280807860b050303104100032004500710501412050300c41407840c032851032512504040c200304101a45140340240070b000d202a00920559401a60b26040021200c02d90942ca11100340e980f000c02c00424081d2085607000401a1991649461300702d00c000d03940c0141c0ca1010101c0c1610510100091420182c8025411404101551a280081e509200d554204541d1800d240681c0001 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 141137194 1250 141135944 141135947
    0x1e0402032a0a050402040f1202060c0a03021b040216080705070b0f040f05060a0c0312060e04080702010f020616030e010e011a0907050906161a07050a0f05030103080406081312050a0906 81
    0x30b4400303031404034040c03104940c5460311105c3c5005060004980240c0242f05607020b0b81c00c2403000780411402a0040d0051601d2410200349445084441c10f100710f02c10300c50190709482e045521644d0350ba002c0303030059640c10f640c14168a050403035440b201c480400020003080002503013002d0400c680040380c0c001d0603c0d4a941c10003249005503445200010b5130070b100c501c00319201d000140744242221000082c52519420b082c164040202c60a4514a20025140c01196802050020a00d640b44050101402c05080c503807060a5031100715820180c0300c1041020202081d8002c0503007205040003040400382008401c41c200d400300304030b41c1c400c5c1028400105024000c408440c80745038002c110f6494030072002001011251100c005071001466080801d00e0303503012840c4603004942c0c94861944501c0d00d001c1c020840c0e1501e001c480c04005061004100040003c4291000e55080c2e0510302c5207035403800c2000104082000014000003a29180b268010360010028490f09025680d400c106c940c44010 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 141138444 1250 141137194 141137197
    0x21c110d090e060114070c060504030b0105030f0706050a09051f02070618060c0c0503010c0804050705120a1101170f070305070f120e01020f070501020909010801051e0402032a0a050402 81
    0x2444070300b42c06100004200358032501c0c0340804c10380340902c0c01d03003030894507203c051075a0800e8000c40c01180f0006403e006004d500c0442d02c2c0148000c90080c030140307401302c44160303c81005115801c148503000c01c40c500708238061080034024000c003800741000d400c0147d03105082c0c803002007100009805013000214519114070312041d0560307a61b804040711a458008119003031980001c0568240b61002d80c0888c1c981e400b80541c2c520745000c1c1d40c450780329003407600340703103043c142c03103a0000d841050080d903944100301d4045942041076400c1210b480000a9140c0180c60f4040e081c184404180480010000f03480314141a07070340121902c1d5410040f5980d0704400395510745460350b01c81d001c00c0004404000f2200d150308019208880b0344001741c100a402c0d03401100d15000810112143d940110b42c40d9124180301420500608000c4020301541c240071140f00401e914101000c0d00904d400b40001c0c0030740d202040441c2a29124941004481c107a05050056110440384014801ca01d04280082c0510f000e00 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 141139694 1250 141138444 141138449
    0x1401320106080103030e2103070309050f0102070902160c080609010b040b130203071107120b0a050105010e090408120a14060108011505130f0803041a070807030807021c110d09 77
    0x1242d2101c26401d40d10b0558145d004182401d51001c200c40c00c1801481d91200400c05000c0040001c645030a007510340940310741e042e5046107001c2c0c5c041d44003030000341c2c0e40020a0070894030b01d40e10040e614400c0c4050710141c101801c02c05030070942c9a000000d615840003411501c00e0704000001c00a10900700700b00015a00b1002425030b00054220b040d00b06984540d008507000480c500700280e2464002009504004942d8014900c50440008000510040d4158250b00042d00c07a000c00c85503041a001030441c90309034040c140204404400907040100503422100396071008400c01096203000b6440002414004200600303010100e07000c11000d5000c3d51b0214141c40064100301c5040c03084400460b03258000035489154030101c003400040c40940e00c60728001030041071005d980d41d641000790070042c04066401c14051000104801008105094182c81031140d141ca406241313600d81c41e8080380380c00240d900005a816420001c81700481d001200c07500311008210540d82c1e5504549419140b800e82132 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 141140944 1250 141139694 141139697
    0x203010908030f0a0623030c0a0305030904060905190908040f0306020304021507020906042007060207060b01020304030c0501050913140702060916120c030b070302090a0b0c0d08041401320106 84
    0x24191020380415a81d113103030301b041001d0100d44103202d80600240300c03000c503030f401504d03140c02c0010f80d1845424140a00ba001c3d02400e1411b221501b0002c0504084035940c5140700052a40c2c2c4911404000d00c190803540141212248821207689034205800250700c16101244102c012054100c081030489081c1d610540d0010140c1001d0394400082c032010f0910340c684401400c500407072040900c1417600c09080084d019080042e1290118507007003040384e21408619040d0b5000380410400160440400c0040e60720a2a02545070310600c07001c100071110010101d40c03410704050034491000034a090f414800c5000c0e070308451f115240c00030420785070801c000810070f00b44c0c440e1009120220006040d40f02c8240324540440e80039a8984032402560010b84950001940004114142d4038180c0703035038009803d21030300c03040c079200340710714040c0da03550b41c099421050201060000741840341c1c81045141d100500c40c001d000702c00380d0094071740000004040d1203148154007480784800e121500d4129042e40c00030b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 141142194 1250 141140944 141140969
    0x10801060f0b0706150801020a023301090f0b040e160b0a0c06020f04150207090e0606091f03170c1501120b09030c012a0f140a05070203010908030f0a06 67
    0x1e0307203d820117401101c0e40000f50840b00800003803006004d100400080304658007801e540d8644030800042c112405a41480c0306820b01c000c1d140c0ca090280d54241118100070780051078440f0000200c0290006400f40781d4080e141a20440c0000f00100c0c4182c0780200d618030405a150304d41420400501a80071742100290142d401600082c05e181c6c0203140c107110a0300414105580c840480000e600f14039000341c0107070060340c81000b8102e00c13401450b4010043c40701a1544e40b03001c40100c0c0300c08400406220794401d09141d030303007420411000840051a000303141d841c0030000320b5992480320352100078000c40510840c4d40941014890250b4507050b05e8a401400054003a1074139001c074000310280c5458801d000812000b41d44100034030482446e182814140c2049a0000d154003800380c07840420710b0240480b900c0c01c070030503a61180c0f007008004150b2644c15160542490300b11014010303024002c0d09036280541c200207010342c0d40017840c4510480840c100d00d0796143c05804003950410f20400001260 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 141143444 1250 141142194 141142207
    0x507090f0b0703180611190b0609040303090209010603050709331206080106050f010206040c1e050402030405030c0d1b0b07050715060302010311090a05150f03010905010801060f0b 79
    0xd40030020714101c2c0c040e00d020454400040204c1c9060602988080c0c04103030540281d1603011300601c0b081c02c2c0401c40d22030020100c05a6210341000300c000804040c89846c5081c00201014080d034030072042540c01a11900c982e60311190060024007041d2030502c041001c0c002d0000c0c0521602e190361b131228440c10300c1c2c2c00001c840203814030115403940c44039205114000c03106201c1401d8a00c120001440303050001b1a0184c03410081c80900503d0000031411904004100070104a400d03044104581e602506060504e1008500082c0c030703649600a01d03806400002400107104002019145070f800400586044440c400000d0340c2d4401103070003510400c2088891540030801004110360f001c05981000c0d441c01c14540e4800012012000200e91a290759004c14015940d241c40b61400d050b0342c0d8614a45441c01d03a50008038074104920406218049000d11000c0d50000c08043c0c911203030803441402d0300c13541c5504141016001c00d01440205d907180c84400a030009020501c00119201544003d2134a203 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 141144694 1250 141143444 141143459
    0xa020a050915060a020a0314040b070210200102070c0510021c1e051905090604030602070204021908160203070b0604050a140c090108060d03020c011101091b090507090f 74
    0xc4000d115102402c920401c1c4809502c0308401814071405039400740c0440f001501d0b01030300e52a5a55800c440d2210309002c1800004100030442d03003060340403507288804d50860700003180c0301c0725030bc0d15800440381090446a4000c40540107460014800c0780c44009854a0307405000f100d0290310240401a484803200601c480344d11071424407103652524080d02a000400c51034119a400141450001000010364050103000440d5400b000301c00c91078920319010000c000101da40c0110b0102804459000541d80c0c1159541c2e0304039403c03010740d00d00b5100e10b1101d000002d0001c4008803a8062144104024080b01d140301000322000c09600100c404a1620791006000007442c0050004600700c1c0d0340c0e0300a01002c5000b001461044441c001c6480d50f4580032000142104401750040b400b400d000203481001940105441d027608100b86084280040c403280003601512044002804404843c039602200103a0601401c050b29510b003001d0280341c51302c00c000c80303004000d48192420161515000c0c4080c4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 141145944 1250 141144694 141144709
    0x120f0a080c01061a040e07080420060403060e0f0607020105060d0611090a030c0f090b031b0a030f0609020423070f0207080114060f06040b072402030f090601080a020a05 74
    0x80c00c280300024160784c64400c042c020320041c0b19031040032000440c0800c00758008246540c2e00020502c0e00c485107080941e507510f0320340c24800e900d550f50004c5000040080c1c0755841a5030007980c002c2c50500c070300d0030703114211a2503498030000c0c046940189000035504500501071240500c0e07002c0d1200c1107040c242d40356680104540c01d54910941002c012050445c0d588601000145009402620001d0315004030300c402092180c1c4025002c506010b443c0746c541e0703004600c00d8040540081c002018051007400036600b0046034000070107030710040b84840240003480c2d00800302d5501c20748041060f0744480303010074141d10030381811b400080503800000303207154030581c50f1a000c03945030300489450a03242c2d40c50740c0c2520005c0080c00d0030003d91308208050761405034503020340003038240e030a28582420030600e07a81521030068040c211141d107004107401d4103201c004000001c0189801151282821500f10301184819159a000c610408002140b09400450a000c003150b00404021429140c0401c2c010f44 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 141147194 1250 141145944 141145957
    0x2030c09030d080a15060c080309010b0d030203040e13050c0144060a082a04060e040614090706080924070206010b0a0e0111010b06040b0702120f0a08 66
    0x1010080c0a1201991420400d85241403141d440d5015246051400c140403544851500e01031603810810400a003500403040501954014145655a50303480749075a0250142311181c0d074101c2d4021140f0028540d02002410907200d03400014529621660682094101c5000000c0d1040e0002f000c0041d1941c01550780c40080d035900241000345c0d82c03000c5600700a42081d03a04000881c4014006d15014602c101d030910b034084402c85400700503500708550940d42c0c5101580f021104034030100d5202011410400300281604003d1050040d0b82e210111040e4107002a02d0440d2100d003001c0c00c0a44a5401c2058244101001c500405620313250001c100c0c0d081401800d030203c80d00034141d02c0e007940c0c4c0c1240b02c123460b1994102c5981290341000c001c028906801644103000200301480000401544080c014038240300c00d18001e50810803810103180100300c000ca0260780b1900000300060110a82005090310382c1c0200ea03441d0308441800c8100381c0b200e0412072160104d80081c0203480006004e50045d207803 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 141148444 1250 141147194 141147211
    0x702030307050414130515040612120c050c04091103010506040b100e040b0d03030c0206070203071a0613050114030c0411160f0602040b0d0c0e01080103170f1303050601060813060203 80
    0x11070030717030880c1c03598120741098a07600e200c0d00788100700c44003070f081600890000b400070701c001d419104410b4540c019510214000c85003004850281a400c0c403504103d400c0c1d805000401c10410f03d04140381c00c0c100103032603521885c0030b0f509080004a8519091103620103030580030701801110182005c08880c6100c00034690341c0e200356100020007903500d0b50f41d5203001e07461280d01d00041103000c102e0042e1a040f0001d002d4001c6500c06c2003d4070003d6410b4044900e07881d140e065094260b01c2e000c00003114584014241910949090f00003d000d0302c0340300c1d024031400015025207511140d008144020745604540f071300f46014007003150509030106002c071781907041d003d0801d61420040559401007668819408900c041c01c0c042001c2c2544c24883c031030314010f8196820b0800e224808100042e004520510000c2c20441c2082159030740c02e280403007100c200c0340c1d4010000b661608010340052046c08240000d607214881c40c400032580d14042c82d1030300d01034481e0043c040101081035460102a6100030640728 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 141149694 1250 141148444 141148459
    0x3270602090411071101090f080304050409060f0c021b0102030c06060907030902060f0d0b0409021309020112090510050114030a0807020619030b1201050c071b03050307030f02060702030307050414 86
    0x141000f40b6400501038091003901068003102d16075000506a0700c0c40e170400c04480207008001c01c0b4090000040b030b0304444003958041240303c030340c0c00c0c20380040c1a1030003168a0325040c1021441c0b8290f002c00c10711060b9800140c4400c041c01303038a00499070790242980d401603651100c400b1820030314000c44001c1c4c1c400301c5460041280066a0b0200c3c8503038001c500241c1c10f07218003160002d0302c491240150307140e85406581c20088010a40c000910381c801428039000c1c5155151041015a40714280805207226510001c1c0998a040d150295441552445107131205143c10008100c0200465040704030f09001401000300701420384900d100ca61202108aa11240c2000329103440205e02c2c8006410700d026440000d00c2c00c04140a01c451000788026582d582d900d420104003903500d416098400c01030300704a142015048140c9140c100d0710558202a16500c0041010030425030703c00208c19140050b603082d00d80540700c01906903903c1c0000c0c0c40783e1010402c18001442103030407403c008180341c7c400603c2d11 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 141150944 1250 141149694 141149711
    0x3090c030714010e040b031204080d081b0403020607060e010218090c130302010f09180f0e010e030f0d091e030219031704030302090d050f010606081e091e070303032706020904 77
    0x48c0c198003d91119115070040401c440b190394000f0b603a1a4403d003100b81903010710080c155051041c1c8124040248540380c04a414800d010890f800728403180f8142000b195130700c40c10100404071480c40e18a40b071142402c000029082c0014030180e0b080b11315604920701400e8190f90040d20f810004d0500b00040100080300011400d00040491122620078039000130005520304001040e01c84001d903507202603040c129045681c070300000c1212011035001d581180c490428440480c0501245003000d044000f015045450b0303480c1d62840383c0100c40c8290201c1d5244c94804c825082c1620300004054040340049809203d00c00480e0b0360254400c1c864540103160080c84030003d13005c88040003042da0150300c4628210104070782403041e28090301003801d00701c03d00d2411200c0c540703015400400c0c081a1745820008502d40030020008154001e900d0607124116105501510340e0321716003444140c001074205400031098410305050a003550050101c0303a0b410441d5030301c7d6000650310100a054009a451049 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 141152194 1250 141150944 141150973
    0x1f06090e0d031d060a0510091e0c0e030a05030a0e0d030206070305060d050f1e011118040b0d08090907050301060e012016030b0901061214011103090c030714010e040b03 74
    0x1100d114170f01d8440700040c58100302861041d104455046071031110329052907107200c400c0320724906078909a2440081560700e08418216060081c5020041d094412881c0b03407003c0003004809440340007141e82d01d6421078200f07201000510000001f024000d60401030205900b54407903007180341e00000c003515901c28180b151796500d05d00244403400010907004022015490400b0750350f100d0b81800e0080c000d1141228001115810740304142c854408648150f05840840e00d80b5040a00c4040300201422950109404d10802d17513400b80542500c2210320343c3c0001c0d5030b00e018a003620f040e00c031981c1c0c0b00540f1010410040d00c06c14688158030302d40501d030101c44520a50100406c40c0030b02e1001c0140b10303880d4550711380a40e148801400081d5035074148003052040c4000483c100041c0d40c1c000700418a9202c500c90054018514940c8160952000100700010b540300000c040c00580300607411030320401e595800042500c6800e6051500144517512030040301d1406400001010b08020b09854141b07000b13416 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 141153444 1250 141152194 141152203
    0x70606030c080318030705010f05070f05030f0301140a0b0f070f020a061107051f0f05040e0a090b06040911062b091205040501020d08090a051f06090e0d031d 69
    0xc21603e9000040c2c4030319095581c000345649000c00d0b00101078407814000041c091544e140c1d0f010040000c00304940080c000041d800c07010f5550003005070395a40346c02280c0765005620034080c406200c16119003060b001c0c01c01c01b803240f0450b810380be0414104444400808440c1d4001e41003031b941d07004001300e024056600c0c8801640202099120403151342c50711000c5501b080419800240f09100c0b400316150070b0401c242c01c050120b460707440d041c81c0c404c134030260590300d5014503000598600307000d201700540741000341d0150010a0043c281951540d88500421060300c0e42003100030320030300311070044202030304040700900030f44002120b000d280321001d26004207501a00620b420901902c4210600601020b000843e6161003286070451a00b0704000000c1d50f81d0080403039400400601c2170004045160074810049010b17441001c0e29450401040e20780f640b81c046d04507001900d8034022000440d18054070540c40c030843c5903000b0300341e01000e06005400a200030b060720f0307103d41a04401000d104e5014031 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 141154694 1250 141153444 141153449
    0x20c060c031314120328050d0606080f0a05060f011d180109051e040209070e03030304120f0e030a0b0603120f0307080601080919080f07030e031b1302070606030c 71
    0x440000f90310740d0b44200040c1c1c03215100e620700940c10801c01c119542c03044407040f03c80000501e0810341102d5100e041122075100343c2c00c60b04241842e00703001249065005848500900064084490342e8988040c0401100e001703484940e442001c1d15a00306955009220080d580112200d0040590110ba8003052080007103045c94031088181c500103114540c0c1030720070560020100011500307025040011444085009000030784512960350000c1e00503842010b410421407405416203450742851300c0d00709841482c00401303501080c00d214607100c8040c40340321a8168264020002d040c3c070011500c880c44000000740c5980d03014041c211a288414120341d00a1043c0b03c10140c070a584da280c01d20b0001c1039540050405410400d060061141d0290001407010400f49a010381a0b003942c0d00c0d1518034050701c140507800c4a040004244c10f424942c008904060b03445065060300e1440c01042d504210040100b4843c55110319501b003001407403071180d80500005403082000040c0c0d10707101d48446034540301a5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 141155944 1250 141154694 141154709
    0x1030213080a0c08190b06060f040b0909090c01090e0405030c0a030f080f01051305150306090d0e0a0b070320030f03011d150616060c030c140703020c060c0313 70
    0x304060701001107a0300302500910b15a0042c05500170940c1311400f9507001340340003a0007101040042903442d0303218412103200890078641550340e5540c0b000980b40380c0e044a1820307445040c144001800b40035010413050784442c8143c1d95001e07103c0c10881c0010500704081c0041d18144000c0c000c044c10250204511800306019031030b20340c03566043e444003d18411000707003d410080c141d0300c01041903840c0e4814200b11030102c4207012074140d440c41c103110302ca41d0f92000300313a030305200f010140100d030040800c900340c0704c1440f80d850640e01490300301030160031881c511803608100020811900864401c0e4080c0380d402030407000d040f0400340c50020b00b81c034580222000325003030800000100810071040d50b945030301d43e86e0b50504049929000c0403001c031409405040c5801003000080012a60072030220103c0c04651000081080909008000b0300400d41e20b0b103814081401092034520b03451010042d9250b60b40d2543c01004405000c02c02e0002e5900940c5640100748014065600052001044c080280805 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 141157194 1250 141155944 141155953
    0x6012310050304020a0801110d110d11131703030c21040503030109050106031808180a0b0c010501060804050a02010e0a030f05010b0102010b12060604050403051902011b0f0804110103021308 83
    0xf90040110003031056000305126890042081c0b0b003100c0100a582c128081e071200000c0100714480c11804a100e00e84004403164a001d5448100c84003010180c07a900b6540d804000203151228001002e14242e03d114102c070317038014000074002034081c0c0020a01ca80811b0142054008007480035080710900303076001c54545c0c101000500c41c1c0c1791103200305401801546010310038100307400c0784150002d151007400b40880000058160010720800170382c200340e980103090681c10039030700c03210320b40b072038125964403c803950030709000040a603c654005d45c001c0fa000805044078a075650300640303464030440d2099811903010ba00000219102c2e032003520707040d0700820001c9228100940024210743c50700f545288954402122031022040c001002036120702e040d41c0000b01170720349040c1a1114040c0607090315801d00641c05400c1d900342c1c10341100201480421032445818080130741511005000d50082d0000303145240040d010074543c50300c80142c1c0c14181001031508081c4030031000302040720382081010380e02 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 141158444 1250 141157194 141157201
    0xd090326041205010e190b180c12030d1104240309120206060a050a230a050613031a01050d021c080a0f090801050c031311040c03050f09010504020102060123100503 72
    0x500c24012800306c00d02c0309144503c020f075500b0900c80400380807132a0581310344da00307403500c010204003000100b0b20080144040049424010360350b54030a0356252902800d0640106100c0e0200e01520243e503c030040f04840c620b401601c000f41d0781d4a003440d180c101360b1034940c1c00002c1442c0c1c86000481d100c056028011600c0e280302886280011940302c94014105003004106a18100365920031414481c04071644840d0f92400151140c1e00c190442c070352007000090217a0510381d0035803004040701d00c50409030344142d2a800901d0700c200d1091084580103202c0148410052a1600c000310340c217440c540d1001600c0f000768544001c55007000999101091031000f401e02c256800c01900c03001402c0e01c00c02440585441d15906000c0e00000e4000201e281c00719200b5001c1250400b240e1405d10000360082010b00715000000b006031506840c00d061103200f06020800d01f40c010b01800744a075030181c0041549910b0502d2003840b003445428082c00b40ea520a0465244d6655500c0d044012502070f511641c4906 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 141159694 1250 141158444 141158471
    0x130b03041401050f0c16061533050d050a090f060c0e06030c090f01050f0d0506040c0e0d030f03020708030901020306010305090d080c070c0b0a020f0d09032604120501 73
    0x3c102070600b080c103007240c0c810841d0380403c030f034110744c071400b81e20054480c080f9051030608040e004514400504101c04000440c0002d1205e103410341d40090402200d8801d000308a140ca4080b04c0c7c50040710008004021110f040803680d084140c1003120a08000b4140301241c4a01e00080041c000840e500d94a450b0041e182c2c69104080c03030100c45045410500d1814215045041482030b046403a0287c06052003008807a03000d0400d40d4051075080001640c5d8104030781a5000404044038010f1003213141c041a80c0116110744094070200754040c181200c00388054a0607104000291016000c1580030041100040d039040055401010300d24005038880c01c1540016094440041040c4020b910101410700a035500c130700c245800201e651580c40c0d68011505106446004c503401070101c9440c00101c0300b890700d50024800e00f5002c070710002d0b2941313180112000c0b240d551140c4005440c0100500380b003500c0d2403801801003058100c03c0034640c5025520781c1c410110178200310381074820342d6640d001d080410 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 141160944 1250 141159694 141159701
    0x307030c03230d0c030b03030304060615050a0f211e0c0c0b0c0304230a030806010201060f060302090409020a15031808071b0905090f070e060a0b130b03041401 70
    0x99040c002c503520601010701c081494040c0c6440901c080b51100c040c1185280079501c14a6000f40c0641a41c0d581c0c6480c0c00c2000c05007810f407086c4c0308101c42e000d110410251044090328190780c4a90b0b0364448080c5c01c454119082d55403110800f40c800201c40500d01c28800718440d500b40c01c0980b510403000959107040030003c4a1612040c00d0a01800c101050005010381c2038045c1e210074801c1e001034481c6c0381c0b800d0456071206400c03220310040a030f40351494614080094000d05840c800c1d503800c2c12944d03135800124262084c40c0f2407281c111001c89014019240a034000d0005c0705005480000c0b01c0d680b5400003003c0310002c0c3d0000824004001380c01d84042d500d400b0b074182d078a01190110a4407409652600c50902c11694082c2c0407034002d68800d10f0140d05802c0440081515250a12550400d42001529810410034500e00c6109480d00040c00040c3d500d1060320a41000b0071700340c0d400340340000614540d84032803a41550b00b4529400400d809080a001d075014901070318005031402d500f8490315085 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 141162194 1250 141160944 141160967
    0x112021308250b160b0709050a09020714010c1b170a110706090e040305030a0f0c050426120f040801020c03041a270301090501020d15060f052205030307030c03 70
    0xd10804000884d19804080c98103082c03260b000b520100e441d9100b840840d056141a00f080341d010002c0c1400081000306900078014580c001d0700051650311046185501f2200344508041c007203019400c01c000041d0300c1b070b50342902d841c3c0070740c185089011044007d040b21b90b01189900c00429524500040820f2040001502401d054201191403600b040391031500e50388010801400c009001000550781c00c1c0701e4110104424004a040c80310b09800d50380a0241c1e0407078056030342001c950b0581448000c3c41000c0a00040e600030024221011450645055503404208021140d45003008001070200007440101440041c0340701954507035080c9800d15048002c0e4050600300707030405001900d040c00342c10301c080400451800036600c48004860100f40500252440500a548003103101c510901c441c3d04042d00000c0911200b040c0355071a03440603a07200b02502807001c002031040c0201c410240d6003840c0c41010425000d80804042d54410009103540d10903103049001401440754a4101504400200708 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 141163444 1250 141162194 141162209
    0xe0f1201020f070c270f0615020706020c150304150207081303050601090504030f03051b07030c111504060c061506020a0507080f0c06090d060213140a0302011202130825 74
    0x202c007000e00305400e06a0a00c107003e0340401d1ba40c2c10303800000c4481644004010403440d00c000c19910441600a5220f0810703115a40c00f43c018900c0320325603440c1c460709000c0c80341d05802070135066484585902050004404046003c00e90800040c00484e0f581d00151442101c110344580b00c030340c29171034014101030042e40001480c0d17007040b041c040025000341140c081d0b220310340f40c0010640d80c1c800c0ea50f05075843c04225140803044c001111001d041e80440800d1006014082000e1204404c805114003d00050b07064126510140400d21015118512018070359000e0540460b5106103451401d0314080c43e070b0b00c00c00c05a441843c07820304003c0c041c080c8000070f00f00740020f0502c00904c008410b848038400c4600c04d00c07400b4000342c00320380c40c1e543e214521045a0454000c6440d1982c0e500d01ca0322540440c01216071605082d200c0000d42c0c0741c0b1004810a503075043c0d603200d0f88a0401e1710242d0294000c00b0403184e98040000d0302003040c900800c03215248181d52107003000e2407202841080d00c650f100b50007100 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 141164694 1250 141163444 141163469
    0x50304060306090209091501090b03010b1b030906160303090501050f06031006030209010611011407020606031b0f0f13050c0307120b0630070201090b01050609010e0f1201020f070c 79
    0x40b50f56076154900f035400b504001104003441fa10100480d16035110340c02044001801200209003040860060010700c000702407035000f09030340c0c1c040360f50b507e0003849503080d40401e0400c002c4014076403601a03400c19030b00c6428003207028103942d6660b500b500c002301c842d0310071035950004201603440e0030404c00c40b0000e1990702c100900ca05540105030848014043c0c40140200c4a48030207000e60254003110340c400d244064188103050001c4001e48405090380c440c5d110b441034a01e0540c4000d604402d940c01030034000d0400c1130f00c20202e010300121008060403607a00c140002c0254400301c091340103191195104d8944140e0b645090280507040c19907162106003c2c514180300e00c80c181c0ca0b02012518020b1040d14810140c40d9220142510302420345c1f0103e00e582d03c0e0000380074a0540542160050074424400d00c0c4d016a00c80080c4002409050502c1c0d000031000c0280c0e4070742c0d080c05041c03443c108134003a0404511303408030a4142e00b0f980c8200305030324003400005548002c1c495a5905940035000703072040304 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 141165944 1250 141164694 141164707
    0xb06090d0201050306030c030a0c030203072c0403110616140406080a090f021801081b01020a12090807141305040807080310051c0b01050a06020a030509041401030503040603060902 79
    0xc14102004800a060010000c0841d0255030b04009845594900034115401c103006490520709028661208074081c0c4240900802d01e0003920100d21100c03100c0080b0003903075034110a410078a4881c0504160140000c004802c140044207100356171182004884c20030311324195000c020710003000800751002901c000c0c0000c1c484140d02c00c0500f0b80006200d60003181015050510040360048070300001c0d84140c10b0360314001020303000b10446048602102c1959007011000c0d5464442030340c80340d07000b401600204090750000b0015200b80740c2d012018900702440c19201c20b1150718100058001c511000074151a003915460881c9602c6c0c69030100100a05c40303414a55240113450040a03002000d08001000142c68040c031240e13504004c0078010305004801c44064906026100030340d40c1079811202d514004192401d1003100082100e001e540100001d104079101182c940d00302d035031440d610a8441c18403c101401c2541c805000c0d5010351302469031940b400401804172000d640c4000e111900500c42c2 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 141167194 1250 141165944 141165949
    0x503091b0a0e04290a0b1c032f0a0204060f08060c070807081605010506010c020a090f060506031005031006030206180f030f0303090d110a061806090b0a0b0609 70
    0x1a8030841d025200c010300c2c0c070b484501e400703d80400043d440e8100d56000c81000e0503000e00100650703008000e01d03a41000405505000e01c030010856810200701c40e11100799400020303100e0b00812003503000348001c5170442c4e1440e41d0107540b540ca003e018030070300340c1c42203101034258a4103200340d00c0103103008050442071300e24200d031240d00c0d850000c18030103031144040307111414804500308641103241d100703d540742d40d440d4482010502000103003003500c5540c07030b280000701c255000781128555079400518000c01d1318600304400d405050400300c1c103d1140d444a800041d0790b00e898001c0c5000314420784054031081e0038001071600e44492026100b48041c00c0c108108056201c02c0d04480c0c16050308800d84040303c1d280d0b004541903240b20b01010707425202e103c074a2109070030080051401303a0b409100782d41541030751034812141041e8404841c82d06410030800c2c2000241c840e0301440540320028901440d00d0720076102c0004413415810300313071130141d0341e0400c00c089034100e481903540c0c52804036030301c50411040c20701 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 141168444 1250 141167194 141167209
    0x6020f15010f0e090f0601180615200f0106150201110a0503190e03030a09020f06070b0f09150106090602010b010f0f03090206090406032003060f04120e100503091b 72
    0xd039150b4080854013080303403403400b07202092040725804d04030342045d40c0d102c101480754440d40d07882c81515031505401060503070360782c81810412012565080700410940d80300318014a900c5030745095610030300c1d000700440442070240c88005c00c4100128220001000400ba00790b8840400d00d80c0307250020480920740e84d8004050b04d03005141c100480f8003240c140c40c0074400500076400c048070306110101c104040030784590030403811184250340d100a80408602440740d240103e90000b02858240c80000c0c146009007061240e00034100f20403104041616861030f03002d28000c1c0c000030b0018006940c00d215070394090003000310f00002842d0982100e600c3c16002800b0541c10f0780d4480425850b9009071041d9550342081d20034a0b40c0c001c0082080c641c0da0300e04040807102d24640703c01128041102210320b807a020440703900c0784980110310036071541c0d5950f9140b1607001407040d100c00d1000d40080f220301d1380c44454000c22801060740b82c11340e49050075402e082c64100c1d010524405035090f043c600b1001c0e244c400 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 141169694 1250 141168444 141168449
    0x1e0c08041221050c0702040b06030c0403110a09091208090a0308040327090609180f080c100507050c0609070506040603020a110d02030306010906080606090f04090b0106020f15010f 79
    0x18101407000341980c1014019880101400755003420a001d0103d0320138040c00410311103208880070092080180c05104040c041143d040d80c0142003800100040307206808030300c1c0410002022070b8010758071642018100d410702e00c0b041da2014044410020526005281150030402c003400a1011341c038243e90082c07141c0c00081005080040d000e0038120041010006042070b17108000c10140c45544829005c0c4c0113000c0c501c181010103051200025400300c20f00f44994030315400c100e00504480c1d0540300e80b55142d1090908a07081d00c1400040513a0002911503a40244440d5403916692003e070f1640c0c614180d00544510000c0c0c00410b0f04110300e40e210001c07030301110003500700540c407507100e200300fa501c03030140c10200045401003511480d04554040000e521501091322290402c40d2241402c46441b007003180c115410040400080c500c0e40350040070081d43c040d00030b00c04100b0250b2070b9561a86860300303900080140c0e00488170945e11050610500000403040d4680d4031043d0302d0315960f01c1c0c200c001c52 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 141170944 1250 141169694 141169697
    0x10e060d060f02070606080607021212150105221d060d110a030507030f050d0206160518120604050606010f0806100212040312021c0c030e0a091e0c080412 68
    0x5039411540d0b44401d406480b00709800890401085503075000403912154100c03900c1e00103009414107410b0640d40c51080d00c041d0004030f02070104c6541e0b40100700b000011202d801038180202489045100300f01c0454510081180400320003c481c40d01212042900340b800200c0c413000c1c100070400409440b100c5a4032865034001c031840d40010031850108042806980019200c1c2c051541c010040c091121400d00744640f01da0100c441c80c0c5982c0008a03210352007510f2100002000410300c03000710f03100f00094030448800d200e1302102d0681900c00180d040520045100302d9410a00410060200900c03d90ba8010001c2c20800000c1d254620024511070300188810703c580c4401003150031980c400c1169030480d848024016541e141c42e030400d034949401002c640340040c843c0c03080c0108011b000b001c01d0b00e004800d0f92101000c0d0b000f1582c06076041119400f840340c001c5016100062200c0081c040c0b030811030f800680d5024036a03056420300b0143c0b0302c1f140e48007007801121414400000d134401c0105802c0c1245 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 141172194 1250 141170944 141170951
    0x9020303121012060b0306100501080a020a0e0a090c090603060605040e13080714120a0903110111010204060c030314010b040b03090f1c0f1e03090201020a0209010b04030209010e060d06 81
    0x2034418006442c902a0042100304003405070340010002c4590290310200380441c101e82180e0764a800300d484040e1540225800551250301180f031440361a00507001c420481d05202e0042401c000220b54288090b6000f848030589a1100702386e002d0b00a80b40d1405041540340901059003807040203801d51003580314088846004d40001000c0c131007040c00c8164410340c002c04403076a03801c490800c452428040180440c00d405503004110611494500320f90b1115160740b20500c1d0f040c40c41d203c4a02c28940c01003040e0610210510409a8043c280f0080000d01810b0716440d04a000c0c5003002011035050000040815a00400500030700c1540410b0b241200c0d0748818240d9030fa50b80d11200c070300340b02c50404070030507074030403186d40c0c0c41d104507030742c4403a00d42204980e24401c156065200840c2c62850784480311f41c95260f207641840310036102707400000c400790060045658152036a030200f00004000d0f071200f40c11010103d4244110f10380460907500514000d0503595180c1400b10010303c0e22008114000c003101ea4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 141173444 1250 141172194 141172201
    0x50f0a05090a03080c12030108060601030b04091a09010b0402040b0d050403090f0e0601030f2a05120a020d111e030415020a09050102010c09060206060906030f1912030902030312 78
    0x22980441c0c52000c00988508400c943e280343c03a600d150441c89481c1d69a0240340b4000c11107083d140e080d00d049600c88c100600d01c0c0e40b561001500200a840302d07203500103840704044804178261495080400c103a40740c06d04668600031152a0841d1215559075100d130340108810007090042c1c00c1598095103000700300040c1501c440c60250359081c4164081102184a04d900181c511099102d04d40705003000c1c4c03018405d020f0150004021206020050780003049580303078801414085a02c0c1080610503400d00c5c51800e1034244403501d510404030744600c949500001ca48030741e01c0242c0500089020b00c2600c0398102240b03904000c0c040e2400041e00f270000500400080c09012424010503004a07202030110b65480d8000b070b0003050512a40111405903080c02c0510003d07512074160002103c1003540a841a902c4650803c022501c0182c0300c0c56152040a02614643e802030045036a034444c0c000a00d10304680070702e40035181d45c2a001000c001e043c5003980d60740245c0c07008005c444100900310320500c483ea4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 141174694 1250 141173444 141173447
    0x40e0c060a0201180602120705031312021f060317040303080106080a0603080a03140705030c070611190903030e01140f07230c010305060402070201020a0803040303022503110607050f0a 81
    0x142d007804072204e0710344505420702181d54014403102210200344844c0350fa850303605a44a102c145e58104075202001c418501040c58500c6107041540e49105881c50210440d01440e102501c5038440411710780d43e42402c2041024445070b100c1d800c044490b40c541070a00c1c41d28082d0010a0502c64142405141d5000031a03141d40341d8045006158042c101d42d03295a141d8800500038154140788400d45a121404200f040d401101500e00c5100b809420b9458003206903154005000a28401503141c031060144404ca0b900c141d2031010600c0d05a40c0c0c0f0035500b49182002001c0e007125503980c6040c007100950001c80d00761003a086420004403e070401f9918503d40ca400c144403e26900300105801e901400344041c0780e4040344400c41c100003681d0900c0507444041c1040b00301c0c030500b100240540e10002d070500000382040c0c003030340c1e00c00e0088c1801070030030041d140c481c201c0001c4607072002e5000d004140d00d07000701038200503c8442c0340401001003066147c8650090b1003842408003a412580c00410100801c5 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 141175944 1250 141174694 141174701
    0x1c1d0a050f060c0f16080d020a260d020301090e0d110303010603050c0c0f0105061003060e041b080a05030702040c11061504020f040b0405040605031f180206070b070201050105040e0c060a0201 84
    0xc440c0102100c0301300340070403681924101c40380161b10460141d00c0c0c0e40c4005030f2000502031059038000814a820503c1e140d01d800006007401100404048240040000c0c140703039202950003840e031124046070444070720242d076080c0582d03803603c03105100c01c083d0b050342071600010070789043d111a070130002650745031003c8101c2c1c240515504407180c0d100c0c0a29030507400700d040d0089030081c0802e98805c08109604d000c26070075030b641030007254031a031031000015002c501d00071000e072004401003404000e266103032081c80741070583c1b800003900ea90344005034560460401e403159450a440e81c0c649007000304841400c881d152072000d0070101d0181c14a40019507140d455a040700c03142d003035074000265a140c1c0c4500f000d081d83c00504c0f90034411072410500180509012880d41c3e50181c0c0c074840041000c640c26420070052407a184c418451a50199210005071161070052611a000c1c00144507941b4061400034256030058008500950038050401072440f00010030180c80b100c00c03941142c58441c540d6049005 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 141177194 1250 141175944 141175963
    0xa0e040c090f09020d0c170a02031203060a050a08010c1403090607030905010f0e0601030c0902133003122d05060310050408040801050a061401111c1d0a050f060c 71
    0x17046101c949410407036400549400c0307414540e1207a8800e442c0c0d418660b2640000200030b50581c10501070b910480da5108008c55002d01d0080607a000360361100049040200b680d0070880250b9941c00b02080c01c545c11080b02c3c0c4200c9040202c051940c5401d510080c0c44640c050013010034140c0381c64101040103005c0d0482e070303980d5406042c1003007035400c804440e81d03603500c0c28407043c5d03142c0101c404081761007487d0b4021650017001c900040807205180814650406c0940c000c14a020140041001104070892400700781c054040d82d00e02c6491019140e13508100c80303684020007002a08081d440142280c0e41c6c2902c1c8454554001c0003c0581ea824046414480140060f0304890300e4002008104070400f005401a207104034020400e80e40e900844000701c80c118010b14903080b4650360003820b158401d03200348070310000a90540c0e140c0400c2003104a0707003038014414440840e120b2042411b41000400d41d000004404a0304000f009142002154214a003915501d01501c00000e02640e41c07181000b80d03119 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 141178444 1250 141177194 141177199
    0x6030509151603050606070515040804030b160f0f08010b1804020307030920031903110d0302090f040b0d020d0c030c06120b09060310020a0207081006050a0e040c090f0902 75
    0x3280d10b8440d0390820a04009010100801e20f0f20020411909105095840140d030002c0104448a8005003148070304c1c034010012101e20808000100016000c882c0c1c10780641881302d0046c041c40c0c28200003400511081020104022031140d07002c0302aa84000c500e4115084289a6541d4507000701c200ba0035100e42ca0340c00f070340148c00001131040300790b4554040c2d00914012081c6070302d007910100c00c034201001c1c000310055040d48004a001c40c080300c1c0c0301009100c41e100e82001b0300e000700c0024900381404600d41a02c40441d9020030814800e0504401d19001200300701c604001b2010b056000402956040c01d029010707214150519003000042040007004c0e54102d41c0c02509a5650784000b8201c952951040d0401800d00d8080005d6060003000e0790701456008002e083c0041000240000070f41280f4a01000c6125078500012041024804807500802c85680400d0350f038103080c00c0c4a0148540e601c110460314100c41000302281c4810000d40c01d0b9551010301041820741440c1c800060a5540406503 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 141179694 1250 141178444 141178483
    0x1b020a020a0605030a1d280c0e13050a030216050411030a050a02070b0a020d06050607080d0506130c0909050702070501080408070c03020a0b0705010507050c150a060b270a050a06030509 81
    0x40001d48002030250344040c242680303a50901f6408503038185070f44441401000110484401d00002403004001544803803442212021510036071034039450604691010b40250304040000783c003000c42d40b4441800381406445c140841c0c15410701c4003035030f0f12008109022042da82c3c0049089030b500da0301100e08050700308803201d0890078907118a40081d0b01804c1c3c0628158940b09001505040480039981c2c0a078024046070700301680310a01101814004040b20384c801104c040707140c0c001100c0d02c13614500310030710341d106040181410003000440340003502c7c0708190b5101d48001c0041d0f07a0301c8031b02036034841d0740111a01c0d241c403000e1501d1000d00c841508000d61100d0070b5030004c1000318011000d026803600030002132045840b400410354840c403913104851001d40080e00e010746961103030402143c0045000000180b1160740da142c040e03d6421840310825001100380d03500d19000a214000d0300350810031070f08094943d10f80000207100c0c440d40e00c9804140b50b02e07000010804901031040703000904c0c440b040360 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 141180944 1250 141179694 141179741
    0x115021005060a120c330c02040b030607090302030c0f0d0210030f02040b07061503110d050307060608031308010605010503060d030302090406091d01090b060910181b020a020a0605030a 81
    0x1010303501c1c00c60090507800c0884050f0006c01c1030506414004000482200d580070200000045030700a4115100303a03009038460030000440c0c0c804208040c4640c90f140e480c0d400351402c610400d414961070708000ca201d605c0c003510000150b1f035280400a2075550490f00b4540121048600b42c000c1c0c4a0340c80413522071840868005100e040c400001c1c41782c940300b01400c02c000820040500b1580080780005002c00904040002c510b080004021845c20b0050003181e0074400d0300e0b80c506c01540c0c4907402040b619040440d44061030700e1207100708005490000001d10101c0d05140009085000092406100d0381030648040c082c18040d17411902e0240b00034000b40421a1203140d910040d00c58020390680d98400e401d8510ba50340c106100740c801079548a42542084e071540e00c104046824003400c461804441d400002541194007140c1103502c4d111942d0104880d50580840300402034060718080554010303584020060752200a1001500e1040c2403d580b6a21005440d00c003c1c07261030800c038150464030900 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 141182194 1250 141180944 141180953
    0x180d0312020a1d0607031202030910050405070f050307060206060f01110604050c090a0c050717250506060604140d060b03120301080f16030b0702012c060115021005060a12 75
    0xe410312403e80110002907040418288503440c402c001010f40003411100c04124000800c0d0011138102c007007541103c588a2244606500311241034a04842a40c80700f10100036000d1481d40500040c0801c07405040d81914162010351a02c10041006103d20741460408106a004000040c00301601030304440c0e203860549081d640e20002000d10b14441c690a40c0060304040d060300808020200740d80e00e250803c0078a0f554403510805000c40c40030070180c01d208011015883c5030103031030300304086400b81114040070f040940c1008005801540101030400c0144489603e045881000100964410b505071740076003000f10041070304610045d498040c05114207460b95650029505035040e02c415110031801e0000540d580c0c40954001c40c0941d165401e0400114203002442c90707001e040e0b400086400d040c4a400d107040350340100800002410744402c40d000a56040103c1405010300480100d00c08241c0c08010703584140f035030a1000c5c1d00b600c0f44005070700c0361900c105210041420700400402c00138140303003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 141183444 1250 141182194 141182207
    0x330406020a03050f1003081e0a050406030c05070f0b0612010204140a09090b0712061a04030605070c0c0b0a09080102030901140702060709060e010c02120d0f05180d0312020a 76
    0xc41d200180c02d2101103010600b166a85a01a102580000700ca00b0725603641c102d5140c100a6118003410303942c4c03190182d00201ca00080010b0360403641d80c6541c5505001c000703000c86214480520401c2814040400003c285000385d00c032450300926400d8940d60b440e00000e104000e22220782605500100e00040d4042c03040c100003404420803500c282c200c40e1511030b1401100c04021004d044035100a010a0661b07003d01d040b09070708440e200b40462000d40301c0c0b402d1918105200381001c1801000101041845024816140c2001d2685824074041c0d6482c2c9900c1100b000c980207104159800181302c44a40c0c0c056041b1030b00a025003c0290745030710380301c00b03080d00a050400c8880d99140825000030b1000c2c0c0301040552103100c80352141d103560383c1451402c4402c4100075802034184200b104410000d640c501108103000074143c8028010580c0d0048010030100c0020301c0e6400b800310a12540c060b080352a8034003090b240d011360f0180400c1110381411150310598407140e0f030495100081214003241c1c00071 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 141184694 1250 141183444 141183457
    0xd030c03060504050c04090504020d140a030f02012a020c0a031b060c05030d0209010e1f02010c05040f0b21040503030609160e040b0604050a06030605090601050403030233040602 78
    0x45007000700c295280148015210222907148140c4001c01051103200705c0343c2d1003d904603001500e03a007141810350342d556030182801030030380e8004d9129540440c04c03d503210701441c82c0340c0480c0c40240f1005009503003800384100300e01116890346948510503659035100b00411a044e83c00101043c40155980c00c08a0000500d000e42214142100760041030b450b004000040546520000030341ca070407866007803e80290080c403146030411142038803450250740c620b501003042c4880c105031031404025128002c0d084605002d9441c05200b8144810071102071594000c1d4112401d1291450b038810f030b034104901c44007000b1901d40e90443c80c0718040c0024080001301541c81084103454064003038072000000c1e00c401c000341540e4000501e00328104522410710390000c10040310050402e81c240340d01c900c009100d20005400c6000001e03603e210400562a20207005070b00164203003005172902d411034070b00030745540100c1504402c00c50704402c5c01d02c00e101c3d00301508255030494058614a42010300d00f0310042d50182 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 141185944 1250 141184694 141184697
    0x127120c0605040602030f090f040f0222050a060513080706050c0f071802070f1401201612020304031a0a05060a050603130809060a08090f0105090709020711030d030c 73
    0x105008a0081c1c095012542901c0c113a800860810300720b00700342d5010364469600103410030348440c0e011007c0c1d295402585a00c3d03140b11005a02c6141640c034001a0071900a1260999001e02d9402c0080f0744840f08607400740d400c00e1501d82e82d40c854840303001401d46042d5004403801e10540c4c40025100f80c1c09006002d05005107820380d004d0401700b4003a40d5a84809004082043c0d441c0c041e001c51200c4180e0007030404078800c0440d904180d01ca51610755418071109181c081e265111030b455481440f40c100201c80402c3d064144500780141c0000f0640e40900003a00108a000d0310201c074072204c2d000b04103440041d644a09499603005400c00f0620a1080942d00d4110b0315040c03170045003091401d11646001d070381014144d141903075281c610b51030003410314070010ba540e804100441ca0b2070b502c030100103003050602074a41c880607061403c8804d26110200150007441c0e4981014130200140c00701d0540b08482c4624809a20b80216041010840c65a04051541072162051100c0c40c9501908200b814038040e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 141187050 1106 141185944 141185963
    0x5160f0c021809101803030207050715050a0806030a03020a151d01050f1b0910050c060a0f0506100e0904110d0311061501020c012712 59
    0x4101c1542d070b00469810443e214204000c035802068010038204040074961039900303440001e2410007410146c0000d01da034180300c02084000064908880100c152414102d400f5180b0384c084c0031003101045d14140010850b10b4041491040c1c0d07170301a00505240440c1c0d83e5881c0c1c00340e0941c004051160354940480b00d40c50081440101c20704803940c00040c040c01e12000d4507005010050209506132000c6d10780c440c2c226101010707607414034001d40314400b4030b203100407095525000d411070780c1c0e04034403615080216640c1c140d0401040110340400c100303c580c40325001d100c10040d00841000201d1281c503078400c25403c0c003804069009015071901c0c0301040d116000160b059641c00e00030b03000240d411200c07036040b4100b8450315800807a045000360b2100804c00010391103054106400c2d05000850841d1075040c00b4030381c021107030b03000144081c20b0314640314143e520301c040705a401034625805 = true := by decide +kernel

theorem cover : BRFrame.Cov 141007194 141187050 := by
  have h0 := BRFrame.cov_init 141007194
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141007194 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 141007194 ≤ n) (h2 : n < 141187050) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
