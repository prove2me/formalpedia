-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1852
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:54:36.67452+00:00
-- url     : https://prove2.me/submissions/bcded5af-e281-4d31-96b7-87573ab9eda4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 332913669 ≤ n < 333093525 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 332914919 1250 332913669 332913671
    0x311062511160e0702010c0212160506010303030204061103031005040209130e03031e0601020c040c0e040509060106022a0d1e110906030f12030916080d0215040f020112060f03030201 80
    0x1505091003c54200b0002e410381086a1502c401949190740001e54410b80b00300020f401900c0ba410000840700d0f854000b40018445d0103100000030801d070b0160050070668001d42c840943e52120403608075501e000031074600d030039440c80220401a42c2003e600600301100d028104039072404078075150600f038070340c000d140e880319034000020849442a0034010510301c8001c80403c0b40c1606004000075581d19018090900c0b80d0350301d8068000d40c5001c0c01030b1044c40f0a0240007401285814009552100404d10401000d40660b81e06002d1580d2155440f070100304140360038070000f00d000b6081c03050700702210400712861141803174502c144030a000140b4410b2449000c600680300300310000c2c042c403804090543d034040d5000304581403460402059906080300c0c030224042e101c3d5103020b0aa85811018a100800e07414100c6000c10446408120490158203903001c68034441c0070203180c101c181e03d0844018144014600b00100150700c01e6110102064280c440031481ca078407280c003c000c01c40160300440150b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 332916169 1250 332914919 332914963
    0x309050312070305031f1a0304020a0b040305030a030b0d06020705010b01140414040b0f04051f050117130c03120e01080f0912030a0603051204030311062511 69
    0x585010050030611492428509061103015a0302503d2030001408085200c10340009048846d03080824070703001050000e5650f100030300c0241c0c10304082c0d80280c0f410f901032003450f000400c03009103410866041b01e5212006500c1c020040808400600c80301c1041540811040280c80125070039002402015000724000034010440f40005001007154450030039000b20284030030001800030104200e5207040a541c0030800c2c120950004425102c03402042c0c3e4044e00d8a0180014405802c1180118132a41c0d9640b06056498400540301083d08103002c41d0384c00e4042d400900284022000d20141911404c0d01c921540e407030780e0300c0c44c0d4080848002c0c4c1c3c0004054641d20300c52513070b000c090550000c20460310201036080050b0843d0710340340042c980d0020403a002020800452040d44020012741c3c1110556403005030b01c540d1500300780d0007840154005051305501540244000c50014000e103102c40803601d00d0406031050b494181111003100061200750352038038016200500110f0b4455180c05110a55 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 332917419 1250 332916169 332916179
    0x6050a02101104060c060f0f0c021011250501090b090c010306050303030112020607053a021e030408011b14040f0b1c0f0902040630030314040309 64
    0x14102a045007980c000b400c1140c1e050207151072034121020340d1030600c0e01e00d0815086080000251030041075840c7c2003441c1c2680c0002c919599400200c2c00030f081d03400d880500c0340c0b14846809aa440c100041c241d108104001c8a000c0100d860303009007031080e680c40d0501030032561619400c503039041005540040d01d25040002010301407286003035098090034100503960400000c00d68034041401400c00a54041e4a02400e540d1680261550355074807204640030000031080020302130250342440000704210392b109591400210807985500501036004000301c00c201625660098555483c0040343d000400021800400a00605038100e0f880603210203084111800103240e49805400071141800600060002c54010306a00c2e0898248600d55074585842d0041d83e064008508122856985010036a0740019400d80060722094000c032402c00c07079942da9035030020816200b0303615550442e180f240c1c0e46003071040c030040308204035000703280c0080d122601e80483c1003400c90903101030300450135445003085 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 332918669 1250 332917419 332917423
    0x30307020d030506180c03071e03230c0909040215070c0305060f09030a05070204060b04090f05010803040f0504021b07060c05120412020105090102010e010c03020d061d13031806050a02 81
    0x504400156081e040d44501c00c3c85009400c1c1c40070b8491030b1391b6100000414501d43c800d00242c0000c07136042080800c3d0240710800a001403104202543c00e2900386c1402c58000d801c0b040d82144181c0d0403400316803820300340707030100510039800400880c2c2c80440d0000715035055698001a1100b140f20b01110480942107080846c581a0001c01c020780701c0c1070500422010352404016034440b100d403410410388801c414400036010740010f402001c10100701180006905400350095031440ca1400e03410001039072a0052141c40340300794002d001c6442a0350000700154141580140240c0320300c0410119040c601003c02130a00e10740c4d034040000100011203040c00d02605000141c007210031340194916151600204d4000d850302e810700a0305000340800da41c00264000c1d00100308862607407000308036450042d2000760003900080350824a0354600a0085408195156255080340304002d0300703501580c0349070108442c46040c80e4118208481004113505019044400d0005001d040d101c0e50f450301680c10b4028 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 332919919 1250 332918669 332918671
    0x12090e1612091109190213140109050f13022703151605030703020d051f0902030103020303070f15230609060906040e011116020a060206010f0e040311030307020d0305 73
    0x7031032152816500d940010b89a0146820044069440c100d550382c55a0412170408000c42e45101014000618000e951004080c20026101046828841102c04400454949080707000c0c0c0350300a945100300c1c030031510b440e110442c060091400050701c0c055008504a40c1081140c5088070b54628030300310381e10645401e1000321203440303901f0f010070917601d8065050822000c079034020509011000001c01d5410f07201c0d070122200003840300420f100e0f9060170b0074100c0303201000c1450802d410351f0380940400d01704468000c40e412203170014015803c12095840e03a16840109680c102d070320740c003181c00900d40040c1c28000d18502045d07004901d44561101d03001e0803030700480104460300c9030301c954003042000c0c1c5e00d09250607001001030f5400240c01400c501c9042c0107002998201c05403c9004c85c0300c41c4920f408000e402c9020303100755030807e80d195842d02d059075680c60a024140d002d25008600f0300084000012242d4482d000f40361902c090300d424160b284c1154000d0f560400141c11040d04030300b10350381602540e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 332921169 1250 332919919 332919947
    0x313061d120f070605070c0b040f02030c12070504020306040207020a082a0d111306171c02100902060f0a08091b01050f0d0b10020303010617060a0312090e16 69
    0x182c41c008007041c182c91544549580100700e29603d502160340184030706034030a5000c1e0720080c41c545070b04090a00300c02c0e2003000c40701244a4450750b801208542401680f82000b40e42c0c40004002c50f60412003040040e410003460a0b403c19400d21212000d41d030750f16010b10040103410068160f001d2043d04402c8003d910203c031003504d00c8001ea0350511a1540590000115008542c4100454031540000e0720200301410041c48a41443e00100e42c2629121500903035540002c02c03104100d80044240340398004078240783d000340e04085280c0060702802e82000c0d000c0c40c80200706a1400c04450110b0205400c949040000182d00c1000c03c00400401c0208002c85200f690201c044c03a41c070310000800510032105030150120011400846d101100e8028018a481c0108041010b2411800003581e0b81c00910480c40011211261b03800c50078540ca000034001c6201405500c80c0700c1c25503c614500000f088100ca0030040a0b0b02d0018200c100b45c03400c07038001c0301c51204410008401c62030040241041c1160 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 332922419 1250 332921169 332921203
    0x3090607020c0907210203150102060603070e0c030406150608150102010905100209060906120618040302031608090a09061d061804140118030914150313061d 69
    0x4002075941c0c078009280d00580c9171030702241e6480d607007024903100c030310b0030b0384000d0307410f001000b40000f007244851041808a42a0300719460f664550003050b076950703060302c1007268041c540c0c000702d006540002c2c02540d110f405a0f40c0420f01214902c3c0304480d20740a40d1091000030b42107024013404128420650310301d21381c02d100034003000c003407911645c0d00c80240a10b951101c40c0e002401d0000c1d512201c0603607000c9800100784a8903001c40403980c418020040300d0039446020b02d04100ba0565080c4004180555015070095050082031002e00f085030758502d1301941c0c94182440140807695400c03403841c018080c00f00001c685145414441e0400b25441031603a418002c0d28002c201181d1182d00c0c4016485404854540003500d41e418107500380b000780850388903207508000340040203640b510000858584682d0743c4a10140c0e840c0700350580c0704594046107602c481d10380023020740f0115607070145401c03181044001c11504406d949841c22201c0d0901c2c8034844520203845808494418020158140f6114413 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 332923669 1250 332922419 332922433
    0x12030c070f0626060a09060b0702040e1b10090909030c020111010209011202071109071106010b0a120506041d0615030f07030303020a260f060f0303090108090a0210050309060702 78
    0x380000f0408a255a40da02c0100c4090020758156a11101c0c20010000d14000b04034140c1c803500703240c17180e40c040e540c00d901682c04c0036000d144001d0001149449489000506005d034945841000401014410b5400402c03040000116187e501803080c86101c83c400e03101c00070f4007842c2d07200140101c48454240e8405034418040c0d041180d07089080e4402020703c0000040c0d0f41c1f00c0c0d901d0804406881461282d8102500104100509820181042c06480208100c41050380d8800d1000d155102c2d000902c00007503082c42003091841d405401c91030300040001c1c40800c0940c9000703042001d030824042c05068681c040c40070300003100790329040300741c000c5c0065029054052540d50010323a2203207588001010554006007000c0c07954800d10480b0741c20455002d01d00e52410350561000e442090a4400e070440b0b5008401103411031504484600019002401860404244000545e60311030000c00d8406240038078404c01006a0340d100004903091480e4071102d48a080050210b80340c007900500a07019948000d03 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 332924919 1250 332923669 332923697
    0x14101103010f05131d0d0306091503080c101107020f0d23160b04031e0b01140102010e01050c03100e091c110d0206011a070804090b12030c070f06 64
    0x400b0019500141c8210072110a0076140100803d8903040606214401400852101401203450300001d02d4681d01480340e0341d215040c2500311044400681d04d260307040d039400c00026001d40040c0c1100b800c800300b0707142c950214203602810b80b4481d620344076844d8400100541186008070160010841c2500c0000e561003182d51080391941010401005540b00a6184054400108042e6486044104a0040305075030b81c1c01100c031581041c00111500151013084982c040c100002502556407c801141200e900e09a600303040542d403071074514115520b98905640d100024000e540c0103107490316500d55285413409104048004981203211018401401c1c030403101e400107809242d12008228654204075002d4054800c2818030803044403d0060103280b141081d00454418100c42101114080b800400270300440d03503208940f0020b1101206000c01d0002641c658010814520090044140d8510705441e4510b50b40000f50b84181540c0028018890710000c030b45400010190360034598612681c00d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 332926169 1250 332924919 332924939
    0xa060e13030c0203030705010c05041d060a06232d120408160f200303090102150601020111070c080114070f080702070b0f090f010e09010303030203040f1410110301 72
    0x1014000c0e0070041c080c60b144040d50b4040c411034485540c0b120003001412604100a01541c10512550a10015141c005e0041e5501e200c0414450f100c009c2c040c401250a140050307030a10098207036198414000d4418405100036074004040000192140d9551010192515040c95129003c10024a0b0701488034100e000110030321287c03c00d512121180d03d40440342010110b0341e4025001500c145007041180040c40b0034402e410b03016032460306074624680d403494149641c905c0703044815070060380944004110000902d0030590403600500c00410544a04811101144c01001c000d0310241d20f44402001724510901c5040b00109000102624521f8120f0001e0088900494040c040c07108410014044034800d10410014160010031681ca5550040000c0029084100100c2c06100c80151000c8298003a41028421050040036030225a00b1960110040e40010304200e500c00a0090035100045403403981c3c40300c06680c0f000500d00850030110140603150b0b1300355006145d40701040140102444 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 332927419 1250 332926169 332926201
    0x20316180b03060409060504030f120608071701060902040605130603060f2c0901090303060806010821070203030a05091008060f0409050313120b09011a0103091a0f0a060e 75
    0x840846181c42e0390fa688040b502608203103d00400d180d25007000c00003010340058444d03000900c5542d0307403410410204845004c0359a03d0003003480507070100d4010004d840ad03a0810b21200c800140001c54215a40e442417000c0e80c20942014000c5000821250450b9800004000c000d051520b014424030f45000c00c06da084001034000d1901008100f83c2e40c031134407540c50030340240920032612103003283c1c5041040c135402403c842c03004400180c2082c10010355060009242e074180c0c0c1e10f00d4040c00400341030305403038905400040e903968000d9009001c8000907079030038800742c00450b07210b4507683d60750307401e442c10001c804406d5000c900600c0000e006000e000d0301e940c000c119070b0801c1618005240c05290400602e5802510070038107200b0500b00c13010072282c0c050244803281c1031007a10400b03500d440c2c40703503104c4c00d0700c0c103003c0c1061883d03040764103800040d0301c04d0f000104000d0103a050010b01110314406a0f02128084416140380001070041c0721400030648990401015403503440601e03424881200160140 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 332928669 1250 332927419 332927429
    0x1b0a05010c031e05090a0509190e0a120504030c05040e0c2b0501090303050903071109060d06020c0c0a06020a020a051005040e01170d030b031905030c010f02031618 72
    0x104481d4000400d40151003420490390114541071501001480080495200c913060600032039040000095608100c08520301846c140c20008002c5021012410010a000000c00409101d42c05d50400402d1b045405490780440d166501582daa042d810b008d0074030074142c1c0c86580500e2074003c0c00480360402155010810741c08582042414504074031907209c001b1010303000484640c3d40010350003001030551000b61000c3c40381d00e084c0400d1ba1404030780da45a00940c00f000e4114600c0c2600d0503002d28100c00303500d501c950014201034070104240ca44100701e800160703645072190f00030b400510052070321030010402000144028402c7c4d0019a02003218a21984596406000e00300142e40c0c2e801c3c05002994040c20892028520560b510402044200c200390004901d5000b18244220072511034002c00e040703100041c0040500310200c440c0b5406155402e0b605607820b010521143c003980d0828050281000415000562242803119200520040341c800d40024000603801c0140081101c44811007101e0b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 332929919 1250 332928669 332928677
    0x40e1e071e12020a02011a010c0201080f060d0b070c0614060d0b100b07030c06060515041202150c01150e040b060613091b030b0301290a081606021b0a0501 68
    0x164140c0151507555050b0320300308005001107186a141d5134150f202da010544540060b001d0300e18854019544c2d1442100c020740040c0d0740e44002000d0002c441102600f000c0c010f0b2041c10070741c42c26265092003841c1622140c0001d401490b8900c107200c20360080d900720b01c45608000c1014140342d800100180c007444001070160040c02c00042100c0e48081456000b0400801031036034a01c102c0c07400034201c00b0800011035886140580200302070a041c480045004114800303a8a01401d1190110702d5503050724080342d000c2072a09890324000001700180c0b0081d40080d0011030f1150807002c21580c0701b1055000380b14101c0300b81e0304000124002d2421141c125500742e400c40d540d52441108004004088e41101001c01d00b481002c10500e0030711420210190140d41c0e042090483d80c208050907601c0c900d0b000c184481d03003d0102400905c0c0818020000d07040181040b29190341c8003521800d046041149110200c1c242c0c0081280a070140040050007107016001e4200f151918001072105045008441c104 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 332931169 1250 332929919 332929967
    0xe07030e0106080601090204081209030c0405091e0304090f11030601080403111212060402090a0b0d2702010e01081e0c1b0a050d0903111e06040e1e07 66
    0x240c00b980410701411825003507032030340d40c1c40303540b070340c1c040d40c072070b21031487c2d940304500017604c14042c480300b61200002c0080191060001c4841080090000507098111030300030041c5140301e40c0c0701c880080314003822070300185071220320307080f0000d044403d450b0074280810f00342030340d102e00c0301041e8044903845142400d11514540b00c50904a42c0b001c0003003800d681921513140b0b030b8080105403101508a003e15098100180d599a00511080e0b00a40c0151030300100401414400402444040e040c1d40710150360004030461000d0003107801541507164071020440a50f640015540c0c494261301341c0c004282005020703810151200c000043c0981c40b41036040c80c1150104042d0041c0801b12004105185281d15240d01024141519074105c580115200c0c8a00d02c1650003103401200e840741100d8010f6005403121118205101e5075a58245041c0d14960766042e25040039542c01c030103000a05001340d03241809141c40308030103234400403074440544200804400c00203d00c0e400304d001c00001c5251224101c072 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 332932419 1250 332931169 332931191
    0x70807060908040e071710030b0a0e010e01060b0702041416050906090a150207060f02121c05090a030e0609103c03050a02040b04150210020706061701060e0703 70
    0x10b94020fa4003d41c40b0843d6040a1003802d5a01500455508030020f9040900f600d4089144001012a210041c0b9825074040041c0060014be441f2480810b80301d4000314a400010f100709003100c00310740040381941c802080718410b6042c1840b0b0140c90100001901c041810880074802d01c4403045c1551008010b40090345068640302c0c0784c155421101e000d070841001584076035210f0041c41110074901c00500c1949030011301c1c54498008568034461540161420783c1c200f00b910005540240c2034100364885039400e4880f51091032107a50300c5824244054400c0c0241458000c0c00780c0f15141c0c0740c501c20071080c814082035603036484401d0305110450401d0b0844d4450655501c010044100d40e5049104550758200c0e01070840c0b0200b04070701d2a49513400c210558038000701030120700540c020b12605010600c003c0c03041010000001c555804c50340100c0300c5080002c0c2026041ea840807804481c00d54031060200581d04114003903085d00400d41d00284509401e12000c844c0c20003000300300800b050340b6000c1d4522 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 332933669 1250 332932419 332932433
    0x3070c14030708040b040905064f061502010209060d05150306042d050c0d170313020a08010507020a06020d1811010905012313050415060e010201020708070609 70
    0x120b1950100020303868a035944007069080c0c2040c4180c121680c203000c0050000c0c5000320055503800c3c10004c0c2c0e006950f5041c6101c02188408825080602294842001100c843c0406640980500d54000704036103080c00b00c034413141d84e808201c250542e0b00511009229070f6400e4107850007126081000501ca690300c0066030030540c03401c501035405008140601081c042040302d003448200f10409402c0e648084901000c036a40c0c09410081c00c0394000c124401d550b0314203060a00d000074003594002004208c0340c81080c0c810351040c2c07964040310071702003529001c60401c10f041000801400d4000c0140e803408202c00b0303442e514501402400e05034002040c030341000040d40700c14180707800034000c1060500303d40340501055044d500002c0c0801d62a600002e500d600c640c0d42e42c503007018100303500c444a20b920003240e513484d0400b170706440c5215034800c1d011940d5142c61280181814818a040b44800c1c680b0b54060204490a505c850440e4010003540000c543c040e0110754100b03074070102c00902c0e01c00d1828159 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 332934919 1250 332933669 332933677
    0x30a1a06060d090c03031b08070f050102070219080606090c03060103090813090f0e0c011d040605040507020a06050c040807030f06090b01030f050c010203030412050310150c051203070c1403 83
    0x6800b140c58229141d0038400001c10070402d50340300761690303150100d142410041005484900520101040003d0000a41d40b0310300907030b40f644110009428040d1960002d01681245003d21010b051401c40c200305119007000055001381080d40c01c401e8030304107055804290710008240c203060503201c5c140c00c0c00700000e000403564103181200403101c1e11522504c200b0040c0180301403600c0801d0526640c0f5540000100da1040702980503101d01d180c030b99803451201400001c81c0b6500e94010754030907000509441c3d60064034441c001641c00fa250464052034100c1c01c44202602d001017403042480144140c0303900080d10000e81c0e0300407003080c003050b03514500440544060715008050555110000040084071125075161034858420707964004242d2004903906d0200312005030003c40781c010f090310081d004400440e0020500704000403096100d88050f1940e490703410904000403160340c9640d00b0f006060112103400c107801c1e804a40395040280c40248038107500040503049014103414038000d44000c100b21 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 332936169 1250 332934919 332934937
    0xb10093b0d0905120c030c21060709080105090c01080601120f0e010203192306041b0203030603070f030c060302280509150304260d0e070503010b030a1a0606 69
    0x9481e5241e454400030b140c01580d03c1203d0090000801d0904001c50115001d14804405401054842e03201e00c00c1000c8061000d00d1101141e1200c0b6149000c648207100b650310a02081d00c94504407850000583e08503403004007410720720f410002c0c2010990b0707444440c01d90085024a0300000b16090a90342c60020492030307100001d4503207401d0141241400640286100700305a03202e19280040c00103010080d91100309511040ca1044802d140f418106a40000e402800241000500b08134103500400c1a0726030410500c0580d0000c41000450701d410000803010707241c804d06c8442c040d4615914800b8441041c0035160905402154410005aa50301c030fa00440d0b004200f50945201401006030265114541d4103019107801d0880880411512003200d00595101800c0302c4011421108640038810f41c0d105150303444420030401c0312094541c0940c524642d0502c2c09440e8152030303d000c01d800c42d220249080d000741c2010b044080403c034250060001c2d00c680c41d103903501c07681e07074180050000e00c20341c110 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 332937419 1250 332936169 332936173
    0xf030c1215011211061912061206090b10210812010e0915070804140705030109060b03010c02150a05040507031205070b01080613110a030f0b10093b 65
    0x818292015004141d14004d614101d207001e414410b00085225900c003240c100501405007813000d40c42186100404515584005451a142c0707503d0350310742481420a4a0b265110300f4103006200c0c246070895046605d800301d4920310b505e0310500084980d500400e110513800c40030404400e2000400807a07031820b4074200010034568444d40000c80c0c1c0c450940d014000d03445201c0070701211412644241e0b0080a00343c13034070711456565654551840404200c0d0001d607004207500000c890310240035290740e00d84140004103001c0040d030141801c64455078190421036000da20704002c04411142e080b9000942380c500441d02d075986081c03003840d00c9480c0c1c0c8000e10846a4454200002d540907010700031103803045a040440d640d070b4440c40c540d20b40d03084c0c3d50f00318548071101c91480000e20069000c4013600c2c1c081e0494140664a40300c1002d6a4140300082c4c4010b00054108480e00710000c2990014140a0008002c2d00242101d1003041d82c00c420b000c150b011060650480c0b010207901183c613092039031401 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 332938669 1250 332937419 332937421
    0x908040b130306110702090118091203022709070c050102090d0812070906051c060807031a130309050915040e010c020f0f101805011113050f030c1215 66
    0x100241c0e110610301c410b031016403030180c8180784040180304681009030020200d84541c2d007050040c103d0f003030709604a6644189e0b40c05407100041d4022282042c02d281300d4500586440e4a030344810070102c005240340f40c0c000c1c540c1c01c03245081e0344c800b00540d4100701c141c81c10080012051038800c3c0240700d81440355501100384000c500800400d100107118001400350440400c0e200c0340c01c15240c00d0707424040c5601040e01400004119400303c1110b095000e010000825120768401c0140e061001540003135403000400e000740040d844088001a4010449684040404141c4d4500400c000e46070700503103201d01c2211021070603844040c040d40c0d0007090000d00c01c0041116000903240200030a440c00f03070140c0201c1d260a0342118011500100060004000e803d42080c00d100b844014180c21564010b1610900711040104600340719080740718140b440d0721540d400d24a111503008007003a80c031061086a400d02c0c0501c050310080f5004460210682c0c02130380320105407800a0424168070070f29035583d2440300c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 332939919 1250 332938669 332938687
    0x2060f0301090504020a120201090b030606070609080405010f0f02031603110d0305040b090714210d0201060612230a020919090c0309030c1709090403031b210908040b 73
    0x9840203000702d20841d0069030741d640e030715030380d010017100304a0189c0411052041086480d42d05001507178081d80003400b0380d240001070340d01c0c801107a01c41103043d40d42450109082c819940c00000e40c031105891406c01c0a4502601c6400a40d00d00c181c814815942240f0b043c00c1d0b0426005000b441102d00300311082e03c01e01105800d0080003824105c0381950801d0316240450442500820407030700b41d0342442e40f070400710403410013030044042101d411400300c040603052800d1030507000d00815110342550790000c40c500303182010007400c482c000602203c40310724284441c88240740e00c010b111102c0c40e00c1036854099a86541d2403000034010121002e410500000710011000c0c41e9484103010351300c0c000750801c00074081c48411400c4441c2d0341c000801040c800000c410110340032600340c1c9845448070305018542600380d008280910b006031001c9000c01d8440f5402440400c0c8a2412000c805035031601e041e0250380910708003000340c10b98600b07481c7c2d10360f2004140180101401120003030b0500782515a6103c1c002 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 332941169 1250 332939919 332939921
    0x30d1814210c1306060e01050304080705060403021e15040b150406092007022101020705030a050d0b0f0a14060417030307120902030a060c030b031b0307080105100605030402060f030109 81
    0x28500340c82102c00c20790602c43c0a819105210541d120703595080942001d500065826520180054803070260034422440040c404209441c40789101e503002e422050080c011108070b0319060030010704240c024a41960481241c3d80100c1d40c016088151805031351100c10501e00b1403040348400e250481e041402c0440c28122a800200b40ca500d22a1504203050040c00c1040c114080d14400079448001c0480000c0311607065a489940c1d107000400040c9000000c3d510035103950300101d0b120012580209000525a5981c030410303140c0c0d50281c1e030b134551102c00f980004144603158007907440c1d15544150402503644501007901c001c0e0069105003440b90a14450242d643d410403280b6000044250700c000d511801140255050301c2d038080c1c001c00c10860541c0d103020203444500910300030965540b1040c500c96908000729003450040d00030034030006842c4000d0504108503604600c000c1d038102010b02c160204420020811140c0a00e081e6450b5203440c8001201845034044002c81c00783d012002003001c44103 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 332942419 1250 332941169 332941183
    0xb091e04061e05010e18060c090d080f0d140105030f0c0108090a0804080a050622172505010b0609030703060b010e0303040b030108160e0403120609020a0e030d181421 73
    0x914050a604803a842c001560700c02044450ba09510024409809c9906144803041c101921034040e660809000800c810312a41041c200b80203110b0711196071038850000311603914050102580581116029645400c0d0b0351307042c0c81c520a04214090000880d80710040c00104d40d00c65005684c160b0b01c03030f80c6481181c2d440b0f08507101270305c040c011400403a42c5840ca110101444841d0800074201425140e2500c0030b030107140c030590681d196020428084140894011914000c040a40e0003c840020b401d215007150540e1000300c1c000e003010400000c01341d60002e005070803280d1015010821030307480300040320154500c050190701448007103000301d42c1d00f003014040d50503148400e049038803040508200708001d01c400d10580e03120340030306804500400c3c400c2c13a0303001450b201c071800400c20390343d200c03900380c01ca9001d4042c200000c2e82c5441d43e010a0b107014400704090882e20701c0d0103a01d01c1d030f40c50008010041c143c41640d1f9140070003000141c864590307003000c964694945d4000c4845000c180d8904d600c0d508 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 332943669 1250 332942419 332942431
    0x31b1302070602431109070c03080610090306050603030919030b0916090b030f070b07030801120221010f060f03020f040c0f050a0219060b091e04061e05010e 69
    0x81d200204da610050030510716500e0300714280c0f822090900b0321070800c08800e1050820b54480210050b03100043d118221824041c1c0c010780c1d2030903528400e5040003440140090049445210918080310105500c40481070907a42c00c4500003801d900c072540068030b18426107204d0350300700942007001400300400d415080101d90040d0384000035a941c80c11041d032241c03c0c07024905030b0112038240070b011450f160f5110011051016084802c900a000881c45c80c1c148590b020311810721000038a8802c043c1d02c400418010b0088039101d118010540d800140506601d0004000c1c01540c44905401301c03000750030403001c100010508120003a10380059050540541c00207170301608846092841600f400d12801412603141e50312102c0751400c0903070071501544445000303021482018203844603074030f1403c003001101d0300c601400110010080c0c02d00c144d2080c000d201c510404940d1001554188869102580c490f0740154001442d40b403c0900e5840d0340c0c07071360280220b01d52411300041a180b9802110f58090b031 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 332944919 1250 332943669 332943697
    0x9031603031106010e0108060a0506040917130801021e0a02070b030f0a0501170607031d010509060a1107050307060b0111030a0305010311060a020c0f12060f10060509031b1302070602 80
    0x181e01c403103c04040c2c5c03400f8451500158824000105065500d80c08030344c02400080c0040b42e07448013901c8090402507849000e0f5000ba40001c0e10140303001c1c26017100001007001c03400a600700036140c00344070030b0400e4106509072050b20004080100d03600c2031152a01030300a40010a40340c0c03d111a440f02c070840100d514040c410700d400004107061901103000580413001c40700504459480c1c410440250100d07a00c121800c100c40d008481d19000207000740b611903007005000f4078440c82e010500c2c009980b221403005001c0320040045001040f13001c0110755005412900101e0a503400384012601210320003650143c1c1d00011440ba11402d52640140b0304a074010500d0400306020202042014845d401c2c98002503800a0040c01c0349040c0301c5580c144182008040c1000d8a805030130702800e020040b00d00c0320354440d0030001c101161001c0520100500480c0c9003840c10701d801074020075902c1c181904010b1304440740c00707051002c540d00c40c80303080206910701e60b00b59200c2d5018900341c03001e0b40101800140c64 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 332946169 1250 332944919 332944921
    0x6020d060e010308090d1e1109060d020321042103030f1e0b030a06020415170c0a12150602070f171905011811040f0510050609031603031106 62
    0x1c000740c1c0c40018140d94003e0801403800e0f40743c03410170411185d1020300b140c80800000020955075000011504524012000c0451000b0301004009048500500083c8038800c1e10f002c840141c2c500140d603116201100d5403007202011001074114003030141d0fa03c004084008621000408800c041035040618440c0d1018460310211000040603100d4580119090b1040c540b4140031006140c0c000505029024007518600c42075074a91005070303030145d0005107007400300c0190384068a5014010340f8018051600340e81060600c0e03415200d40b88110100f080800c43d0f0340704040e04031a0700703501813501401141c02940b4480d680300c0c00a92910420b2142c80755141c109007000072507000d20760691409030b21045c003808103200000c44260314407080c0718003903230b4a658038964555003034003410410714101d01a9040c030740300351050310030001500c001c1c21300100d5544c18401401060401d40c0155020380380121070054840600c1c40c042490401c490780010304c0040020300c00001e242d00241303031001d209180c8003035440d1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 332947419 1250 332946169 332946179
    0xe0c0a020607030911060a0c0605040c030201020f1603030c140d02010e0f152809030c06050c18150f030a15050d05070315110309060601020105160804081e0706020d06 73
    0x129201c0c044080c105c42400700840103540340c60b07070040245001c0703400c02055512154031003000721481198100d904819503071050055680400804010142c1c10005003003001d40e82c980b103000b08640d0312004041c000354248002c100070782c200d816405c406901c2c5c211031000b84903010090280c1a541715611350360041201000f007440c1c002c0760080421a1130000a0f8080d245d004000d43c0b01ba201d01d50100050310802101c0c01c3c000c65501030242c41d14041e6075411405503950400504541e030180800c60300800030006443d800f214500c00d208a04400c8940d0001c10041c1c1000c03241030b110b1500b1142c500d000010030030a0322407080c0e10508080e03901104c0c80b140e0f1030b140e005112001d520030501404a0348540c42c20400683e20300c4107403070f224a001002261515011000b030045400035034150969400031401c10100b5603091007019402402c40f500c100e00c115984a0103448000041e0028200c60b40003e56001c03160105030402c09036400c07182d440740d900d01081c10300000940000d440c000b103d0703080c8900051 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 332948669 1250 332947419 332947421
    0x10519030b0c0c0c130504050d0305042f06161401020f2706030115080a0c0e01050906091c0308070504050f010e13020d020c06011a220e0c0a02060703 66
    0x82603980c05044121980c5075200285803503040b074200904580325002c1d000102d034940c00010107078820000b01c01300f807600703140c5001802e10160100316003c041c80c2800f0070011032940c404120481e040208414152410420510304d590207001d141600024000740c44000407031050028840b1034002c24018012500000002d420b0340708a8500d5505a007040c04008c1400384003600c00701104c00e81d80600e0541c440030001150321500709a00c40b00c580c500003c6603102fa181c014021551104114000300140c91400602900c0e4803801c00d40b06042242c041050a210f417220400c803490054010405d04140c0d22042c000342d510000200d08400043d45103001c502072902440548040d51002000d800c1c00060035401140e020701c0c50341540e60311800c01c1d44074000d0403c0920042c04c17010354010380943e4515042410b240340c0301044c1d01400c0b10845910ba10403100c1d100d4015034400c140500c0d0034030303d050012614130742c03c003080d5000149148054001d000044000200800c0c5490300da4090341c000d541d070050305030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 332949919 1250 332948669 332948719
    0x4020702010507140c0a060906030510030804150504090e010903021b102105010e010828030e0a080105070c03090611060106050a090812130b03040c0b03071b03080105 73
    0x1d0115200384442d0000681468504030b07240300d00000c80341c82c11400700009007050510b030b0000020601500003888040e9160294651004180c2030139410b840c6159101641c43c070580c4102e40c032654041c0c805000640c85041101c0041006020600a02c5008c0e08505d0082403032010403005445040040300401e134008800c07806101c0001c008505041200e5000d07240c4c58106011042c514080340300050300c115945c481c00340a0032420714034851130360501b18a20728240181c3c002502c0d0030800c2c1c4009044407000c16201030807541c10b00d06070030b0f080341e0203021800010443d0070102d099403d0200f040101a4040c105c1e0490a01943c0e403220308603078a0400341d50401d4100d0301041c0d49d130008401031010710701400051000fa00c00d0f140804038a660341d100c040c10885a000296981000014400c0107080103541100c0a0140311600b14034500b0710f039072481c0c06605203115524155001100040c1c2035030280c003000303d0480c02d2040c20020b0b03c0c05480e000302188024001c281c07140400d0882d105103100904004 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 332951169 1250 332949919 332949923
    0x1d0f100806040b0a0b06030a0e16033906050a03050c09091303050c1902030706050c0a1b090c12060e0613020c07050a08100b0607030c030f03150b0c0606040207 70
    0x3420898a55803904110f409004015290700d40c3c8400e90646113846640055102d111a20000151010b0918656091234070b00864003200d01c88003c0d00303002081c09032481d0001c1c125482c440500b00d0916042ca24008403200d80c4a45002e4020040020310319009401040118055641002075544001d140c00b054040c01000541101e000000a80c4d0b2640c05020f8030740c42d500a0800074140000c6c0c602c0305103070001e0070005015201600225400b1030604100389805000f943c2416070134440504040c0c0e6880c086c2d100098005900746d800c8600c01c4900180190181c900030f01e0500450320088000303000e8046006020590030b1820760009441e002da042001d00903400241104001280500410040d40201451841e03a01070b0000010b100c0d503c00801380c0082989401408094010b00c0b1500300701c441e0314503201d008540401040c0002644a42e19590303042d818200303080140380b560b50440c0204245040040e8030418400b000c0307030401d9528058081d0201003030444185036146020701060780100d904c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 332952419 1250 332951169 332951173
    0x60903080a030b0a0b1902160503062707090b030f010b0306010b1e0c010b0a0602010e100c0e15090f04110f0702031906270201080703020f041d0f1008 66
    0x90030764030510a8001c0101020020580c0c818941c9039480420658400c0040000702d0394211030b0f040340541c05009006a5410001d601c0c1e030381c1803038007001c662126001011540307015000c1e1012030440c81d00e0b880c5c8603894229413003110313802a241c0042c00d0043c419010f90038400e11850860303910b140c0d014060030101400203005403805074640444c800b0960000510700b0406800318a02d40328201c8a68043c103124001c07940049140003002c0c0070300c03004030360340d402200c210b90410314000c001d10400140f856414007440d50000e507140c0b01d041c007107494103006d0a1441e40240c5000035405003164003000ba0505510840f603182c0040000020041203603441c850100c000c034030601c50420302903020130151019030700148c00d6406220b02e4804255281500000072130340c1a0b0785040d02102c0240300070010388000300d215090320081c1816000038103001d0005110390101500041c2d03202c07a2205140c1500c0040c00402140c1192500c114160380c000001100c014400c3c0d6110000601d0078405807901200b01c42510b80 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 332953669 1250 332952419 332952427
    0x31d03070f301101020c060901060e0c030c0901080709080f0d030c02030406020c0415031a0114091e04062012100f03120221030f0916050409020d05010606081006090308 74
    0x5581c3c1d084000400c10182d50f0038040b0315040b070818410548640c60200000034038900b80402a50108000707441c410b519a428003c0000782514801250581182400c104545030f4032200c080320400c4290300180748500403401c2402500600141100c001100398909001d0410101c104a0b901e024a104500c0141c1c0031100c0c2d000359090980c00345594000c0e00c40c1401d1403644a4403400d825500700c0d00d45102c952503070310041100d804000035180d0850303030032a803512250400078800e542c00100304c2407520010905201040800074071381d0099600f50301c4055001e495140040000c001034201680c00e40805510800045440150890110035542c500c403044a103a4295190f9032400c1e6140f5151501b544650204a082e100b81c0b0f5003034001000d146401150341e850906a000d9020602038500b1285902440e144c00d01c06800369048029248103440000745124a1300000d407040e00c1c001e80c043e2081d4070f400d50210b24242c0c0101e0951040440703400040c1016500e2170f040b1f80340f001c540300190450354144 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 332954919 1250 332953669 332953763
    0x308090115140d0501140106030c0c0f03110c1509040b0a0e0403080405010608100209031006241407030309020a0b030f010312020a022d0118030201031d03070f 70
    0x4066a00140c2c090072603003150107182d0360389084645c04044000360080c6c03c8010841c10381e0601500034828181c0c6044551a0401c0d5a0507140e981c83e900000c0c02d100410400d1144032208100d82c00c0340100080c42000d00c043c2d40d2108001d127030310480e80c40340903500746240818541130960000040703425030301e43c3c4d00255940d514112500307072010340202c0381952504800690080e0410082c2c6044840720001640c0f100181c041603d01b540c48084070700042d0071f180e0204080c1401c0000100402c090351444440280d001e001220181d0460f0104000b280300801c55000741640366101d144214030940b10403e83d2615a803522016000444d035103102c5020311001800040e070307100204403960170140111000c1d030604c0d6000420819041200d080e440140c2f800325100b11440004040c0104801c1c24500b0100381c920201507460a045c0c000a4140740e1103c0c10322201d101d420440c000c4a002c554140c940b60000c5150029001100c15001c2d59107084005582410803118006005140390410104030082d40c00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 332956169 1250 332954919 332954939
    0x5250504050c090625030e04050f090a0602210109051b03010e0613090807060903020c0402180405060a050a090c090b030723040b0c0c03070b071a0604060302060c03070308090115 78
    0x4811300b14003405e1070403201620842c041ca4684c0c0710b480f039250080001c4440d001c2c03101700e030f0f0700800101860300082c052043c00307540450741c08090b503085500540d64494070a1600030b405440d010320408503001c076000151f0074500d40d00c513902410581c001e04c2c10036010600004050300081c014a03a162134403401081c010f141400c10040815424180856207403d107403503100654110810a5841a4840204004140e414051b070074074450225421402c22500860b40c0d05918000d00c4c0711802103507114080756003942e40720005801070134010880801680c4030128100035100a605d85000328a070710502083c414020403e40c2d00c900c095a6a85d5000034800c1c0e04084881c00c6552907100c000000c00003c03c94132400d10040c140090b03000e008254441200d020305240040543c0544e500d05018080800000d44505004a0151465152109940f00c001c001402808241d000943c0b00e0b200240000b43c20f4004009007040ca8029180e1001507030384c0300311007400d0362442e04040d540040b1861007480380000c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 332957419 1250 332956169 332956177
    0x3050f03040c050a0b0307090806100b030a0b03030708040e0610120c0c0611090a1d04080a09081005060306130b1305011b170c2a0a05250504050c0906 66
    0x50072030500c0c0c983da2200401c0310100f0980080d0041c500000821413015003203007445008081c0500140580d01e032102549006a10358001c0e0349030386000002041c038000054000951180f0014203482c1d40e07120b60f00c0e10301d5880d40b040c131450303080074140c400096081c40e0015507440b540382d00d40c80e201e50302000083e03140010041018a030040c000b20f1070240e00400c141d8801d5550a0b020b040d402c0755034aa982041080c18840c942c000814401407201c2c0b55009140b8905258129600800403900d40d840c0e120b050f1036100140e000b8411512032145a800d200071150045405400107605492003602d0794100c9041c0c860714540c006c1d0036541044041280c1e01d00341d03480626210302407400000e0841d140600020780c0200d1007440350024a40849159000c4249031410342c00c8586d02584503c1d1200c86840031241c05202e0100c014150100110321404220030f00c15a08403560007001e88040c1c003250001035009003075140035544129656032000c50702e42001c1c032955001b40441c010460030304121100300005584 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 332958669 1250 332957419 332957423
    0x3050a020f0703080315030703080f0a020f0f100c0e0f0907090b1b010506030a0b040f1e05070806010503010b01090311150310050405070f0c030f02070f120c06090303050f0304 77
    0x1c00c241c00d400074403809021100183d4801d141641d500d040c10348000c040103116201251080d040003000700b0000b94110102d844200121003925140ea20b24141a401c0c1000c41196103a24061079045e415044e00200c3c1a07942c2d070300074141c200038101c90944100c0e000c5465582c459044010465000301520340104c0c690b501030700c02d20f03044002a44071039008d61a604283d9103411103480600220300340c1c001c280101c0c0c0d40000150010044100c26880c0c517004140040d0003d000d40c0141000c071420710083d04141c24408203072280c0b0407003c6003e40fa103d03555403c46d00c91070b5058040d00e00041042c0c07030180521040154140e4a808100e0f003507072559002100c10104142e4006409602000079a403880040c501c03401003202404100d514041c240401d03203500628030010001c0703482c21001450380292850480940500c0c05a40120315814240d1601d0b42540002228040d20701e00001d41240b4240c0445020b4803030030614000e19940d000c140e5040c1d105000c000c0c00b0610600445029208034005994018 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 332959919 1250 332958669 332958673
    0x3071704080a03090806010e0f0a09110d050c0a15021e03090d2d021f0e03030d0e070905010605160c0905010626040503030115030b19030201080c031303050a02 70
    0xd691401e00c68a803600d03840044000c103030b02c840f08120030300c0140303c41c5004184002d986081ca1138405000268884000e050025035556000003009000400d80c140600c90405801c440c1c0d8203c0c10b04240b5620281c000342984940081d070804a80780c400006460560040c0d50010440e040070a000a13650318400304101c20284824480602c440d41c604100341310780307070040125070221490680040c0b5002d10b07009115a000e56203900303001c010303140c510781c48141c00700005403801e07140c003030400465180c011100940c2d450311012071000055011580000740c1045e5407000c4400e41503640340e00400380c500900c00c00010400078009130114500484050000e01d100f007004400c0786489201070002ca490a0300044002105440003203503112611950242400d032010503600c0c0e0f0b1409a03034065032440140104090481485000360380b640c000e401036464000c00425104807209401d4039582e58410900c026400985d41c840855400604041120301403500403402003c02d200d20b0728256040d03071020302090214 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 332961169 1250 332959919 332959927
    0x260c0607031e210204030f060e0118050c0109050f0906120316030302091302131404020c100218100212091f030b040b0f010203030a091a070215010611030717 69
    0x1c100d040303080c07801142240c0c585a1109403c02440f0481d44400b07002c0b007001510402003480402c41405010030005c0e880720000c140181e0360441c3c9805009000191101a5043c4403030000708400841e00701e058800a0340c610200b65641c1040200c500d80c408a601e80004c902d501107401410200503840d052507024084918005000c12121b4940c1c0f101c600580c00690b0120b048030303c030714068000080b6450194011750900c0c070380d03000000f0301000300e01c18052070000d40c80d034040c0292250380666000c1001c1c1015140200043c000e010065400344560300201c007819081c07042c241c6883d00000140c2c54080e4014551481d0b89100010f465000031481e43c0e0002480703460070321080e01d0f4102040c00d01040da0b0040b8075003c02c0000d010075035044496061042c41d124125480c42c1c1d90001c00e07681e21849049004c20945021b0403d04002c1144090600d0580c070b1403c20410402d400051504040c6081002e1940e1603a841c00e0071240d104000c003000007950800c104001c041041c1c1041801900350300807a0340d00d4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 332962419 1250 332961169 332961197
    0x1603020c060702070807060c0b07230c01090c0b041a0a03020f0324030f03091c020d03021b03010506060304060c0210150617060a060f0201022101260c060703 69
    0xa08a01298a01c0042e0311584081c0b04c0d501c400d110800080072107003054200c0f0034442c0d5604c945e060002b00350808000b010300c0ea110040940e1860401c0302c8a8401d81f441e91000c0780142ca6020300f90955050307881580c14000050110584000c030f804444100906100141c6071000131701c0b85a00c40744042d02050f03024881c00f841401c0000041d401040d404036582c0d400041c1003884200e11031034040e606d1081d0080b80500501010100031109000800c4403800c0218801c820380344001007400c980a03410110448460040503000105080400f02a40c4410a0002c00408040c26144221103164100c4004c0c404100012100d41041440c62114015185030070b8190158404580f100b9441c0c101d0070302070241c10089181c010341d01007031800190f44913105516251010a80100e52031081c601080215165404905e100390706441c04241030003003044600c900186000038910302805201c2003982450110391030703081d203590540d8030500520003a0850800c450200001600041016020b00448a010101c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 332963669 1250 332962419 332962423
    0x6040b070606030218160c0c0501031104080f012901050406050f090310021e0408070b1e03010b0d0c03020702030a20030109060f0b01091406070804170f0c04060e1603020c 75
    0x1a10350b0080d1008070145041080300340007040c111b6200c8181b088164024002c550740d4041002036900070308012950b1a0585643d48061240e81e0180d24240150104040c002c0c9042d0400c8149111010b00c000c001c0b070b40003000e03408001110107040e0109a0400080251a008001410380402031003c0701c0d007082003a001107030030110882d081012280d030004602c0e824140005003a0713503030b1500500f0542010300f402219940c440e058040c04841da1408a13890006444040d0a410101d040c054031a8503542d4401002e1099004040f589495a0410b100d110b00b451080c425601503580090040034010100d480309000240354000b80e5a4000003802c02c00e6880e1400d024140e002842a040010901c1e18040048200c44551031054101300040d00100424102c9001e41910030808840311039441d2610324058200f440303258007030080400280740c1c0340458200817403a003d40268800c01d0301c141c00c1460081108548681c0520004800b0340c0700071404469103402555124140c6040040c94404013010041c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 332964919 1250 332963669 332963689
    0xa03021212010618081b0306180303061203070f1202100e0d0c0602090d0c050a2111010c02040603030804030837020c0102040b130503010515010503150916081506040b0706060302 78
    0x1002c4050300343c6d034015960804014650f8842c0e48000c1c8252003a80400c02d01c0d48078880600741d64858034051902c0c2e40141002c0c800c80c3c1d030980d408451500400c00b580352aa820184640384080075004507544061070b000c40d070042e24154040e40d0003414103c02c0a00081d03400060506041c0d690a9007408201040c0d00c0d8000d2400c01c180c0104504103081e894501001604010b54010a1090140c2c500f444200f0f442c1016600c3c105034090b02c1406d08044210040f603241002600196000742000c50000515030400550b90181e40250f844078056a68280b4814902417030101003a00d00310344640e0a0b0203580c25154484c1d681d0112280503150100280d10b084c00c4e0382050f040324010002c005051a010300c1c60101c11001400c05900a018510f010b85c04001003a507000d0340c0c02e044c007400100151810845040074138411000429801c804d06000c0e01165109501c02c00b200f0220314842c0c0442c1185a05800d151075000c0300030400ca10701810b20f5060300c1c1c56084800e0840308030707807600707008030060340d41503a00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 332966169 1250 332964919 332964943
    0xc0f20040f0204050a09020408071505070f0309031a041713081005010510030c080105120a0501050703270209040201030905101e060504140105091003140a0302121201061808 76
    0x543c0322410081045a8201e05a1000b5074040c81048100100c0a021900310100d410042150030642280b020036036480c890404000c044007100b1041c4810140c1100c0c410003038a004412018003050f1420640c0c52105007030324050700072000c460410000400c82e00c0240000718202e0601944541c1e9003280030301c0c19600c50640880b0a487d20b005010300d0401c5464505203c00500d000d104484000201501c0c425040c000c0a00681000303540f2034001c103007080003019480d8054020802c51610381030060051642d00c944038a0a03844103920401500c00d224450000d40e001410455161140d40c0194020301320100308584501807481c8004a43d1120301c5100820944855680d180440e0440203008442c129000184178034030301840240071820521259040d81d100340c42c07120303107074440d070030340264090190344000e0242603003d4500403422000308040800c54440d4007102c410211084d030401041c00785c0c4e1680300d41491000010080c152095031000110b640c034403428014541c4503030390b2604000c811811 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 332967419 1250 332966169 332966171
    0x30c0d0513120f05090603040f080a0f120207020a09360507060f020303060f04020c010207030e0f120307060c0c0b07110706030203010503030906090f06160605070c0f20040f 76
    0x1d0141032245580900b82c00c5800c928011032240002c0300c01074035a014041c1e0a034003d09001c000078041100604150038025040b154258503204ca80c50000e10f071a01000354000001c4011a210744c2000f01c50003070f903981d190300a00c041c021606241c400c01c010040111028410312002d80c607180d16a5060200d44900ea00101d44c511700103403503007002c03840e041c2181d110908004118950036490395001c0f054980000c1c0481720400f46554030390019000c0c0c061444803070203951002818004040e080070f0241c0381402c068824603a0404000b0402c5601000760070024080d0f04100a0703900051520390200900111a0810b104040681e403201c0c80c1810048954802048010308128040c11003004250024280351606500e1507044c03801081d100c0c01005c1155005001c0461444055510a018a034840030b0103800d540e00c68107035400c80c00440c01100800e40d442440d12000c6680c0350320a020042a998104216000da2455540c40a010102050141804461301d50041441303a550380504020408c4d4884 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 332968669 1250 332967419 332967451
    0x2130303050c0c010806010f0507031403130501140f0c1c02040303080405150603030d090606050913140a030819140a050711150408090310140403030c05070c0506030c0d05 75
    0x8000c0f0716001e03070502d100f41882145e44c00c020442c2c1c4e000e0088401f44403245401511240305203010f6420070f041c48404040660044104000d1001118469407020b004400030301030a040182e08079580b55055544007200c8071680000350092513000014017030061082040180144140e00c040120b802a8100b2000186190144014060100708400f042c4c0124100c2c4402424050000390b13603031198042580350161035144100521607d070b8021002004003404807966450440d201c04018614010100d0b4021000c403132010b00080000b90b00041160300d0303100c000035034030342d000c81d20b4905234268550301040f500ea103000000c41140200660103000307040c6010559003447c002c00380210000704001c1483d54080d0201c81440d071410169940c000d904030180c26601c00c4108042802d0010415030078100b00e0403c800d0016107844206014801c5000b9a002c019000f48030030216000d100c1c03800042c00c2014408410300c00d03813406400550300061844280307854803a0810729141030b02d104413a1503402ea11a05 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 332969919 1250 332968669 332968687
    0x30207060b060a09031101030920040c080702060a021308031c05090a02010c060b15070b1906050120100e03030906010603090b040f230609010b0618130213030305 71
    0x2010700448030700222100c2d030806820fa4002840440c032403001a03e901c4a51944100b0ba900035803005510580000301e0944102190040402590204660354000c5242c40380280c1c0342841980c0d6103005101d01d501501290300c8141c01d440c041e400c180101d003110701c4000c100158001f0100020302d4a4040415a100e06050113421841102d0005080c40d5164001d01e0a0b00010307a8031000c1443c28030760016001a40340100c0000c5883c42d030070101c03e0518a00c0015a170300501804050031441000c030b400c3c241e404060740d110940c2c2664160f00c240d6011510807104100c8108818960030000e4008030b00701c550342c3d03000f521042d05035060700300414815003000086c003003070684c00c0c861103001d4011401d0078008a8000d50b84c2c1ca20006008102a1a6007044156141040141d110580c0c42607200c0c116290405000e1a22985a2030b055440d01199032034035076100400d0a004003a82c12201246840c80000c40e441030900240b225a4040302000079400c03c4001c140705100d1440d5000745000e0b5651980fa82154 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 332971169 1250 332969919 332969921
    0x90504020112060b09010c0c0f0b0d05060102070302011b15020a0c020a14010c021201240509060a080601140d020301020f13061103180d0f2a080714011b0303020706 72
    0x28200c500040c0d41400f106120403888402110240d590070310300042a0000d034109654450040d400400b003005140c140014080702d920702602201c1e10702c0707074100107030f444903001680e5070025440002e01182c07015600d0703c0110006200340c4543c85c041c804075001c88001c0701c4a50100d0f4400080c0f0404606c54140380f40179420429903450144c900f400300500d00b21155400604000e031402c1c1e00034440c200805565046240a4002c03071103a051034143d009040030900c060044501860084030302400fa101c0020f50310b032600364540340445030340d50081c1880e0707400c0c07001c00d41c0c00c1150681c040f9080f121178505100161000d00c000c1005c1181e12000fa03880e801e8a03800300711910b11a50000302080315950b6860b10316640842103405403118000103400301010302c004958100c2d0b4009018110001e400e4401c014080308410134460150301d0640e45800d09100308400560031103900400101d0780c000f0f802131100040300318190591036414184041b0182800443d0790344145010704c1100002c0d00410628100700031 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 332972419 1250 332971169 332971187
    0xb310c110f0c030303041101090f060509040e011415361305030d0504061107060b09010b0a0e04050402060c0307080a02010b010905090609073e0102030f010b0c010609060905040201 79
    0x1c200007401e5491030000010b43e0f02d0201074805403a608020001c2d100580c000e40c51100102070340c01c0401035950f82d511002d0321a4000c0c0c510030f8080c41c1000c00d0707804003010600c11001259035141025849480742d65800c107040d80c5000301c10340c010021104450030000b20820003203000403842410840d040500716048440e0307001504c0f4405400c3c0c0c4c49450800503401200b5110307c9140d003800000c8591382ca003000d0b0003900b0200083c4000c0c240c000703580c005102031508094400350065038600003690303030780c03032041c04603c1194000400254064041d403520320341030700b1068205000410320390510400e0b040b11400c59021280c01c0384d10703c3c8001007207111643c080c0200c481c00c070400d08200030700510340004200b400b44010305142c441e58584002501e081d00840c468108900e099180025a40451903031113410480c0c4061400c0221a007445800d0040d41402104d00c1219200b0350180f5603440c0c08101c452035000881040c100b9500c0726030210b0748a400344248401094201c20200c1c59091a00015000c022 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 332973669 1250 332972419 332972443
    0x100c03050c070308091603050f010e0c011b020a050312030702010e030f120907080d0504050306010f12030c080d2306090108031b01060305070f17010b310c11 69
    0x4101010072031120340101c15a04415018100581690340b80c55155013021405051a111a03140741c402005101002889901311105407000f00850200000c459650701742804146002401c2480c500d61500304061011403403500c081e140300500e984600010b030405542205898566001100304410300d41e090050418852611010b140b400e1060628811035204000e54050b4140f80080850360400c810070003180101030090a03030710200314121008203194030034414103110b0b100390310002c5040c41c2d48080703400c00c03101c4800c494110195a030f501500d1040181405640f0700c1c006110f4200d2400750f41c0150f040000c011141070306908a5403158180880c000ba0019010341900340040c0032441000007214446140301010143c2c440081b0701d0540900309541004226000d1907100140090b03240c84000141e075214029201c80d480980e112a00300d0301c08840740d96000d43c0640a0888408802c0c1000c032180000150303003144441d500c0704480555800c050100300107850b074050301003803070820300814a03680 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 332974919 1250 332973669 332973671
    0x30a2303040b0f06011b1b0f210f1e0b09010e060103110a0306110309010e12030c03061f08040311011a130e06091b01030204030201051b030903010608100c03 69
    0x42001d0300c03a0b1441c148024015041100464040740ca10781c0500c925144070324400d080304242c01d080703250007000360029491405c6094402400400d07000c4550150f44191503500110100440300619250748072190408c041c0c9011904888980210f29020a03a00d00f108140c0b441e03081903400c61404c4d03910081d0061600c125a45010404004250042640741c1100d0f0048140c4417861840e00001c5c1070480203500040020b41b07402840380d64140031320084d502c02e0241a00070860405070340b10319615802ca04a0384182c3c00c5081000030800c4006001564000001074a98103880100103090001c00c244126400007090310042040101540036a03043d021a08050092201d41d040070a0a030030403400845036803150741180e50007a0800403035030000180203004c1040303e0040c288101107a85918241003e100e00340c0e00a003100c580b55001e03000716000c480d03041e91001c0c0b5008200c4410490141100d82180480c0130400c1a19481c1e03a09000e540064070404010f4a03110358910301607002c89044150040600d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 332976169 1250 332974919 332974921
    0xb04080109201e03070b0c1e0c03030703050f04050409050309130b0d03140f1306090501030c090506070204060302031f0e01060b09010513051504151d13020705030a2303 74
    0x7540300c041c001102c80c2450304a403225002c3d010002400d03d01190091490080c0c00318811005060024500d56608055080043c5000e8680700160311407610302403040d010b510030880d28000a108100810040251784d41d440d04040d203400c0068155814280280c0c0c60350310209082c0c255142410314000b041440b504200241d608020220303001003803540740901480505030400e804088203070200d68100000d80442513072054404580308151540b4021000018503107000070400354040e00c25a02d140039951103500030349203003104018003680001ca00701c1c0c00135100e0a0010045e02d04201141d03070100103c0d18010720041d03c0040c60204d805083c2c102c2020303070600b03404120041042c6c0881c0e42a00080c03a1050b600c0703a1480c08020006003542c00036030028008004072045000080c00340c019100300780d1904001c1c0798601004c44440c052450302c1e800040a0b940c0201c441c0c030740685a90b4140a1414004d1308110690b107415045800c6190741801143d00b42e0460201c028040c9408031002009032041421 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 332977419 1250 332976169 332976233
    0x71713061b0e010e0a030b040606080f121b0c041103070e0604030c090207030903052d0a02180a092301060518060918101b0c0203250b04080109 63
    0xc91045400b030030305000d110302d400d44060300d03030781640006542c0000707012a003414a850100e0003000b0038450418203000310380c2c0020068a02284441481c56440c820500300809080f282d403450f24400c00c044041d102d010b007141c03440d0f00c0d1405000c400c1c00c502c0404a0322850509001b404000c556050075120756400c00081c00052202d40100f401d46d100d008005803101881d14080d14040c1c4a0741001d0a03030710400d050101c0742c000d1690000c2d4000303e40d81603a12000d502403003556541c1c100d8039000750304ca000208000e079450003000c2202d51000c1000004606146c45071a04404145071808540c140c00c0d4842c2420500c400074000d0200400e01a1403103102c55450f03101c6d8070b10003140504040e125400201c085640c0c850041500c01440d980355080d1944600c0206010008000a2414500c0700c0074146c1401c10103800348a078200e0941d00500a004d40751040081650001e10a52884034010100500415000340c42d0010304050810700d000040c0307100719801d240d200302d05140d40152118003002c40b400700c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 332978669 1250 332977419 332977427
    0x90612061e152202090d050102090f060313020409081b0105010e01080d02030a05070c0320130c02031b07030c06051315140d0e1914010c020303060603071713061b 71
    0x40f0148201071031040d401c1400d0480d501038410000038a0b48285a40048828010194002c041002040713440301c1d12490340c0000d000349800203c8100c2e680001b1138034104054200b94005100042c8111000c1e03182c00309880c0080c0c2100703012100c0003c0d507903442e8014860346914900180c050704102001340b02858003200c00a42da841903001803c10800f0108000080001401c0200040c6600404d014000c4000e030988480300c1e14904a09446140f00081e2642030254500c11703044401565030145181100462a00300d00459660303040b841c03482403d0000000c80c2a00c2d00d0b610117000e0903660241c3d00c01c54001d900c441c46a06421052807109203a45c14100190000d41e81c2000094050710503031030b52080304503a002421071040d10a510b00503035074680c000c041c002c01210782161150071482c126030b10074181c10b401c071110302d40c3c980c1c050b90080012400501e81040550750020041c03810300f0b00c01c8a0720108900540e01a02c1c1480400e010402410821002d4094031204042c0d80c514403100c4410110014 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 332979919 1250 332978669 332978689
    0x15010803040302090f044205092e090201050d1a0306090102090a1a0c010e030a020f071203180b04080105040c080a020a03060f020c0615030c0109060e090612061e15 72
    0x100c900c80c001c514400e032a942102c8601300c6203840b542807c043c1e000710345410018000840701d4110900035480b02c2001d04503c01241c00c3d4031817045034442010300c5130036070442c0140b4910f81e003039041c80381c1400f686044a460f405807107001c034241e644030704081074070009062030b02d032000d00f418a043e401403000d84442d03102d0203c14011980e240b01115840c0b4004a00c0082c0c4e40704842e0f03039101a500b081000140440d00100910003104e82e039081307810547d01c9032074060b107500c0c1601a404d442180c08072230501181c880c3c40030740c00342c0344c014207420016651441400c40d661f105510520030b40c0d4440d0200011f1000415080c001480c10402401b00c105003076000030301d1880c460000920301075407000c49400b07144140d81541d1102544d07104942046c18090090b13414504541d00c010311912511111681951060700e0765812680140c403458180401841085051040204442e80200e0741901c00400603c0400080b4060706089031440d4025001c100d5401d80340100030401340c24401d04201003030322500c440a0756 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 332981169 1250 332979919 332979953
    0x20f090c090f0f030d0801030516031110030e0f0601050913020108042a080312010609080727050408030a06050906010f05030916081b1f030902010215010803040302090f04 75
    0x1030403680c00000029a000598031110f541512032604a0050503400450707640c180c0b0300138000c541078015a50b0340c4002e45400760100406000381d026807180c050074141c844c05440d6030181400b02d098800c00100d9403900e030301132201d4013181c2d119030010002c07410084640d40c1c0100c00704031500715a0f60141c001801c103c002420041030307040d605118110000703c0ca0028490612091445c541c103540d40d01e4000c0da0703500001c0440020441d000700000d002409646080d0031a82401c014055591400f802c4d11440080c07443c009407071141183c59000130f5005c5104003440340c3d04c43c460064881c05d09058041c00c0303c0e555082540580904c00a20040da030b00a140f0480c94142403428035581c0d034492180071706014510302d042d90321020032100482d1201012500e0426699003403514228150301d0420466109112100c000040c3c4007030040c0c0d90203503c00d0300500381140c0107004651718003a0f03410001d6204c035826489441d094001080c01c0c001c40c64001045c03a041140100c40700f01d10304164651001205040f00e074 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 332982419 1250 332981169 332981179
    0x809011518060b0d02040303020105060916140708040e0403030b03072102030a1203020715050c07171c1a0102030405060409021c0504060606030b03030c0601140307120609020f090c09 80
    0x1c01050403800e80c00040280c00701072a42d40c1c80e4642040d500c40030b0342007400118090f50038000000c03900e003407514002d0b125401d6501940300c1c15429480645a03591000e000610031681004002c1c0030a141c00d0042000f04111258041a031503e414010129482410303114031a811201c1c04001411a001d802c41d83d40b01342c03489000c032074000ea04c0040d280a140b08402804c440e0307024802510260103501800d070850203001d039060310f1203000d420041100c0007115803502610050000c0404610070201c0180035001c0b072140245054a1144225042002c89142800850311103413490030341c005015041807039110038001176041a0a000c0050340c80e01903805240207903940458440812417980801c0450303c40078a004119070308040c1090800360a1501884020a040080c15690360500204030b410344507561001d02101d9080c600310900c012049180d0540c14882c004001c104184100005e100381840307000e000929101c1403040c083d50700032990010344210005820801c140c000b10080f20000d4800b210 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 332983669 1250 332982419 332982449
    0x20010e0c011110090c1a0705030a0c060f181709090103021009031a010e060915010309021f0513060207050102300403050105060a0e07020c09090a0b1608090115 70
    0x440d507460100c00750f501c0382095080007500e205000320042c00d68185d40030604d40e0500d104107440b5010080c420980001d0841e441003003d07060701d61040754031741101446104040303060741411211400742ca803004120404485101149020003220b0021a03140c0c190100c0514100795511001a02c502c0c014807001e07000d9481d0030144071b0414803503440000176580c40324080550101c51000c503451f800e800d0041c410211314000220b802890101600e40c4564a0181030541000611004501a00b880c0700202e030441003444501043c10410403140e99034203082c1d0f8401d0346581500610b01600c0c2c4560b8048019904401420b00940e40d010980d40034011550182d400300c0c020418030b130021001200c03903040e00c000011034003104101040d0420303809441c1c201c0c0c5a000e01070325000d0f40c00c1107070401d4904c0303400b59000a09000960811500e01903000800109885a200050300c9000010783c044420070050301600244420b890f4200001d290805a020000c120041d03580c103807941e0441c0c81d40240c01440031002 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 332984919 1250 332983669 332983697
    0x615050c0f01021204110306040b0a090f060e10050a060608060603100504060306060509090606013e01020a0206150604181808031b030402100302030c071220010e0c01 73
    0x1164980c40c070144003c650303800c803070408240d0750301c000d43d01180c185610f140807916901d400100580030701d0704205080602e407182280d2000400500c40100d0b08120f05803078941c086103c030320840360380c01841000f40c28900803180200089074402480c144915280141c14099039500a03065a481042600c02507625140c0103402c0002c54103941c841e40c5c2c05800c0203800300c00c01109800402c111002500d0201c0652201100251948001c8404500140b8810504920402d441d01c00c1c0300001c040101d40c0c4000c0407030120384980c20305c0c8880c0100c400e0f900000c01d1101c0690400000f6404045840121a1100310398000351851140e440360140500f02683c3d01d03446140c55501019005d80502d086101089203031900c0580d64001322001c0260072482882c2e1074a010080c0c0c200d0340301e19070040c010310b410302072014198001d4001902d03510000009204580004508400a0b440d882240e1510944400302244114842500700900c1090364140380354801070250014201800c0c80c0c09003882c5107019616 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 332986169 1250 332984919 332984923
    0x1806010e010203190e132906090301050c030405060c07030e010f1103030a09030305090d0905090c16050a06060b210702251a160b040609080c011a040615050c 69
    0x51120100300e58020b101048460380091100346079440c01e8070070018006030703405040102d4106107a584503a004121025000c000301350507c80c0309420041c0040e013050410b4001c42d0843d10110740c802030142000040c4804c0c0301080003a20b07400011003a4552414080e564000d280009082029050001c1c0048224140380168441301448141c002100d884c0d10b0650480d501070660b03104150042490140450f010050101d0801090000c50301c03a0383c20700740f80906011180d5401407405503440030034082440c0069100d060212500c0c010b900030814021981090b008542c81c640c03000d40c403114100134100c4d4a000d20740c68500310320f40034070000c0015a600b41c0c06034180a050114100c3d6100b0603841e841100e034109148205880804440c0103e4544403180c1709210701c2407402c0103c007000e420758048001002090034035401071090078042400f1540e40e0790781d415a00100c480420b50317519180c0d060010b0262110b42528032804a0701404004c2c50401030008d4103444600000811000080c1c1c40000081 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 332987419 1250 332986169 332986177
    0xa030504170312192703111e24040b010302120c06160c0b0f04030b19090f15111b010b09040f02030d020616050705010b0306010e0a0b1806010e010203 66
    0x841080c0712500e00d4554000c0e1329010350109102c4e446481e01c00740328040620f482c680c01082d80c084503d0111560103440c16640784140000d07580321480342c0e201c46040b880c2000f040200d180b032103c000f0035403003019110318507000c8901e5803d540300d00146410400480c2c0e409441c5030440f50180d440004000c3c010380070501380700c103071800942c0140e4000717013803034200045000c0c01c03e00b41d000340190011a625041e10040b644500c01541030101014001403000c02e000c1150160044820162445200b1301c500500065981d01841518040c11420509007404034482c40480d42e600124002c000ca806100c20114003801030160420503400e444400c52084d02003580100d070138000051245625280c41d04d08400f0011030900100e009000d18400d001015000003540c41c000c50030403613a22490300205008450b1070b00640ca00391120340d00c0c2d0701c09140b50b44003409401d010b0822541c4521302c91801050035020703911900c000c0f9000d91402d80840c0c855290302c0000c070b038010b002445c04e4a03400300c2440040f03256000b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 332988669 1250 332987419 332987437
    0x7080a2a0801052106041b080a0b041208060d080906160501020405150f0405010e13020a18150801050607020a030210020c1309030206060904020406081203010302120a0305041703 78
    0x1038940845600740c1100101e4101c86049801c451020000041341c1000c11140c01110440e601003000301300092100d40c0000e1685408070b5451b00910741d10160035180c00d51940060350900301030f0043c84140112480e05042044140c00c0130655814614046411b030512900c01600d5620003082c03001c0c4a6446500715590315800354422252038049040c490300079442071080600c1005a8103415a84038600029645010001491142028a01b00064600300041c900e00d42c0e10100f82d400e841d001c4c110600c060100211640d50300302c101909020300f070000070700507040304090704000080c3e00c0225504c240140d0550b1002d807403a580742c9801d840802c0c503500a07900000c1d400300310071003002801580050403d00c080d00c00c4490740003480d0588010011655206409001078104034000740d001c3c1000910260441d1000d00300203032503035840b4241d90a1000c4400080a03c01c40000100b0a43c0341403441400600c00400180c200d007034450340e001e00a4801c40c41901c0c690300700032600010aa0f028010b07204000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 332989919 1250 332988669 332988731
    0xc0f230405061b0c01021906050601050906030f06100216272909060f0d030e0a09090312050c040608070207050301021801201009080d0c080405100507080a 68
    0x52203000d0b107420100e443d100c03200c106108422280d80303950701c0001d02111124100307542500d10900d54031501e01030306004144034140038007000001c0301c03500e40c02c0045100c1d0142e040da0800300c6c01c126013042103414176000c8603000c5501c4032480c19104051842c410084801151581468050031502420000b00c0242941680e41c80e00840020070f951000003403084022140040002e80441c800704080c4a5040d100c01d600404c4002e5140101d04051000041c447d020b420004502103000f000514a650160400801035860b2500e65042540144401140c6c1802c10340611252504072011680c500071072144108010071500810030f018000e11806000d01809802559104d2249400460b20744c100303421140011924400703402c10a10660906c014400c00c1c03805451503290b10080c800280a03d02c2c401d540d010340401002944500724801c03600e04400e00e80341c40d10503103042c0c01c009080000c0c0c0700b84500b0030b500780010410f03515032042e05280d10080e20140012100310381d0455050301d030317050581f1070003030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 332991169 1250 332989919 332989927
    0x10e060f0c09150d0603050d0f0f050f071b050a060806090f3d06050702030d181e091503210c060c090f080c090c03090a0804090f0c0f23040506 63
    0x701301d81c1e00417009407400380d4100c1e18040502e2804544041d8420108400a0701a403d04120235101c2d400030060b0017414560340e4101401a260b04100b4030144101032120158008100b245040040f10302004000700e040040280c6458401f00340d2921006020300020658071002032210400ca070804940204d40c502211043c0714120455201a5402e45404072a594545030003e4840d21a400b141c6440341d024000e00324078022001d058035841210013001d10286014800840c0691361948141e8010181c0e02c1c951503484c0c80c00311f0b039000320b8038200c07810318401c1d01d441814004192505080301e543c55000184100d801c00e450812100c04400d050002c240b6070810445000550b0300c4403000081e0b0329600c1006840e160341c3e80c4000e40d07444c01038801a4001071030000080b201d50800c005950b20038006805d48041380c81076561200d2551264100b0401c0c180e4130030700c27824200024030030041e941c146801e04203204080104050100c0c030881d1007115500e503000b50318085200c50401a14020200507100c0740d11 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 332992419 1250 332991169 332991187
    0x7030c1b030b07080114150a110709090302070e0c0f0403030e2205040302070e190b06090607050709110703050d0e01061a0d0e03040f050d031e030509010e060f0c0915 73
    0x181c40707070a02c6000d10742021411451b0341440d00807008201d91102820540c9007458070403040d1a80d048020405100e405205000140308800380503002440c1d00c0fa81c041c080136414100c02400d420300207083ca1b02441c07000d0006801076040c1208450a8030307054100440c009120000084041c0f0300e180c40100407808601122002d540c95400c1180241e00c80e07020744203420303103816044041200480d907241401c0302001d89803000c1c45c915030050304655000b9000518150100000c070310035070f12041c000c0314140e01220301004003a40500c101d42000901c06041490880c6070f0b24000d0141c05030300d1401c101c40d5611030896800100940c4010002c086440c40c41005c407108210001c4150820324000400741d08290000070102c102100319400d6684003003078841c10f21f007007000303200c1e0540c10a031003102030203008050200c9130468000c00019040c1c035030390302080c00c4ca00a03800c2400d462610041007143e500460a110140f030a60808951080011482c1510380c8881c074005000110310148070000c000e00015a205 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 332993669 1250 332992419 332992427
    0x6051c0303050702120a14040510020601080715080c0d0e010603080405040f050915040203070e161d1005031e040803090606030619111b071403010207030c1b030b07 72
    0x18180e0107034808000d5079584000a03a2994513520029525880801c000910f250043c218900c031004103040309403e282d180c0780441c8600000d40f00950244c0c0c803074401000041000c028000103440c03171000f0340c0e03150780a40d00701800601340034104001301200850328014414041d40040f0722044400024012a56281040201c980c0507000d06809141007940010264a450082a015000c0d07040101901104034035802c4541001400484c0e1500a08000056548000101d00d000301c4840d602e08038a4404020302500a0144018511002c0e0300441007031940e41e244a0481c004454904103181e91b0b5030f50400c4649034030540410002d07a950304005120034000440d008e10311034600281115003645918081544d607040c11104411a8405036014803000e081c543c000b0045043caa401090620b074800c00d00840404044085c0c0e501503000d0403082140e2101e48011501c000015030086213040304603140208001c7c150f2502400148465034541c01c4d844800c0c0602e0001e641046042007a410000c0b0010 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 332994919 1250 332993669 332993719
    0x3050d0f0c230f0712050c06011e1520160b0904050c040506160c050a32030a030c0c0e0c040305160b0702010c030c080309010f0509010e1509010605 65
    0x207542402c1120492141c4400c004481810503100c42d11400e03c111545c80040e51580c03000d0700400c0001c10700c804a504541001000d01810023482d04400340b00401e0340845034080c0070b512042403280f90140c2802141e8000350518000000d002c0100380c203407403289416180c807982442114030307400442d0001490a405502130410b8040446061005e51500c45c2c904205000314090298040300c10444101191a401d01c00300302a40304040000c882130351040000c1045d50154041d400200d640c0168092b42160766000c0340c0b46170fa0302c01e14004a068100007013980c0b2040300c140101440b8100801d4400d00800040d100002c4c483c43c0301c1e001d004c1c607100c54002c001d034000b444225036a100703041c00350040c6039118030200700340c0f403403408444d041060340e800444800c11811170170741c14465031aa40c10041407284000350b2091900000100d00000c2104911007140c10007414103189925049903103c602101190882082ca001c1c40722240d180c94680c42c0c50b00400e2164000796012200e0000c900826218072900 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 332996169 1250 332994919 332994947
    0x2130b0f0a06020303130c050409060f0c02011a0d080d0c02010b030f01020a020604030509040212010902130f0b22080604050c040c05032502070306050c1b1903050d0f0c 74
    0x40c080d2914101441116446070007010003680052000814480700403000310b180b10302980100790364541d540003181c00c50b280001c059070101d4032410011945500f078003d0071040d20240c802000310794464000c001403071458003d001e02c07910440c1080802d0042000c1615103030420700004100d01c04402c44064020401107032206c1c024002d40c0c9442c40d1004e01031098500d076180c560041c0c944e90f0b889581c102c9003a88200c1c1034603441582440700c4000c1800c00000103000c0c06e4204001070756415036041715003100300a94400380020b20301902c203200041d0340d00180c1d82064503e000006241c0800b800384000234a290708542502c0c401e0804000074440c0000300d1900034201a10200107c65208108840c1880f040320f48011454a0308580400c600c1740e0b04082100450901c1a030710203603200d5680c00103a03001903072082d04800001c43d03003d03042e8445401840d0725800d5140100292400d98045031094040014041d09000340480d01110400c415003201c45840d090032802c0040310018000584000585849 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 332997419 1250 332996169 332996179
    0x2010807020a300801031101050318010e0a060e0106120602070c080616030f020c1c110313030b01120f15230a0b010509010210091a0f18061003061802130b 68
    0x51100c1440c016890076050347d800030498840d20400b17500541e03960788060500d1404400c5e20f1594580100c0c00c1c41000c1c0325005200241010070420306045040d6030404c00700b03400603450624108140550107942580050340050050b07180ca50340c5c1401190318400703a00c034283d0750140c1401c00c0100002c0c80904403d070b1300030b41c60070000d007040004404120300501030b1205040d0700004400a40e05050420000036540740d180611440c602c410100b400c64100d000711504c184d5031100184208004070320094094001503104000422680e01c0b04a061320a80301c001c2e04e0315111000e88a940b018030b402541038002c0d0742c0202800c008001c51502501002111a5101f442c43d000c2c40c20f03120745c424811610600c2050340104480051050318000512018104981145d91005000a03800e00c15510604c100c41455080141d4034003041d2107015408080386803c0c0607042501005110000701002005a94110b41c0c0060441405084610710581100003c0e41c03004400c1400700400c4040e4000201c412403e40f0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 332998669 1250 332997419 332997503
    0x13031e1a1806070c020d06150602031b030c06041e0206040e0403021605151309060305030a12020703050f072a091d030a21151a031302010807020a 64
    0x2640e40d4071000c1c156a40f4001070440d020352409450600300740c001c0140104070009200e80d06444215159520740c0c400c07805a040465415803500070b8049804104d0b4114010710b1804081010894031180b00400040c1051501101044203081800001c0502d0340c0c044e1500d580c0b186c1fa20156040074501b21411001481a82c0120741020b104082c0c10044610150000c02600c000c01c2c11501c464000c413a8901103032081d0b00001416a065010b40d2000714040c2000e141d99440325480201080000c4e0740d42e07031402d030042064800180d070140450b081c84602e2240305d42c44010a1400d0156045003511030804140c4101e03015042c248012207207002c40d002204c1c10000c102c0103a031842c4040c8042c0141d00a150418000340140b2070292038100c0c401d018050100740d501006100314402c4600c8800003100810800009222a01002d000406507604007000207065142415000000c207004480007030401c4110400301d0a100e008010140712640d01c07401080303020041d5504d4100c071205045041202c40c0c0d4400c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 332999919 1250 332998669 332998711
    0x150a0209150915090f0301060b04050909070b0a0e010530060d08090d02030109020a0b03040b0c07152c03030f1b0a0e0a030204020301030516050613031e1a 68
    0x41129001c0c0b8002d841d00030140c03001c2405400c6a0004003400f60030401c656141e8410340c0c1c00703109042c0608040401d80751101d0600c0284039603548010000f000583c484101403146914000540d06044528941800b034074240100403666401740c1102110076420f10428031148086450940d0b44211001d01c0360360f19030f611703d0104240c20342c02140142a106040041e0702460504d258414091030014001103074107039a079404141c40060b90b0307002000e0000301106100400c54401c03842c642281a480c200d50030f02c070803602c0340300280008a40c005162a6628900c0803034001044c11021042e410164a03e03907a500041802d0701e0b58021604016004034040c0043c03400302c585451503641d81010b0b80350600740030340c0b00300c242c3e58000003210080e404100e180700000180e6132170000314003840c414800b03000313180342c0300004e01c3c1c2501e0300f82c02641c402c22040c440c40046000c074205004c104d90f0481300010b05034681d2349a91300d884502d00320250000030300300109140c7c1c2c42c409680c036000750400054106141c01d62 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 333001169 1250 332999919 332999959
    0x302070c0e0a0c03021804090203071205060702010f060e07050c1c0507150213030b0702070b071103010e0c09070e060c12040302150c1507120603030306081e0618150a0209 75
    0x80c8082c0b07220308810b03c0725220700e410194481d6992394030150031507021503112004000101e001c20001c40d1698426020080c081380d080c003031101c104414010901819040c10b1940c400d140e030042c80d803400c10001040700840c0c0d01c01000b1074050b842c036810741d040002016000081060303000440c05c0d1144881485184603146040c030854148a4001d007000c2c1500342195104100058081c00308030441c411004d02294070502c003001880154841c19001c01095000b030306050940d600300700c00c4001a08020018030941d125803401b5a4840321600e481003180940a00241c00d90084441c40941407183c640c1d1b014401240e0002003050304c0c000c03240c1481c85164000255405d109520b80b10a003a0000c2c503003140700d10744406c4080d4020026003480781c035507141b1003511001c44a042e442500069103c1d00100030303080301030001e01d10005514500c9900c5a06584000303035142d00207043c80000c0040c10b03100184110051002800c1120300413124006800c1001048000e5001072035410311580140c045c141d01034400e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 333002419 1250 333001169 333001177
    0x7110a06081b0c060a0b0d0507090506130b010e010e150d050a060e01061b020d06050a090213090201090e0c04151d1f08040c0801062603071e02010302070c0e0a0c0302 73
    0x81c003005105940e585c280800c040c2550401d040d404c100d1001d040800900b042c0425005045075a9000031341d441c00504121240040c40d0750b41c07400624040780451140d9000d145a540c002c1d0a00b0100101150740c40460031243e800c0f1800c2d03044001c003065070b4180c81421f0308270300d01a180d01441841217540320328414008400a100d22004920308204d0602192101c9032407040b941e0000742104170800d120b40b60340055902c00c548015000d0756840400c030462801502c18411700207034000404c0400f0700e56001828060480c043d03585801c8450740003030085500001154098820720042107040c0d15001030103401901020b4820703c84401d685000d140e181441100d00c111920445442065404090803e032005400644181c460003c1e5031804200030401b4050f0301c00600080c1c1141ca1001d02802c4050704180c542240151580c02c2000001c01040440324541c01c005003022480700c41036014070069009104001009000c4040c5080008008203a081000d01c603010800c0700340104030031620304074101d1107 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 333003669 1250 333002419 333002437
    0x100207061406030d03050912040b0706111309020f0d18050c011b0b27030403020312070506220615080f120a030c02030d050a0b011805030604060207110a06081b 70
    0x101810340308031418400c0d00501c0d0849084d009523200c2c542600c600022035407042c0c0014804500000d0b458040040f03a03c140461000f8407244541030000c9809492100381d030724460700e0f46582d00843c0502d40c00d00324208644080d04103410800130354102a82032801c1d407800c6181a5124000c204030402030f540109038407103021001482401c80314409a0b100d640c00ea001401103030303040090324181c1c03800200150114280c40d5448005507241e51540c0b04140c90050944000e1020002c141b2803031000800014901e07070090303002035101d510b0350403e6a46e00e031004103844c03001d400d0a05000032440414010000402075841010903146044212081903945466108030000605000c00135190824070a070300c0b0300015a8640f05803407030700400b00c4199050780c50990300300105541c1c0390507a444a62b00062801c0b40762003600341c0301040602c0c2c080000d88412000b08043c058540000c0e60904100c2044103054022000401c941850354a4410003010810f0844140101d00f00000d000c007113018055040c0d0714000c0c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 333004919 1250 333003669 333003673
    0x5040f1502040b0d02160b09060a0e0f0a0b0606070f06051803070c03060509070b192303010b0906041211041107050a0206070c0f0b090312030c0702010311040810020706140603 77
    0xb203030001c3d401001b580b0140000603030024004000c0001054840560b00408102c00203049500704150b140040355003d1003208440d038001c03450103c54210103d07902031404d030003210304c0e500da944810100311035104041c0004c0c000d07888510080100803c40d40114003a4141d01c03180c031030040652422507943d100365403000d8600a0071a0041000507441d03040702c0d520406a40030b42c1c0300240c3c0d0b021340d500150407a1104c0a5010140c0403182d19440e88151520840b01c000c2c0c483c0002c0464041c6d100f109440180103007880340e1000268074001c0d4a407002150000c1c4140c0d44460251061030410524051000d0840b62081d410003842c014900d5102055030032103030700940605108001542001481e82c030400040f51481880b000014583d80f407100a80c009184a598403959074951008041c180280e0b50b207030601f030f26070038000c0c031140700c8801058a20482c0c2c282800a00700301540d60010150003207502c4012240f01d180f10f151aa203410360080c1c40700900c07440051044100c07070b0a0700122080105c40480e00b42e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 333006169 1250 333004919 333004927
    0x9021809070b0a02030d0b0d03090e06030304050d051006061103040501050903100c08160206190b040912020a0303110306010e0108070c231b1005070201030b0405040f1502040b 77
    0x220541810542180640d42254001565082d00074020b0b041402200007603000442c00c00041c2c90319000d400c00011044400103107000035560f0250694940307010301100304a402001410340d0b1810802c45010f080014540c0090b480c161500590f41e01c000c2d42600070107828034100050083c01445020800050107010f0350800d170611004441903000b580641c3d5051080310503914164201d07201d440c03803500da5503940409910b461071300c2070843c064607042c0504541c082c0c03007042081d282c08803083d0301c42130410001003811244000010040d050550340948031b40c984c3d040340b113071480e000140740000c14444e4405000301502c1c800300084501003200e415000c2110207088001540c400e6820680c024103d08108854494540351030307120103044680c4610094501c50185400f150800005880000e03540340003c5071120080070070165042c2c2045d0b402032103408031701c1320704580c0203800032000130102070010481407a0504005040080550741515203026610020082140500848068a10f00302130b992070 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 333007419 1250 333006169 333006199
    0xe1006050f0622090209011e1d030c120d0e03031e0f07060207060b0913051b03240106110d020303060d210807030b0d05070e0702010213080706080a0902 67
    0x100c0c0d11001c40c0071205808010165103540c14111264013424440000507141c6012000240c4a0b8180000b9002c811010804034010a5031100c01140d006480410003808049100003281c0340402d0801044d85c400c40000010400b004005002c11400c2413540d00d09148802e54010f268907031080041319500240324010023000c5810020040c409001c0741d500881c604812926850100c1c1c106800c206c5031103444c0c98100c491442c0030940550048250845014424615941e060345d40e2110100e03150b0b100c42c0e0750520903055500f402820704000407800e0030103c0410303480000700801424041c1501041411086121201c000181c004501285400451854403540300300031000c62414000c40783e002d101006406c0746002d0000c1d01c41c85403015100d240e209c2c00c243c84090152100c0140d041d0080040140b241c0c0820ba00040b41e00c1100e9014007481069114490100c1c06481030413240780650002d0000081c5c01d81d80004c0480440d4465581c0500907243c030300048003503854a4101a40c000e04903030b43c800c5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 333008669 1250 333007419 333007429
    0x1050705060f1305030d02030a06052b03031b080f070302030c0a0c081b01050415050c04060c080d1803030e06070f050d090c060918020c1c110a060e1006050f 69
    0x5000f1026030345240b010b41140d940c20740b442d403100041030240c1e0340100500584014501441000e072000700c2d0300c5c000402c0003081c180d10707000b00c3c1c2d0303949180c0708900f014200c00c0c11f02990201701200d0f03008051200b860400d202c00781407444140d4011001584038000120f1280c400c2c0b00340e030300880c046004a854981034a40865009019a41c1030340c200c601003003500d41c0c14068551a40d549060324001241603d82400c00301c0030000c0884410420074141000c100d1942e0034401110290345460401741480c1105090071f29060140c0024503d0f942d140c15600f0100340381041000703070560700c030340d800b48400500c0700580c545410040d239102c008200b0030f4101c01e030320038058030240262017038100001502c4603007901d56002001503030340400041540100180071034142c800103800260442c480540c60042d00c50015503485110328501441c01000148184840e840303603800c6203007035200d10102c03802d28486080000081050040b40c042034400c801c40038070855918001c0304203c80c0700410003a445116082481 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 333009919 1250 333008669 333008671
    0x6060e0c0a113d06030b011403010b011e03060504050106020a051903080c0d0f06060504090c0212091903170d06063e0a0f0501060e01031707030306090c081501050705060f 75
    0x100e00e0300c000f0300081035140700d841160000c5005100591055140580800540e040114500d001e81d042031041ca8450f40c0150380032640410b410203529400c4080002140101103a030802c5501504103000082c41a41c001403040000b40240241e80c0541d100307000740e0701c00c510440c00040124180600150114250b00050302201401d1ba070003180d95907500c514003003219416000300010401c00300e8103101c890351500c1074289040e01400205084660700415000501031800018424000042017200e031901d010240c0009645c0001901d45003500180d140e08141c03c002580c200982c0f0300200020340a11034a41501c42507210001c10480070106e1280004104450040c1c0902080600c41c000b441c0701c0800207086010302031759080040c41410b241040c00d40303515070b000c01a40e130084070040c0301040708410301103028501558020754841f8185000e9019200b43e50120102a141c03513240d1600c2a04031081c0e5100d00d0701c0c008002003030020f000055910380560f41000d05103500c140e001900c100b140c01e90702c5d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 333011169 1250 333009919 333010003
    0x20d020402070605040b010311061305091509091005060901060e040506060903070b031b03061c03020109080d0b030d021903080907050910080d02010c051606060e0c0a11 74
    0x141c41c2c99000d0303d0fa4410f4a0f401c0d01e049401c6803104d4010401e02404d811159410780d000c0301c0e264600400c280b00300c00714130100d0080758411034003840803a2a00901140310001042c002c0e00c50341051411805242c0c44500c2e24846180d02410300001812514080d000c06040ea003181e142c5100750003081c0148070081500801003904007004100c212003d980804c5900010700d0b0748400c00360380345040c0302c0c0c0c00b84d042c5a200ca84c4110500a10074040e490f0350303248071801e0442c02050240310344c0c0303a10f0600700c0c050101107a0280c52164009030742d0000441d9a00204802c0d83d003a01280ea0560620b00100d9603141d40b07401500c200340900c4e40410000307114640d0190005c494000b21100c0319142c1e1f00058101c101030340c240c0c00714805884d04106600042c4641041003010b07000812143d000513102806500c220103823044142203006c0d0100401541d54099000b2703149085503080980340004170340c0003660140c002030011400050042c0c5440c0380004d8621219081c10755054000c8652403072135204500b203403c003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 333012419 1250 333011169 333011171
    0x30f030e010b18040614011203030b090603060f0c0f030114040e1204090f020c010c020a120e010207090903210f060905060d060b061204060f110a0f080705071e06060e1003020d0204 79
    0x841c0d850720706c0b41000714041c082441c12091a690315103405011120455013803401249540c00304651a03174049101c41d031041d1880124506903031003a038440418400c4d0f980c0c520705940040b001241a00078000389060b0a1825a0200180003140c18117a0b0340d01e8000000d24500b0004110a1200003119044886901d60140c009824280c1e5800c229081d240d40600600c0181d101003512800d12494504003140f1049504151140700c4c400f80001303440317110300d0003080c11650b05ea00e258001c00d4407030a02d807041c2c0a05508400c0102004283c5000580150300711000060304000b40410000c1c494271030b16008000003004044844455a205005819000c09640c2c0c820002d011032001c1d4030840c1d0701984a28455203000818034401c4640d4412602c6440a003074114009003c200140e503044000c1d241c5540b400e0821040d60b580d08441200c181c802c07c0310060880003801c41d800010304020011103800b41c0306860078400980c9881100e1003002c4115030030001140310000c10005030030105507002c202800604 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 333013669 1250 333012419 333012431
    0x715051b1c020c1608060601030513150b060c0a0308160e0108061311040b21130209220c09240b030a15180b090910050c04030c03030f030e010b180406 66
    0x6004000303c507132580040d006030005410011150390510403158003c01d410038124805000740c032045030034001401170307001c9180e546407020095a2101c0039521000b030345c1000c90700c500780726141c0103141c00e038151140039500b07034007280140003c2c0c011918241c1c0b512060751415800c3d13542e1402c028482c4d00e5145c10940f03ca039103807540c0e02101c043c1c4005002800c00c0088031070759080c0c0c045503000e1742c91480840c1c10112015105220294071008800700c1015011908100c240c1c032000341405004000d0054918915880c030f920388204280351000008445103440d081040200d1901525035481000c403282c001c090290000b8004060a44003454018075900c0001908100740041c0380b0081e00540c200c0e00c60340411465070070702c00002d80501c520740d6109541840460500000311035450328000c001040311511000014039051000d42554000c5410910a660a503aa424040c1c0810000111400000d00340740c29a401003c0501603004500c00c054840311202c40040040b503490700020300b085030600d48400c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 333014919 1250 333013669 333013693
    0x10080604090c06021614090f06130c0e04050105040912050a2708010b030705130b010c060c03060f08060c1c09060c21050121020102030715051b1c020c 66
    0x2190b003070181000c0d400819050a00500e4800d0580d07465110402865400398000c20715102c04251a4110141201980c21030b00c60350001460306110a07000f291003803400e01d4503040260710005001c95840255000c000d1662a4018801501c100c0300b4040c0c89809030b5400c007070844c0d114074000c14042169280c4220b4504001e44010741c50350251403003014003120090180306040c002e1240b43d010100440003028050300d4600841d4440b14190107000680d40d030340c1c002e590140d01400101841c541e01040410050142e008090f0042c6194094ed010044007600003159030500003a1301806041c1a405041c10802c03801c09002c6480c940503d003c01403a126180100050903e0003100c0e8906200e49694102c0c8142c4020380f045100342074001c6014500303281c01000350300b085002c0e1440d080d040300d120306601503440c00142d00d181702c0c458001b07090201088045241021581c8100e0107a0300d45140e00c40c4990f1150451801c9019031191841c00d40388045410001506642c024420030300d0200941d0741000c455 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 333016169 1250 333014919 333014933
    0x2509020c2d0d0e0a0b030709091d07120515040f021e06070f0b09070b0910030603020909060a0507050a080a1e0e1f0212070e19060507050d0504051008060409 69
    0x600c55400c0030610a101d050f0462400c1e01c200c03005005004140303400c0d450204801810340100c0e03c00c0f05840d595600361007030014820780c0c1d400100d201c50011117074256600c005a07401514056000d9440d8050100c4000a002c506203003a401036402009822120782c5a40070004500d0f101a60501022003005035180103840303a40c05014514003606034035813040802c3c2041428014020103007420784c1c201d00e03420300603104200c00b5102d50000594209484000b40700b81070b002000b45801c040d5000e104281040300c241e4000804a110b048070003814801a10380b042e0a0702c0b5030013002181c4000c160040002449100e403030b80800c10b00c0d0203181009030110f02c107803071000c1100c80012010a9580003408c550003030202d1201c02034480101881c4c118507000c1440c43c2000c05040140411040040e0160b13103400c1d96551040140e2a03140b01c696500c0c10342d030307100f03c0982a90b00000c021a03007800307045400c40b030403802501034a0880c0c40c007821b00110880324034411102600014030312940300b540c420402c0089a04 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 333017419 1250 333016169 333016183
    0x1d0a180b15030a1a0901050708010b04030312021303050a141209040e07031506050910032307031a010e0a0506032d030a090509090123182509020c2d 65
    0x4d1126a102820030352010713802c0d00c10003051101480302c0c4070700421080703400004031070850ba018a000c5071442c403141c0ea000040d201d50540a5542c001020001c400c0c0000441d0400d00079100b100c00340b49181b036018030292502c40c00c003031346030511806010b101000d0034030741c2100c1050300c03090059070403a544030b6550160130441003510000301591110107000600b0442c81d00ca42020100800d81c010602e156540440f0301c400e2007240c664070740503a0804020b21800c101c06009154010040840c042e03c0008080c50700109200d81d0090301040400704145d01010b200d4940a002c000e4040c010310720b5200d012280a1005501001c00c801003030103560860102072014290302200e940d505031b90360f86404104040d00790060200d0089074903241044000c0081442d03040888000c030318041115950780c0281401601e80003050210070700035140c04481d101c80520301074040c2002089007217a00740d160303155801280142550401c85a11104504005540549a040c16600500c90302130701d080340008060b042c520 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 333018669 1250 333017419 333017453
    0x140706050114150913271203050609090a110d15021206010206130303110d02070311011d21190503061f1e0302041d0a180b15030a 57
    0x82030200c0301e2003514080e080300ba8030300396070741026080c81c00000019440050500c9108000d907501e5045c898401002c21440b0199810700402c101052042d04021011f4120f90407401c001038680000103249240c4030301003c2c040e040403001080b03a400c3c40da45140c0080310030700007264840d4885000500003000c02c0100300c0940000703003000da01d402c00d44100d5400103030060b0445043d5000308082140302007040213011507154152a003c10410091503054003d842200c560301701c1e09000040d403005042c0c0020f000482c07a00c01e03000822418101000850040340c54140c0314000e03810100f0524040102c00303030355814101c1503140c00d600d05510295a88004400c4a810001003a00842048550b2030440200e80b548101500241c03519500d000c001010100a0020b005583c0300410b021900f45200ba41502c0251a59a0f00001e01c5c0502d04022030145404540320000d042c10118011002c0052940007440983c0c0600e100805456105118800c9a5030b1080140c0601c1040850300110345107041d104a100 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 333019919 1250 333018669 333018689
    0xc051309050106050301140a020a0e04021206150c0312270609060601090518040302010f0608010917040e0c0c030c0102040f0608090604320109030905030706030b0604061407060501 79
    0x2003400d150a81c291000e030360140384a40d15100070126411440703c50245d108488ca0001640e40b044c8041c243c800d04070388500c11703800910118440c03040410708000c06000307823001c0381c540c0d100141808030b042441c421422402da80d80c0051150765503810007070b2060b503000504040c3c8014071020f2401032820700742861160b01c4a0368041d0003400000c240620070550091001e00e0892146406c040100702c4c01e501d842d5600038030f4101c0b20700180626100b0b5010780010541c1d15820700c0780da540d8140190180008240a03110080e02d650b034040120320181c202c908460511214004d69924450f0560050300004110a40d0340010011602c50305428402030001d0030050070a010560b003800c1c8020541c00b030017042405142c0c002c8050001244a00d40170190404d01c40100c0e00505004040d9100302841070301c0318021641c01c0030f90560406030000c8000050310015002c581507180e940c4004c80a40d14244203450300000300700000d10840e4440e0100303603136500c1036141003131030b28070303580e0f500d404480007640080003407 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 333021169 1250 333019919 333019931
    0x83c0a0503191101050112080a0c02040f0e011107050c04091a0f01140f0a03080a20060105011b030f050336100204050102030f0714060109140f0108190c0513 69
    0x5503802c004018102c4030f80c40000c21940d0304002d0b0303202c028510a1000303480f00c0000300348942c010748900e2843c5807040d4040c10501070307034802c080d480014141c0c603014141c55500f0425030108042802041d241140d0b00280101034040c0f82d002400020032100320180e6842081e4a25104041c0a00740341501803002c01d41700101d9580341034425200306140d8120648948060f0345602555991000d10b00156900082070300c1d0b0326911500142d0741c1c00101c0904101001103c00c030101d080001080d0513040b03443c03c2e00c450a6028840c10400000002000c0080124248178200726481c0d110b07501465018421610407420301400348540b000a0300e46440304000311000d0410103c3d41c8074140304001c05411030007010360a01d401c0c00d002075100e01501d100c10160032808240701c3c0a101110415407203036441402509c1030b550311001d181008d400c40340780c0c005024070803402091001c1c000042c000d0487c0c80c00c5c0003400301c028000e00840d40099a81d60207907070004040a0109070703aa507500c6441d05e032800c001400074103 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 333022419 1250 333021169 333021217
    0x9030c0a05060a0c05040b07060b2d0f0a05060708030705251211030906090a030204020a120605060306060901030e0708010c02101506020a0f05030c0610083c0a0503 72
    0x80c0d5044070620000c1050a06c410019070040c6020384c0c210030b90104010501a00400114181e0044d0102000403d00803503101c040118110855010f550030603100780c42102510410711503102e04c180f00d1346030882002c00005000c1171500c0d020351f030089034a103812807070b00700e14442d0000803d118680d51081c8008090703543c4204040d80343c81c082c940300340741000381c400300100740a5a120301401c0b40460103044005048505641c41c00543c80c095039004204540318418408000c042c00d442c1918144d0161a004c008281454200152842040000c2c2170502c0c04003079400446c05059080c240c1c00d580e129100001c50079071028014000c0d41d40c0541e00405c2c50f800c035000190180c490720281c444101c1c42c150014810030f9808111031036460b400c40c0800c00340c0e2101d032038654514400e00043c43d4050140b1401d021040c1d11909210003190000c504941131051015010f44e030702c00d03a031400e05003101c0c1802201303044d8040751091045070645a8041d10000c060a480345420340c0e00000e24406403100301c840d0519 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 333023669 1250 333022419 333022421
    0x302060715060902190206060109050126040506100605040302030c040f090c080105151806010f0c05070b04060e01050c0c1e0418140f06010501120b030f01140a020909010e09030c0a05060a 82
    0x406481701d44010310450800e240064456006409000e0400c0480c800500310307000e42d44032007481c044203148070602a2500341803d54507000c0c25208010000d030528000214644500155030a5070780081c0904840444401000001c10110a20b03151058840c0c5440002c42c11143d8840000d1803400c00100c0c1502e0009e0004075800b03101100d07136111365525080544140c0c000400c2d41d034056020b082c84900c001618006071400700050390001e000f88214000410700495040c090011603006444030780f01d030f90035940151914020140c0303070f03500c0b5030000c4c11445892a0160902c1e02c00d070300000e0b00b0b5140081880128042e01c65040c903609050780d0f40c805060030041e06404001c410686080680418034220032081d44a00043c801c0504000501ca01c58000642d6a4014403520a0003801c03200c6121021050901038170140405920080742c203030001e142030b0020f000711002554000c151202d643e080241c011460b4802a0050b50b05120070b200c0302c144001c04201c9410b03080d0040000303141d5480c0800c0303800 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 333024919 1250 333023669 333023707
    0x20405011a030112050f0304120b0703050103200f1509130612060e0312150a0b04050105040b130f0b040e130305030a0f0b030d11070909020a0302060715060902 70
    0x322603100180c00798403202290060781d06442103a25030800507255400d040e0710b4500d100040514901000030000341c4c280c0781810440c40b01303100e82c02c9180942e0301c1c0360095088803400d10002e800c040503200c030592000080701d008541803200a2207030308240401c0001c85c04001500652181141000400c032001b480c040c00408240002c61109220f5281046100d0702c1440300e01000a00041e210188421111800d2055a40b50381034280904454076064420010039010201000e0040c510400301040c2410740340211801c1c3d0300180c5416240515000654085034040d2581c1700c1e1001031807002184c42000318003008004e001064180e030311b581c103104400c0440480501480d5100d2802c01c507100010b90000d00796a4401c240d000000313015280c4e200c100c00a80750802c94164180074882e52a904a0380040046034103983d5801160111610354070818100da989181c0a540402d100d2410401031401c40002c1003100d10a040750081940c081f680b50003a01d100390881e0a01c1c54003c9003070040700403d0b403461 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 333026169 1250 333024919 333024929
    0xe0a09051e1b090d060b0904060204050907030608071a04030b0108010617010c0c080c1c111908030c13080a0f060e06040f0b061203030a05041a07080c3402040501 71
    0x2101d904501110001514407500d070f1594010071180ca04442404865804400d49900261024249141a1412138020344c0b142c000d85108004400124600904c248030300790566030f000300204203050521003290807034070a41c03891082043e0100710110001c1c1d004030201d40240900c3c400468068201b0139081d10200c0c15810101c81070303140046203c00c0a9110581e01c250941008181f81c0c3c400c021151030341030620210034a1900100350726240e030015880084485ca0206200035503000d07294030700c0c060844c0c0003051000b621501083c808111074400c0d610040c040e1440044214121585d2080103605010780c3d00384c207484c000c0c11005084140841405103560007c0058007400c3c191034a0b03078031a0701900303200402400c5480c2860000c4c9064407245500483c0099650460340c5070300d0113082c800003400007110115600b0444c110075102250900355000e01800d241e0310383d0217842c8d4461400e030200740c02403000f2120001c0344003c61810142140c500c0b80074017481c6a210300041040340180b2043c1c0c0c030182d100d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 333027419 1250 333026169 333026191
    0x70311010c080a080403050705011e060801060b12070e090106050c060f09060a150f1202030c040c08070305150a1d060108091002130b1306090608040c05010e0a09051e 73
    0x294500003007036003040f070307585034504c2c103084c0142c1e159401c08039030601600d14010125864100104040070b064280c008032a140311005026927605c6004803400c1c2c514a02c03030203001150a1003000046202040b80d03503408481407a03d01d104008020004102d02420303808100885c00004051010520a020603584844c41011f50540341c245a040c00e0781d2000024201c1507407980d2100a56410780840e0000700c024501426110004c60302e45100583c49000312008900ca4410540956441d0a2a008041c0c1c0d00142e52913075201a501c800c0141c010341002040c420740d594044a16280d6541c0790300f0940e0207030500441d1201c90b1100b0094901c4040b00142001d418040f404080050001e40020140b02a02036200d0150f150b01181220200414580d00803600c00c101c08203e9540c1110110005402c5490310780d9041c0086940d200155030102d801c0d50098140c0815003014400740d40222125041e0f1400507004500455841417401c04580090f03420303031001001000e01803040c00800711056000074014034 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 333028669 1250 333027419 333027437
    0xf08090c010c0210020f0f010b0a08010b0f01110313030b15010c080a030e03040503011d1603020904080c0c100504081209100e0607080f04181802060d020903030c07031101 75
    0x4006070450b54000c0000b48141c400d010030310800c510a101c000c0c00d07122000200c3e2040030200020740d001e00250041c1e03d018400d0032500250804e0140282e140c000009400c00d14106400c800444282c01d6982001c607041c0b0041040f2440300d8800151800258025a40f01d452400c000f020100704000160940b070421015040741d5001c580201c044845e014100d0600103a04030903128421300f076014961015601d5441c2034400480300c20420310b01c00b480b000c6582039440d862040621170400007598007001c1e401480c0341c0c0c0083c2c0021415002401d40260b07810071035a040300c2c200006500350b031095080400003500840e0030842071804100c19403201d419482da4505014103480402e08420034800c840d030800c86a002c014010b600c0d0403048840694110740c15aaa641107048410100d9020b4410502030306103034081e030f000c60324140c420f5450192181c4500b5008100c103808200454204100312980140d08000c20016590b00f0402082040d0840300070b0510246507081002803440048441414098600 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 333029919 1250 333028669 333028693
    0x50a0506180115090f0e100b27040b06070c0302100504080606040c0c0803070201091b050303120603011d0f1b030303070815271506041406120103030f0809 68
    0x1090710b4103685442011080300018000104c6a0030402e900095038508214400324202c407208500780d03ca0304518400d600501e0303a4981412031407003208040c01810100400d2805200303107540c2e20301c071500c3d0020000b21301c1d208014000f50305640002c404861071450703e44100214181401d03c02c0140c0d83c42d040a0b41081d203402c0c1186c0d1200760082149104980d1401c103541500d010740b00c03000b80e032500240840d4981ca401d10004e0b00070100031300203441c0844803107002044210101000d805561000d0003945c2080700c0c90f00c85141c0c0c02d07406440c01e039055407912040380040700202c07004910025440c00409141001c00109424030220388145003030100d40300b44404007500c1c000300b00c0307400c415a45021740703180c0da4212058190009013180c465000902a20a40114268484d6281e14880345460080641c49410000c40075440003441681c0001092008211140c440c0300d10718481309024290a00d02880254450440d5201b40c1003140410301c480811030b100c50380300100d194441604001000012a40 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 333031169 1250 333029919 333029959
    0x140117010506040e091e060f0f060f010305090c030105100e130804050d0614070503060108070c02031f09050a0b190e0304090e0321090c030619050709030c09050a0506 73
    0x540510503131440f440c4003045051404100c03483ca85001110081b2184262142464440300b064038024100c0051802003401c100d4242c800600a000042080740c400b507842c00150003406c3e0042c2102400d0182c1c03603904000d43c5003800307914420000343c03500e61180d07410030795200202100a88072120706031030181c907040014a00c4003254103030b03541101d101c11440c1291034010f02602270551030742400100002844051900a0041c5000d418240c81e01c40241d42d074100c08440c00c0040103800781d451b0b0b20100c036169050300c41580401011980c0c00001c9110201600d80e1464011485000c40c1d00c2035403401046441140e40c40c08140902e403c03035042c03000000e451141d42ea280914014540a255190312152908c0c404000701d0b0080101038030740c140b00b50303209000703a40071a004803200324482c041c5410751840c0d8500442e04a03ca4a140540c29141c581c81506010007000004d14070410301242071004400f203802a00b038400107001000000c500c0f40382825968013139440180002e405000c00c1c00c0e4041e200c0c649 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 333032419 1250 333031169 333031177
    0xd0813031808030403030c0b070e09040305090f1203210c07030f05041d040311010c170621010b040c030b0607062412110109030b01150207030606140117010506 70
    0x41c80c100c00d003141c10036003440704050258000c1166100000d03000007090342140c000030b0003500500c46460b076a511404140c07a80300c110a041c65101107000c0001d000a8081c1d80504180340e00600004640e40fa00c01c04950741d000d407032040301c1040c2d101003036801e084003213003182e04001000400c1c004080d051140603200e107805040c1c0300805210310983c6506005100d1810348009210b06204040000130b0280d07078040b480300c2950107070005800c10788800760410301401000030540541e07450800110b0511410060808090300b40359100410494400102d05a154086655100340300006140c1d000f442c10801281c1106070300707006150034080c2041140e5a110b00391000ca0350440d03408103103240180312082c06507003001c0c803417111441200c1d0046401c07118a00002c3c4098850b2000e010071441341801510000f4840c8402009540b8040051203003100c102ea8602c50200d15004075081c40c1d0304c0340d80d250207607074060704400c17402840c40d021090300f5a8005a80e000368050fa08c40c49009504000110f0940d05c1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 333033669 1250 333032419 333032423
    0x100612030807020c09130314130b0702040906050c1801140307032d06030515010e190e0a0311060f011503020c030c030a020d110d0c02040b0420040501020d0813 70
    0x1d25000290818004d0100c1c25004800400315000d40c5007908110124511040c0709500045c2c00c90441d828802940d03049600400d410084007883c035140920005180d408220100d03000340c0c44407400e0340010081c0c01400d005032980c15020351100c01c0095018100c01c0911152410400c09050b0960800680d400300c0c0e411401d14900402c1c103404002582020020000e804060780310762241c000780d00c00682d44000185c921510640340342420348030800c0031541080c019580a01c1c6603401042894046103c0050550000c1c47c020a00d580000c0b0010b04041e4409402d03070118070f44000c200b007003c2c800d100d001d90003600d58006440c1035041c10029030618000c0e03214401407540c001081504c40f4400c106441c00c6075000d5049a50720048104000d484030340c1c0400180103d0324030b8107070549608010505d207000320116036a800c004082c54081001800a0855241d002590741d2103c1403007040c501c19010400031034444269403645880002458640d0443c445410003003914188240543d4003050708046036 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 333034919 1250 333033669 333033677
    0xa0c0807080a09121e020105010b0901030c0216090f1d06160203090307170607020a08030402010c0201210504030e010c0209060f0a180603020406061e39020310061203 73
    0xa030754542100020407141c2e0000e13001c00780500f070f03030001c484c1e201d8030540400e4480d41442c2801345080340706900382c0c1c03000c0c0143c00782910140302c0c000c3d081d4803c0c1c0c03251200440c5881229031341d162280a05281480300e81101c1107103900c4000d00486184207000700c0c0c0b005010102d0224401d1940c1d071900b500d400015003030030300d1031255094100d25a4400c000392540310340000c040d14059560345404900c440d000908107609401600f001480507400400c4101c40e054207c8161441c50781c490340110b46a030801c40c0202c0c188080c0202c0104100c144a1000c110090880000a11401c00e41000361400350030400076130400600c1c901540c010f845540c090b9402400a0701c29030350841030440010840141500000c0c1d01c01e2009145110340700c6150880070441c3c1c0266000c022058a49408890400305005c503404440d5070018104604c1e4851026040c0468441460400c0c0c49015200d0900001c918031107100001d001109d40415450140031030001c6090f0310004010341803500c001000d400d0711000c005010b01c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 333036169 1250 333034919 333034921
    0x5091008190305160201140a0503090705191406040b0c0102030709170d0c0623040b0a02030103080a0c0302010603020319031b05060c0a1101110a022118040b090f06090a0c080708 78
    0x590296181c41076500301c407d40103441e0410fa2000030126081101d01120304e2103529800505c0f410403010036802e001802da40c00903c207040504c5542c28031040501c441d00400108000642408940c014200303480d82000056a03908041200a20045d1140c00034140c0040b00c0e2103030f0100000015400703920aa550420a04044950074901c00401e800280415200c64800560081c442c1c40c203803451140d441000120240d07119050f1001c00c0780800d001c0240840b01c2001a0015640220031800c41507100744001320304581c03030350b0129060440d240314280c14900201c442e01d08054000d944a00900c0c0b88000350a41400c96417a1180d8804001d0440d0141d0f40c000112040c050b44071300c48030781d4861007101c005d01120080468282d641d50021884400500508902128541125600c102240141581c40d400c11046400041720000d010151981c4940d440c0d044142d69100c4040003446600c1c48901c60b1b00500e025028448a10402800501ca0500e015841e0300c9050300507405a400612a1a10356a1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 333037419 1250 333036169 333036173
    0x50111070302040203040b18030a0806090c1e04050a05030309060702040213030b0907061706010f0f0507140c010e0307030b0103060203100512010b011206120602070c0509100819030516 81
    0x1040d0250300065003140c000400c000034014115491400b80120b560704005140c104018252640075441c54039000a003210040f903c01c1c45c140e208141c010b502054000d01c0d1916040c0f4030881d56140304000860500003007410000c41c580142604010075040e0099480c0011000000d01144a4054000d1240b036001c0380c100c80c1c40c112122030b940515405000c2420340e0400340b42c280e50b07038121403151400107000c0d1040b5007580300f0101d1545028a2042e10ba80030500d03101078050b04c90301008a1a1000c000c0180814400b1500a111039000c0030200800351054102c0e2400040500d41c4008510f80a5805860700b080003c10100003541120b400c03420050f281d4407070300030041079407405510141d8404916070450000f500d040d80f0554142c1c00980760b0117004100031a0403c15220180b0440910b4a4420016408124240c000300921441030525406094450000034140f800503680d0460200511005201c0c0100c02c002c60024521204002400c103002c9540c010180d03c2001c400c40da400a40141d8001 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 333038669 1250 333037419 333037423
    0x1407020901030b090c100509100309080910140403060605030d0801150e130c17061f050706020909071106090303010b0403020d0303090501020301230402090d2a06090312030c09050111 80
    0x241c0a100401503901d06d03a03c0385004003190480c2e40040d20410056061084050103440341a005590242e07425040240e80010030840c886c00c0004842031044041260240000180051001d10f120302c900242803400d110500d4600442c003240c4900b03008900c1c0050042c40084c042400310300180d89003980d0800c0144001c1000f61180e4444100740318203181001d4221604801101050580500580703560f54030213003040b5030304201a500340030005810700303050300b1984550001e04c1914024480580703014204000310300701c440c00b1100c080c006284442940d0f007080c0144a5290040e0b0060000c41c2554142105600700780b01d544002132103541104102402c040c06500603498603600303d80210748030b40c0e5603e40030500192020741d4031040ea50b9103200180c24034061003504c0c009100540320000d16a161780c0c5125160780c0041c4084503601c8002c0c4068140300010140d80301901080e515214194070318508050703080c0d40b8a42440c10f040c242110340341081c0d03001c01604103c031002d203050201c140809071058 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 333039919 1250 333038669 333038683
    0x1201031209050d140d020a08041203031b0c0b0705270120010c090609080d0507081204230a0b0402040f0f09060b090f101202120d0e011407020901030b09 67
    0x2a00b02000300240e10a000c13800348000b10700185003054654484029000320b85038000840028030420f03080c0414030041610b2211100d03514420300b00040e8803c4070305401d546013101d242c05000015010022072041081c0c0440310b0303801c001d5600384641480c0480452241601d403182802c0d04c0807072840c0c03100c03005038030440500700c5d0b009800301000804001c0340040c50181010f00525000705071403160000d0003034450701543d812030b11718901a080040c60040200c449038030220341514044400c1c41080e28504c1001c0540d40541e208d140f03203025481d07801da03160050284500c400007558100d0892400481c04d02c0121030352040c0d044400061081074840d13058020040074500c6444c00e80707000090300800c103131540802005142140c1c06500c07039807172610b4221254401c9485100d13400b0000010044403919004404050344010400d50300c10616400c020300e00100b4140400014803280c20380469075802489401008240c0009107151011a4010940c1c0001c18070000740700340d1414001070b140e000144016 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 333041169 1250 333039919 333039929
    0x80c06091f020106051f02030301150905030303090307290412090801060f1e05060403060c020304051302270f0d02030f031b12041a0901020c0a0b1803031201031209 72
    0x60416034840c01d00900070825401a2405034405400049201883e1004001440110f0f4021451a82440c05034041c10b0700201e030b0301d82841082000490b040c1d03400e201035841110250002d5072260914104001041c07210211b07000b01c1d0001c010204500c20120032866401a00100d10202c11034411004448004459005940300d510348103001ca0541244626001210803286040d07180110a0b0551403a1600a1007107690041041004100207155070b0840200a003541c01aa0306140d80c0e20f012482243e40000115003440e0b000801011010314401e42c50101001c10300ba0701805015000441c0c01001020324070740c49090804900011943c1c10001ca0300020a00c1007a01d032181c4400030a0481303840114090b01d220700079250b0940c8010705c4203090303e0840d00602c000300700c8030f06203074940c000b541e0080301880d0440c015010100c08585425240c80001e103036035425030f943e6265803480900b900541000c0321780b1030303007040280201e841404481c1074107694001d41c603144414600785040d5002d2074280c1c41 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 333042419 1250 333041169 333041209
    0x5180405131506051203210a02120a02040501030c0f0822080412032c131b0e0f01050f0405041806050a0c030c110d11010f020d1a0109080c0609 63
    0x858032000c6942268007160416681c12025400c40021103440c1d01404030195400f8401800191f40005100225600700181e010f0051910030507043d62088102d046501d00c00c5981c00140030812540e2501c07031102c64010500c0c00c00f03002c0300000e070000c0c900d072009030210012400e040f40c01010a01c03204480030315203620007017a42d41e0303550b1950343d64041307002c0d03034010341c0481c1d20f8860204820020008400d03040c1042c0d4a010b0080c42d002e000c04c40c22000306034075200c600343d03196526400c44010300c00201c2820442e46411a05180540400001e40102500c06041103c2402450301c000c92010584d41950300c11100490b0045500b105c5a0a54558400c080c0c800c904100c01d100c0341c50010340c8112098481136400340888480c138001a1592074074454502c80740c0e0701617401c11a01602c203c01c59504020b4403400483e4601d441484002a0f80004071420152680d56600741c000d040162103025810b03400303090001081c0c0c41d20b41c61984400c0800c0c00d2602a0200140c400b001c1c0d512850008080030203019 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 333043669 1250 333042419 333042443
    0xc090510120501060e101503050c040302031509010507030c080a0e0f0d030203060405150d1104150e010e090a030210051b0f070b091b01030b060702030307031e0518040513 75
    0xb07009018100038400d005c0c20203500b03c04a0520b20242c420001500c03054800b88200d501c461034224001c05005010001e54142404084010703030701882500924142d03040001c041d4145441d103242142d030b0182108040c0352415040c01e105540210340e031a8816440040020914210010182041c0d20f021515000f4042c48410502e02030309507001c1c6000300e509030f4003040242d40d008000c169912080342c1a552142c0c035000c81e4000500d8440300010240030241c8085000055201c01010104d801e80041e400300f1070450041c0070b03d00045d241294030140c030310020500d21070591030103511200381c805925003054490000680e030340d0028148541180e04c000e0900e569070121174141890740c2040d01d089031949403040107d00e100d9800900c090711046400d5400300e090b03d02c480150000c01c01c40c81d066400070414003003070000d40c0e4244007501d505030090702c607d440c4002c0c0100038be0501203452501003e01c0403c3c494483d1004040054659603481521b000030203850b0036000701d03070480e40018010400c0307811027 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 333044919 1250 333043669 333043673
    0x14030601020d08090f0f0f070f1a03040c03050f0f0f0d05030f04110a03030906020607032d0908030c030105011407080712050c0d020f070f030b0402042c0a0b010603090c09051012 78
    0x7c40c415500007800030b40f94680e0301c801000001e041544541c4041040c103545036000c0108881c010340d04a8414084031074010b580b41d0ba8641408079200026610744c01c140c0c0d401000400510400000e00d400c03c0241c4805d041c01c22002d819800060203000ea07115004002404100107070b01c080741d504000400e40e141c856a00d2800034a90310060085c40c00600800e008110880d010703008020495862540c1c00545c0c41c460321f15100c8042101100c030401944483c020b0003c0741e2650300541c081d5400303c0300659290b05000c005040b101403400000000e1104001480c0454200800e0714200356201a04900040c0b21a1040300d090044400d170101074021035901c8058240c000130028400003914040d01c1d041d9070b803145c0e90041da031074503c409000b070800071001a0041c40d080e0701400807400071080314024402c0900c0c460404060790311107218558407600d040701c0ae002090341000d00400d464542801002c2081e0740b11004841035100d1200e0b07464403580455a420700600708200a0400c065840070b4440c828 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 333046169 1250 333044919 333044923
    0x3121103061f0e060a210218030304031a0a0617010e0705040905030726040807032d020d0804120506150f010c030503070509150a14030601020d08090f0f 67
    0x40e1203a910608480120140004040949120800c102d07250f00d500078610500788801035006519030001c1001011148000b8003240b0f00400880400d568010780f110a007003200314100388007a4049219900034401080000c80d62030340c10140224615440e8410b80341c0c410624050031050f004811130401002d1850030142055014800c07280202086415081e51401070100315072007000d000c1c001350403c004400201c0c4901111210b402121558502019400351030540d940d08160440080e64100b41001c106103c1c60108403030700d101c86000750310701004401c40a407803800c800c440c00900910700103550790144000c000c140c40c0100300c4c2d50003c0074807140c00c0c5496034850304103c807401c40302c1030344400490050900d090603004c4288103840d1a003004445841c15901ca800041ca0202000010003a5640c66100c40782030610181d0716001c0b09407601c860703450141500504d0301d0384964610062081022036a40003442d40c40601c49410040e505888182c040c40c14088108201c030b090780f0815083d000700d5500 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 333047419 1250 333046169 333046171
    0x50105091b0f042c031809010513090201030e060a0603140a0f03050f09030703080a030507030509031602010201110c0d110307030807080c0702120102130f030b04080703121103 77
    0x100d00c09961910841d41c1c045444035440300141c58228440d100082000e0509502c00c0d1030614204100b00550041d85002240c5840000070b202600d80011400c45100e005a0004100e00d04044a9a0f140307503050102040030b0020084407400c006868021080959010b070340300c41c94100108017074801500e840540c540203010076110466205000c1603a03a11507040115204000742d512501120100d89503440840310368101303400700f181340402007100740030b15502008050015403003040b0030391311500b54400103011283c00603e440145414802040401d44001c02142c7c0712030503401c85481060b0090004074010014022811240710700003a02401c9020300056001c040300c803035038803000b950f03c405c041140c403400780d004010040385c8698040707000f180c010383c062513210f8082544142001d0050700066010300e68411407802a235400582c100085007611010380141034801e0626294610b107545410071108000e00145c00d042000c5076010806208811003803040c610110140070105c0144188102070348 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 333048669 1250 333047419 333047431
    0x50301050a06032003041407151403100b030a090c03080405032e1112151207060816050903030304050c01030b01030507080601180b040801050a1107020604170102070b04050105 77
    0x141d02680060754610038043d400140c0904084150b03980303070b0f460007070120f500090007c640f400640032008000340d8040003035200820050341307445200900d518010b0503480e0420800745012404204004a42d40e21407910011220540764095503552240d2100009003101f480c003d0a0000b015000020300c92504058810382d00101d060b00c551503240403000015800c01c8000200b80900300190300b40b030720f03100d60254460741e60020103246420308214144410040032904520100301140300c0a00710300740494658100084140284013250402001412000f401041c01200e4628071038181c2c0003504c140103440413a400541220340704c0c2450700d4240c1e01c2d207035007080103030000340f80413100c2d22258400e0041c2c0d0300400d61900c441043c1e440c0c40c0700440380325584400500a0340d200141c001100031094000700000c1020b500009418103180d5036400681d91200081c0c2e0351301c8024040f6001580c0d0358002c03030701103d40d0300c0300142c0c04078240e9411b280a4000d00324082c090840b0103080000740941074000500c142 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 333049919 1250 333048669 333048679
    0x150a0b040e01150801022803060902070609140304060921060c0807030b010804020a0b03130b2406040b0405060307030e12071b080705060a030e0d020304180b0105091c05070605030105 80
    0x5902c0b80c00c0a03080f03003d40e0031403d01c0c0148602819800051102000d807c2e1072440c50080380490300d44103040b007644c0c4844422124150740703801d84010f001c0c8501008145441140183d40ba007450f001c001006401030340114040e80740940c0302c42400c09402021018440c0e031150b000d10189000c10b00280036440121001c500dc0b904000c07044ea0590300c82c40f00280b1441d802040c0c1d031881414400500303080e800080544a145402900510105951044291090241290074880500c8955188207103040e148100350290505100c184095182807013a64250b41c0155030300c0b5240c1d91040d4044001d40b0004200d40c3d96801466084e03068044c0ca03000038074034980154102903141d804e1807000704424a072481501e10070b40000b413041c04145031520081040034410306c0d0200c1c103074402e191b1180c00d102c002d41400c40540d100060030031210000c0c5810300e1860007010401c2010380181000030341948282c074105c61080c540e03031090b0f180000581e00d0810007650008212404c4540f00e540140640e071082c006d591241d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 333051169 1250 333049919 333049961
    0x10903140a150507090317120c0406020d0c050d081e0c1e0903100b0607080d090b0c03100302090a14070306080f120702190b0f030a060611150a0b040e01 67
    0x3110b40d601401d4064006a950001120300d1a241d0707041d4807c13011004c140a890401040071581e5000724158082c58140c02c900d6503d80c80c0c180c000c0c1c9030540621000c414004291003400110300041040b0390000c0303044c20038007556503510b8515441d00d28450340c4094840e510310b09000d40c40492074041c204182c17040782c1c60b4000d00d100d00e0a07581e00d8010303210300c0d59240e800210b111148001039000007012002c043c20682c14000b0580c0c80d11071607003100e030303144108690300c640d148148030307071000d10913003050541c01841c1c42c50601c480c002070030781c0240c00061300030960788004c20b91100082e407008000c4440220a1480e5040001d030080c0542218880c600780d07441500b4840e201c0c000041600d4503d03a0454103442e10786101d5500307229025600001100c10412030000000f00b26440000800d520b80f002003085669103031201e4050103c900c6034001304100701071319250310f086401c0020307841c004021142900c00c0d03950340c0d4200c12018104019440e44c1050910001c4501040150090000d803c2c28040918134 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 333052419 1250 333051169 333051203
    0x4051012061215150807030303050a05070c0503040e06030a0204020a0206190c0509150c010e0a210e131514040501080316021003180c03140c1e010903140a 68
    0x2408810005003164114010a40810301260302101e0f80b2001d100120141c2945c03180752604240c200d038019008a501c0b1001c1201d005442d1081c668040401e06254000c10300980f9a20398030300980c006d5800c4000a86d010401e103940401a9108d900d5004206542d14005d0a030001e407104016030307088050956102d44455a041c050140c44401182941c417141409000c4082042c903482d02d800f50380700c200040009441c00070085c09004104a1414014a809001c034a001a04240c0845440900440b42d00f07001c400181e114052185001c8220f41074250810a03a000500501146100410007806402c000070350303058240390716800150840e4100426070303072074400c01c0d102d02c540c00d002c4038076000511612006282007019001c500c0f445140006207014401050090034502d000d00342d500b80d6002c8000c1040048c03008034100030f228414040c0180400c40b42c0411118107900c40f200c0000148945080781591049104000a603013142640b19145001d807189504c130000000180c55101d00c40901050b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 333053669 1250 333052419 333052439
    0x90b030a050c011b080301300f0314090d120e0916080c07060c0801181e0f0b061603090f031106031e1609050103090809040f020405101206 61
    0xa405811201402c001d0b112807004603140c1d0402d160601d41400301c009581c0200d44142c0196000c1c1c01e000e1084518114101849440e010a108201c080f50011100c0c0c03800180c0c91851040001350315080c07c0c40c803030300220090700c1a4001c046195800004c0f1505803c280900710103a08280d00460300c40e035501090b20390600000290071580c036088039050f8522143c002d803081500035400940610320a042c08825600d100580d102d4060303460016200d000103120908481e051554480c410001c100280b950050740c071000944406008002c20b0341c0d413008036450f81c041e40c001204280c4c0050115a4810154105050300030314807005030002000040c0100b10a0240420001580d4000b10f480d80070307440f407000b0064194001401413403000c0300030840c084030110041c01d56000d15050001c4004400352280d0080c00304107a68081410181840c0180020582e0b10003110300c907040681c1c011a01e0405288050040d05c5103a2040d070b04200030200c4c2c00015644000301c82240460504180004d66032220b8960b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 333054919 1250 333053669 333053683
    0x13030c050f0604030f0501110d140f010608060d081e04030b090c06120703060e070f030c140a050906090a12050d02060f0a020337051303050a0f0216090204090b03 71
    0x2d0304220100010701c0030400d1040b0b08000c03684114004103c000200d00d071580c4541103070218603852601c1d01105244441100006503010407030000e088425803518030700402c41400981503601601c43c50440c1402e0100c5c0300c3c00c99007200025400c5196584102d03d1400d11503001c2e120984078020070002240d8007020102e20324802046c0284034505042e80d00d0803c10005c6001b600d80c505240d590400003490103000704185200e0b4441c0d494501c202c075044103010307081d1400c5251400810010400c204084c04581054515006003442c1a948558400f130205860703226410f425640800d8011000030040780700c00150484a00c40c80030703115004000032003660756101c1640c4120354170800d14002041e008481c0d002c0c40c1c0c040c80c41c24002c2c2070b0001c130014408038601244400302c81a800c41c280c01c40c0c2101c0b180205500a0210b00d915407005005071402402c0b4042c106034841080840090346640c540708200149031030700c3c400d40001482d03541d8500180258814410b840c0d05500348240d40070f040ca4081456 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 333056169 1250 333054919 333054949
    0x602101503230a0303050613090203060c0c030f040e060a080d09120f1205090307140a0b0a0908010203011212030c080105360609060d150c03060302030313030c05 71
    0x2035803481e08603a030707554010b0900036111000302d8440401258544040080a00541c002d45002805082243c284040c0b02d815081c8018078905003521213005171400a00c156020b88010506070b280e801100002d8254451280b220132801000b04012460044000055004986c11034110101d01e03551000d0648039414a0540030104107080c008100303641c46055401a260320030f0342c80c950004440d582d0600c14840361200840010004941c903055802c0400501000c1c00340d81c0c08038406940c0300b800003808640c5034002c0c005800d0010401c83c0b15140280140f04c05440e440000b59100c2d078449085170000c00c4480c00070307154107480080c0f02880134060300ca90b020088072079903100c489a0a180c10b000c0240c180c450f40c80401d80c000d070380355074003415020b200d1031407560b5819402c100e500b03040f020442c0c00d03200580620300c65002d0702064000218540100c00c20086c00b40030200b5100e01600c070580080c40c082e44043d405020014801c011845141c0d01039046e00e210301c0900404039100d030280b002c190905507030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 333057419 1250 333056169 333056201
    0x60f16080c0a1805040f090c05030a020a0902090609090c0d11040510230714010f0c05032e061710061403100302040213060e1c02100c1209060210 64
    0x19541445200d90f10001c414000c07105034441c0d8990ba0b0f008902203450b19110300800c030303565451040800001111761401400201e00031b0085015070380005040d0107031380c030030a4040703a4001041c4010343c480000b0713605410402014103080703180000d102c8a442c2d1100c18000270540c60170341d002d0500040c2005960a50780d0103000d85500031411a0300340c03114010400f213851298550030700c0a018841030300050034a0307032040e144040c881c0d0026400500795107440e005085840d05041c040e04800d680b0900f46d991240c091070101c0c16030f000c10191220601d040252101841c82002c0020410307940018400c409040580301c4031890b99246000c4038240c20450003400f0003c0c140d02201c41140180d0000b548c0c01070302e480003103448507030f0725030000d0b080340d1203251518501100484100132464204400140440c1d060b100c1c207039803100c404034000300a40803000080c440d072001010b0a4025200d001c450021541c0020314030034142030940003400c400c070a4450040148244e440e031246802140c05030141081404030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 333058669 1250 333057419 333057427
    0x81c080f06030f01060b070c0905040302030304080706060503100207031106040209060d050c030f0f21030f07051b0f01060b120c0306010203131409180706030f020903060f16080c 78
    0x1080314030364034000d031440782d0510807180c054952000c00c0c0304002c0100020070740304e90345507030b90701e0710551203205540310302100e13172400d000c003c0400d0300403040740d80c02a07000e00e00c0c59544a66181000c0100001e0f00440d40500c03074032040e82d02d200025402410305c0c0b4002c2c2c0714070b040d103280c503000640c0c4c41c40110780080d08144140b0104403242051012806503512071825030383c1c0b090460020070b14000c3c01e0090258241e106000040b204c120900070510504416119001c440d0880c113024121440041e144150504078440003c03031140c402c07025a000b04c1203c060341155054460401640c417620000c0d0301005510f0305000050308200002111f500c101884841407080d40c1d101e900050b5038000070b0410b819804204182302d840d0701030b80e00500c0a801350121600c10019100c06102c541c0c0c0c0d004000c00f075401560f0a0701c1c0050400000c41004407845450041109018111050041c1c010602c4054044c802e031000d0016080c0111144d510400c00122908181c1c11400401c595200096a4044103204104 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 333059919 1250 333058669 333058681
    0x203120c01020d0905241317070803040b010302090c04180906090b040506100603020a021506010e0a0e04050d0e0603130201140c010203061201021801030515060310081c08 75
    0x24040d00d40304000c44001401c151090032203905543c4003500403206038000039500256001d1040801c9941c01c5600036450084c6050306001291420140703002e0130708a490300341e580c02e02807440102c4650342c0d13202c280c0c0354803428030b403030301861160082c00100d10640009001072981140002030718101c4001d0801111183c05c144100c4005001c44201550700c103840301040d1010824140c00140964071882c014002860100803008048800c2c0d00502c0c105801000700000300d41c1c0c006a100c40260007035401191949540c001610740707144c500d4509070000800a00001d8000f4ac0f000860702c103034020400d6943c0803008010864840040f12103040d40302d40b040c4045003001c20790320b58030b00e44903206040c001c0c507003d59104540d0b807a4024202100080e07400004102150420f5040500302d104010000e508003004c4034104400c41d1043c2d20302a041658400c0020b601c2c4c06c2403000d10502043c0a0b0015641c0d05004007204c603008400d000385101c0c0d10542021a04400c441da80d1400704806590344c40b40241c42e52 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 333061169 1250 333059919 333059953
    0xc0d060510080118060e06070f0305090f0609010c1803030801030b090a0501110304060b2e02160308030108070b0315040207152c06221b0b030709120203 67
    0xd4038440c003050740d0040226039010240728650040001d40c0e907001c0340b42a28940b08007034030a11454101290440024025800e8114040d00000105400c020034560341c3c0d48015450920002140350452050728140a18900d0651008030480360f40c3e6507545d950694503a00944462807444014006a080710040001c2400b041041c0d41024041c3c068428120861300c40c2401c0d50f0420503012400e240001c24442044064480c1000c1d00200791840c450070420501001024811050580460411824420ba8044c0b00b4801c0c840b5540118a00342026600d0f8209100290024003071040307548070340c1401045c00030035035003070782d01c170304081480842c103d20700806000281d0005c0300100c80071a900041c60301007a40034015022115800386414580d80360304880c80240381c805002042090308050180504400c00e003d516000f07074021140c48d52902414903108480951451145075041180344010036040307902001180607100d580d540c3c607840350302d408904800403811b8000941c181e100c00308003034090441d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 333062419 1250 333061169 333061171
    0x30c0309060708120118180b0705030901110d050703050105120a0312020f120403090504230c0f070614060423100f0305070e0903031b090a0f060305041101020c0d0605 73
    0x10070f03600c0341d052010400c1406403054080c1c0250b00708150001c0030701401c4c1c1461080c01c05072200b0550140d0003038001c4d106e400c00342e04041c084004025002000030a0342c07070250005101d0b0b80b01103215580d18000040c0c00c800903c019284100040c6c24807000044601c0c1000b140384481ca4404082c2c424001d1598042d10b0b4400c4041c1d01d00003a40d020312280c0030401802019010b401040d054403130b024586072a005041120540009120b289400201850f0068051010000c0121440030f40700607140c1d5421540140190001c40e41d030343e01d001030341360204003040e04005240000b0941780070158a80d0010481580c101d0f40c2180c905c8400d07030603541c3c0c615900d505c0c400d030072509030000400f4503600c441501003074002c290001c2d00d83d50b020003c01c010705a10a54030a6101000340d01450950810607064000e00c0f180848110703084102241203e030543d6001d0707860004010f40919580c566036520340c0036028200c12902555010104c0b0000811540040f80a1400c00c100604245080001d59141401804 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 333063669 1250 333062419 333062423
    0x602030c190302031c0b0a090c0f02010c051e070609050307050610030b0a1505030f15010f030b0c0d020906130611060106020606060c100c0e090a060f051309020a2402030c03090607 79
    0x1b4550030010320039150480d190029010021700410302e10200398001e41001000e2410200b160315007030140f01c00e651300000f61400c00190b00f01034007000601d400759004034052079070017074800752a00704040b08000000001780016032242c030075941345a0301e900482003415414480540010002d1000039036100d0554820071075030342000e280d103914a0b12500440d24050f8416121105940461030322903a40300710210300f5005065880d44100b01c0f904550314015803541c041c1500111190100d4619103030026034050340c1e02094050701868603840303940440040f4840600c21180420340800c5070b46140f50000c200302d0b05031071064000341026102c902c00e211459210001e00d407441e010302005840310002e03e006600e4030400079950a03c0d2060182d041101c100006003460700300034942001040b904440c1c5401c041228412100c100b0340310a0100c070007000d0010004000d40c070126904020440e51001410484865403034089a05003040940090380c3d2480f56004c3c00110758014001c04e1824600117000340f81d064 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 333064919 1250 333063669 333063671
    0xb04051f0911161e0c06030f05040c0506070302030403081603090803030601021b0f030304090507030510030b0f0403050c06040309080606030a0b011401140412030e0a1401110c0a0602030c190302031c 87
    0x1100c121805048501003640c105c400525880003001515454000c3c5001080c41480c101300c00c1c02c2c107541e59081504607115590040c40c001c00c000c4103042c020303c00d542c02960040b1805568240011600160740c59023030080340894241d10000c80e22400c0002604e10419068005007a010300720b0b25039910314ac00c102c1d9415480582d1288114072914103101900040079042008111802e10800240940e0390007440f01c0c0410440340d0003080410390744041c00381c001904c1f4174080076607111418129000d20409003040c01600c1260306120400d540076924100312075082040c1ca4841d1161010162524a098405000d40544400600846610303014492000105040540284442a21a88060300983c2c4507142ea01c40d414880c0c03052640005080300e0365901182c6160700c60b42000401c811020142141a04200342c10340344113070180003007103050341c0d006d0018080c03c096a23460380300941c1c3e5409104869046e025007001c0c4c944070301c00761410410b0300341d054010350304040c120300c1c417040c505401c02c000f48101d0b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 333066169 1250 333064919 333064943
    0xf0402090a0209061209150601050d0c030906020a1701050103110a08130b0103231c05090d051621020102031204060f1112071e050d0b04051f091116 65
    0xa99100c00003000084401741c0603000c149401400681050101d900e8010820310000400c0160703a0700000311024854280c100240349a0b02c5441100142440c800003000d291000460610964200880100c1d01465031440ca82d41d0703813148011003d4800102008404003400d200081a1074080c0c00140ea00c12854044100300c046103448562801000703a00540341c0881d4102c0049001144012031441100660010300c8a24906081040080650400384007002008110340c900c40d990100c40a02c11a000f4080b034000c41144140c0480d07a9800d0711454400e00596000d0b809000741c440241e41403a50140c004e10b04140d500c46683c00d54240040089a405944280f0154410620712503c40c02210040b01140c031541d20000316a803130207003d0009010b01c02100c0201044200825502890314460300d060b0351682180034031100074140280c0c80941c002e0a11040010f500350003410303943c2200700004001d95003540c03032240b0f40845090103441e030380074003080054254091a001040c0c4d403442c0319403403500308 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 333067419 1250 333066169 333066187
    0x501030e0a1e030f210902030a140105150a12120c2906030c0a1703070b09010e070609030302030a03180b2811190201063b0f0402090a02 60
    0x89101c0b4142680180d212030741c2c40d0306150313002c01c00b824411064205903400c8104034400e03080c001700b500e6424101a40300c021002c1103450900260455230390001085c0d40014001070558081c0008035040d8005448280803d0750394600030a0100803102e0000c0c1000c80c1d4805500c07403115101c00300c1e4900e000d100014003298000340c212400c800e50803541000060989502e041c0f00c503016a000350155100c0d5110020304415603462981b101c0c200e40b16286181c0c1c0e05a80131301c0e058218043c07404090290030010040080c010410740200700c040e048101034a0311262108400d480e8514036003c0900107a00038490041142c1c0241c1c44048490803006030002038244540c1c2e00d50804d40220384480c81700d0641e04107680d80014000b17541d04600f03c2d80000380001c0808680c400380710f01500d54080840c8080706903005180d030003940080040c01c041a102c00005500701052071341900301c41800c004000d00c0450a0b0704003500104414003824940f44000d02d6502c42d030b001c0011540004c0d0a8000380c0d41e00b0031020342 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 333068669 1250 333067419 333067433
    0x1801090f03050a1701051c060e0f061501021507050906040504050403031d0c0102030d0203060a170303010f0b03060a03111302030a0605030c0d020f09070306180509011d070501030e0a 80
    0x3900500c80d03526959034440c1540c004040046402c5030000a02d41140140159655641c10101c0701202c052045125605410a200a0f0510ba00c004045005001810341d841d030000c900a84103103103403406044144581801241d0390403410240b80e50501c00381c0081032040b48204010404040001c00c01c904107500d81002404444003950110302203980d80d440041844001b140324000c0e440c10f07402034461041e001300081c0d142d200f020044200c0c5035000000448c11396440c1e08640260840b481c01c811700702010800b1a550b0f80c401e00443c40c20106040000500c1030114080300e02c141c1c0064000e01000d440c1d550340c481e42a02003046d19600c180302c00801e0354900054800b440c42031080d80808035040313151005040c10014142e011a010360300404100016807030304036844a040009484001e42a034881008400130841038004004095450032501400c18036500100e001d078407080020044003800210025031008055a004016040900c003006150b000e9441401a00c500c8026224a0586a61418 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 333069919 1250 333068669 333068693
    0x201081f060e01030c0906021b1c05030913020301270f050709170705090f040c0f0b1209150a0c030e120d060605030f0613060302030f0a02030d17180109 67
    0x78005518010040d01c07541c0d060107000c81c400c107141880c1c09486e01700712009441e140c000d407406510440f20303001507440e501d50441000380354580a1190300403501303610f03080751280d000b0006030f4031850b4140651004c1207424404c903412100024281071f078940a40c101d41c03400e00d4406411142c4640e640044072404004c50040601c030780c82c030b80e40d150300c2c003030074198181207210303610144040d6940496424003164480c0b8036040c2c0c2100151002c040203030307594078105040e0005904241d07240b0f81d00705000076106000360043e14464045203055280c5650f1104441d0350340000c00700c50300c40b001100d408280c14510591101202c055145008104610020b84491812180c03185a00a403800040c082516441a00c94440900202c0c030789180355090080c0c0003400407030080c02052081d4400c148051081034198806401194040c007500c5e2650f005100c1603031100c01d818400c2e8040d015030f50040c05070f1440f901c0f0b10741d10180c002c0003003055921140903a07111400c000b49103130440d66994800d030002ca54001868 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 333071169 1250 333069919 333069929
    0x90411040911010207080d0909020f0408190218040b070c0503040f0f0504050703020a050703030b01120c08060f01110307060905190b100609030c05061e03010801020a02071401020a0201081f 83
    0x30042d1005407400081c9401703510b90007950f00e41c100081c0300c059190702038512000c4030b0340400050786401540da880501c0744500c0e40005181d02c620102554650500e84d207255a0302d0003261650340078010fa00190002c18000c40e401070900401100094005006040b82d80f00d041c001c0003140e04150300c4022542c05c0b20090b4105031003542c0c0e200000c100c146428000c00c0d5001b14549025400c240c8061800341050013040340050500d40c07500202c40184c1d10900c0b9561200c13070100010b12442201c44805081c0aa068a506000341d1404640309600d501840303240f5240c0703c440300114940304c0207031501c0008104904c0101d4250240c01c0c0f104000d6804052610304460254a00b081d4a05210070801ca00004540c8030300184070511a007040880c1c0340700c0c0500c0c1201c4040e50034550f00d50030340c00b00307480c02c00e1503000031100c0c0b40d4003100214040905502174894140ca540866162549034000121000800c0502d0303401a4000e000003c0154403800c551504040c810101440c00381e0090100d0605c02c50503000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 333072419 1250 333071169 333071183
    0x1902101e09081902090103020105030405120414040c17070c0f02130e060915040312020903010f0c0e1e061e070f03090b090d03110a06091a0606040b090904110409 71
    0x240078084062042ca1220511403581030f40303002c040e5010501c200e10500c0041d06020b408400202070040038411900d0582c079160b2807998698403010850030150541003114021031a021400904078099102909a007107902c854103803e07920200d04a658041c0d00c40c0460345030003440555030058070364200d0900e06500842001c104040000036643c5044401070a000c41607008256045051501801464210340c140c50428094582c8100210281c8122010b40d40c066191404504c440b140681c40b8004040240c5d81700f4840c10032400811000d41c08450444d250208810201035203450080d0051162100f40c000c407052111250840170003541280d54140d03900341d1080e031644100741d03003c89008080c245100d800d5041c64074107000b05850051556004051040c1100d00740c00c03040c8100068124994040400d00000ea09071a0049070000d20760014044d00a0000c045421894124260350030781d40400f000c81e05181c00d41c010003640c804060000d0342c5080280c420291035403514080c2914040c09650 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 333073669 1250 333072419 333072437
    0x307090e0601090e070b07030f0306080a0506191a0f01090e07032705030a030c090506040f1508160c02040609090813090e0c0d02130204261902101e 65
    0x3c8050a0350070104013807100c0d81008909001c0c2049080640d410240c2500d0600c00b45613484c03909500800958100c65042d1244a03815002c0140008a9034407031004c3c1507080e07100096002c0c131082500c1c54170407000c0c05414031030070985003418503510140d0051014904110480ea6030740e8649122101036442d0700000b500c40c0040c3c1e542000d5428414248400300d10741030000c0005454a985030301580c02580101900c7e036611280441c41000f0020290174014481035076540d880411003911340d1103120311100c4203851710f440d074401401104407600c240c5001e00c0e01c45840c030664804440040201d4800c99101d40d969901141e8044284220040780c0d120755121542ea260441d03444c051504942e1208103c2401e117070740c03030304000f102060710b01d14803405507002441c2211920000c0c0444034401b54240b240340c40410000ba8181440e442500000304440c0c414142c141d07030714549a29082100c43c100e110031401c4021070010705041ca080c2c1410850b5180031000d015650b4003040c0c0c045070b584008000151090303 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 333074919 1250 333073669 333073679
    0x1050412110315011707151704021f0f030f052505120c07060b040b061c06050603070305060a06090803030c0912010e070f090e0604020103090305120f270c0f0307090e0601 75
    0x3e40c41c060147c9050925880d41d00030f400600d244043d02a9200741007213980420300311f443d02042801075400703100c2840c021031840e9000403c05420105000002410070340c050150908610886000307040483c0c10300d145184014800880c80035035240c150801104021200403d4060b612150244040030081a5909414140001603505816141c3d10841c03510b0380401d050354800e400ca802c008800c01b10110704050311072503140203003155809960400000030030089181d526612882c414817046410401c810303102c2d10101ca0300429405181c0e190391080001c107000c6110440a0030549030300421070120107003090144c6003511004000c461290b4401882030140240010041001d4400160100040c1581c1d4034103a56859014001905241e0745802900c2498880e034200c8060f10b26081801c0d81508051804000c0c01c142194841c0388042003001d290011002c401c0360044c220942d80c000e0000c0c2c200c0c6400c206500854005250741403184900016104a1501a40d1554682c150150100d58981 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 333076169 1250 333074919 333074923
    0xc06070504061106161d031905070803180d060b030a06140a0e0a0611071a01060915050307080c0d090b0f0106050702010203040b13170a03020c010504121103150117 72
    0x40100062580202c820042001440950341c5d0b0740c0000c615041c0841c0c2c502812100030358103110780041d014001e806400d200100b02448081d4100d204104581c2e4040d6030f1060b80b40c9a0007803c80340d1808915038078403100185811954015068001e1400203501d0381c699001030f1825402200854135a602d50700c1002c06407071150020740d4882c511000c02c0c849850b02841ca03a03103030615540002c20143c1d0780e0080001c0c201e400360a0300ca00941c408805140a1820300e030014610b1024462040002e441103400f081c3e511142d81c0d000102440b944403c2d00f0350300e5905041c2d0311640014281200200f01b40017003005481d0340e000f5110040d00a14490700135080c6143d80d0b090003201600002c0030302104000f00c40050760300004603002c41d00041c0c00300d41c0702d190340000484a141e40d5809078400700d02e240c10030b00c103a40e80820210600752007070f000c0305e040520901c01540e090040344513011f00350104040c184040b481c051141240c42e90024291030340d03440071034041600802c3c04c0e00410820303411a8a600100041 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 333077419 1250 333076169 333076187
    0x1e180e010603290d080706111b2a060304020420090f0603010641030702010b01230a020f06040c080f0f0c060d020705070905060a090612170c0607050406 67
    0x41c1d1280c8100706045100811520024244c0090543c403000924130103000c141c0e0b004c0e0000c1d00700f00c0c107850303501c40c0c0000250308003824403002648036001d9140643ea81110032848550001e504141c03451100c0e186804015181d04010310a03a0416210000d284c0d00710181c88607d0701404086806a8840c00200244103104940b50301140c010001000140305890b0402d2110b4980c2494000d044a1124502c90212001480003c220400d51010701c0d020341108911020b10700c00d030101d0b4020000c0c588010011600380401c00d200744a5020151201e004070b50400d0300411414010380101c0b14284400c020b6203240450445050324184010300c800e026114060000403500540100148001c0026818103510303490a01d000e01d00c10040010200385030b08181d011780c0c05103508032090324495555800b0800140c0411607445100c1c0d5001103020135038920510409054500c44442d00d280e80c102990f555010707410003190340718447d80c14802031814810800025101b201c80e503861070380300c0749051000b50110311 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 333078669 1250 333077419 333077471
    0x1060f090c0c021c02030a0f05010c03141510090b07050309042301050d1401050a05012405251b0501081602060f0a0e120c07061e180e010603 62
    0x2c00300b8840560f50ba42c564140c6184491103040d422000c0e0302c0080d14220038008020b20b200502e4070040103202d410351100e1800d00c0c180d01c00b44220201c404440e82c201404803160040f501030700b8444006420219101c884020701303070421048060f1030b40c016040c1c54010740021a807503400012848010f00f0207020741c02081040442644c054a00071501d9114131405010706400b81010072180310520082c140101107001c0100000c000c0c50910b0420000030300f00901594004403c54084910780d0a003400c2548040314460b61001d00309420031001c1100100d40007107a030500b55100d641100415042600381148035107900c08510b90602c2c4c00000b4208603001004014440c80b2411240031040d004505940e120041d03416410a036903c511a410003024400900d80e0b041c4101c201c20a5070600a00003084403200d1903089502503540c0d90812117100d000c4041c01c10821000aa10500042c003400003070204041000c40006126121071080010890136845800029210001d25001a500440203e01c2d06 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 333079919 1250 333078669 333078677
    0x1303060902040b030309010503130804170d021b06120a0f1407021603020607030c0f050303011d010503072601090f030c1118070e030120070b011e230301060f090c 71
    0x1b42d02000082e1140c04010f04a44c1c202c0d50580c128001c00240130103c078040d016000405541c0030540c1d064036070b00e02c00100c40c400503210302014000c4411301d48501080e42d84005002d01d207440c0700c042c03540131140006007a580010b5101d0380009508842401a03694040c2c0c08142883d036450003080c020f14001d1044418540c0c0e0620420900258440d0412540310503014103080c0900100303440c06081810200390041d051740004800401c95600084007001d112a40a40401059172204101900c48070355110707645001540c40003c0c0340c00340c4500c186806124030000005070307500151700da076540c104c61450103d0005600348402000c0140004802100b0802601e0075840944070b24600102d00201800502c2030100c90181c8600c1030350250041404804500680000c00018044141e00b54006603402c5a009045000114050070f9807210ba900c071004011940b4107091421140e001410a014a426082d001c00e10405216403803d015000090500081510640e450a04c18108031414031994800300 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 333081169 1250 333079919 333079927
    0x170703170108030d0203060310050a1a061201031412190f050915031807030b040203190c03080306060d0222050a03020f1309170705100b09070807051303060902040b0303 74
    0x1c00002d880c102130f0540300c01a9a03031141e40010785032454031101c9d0302c0700324104030030000c0185c840e800c42084071000d104c003204200403507000c00401e0f0145619608403a400700b401040405c0c0c0c03501c5640070040801003a104510203824922210390f002e00c603100b110b0b99028910180c0264018218201600380f231070404c0c00d041c50300d0001130f80140e120310b405224041c04400301344041c0c441407078041d414840d44102e5808560321701d0606040f00e800c58059101e4012645604130750311400e440481c0c0650b00000c01e500060442e03441d991107420280c4004d401c4281803160411407170440c4000e00e200550f80c00709421070320100207100451490b0b0b4108078018401640d0410043e100d900403000569030446485141060001c9000020043c17010098203060b80340042038000c01c0014010321584c0d00171815240300c4410031802d00d040e9070801d440d00e5089240940024050340c4aa0349542d0802d0491500c10b01d0103402000c0310384003004a400903a04a41ea0b21b070880708603e414803c8103050b0b10147c0c091350130 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 333082419 1250 333081169 333081179
    0x21503040302150702030415080906070804050a17090a06020f07080706120203040f020d0b040b0901020f1621020f060f01080a03230304060506040b04060506090f010207031707031701 80
    0x2a41d803c5204000008003807008104c400c1c2c02441590040d00451400d41154206158020907041040d0340c1102c06008202c04100b441d4071940d1075034410743d008002031650071025542d050f001c11503840c04000d04001840941c500b50345041c1304200906240e1b008020061415a41600380300d00f03607001241c41d0740170001c100042d50b007100c41e81482c0a171070640180c8a5072641400c0d00740d042030510082d8882c607c2d00c0c02c0d10800c42d04460703041c090b50107060388032880e076580b900c8203080340f10300d000b500e18680c070902c070302c983e214119018908410b20030b0501c002041c080b03007a03000d0030101c04010b090250b00403800d881c1e24420100404c070760001c8088c0d42c801c01d0303514100b02640c07210b64158002e03082102c2d081d88000c05a000c9506404d03000704082d070f407540d249018113114000703103000d60303055109070300304101a80d40c4e240900801081e41c20041a06140160380420003844816031041c150650003540000404a5144004654510110403106542e00824a001880070703c0d044890150302c045d640040c81 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 333083669 1250 333082419 333082423
    0x12030504150c0c050105040b0f100f120204090209010e01060f0309020a05270c130b030f061207050a080f0706020d0804081e0304030f0306060c02180402060903060703050103021503040302 82
    0x40345480c940020301c80c007490b002159004601c5030090726560130001880208103201d80410301c0350707200d4104044940c689040c0100d075440548103108520424030781c00c4c07000341c41e01e60441d54100d200520010350300200d540499007282e82648980985000880100009500070403a41c040580c54039003001103011550028012200350701071240207003802d401c4c0d00c200c00d50240c0172403d0350f00601c100001d107180210340c038803c0b0b034031500c620007100f14502130000e990b050040590703000d8040040601c1140e0385a100b404800e01d41400c83c51000d2080d52000507403a101c0c001004041c2c20004043d20800c40c0c1060010310307040c220350211085500c00c60001c004503a005076030f1a003080c2d00c44034071541c2c1d0344641c61484002c0d90706000c3c1c8060550020a010416811003210032124200e0b0b20140041592544151a410142603000e5008000c01d0a8440301030811100141d01c1880144180d0a101c001c1d00400d2420201701c5a44c0d01007541c820051042d0f14044c00005007500415403a1480d620700f65400035 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 333084919 1250 333083669 333083693
    0xe0f12040f1401113a082a0a050d051008060c0c0a020a14090a050601020703021903060606120f0504020112020901092103090801050408090d03050f0f030412030504 72
    0x4501e007080400080810b13071007818010f00601084049070b061040101c020541c3e121140c0e9100300d03008100b6004d02c0c40f4220f9480ca60165942900c03443d0881d82d6401d0070210740b111400900c42528490170040d01031103070400103040da9501c281c1e0340c140c0300d03200c580c0c41e0021103030042c00b9801c014660003020070621b040080c5c4c0c964031030400c0320f40d980c640d0030310b00126241882c9580001d50000c001c2d00c01107801c003900301850b08681011a00900542c0b1036800e82c000b2948191a1240160042c04041c40581004052003201c81d42d04000303075011a990381c465400b191948d030011400144c2c08000200c03a80030303600520601c0310903400100402d00741603002078094400303045503044098010501d200c0b40d07800ba5020800420803464804141d9203062190b02c00304441000c2100031609a04d8080b40402c0c0522480388a980d00505d45450b20320410108501c41040000c100e0400c00e04000c407081007919500504580c030810041d55450f818103290440400ea0403000b4901010310b017a0030440400d011180704 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 333086169 1250 333084919 333084929
    0x30f1a01050a050906030708070e010c030e0d02130e0607020d0206150d06090213050603100615050c1e011a1c080310050d0503040608070f020303040318090e0f12040f 73
    0x42d50b03440c04040c0650f80d6000380d844003a8890307804802c1200741d48d0080c0c0310314442c9002c0e640d00b14882d411400107480100320300701c001e400619000340c011410304214019805140c00200100c0200310706c56010307001d881d404d9039200029040b140a010549404200070154080c450000d01014034007020301019510071445428071480f103c460110500c81c42e544210600c5401401141440a8901e807101c00340c40e094a4540c003d210703444180740d1442140c400c4406586155100c1c075010b000c250803c03074081d040039080105c00e0080590a0008003500031078050a0070040001148141899240284004000c09400d00490002020301100d4002420385025564010882903da0b162900542c00c49007003604110740000080c0c41d54002e10030000042c1044544035610482283d4600204072001f169040d44503001d40d1051000c940045e01641402c2c890081400c40d20322055034800d83c2da800d8030104000648140c000305a2003802c441c0500000084132811001c4510702031030840700503625400751140b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 333087419 1250 333086169 333086177
    0xd0507110d0305090904111903031205040305040e010e190c0807182c0903072d0b0c0a0e09010521010b0402040b0a1119060914030301060e01030f1a01 66
    0xc00c1d82050b00420948201d100041d0800066140901e8002141c4001c0381c0b4041c4500c410303030007120090114801240a42c1d600d81d031018110400202e0031400b91030007030305c1102481010b0001040402000c1420344c005c0c0300750005404641401e000210b00c0c11015050f07003480c681441149866140c0140c04142c20124a2611600000c030340340303402c1558a540c1c1c001622417240030b8011103c0041011a5040d80042006030494035190303078190540c0c030302ca1500018044c0b00302a0780054400c01d0f00c0c0003640440c21118086003490758943d500300142e41c04881d00380e210140403458039138046e846541c4d42c06003002600c190b00c065041c030340000c0090210015080b032031240070207071000c05c480a410500790f1090141c0155200c68883c4a412000d070002c219002c00a00490754821904100044442c03641000c81c22000f00a410344d1200005004010b8041d12030304902644049007603010401940200340a68403800d4004080000409486405c0034210040713080c00b440070103040002100c1d40346001e090030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 333088669 1250 333087419 333087439
    0x302010507020d140f070b070b01030215072108070305040302061621270b01090b01110f01050106030e030408071401200d080c03190f0e010e0d020d050711 68
    0x4000f03404410200380041c000c4580720b503044e050750000100e0101403084001030703410f6580c480c561901180101c1c80e001d08000d01100040026080124000790034410310340c003c0d441c01d40203441e52405028651004000003901c0b102d28491164440400754102c10705203010b100c1420a074400940d6901c000c0c02041b040c2c2940c03400c0c0c003c520b00840300020048614130109080500408541c1d0040c150181c5000d1841a41e14003420306004a121042c1443d40c000c80004581c1d0904d00b442005200c0c5010890501c410550704520044041104456081d008000880d55605014005056801d88400e020017640141700600280c4400716030001555200c2485c544000c9058004031020b644103400c4880c00040750400341107a002c003040d40307120800c02d600e804603280c81d2a40c0100322840100ca020072142c8103400940740400c00c6070042940501e4040000c54001600310003e42101d0409829007510f9021031452000180c040c0003692071100715040060410140d910340c0440044100c8403580f14110340e035 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 333089919 1250 333088669 333088673
    0x501031a10080901091b06030507020607021903030b06030f150102010b0d020f0109050901080d030c0f1205070509040f051014180601090f0602010f0b033c010e100506010c0c0302010507 81
    0x1501002c0720b6900311b02041c40802d1400545980801c0900807400028149000103024600000d81c05018550503801010b413143c20920500207000e03440780c00c600b0151500c500c680c1703d64403100958082c6401d0403030942d06052500c0015641c40b80800168107590400882d011647d0707454842c50142e075010b4403805003034540100100c40c14a001d800866000e00303148000306401c140011283c030000c00b1910100303c90380b103959040d21094a2032813440300041340300c01c02c130b225401c45420281c0c019509041250070106901e0001d8107a0320b44204620240750754004200440021543e00802400080620800703c26488042021401881140c14441d0012008680c56900c1900c50301e00a0541024040c40c080d10307000000c0c00fa0010f44501c40317082c3d003090580e810070f14010079040315510840e41d90200d082040300030034100c1c1d01600d1050310905503010886a01340004e01072006e0b204001c030068444440d044c00c540d01111030203092203041200e0901c00200158449040005607902400c100c1d880d940a4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 333091169 1250 333089919 333089921
    0x160915051306270c2f100c0512060411070212030d11040608160f030c020f01110a0801120f2d050115060809210705030406090501031a10080901 63
    0x958400b0007403450307004001c3d442202c60311020309080301001c4248402445000211400c2c070b00030301c000e0b070301703403214200404020003558140304e625030741c0001d0310501265100200c044802c0c03d440ea0380402c0d0000f4218809440c01c0b10440d41c8040c0c1100c0403c580d0402c0a40c0d42018011800000e018140445800b40c0c113150400554a0002d41d02c40c003400790b00c1003d0394807078940c0c01c00c2c03050f030000c86c0000002c52003050405540103946469a034665009400302a411006002c84180c4034080d0f0107010b85905444000b8001c4112044500c07a40c1a5215941c40300140071200503400b106180d200c203d030360000280340c3d00c40094420740140c00710924a030403220081701141d406900d02800811110f40380704205e0190000e5040340a036426503411190389070000d40e181d80c0129a2410715800580d8004d101885286941d0441c0c0303c4422a07030300b410529580c1e035244d42d01582084000c5a02031008005642e414001c0106081142c0c5482c4645481080030400700e05100714803909100b14480060355154013 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 333092419 1250 333091169 333091181
    0xc1e0803160206130801060b1e1903180b010e0421120b13150303260a0c02240f0a11181512010503011803020a0822081609150513 57
    0x2174a030080000795594010021213502c2200010944446000c0d08200d028016058407204041c2101c403181a03d003804049000b410744184040001500300d0f542800304040104d00380c00703050f444010b4422400d050030f00840000301c0300c1001d00105048002c0400d42a4058601c84d007040a40c100883d0383c42c56100065400c2c5140c80a40c040c10341b0380b107503401d00030000810310801c41e0f0007510f640b058a442c45124409101c0b03e0701103400c550800e400840d90601c041d40c012101740080b441072381d8036624580d19a4000b5080070b40f41050031000001804150b1300d040e1036850300116041000c01000e41074548108040c0a41665226040c01903400c2d503000b078445121100b281c84c0407280c803607556810803400c90000c00c400c0c001e550080d803a0841001070a83c514400400f0103170940c00400f02000c085c1d990004561140c0f41141030804164010081c0c00036405001d00600812409014065100f940c0d411008820394000d40c51641404c803030060804410040d482603c000b07035290003000280d0b040e440b0103002c03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 333093525 1106 333092419 333092429
    0x91509090c0a140c032b1802010c0308060d020a06030c140f1603020c1906020c01090f05240c0619060b0d0b030a0c1e080316020613 58
    0x2518002c0e08001380404112454292601d01c03110f40003544030f106001c00001b00001082100c114001d03840000700000c148100700c4030310340009064080d4104040c2c1804801404640c03151580c2c0e03185400a03030043c0c1030000160b40c0c0c0d880100203000301d0400c2000079201c9109500000d00d52000c41d52903402c00300382c0c68100110b000040240044402c011820b40c85840003d003111b494100c0301452210240507008006443d040000e414684010301803410003511440c10301c06100145c07003250503148141ca299900010105c603140d5030804011401488444c0861150550794000800600ca04030701440803445840c0c501000068400f0303401110300c0c00d041404102680300c9603030301c900c0341030b42c00804a4440741950380b2054680351464020141c0740c40c0129006080003120801c45000385181c4005619080c40c620b420b0b4106c4505c034900030f20490f00040c1d0706543c0546000f003000980 = true := by decide +kernel

theorem cover : BRFrame.Cov 332913669 333093525 := by
  have h0 := BRFrame.cov_init 332913669
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332913669 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 332913669 ≤ n) (h2 : n < 333093525) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
