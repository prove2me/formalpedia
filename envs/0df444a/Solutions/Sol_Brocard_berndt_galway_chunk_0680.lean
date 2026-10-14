-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0680
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:06:52.179437+00:00
-- url     : https://prove2.me/submissions/49f01416-2311-4f08-a1c9-451e0e474f1c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 122122302 ≤ n < 122302158 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 122123552 1250 122122302 122122327
    0xf021c051002270a0902040609080609010203151e10050a0e03060c090108040c0317030103020418110f0d1211061b03060f040209090408040518010807030b04030203040e010e010f0b 79
    0x45004400e5199800c3c41d40104001440390b001c142d1090340c02c01c1c0081000181c2d039800c04140000c55a10005a820698a81941608030700c8110740f004010309084900041d941080e803800e8032600510141115119030701000540070101c04c21398540094000100c00d22303820351100602d040c5203001d4005203414202040d40c22594051021030504011949002a05000d082c01003a0001c1d40c000c4403401c54001c80c204d284116038000d010990040703003007801d0b4000c1301c1d000c00403440345650481c10704803012603004108890425465182c07a03000b1001110040440c6042041002d80e0743c154590150030b40e500c40c1c41c1420708600900e8180300d1402c103200c01a407204006c0c00c80380d0102c0112045180044900300040090044403081e0303070008042000c00081003040030040007078640131a510b2140c0004202c040041c1c01003400707070400340e80281742c0806c00100300640d8290000e02c20f00540e81025110083d44000c020300744d102031b12540d26038004101c0e9115140e40300014144159030545460a40d8442c07 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 122124802 1250 122123552 122123587
    0x71205030301063204030629060d1409030c0106050315190204031e0c17070b070618060501030c091112060a0807060503180307021005070f021c051002 66
    0x3d0b6000d0141585241c06541d603d140c0f01302c00001c0e00e0031425a402d46a02042109030042d020032100140313002d000d03020001e85905c0c0000e00b038803d071002800020140c41400a00d400500e030018ac45601c800b41904016642201c8622030703620070b0021515a0300044000d4203460160340841e0190300800b0041180d10010039503d68041c0c1a680501c01505445070800f0092041d41e001a1002e085012000c40c01601418000d207024081d0380160401900c4030032007030b04c1005418510f19142d0118004100c0741e0b0343c6c42c001d0315555000d0b00000541041c80c6820b1850110f81000072280745541c0c1340103108001510110038064a00d94804210020f191407480d5101d00c1100f80ca01480c0503540c0004086540b00c500d00e001a01a9100b511405569003101a00503003064403804601d2010407100d108486000054440580e002002042e03064550441500c55278048201561032225008241c40961165004c49150342c040c903441c5030380c040705070414a060403040311004108900401046903072441c0c4094 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 122126052 1250 122124802 122124809
    0xb0406031e05070e01080f0f0d09030321021204200a03021e030f0706021b06030c07060204030503070b040201030b03070302011e09030516060906050309060a020c0a0b18071205030301 80
    0x702800e02000c6003001c500e040840c0e07019101440d001000802c0e40350700401c4180d60005004110344450600e0381c40f0680314255190340da000a039403100c0401c0801d1007541e80d11003488d007207014a5002d8484891920aaa012409407080742c41e100080c0400c10010140c1e03100b41803081024010014107810010796a10350600c0042e1003144da00c01da0b0701e030110b00d03000c4281010740300604865074014525405510b030140343c030460002d4007070000e0b90580d005000d0b580310100f0000400951851356011030187c095000081e0550b5955030071b01c804400030317104000828066000d4401e1800a2905100050544507003c0340d1a00a4104000410050b60000045107001c0726070030034944070068048040b107a94a0320350000d0300f02e2140c0241170500440030700c00f032016542d0a6580b00c0150341c50340c4064400f8802600c04000c4c41c1c2c00301e1b00003840000725a002c0e01070740001c0c01c16160410480d840311907442e44e0a89108107a1003040c01c015402e00b000704140002072844248500d4914425125642c407400f0510 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 122127302 1250 122126052 122126093
    0x40504050f06090705040e03190f050403080705060415181709041508150405030a0c080d05070807080a090302030405060a1b0503040503061b07060b040e0307150b040603 74
    0x49010031109104511072a00d840e000c881c11031624500c0680c0c0c3d14860301c50380e4012450454107410001c0040101d41e02c01030340140c203560040f40c041046421503540b40381d040400401340800720010360b0b05401001c0c0f4500030001009581001c2c02c111080300c51456014030010301c0d20510b83c4207481c003901044001a0000c04000b0150075403411620148a589480340c4d0240c6041c2110384810310268240080d40d5040048071003880340c10b62800c4c1d068400ba5409850b07540207110308000d1501c2400c004241d1031050800034103000c1001141810740700c040c0c5008011442e030324108005258407004c0b5540c003154011003480428015200079407039102d40e02499000303a10000d07113000001e000d1030ba00c44041e040085125800546030804984a410a0180078071902444000c03803211907c5014035410311005180d01403801c00c00c0c0d540c610082000311441504151107905da07080c64074042c006000b40c1c40c0104a0701d801482a220160102c84443c14035034802c5180500500105a0400c00c541100c2d03005d4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 122128552 1250 122127302 122127311
    0x60a120201030e0c04020d020d0b01020303190b060d0e03090310110706020f090d08040612020405150d1d0c010e180f100e0a02070201170c0f0715020d060f0b0406080604 74
    0x760621030400000194154001e4000941421f40114a0b4018000b0464101040250205800c012070300c0c0d100030381da040c403901324200d140d481440e8039600644600000400480c5045004540603050b01c034480c07000a15a040814000c21608090107105d1342c411081070f040050000d03001404515001d0001d000c0e0296a000c9694840034200c10110f9990500052000c4903225482c58040b000b90b00501412000600e0040d0f114640303150340c029602030742d4000341940302c3c07034030040240589a000078015000c840e803180d240c00c113914410a8000d420340e07090805442000b56620024100000d225001d501071002c00648800000c81e000055401c6490100280c0442d11405185060302070f01303070420f20000c04810280400030011f0307401015007603c00e03210090940407914900c18007010458281142500402c00e2000c92142c0b60010400144074040480380701d201e100c1c61104903001a805012400e03510303d800c5c0140e1040b540110010303c0c0910b1b805140605124004100c1b100140806000c0c03508c9 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 122129802 1250 122128552 122128571
    0x1208100e0703020a050405060708040503070603050105030307020609130c02071d1b0a23030403080a02030f060625050d0908060114040c35010602011116031407050303040b060a12020103 81
    0x5d60031103004050090949803520100e040003040d0340e019119452092040c0080003405900900543e4102c81e0014081e40c10410f483d000d10030345a000150041d0300a0640088030322095091003107440e021407540c002c3c006c01c0e06022089004011000662800c0b00e204001c2081d035000055800300030455000d42c2d507488244080e8291940d50602040001c2e12580b0f0f005507100b9000034002d188658001c3d074401c8242d4407070002d40b80407840f081d158444240ba8480026607a400d2240c010400d0440c00000c0002011580406804460483c2e10844442c2c110015070010558000c3e40d40700039002500203000307607524001c80c103a807a40c0031010340d60007292107038400711400d402108400c40038040f103407040110420707520701d50707469049a401d0010a055940008501a0301c14814140c9003044603440a140c83c0b001c0c503c5900104c0c18000803002c200c1e1840c4100b41080e03240024003406841000215124103041c500444d112100400b454003d0040c1c4808205564203a13107542c4080382c083c04c001038822071 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 122131052 1250 122129802 122129807
    0x503040509010b03090601050a0e06010305061f030203041b1d040302030d1109040c0206130f0804080f030304051b0a0501031a0909070501021903050f251208100e0703020a 75
    0x29940440c0d801200c1100004a07004030400941c407881c2601d0a0328010782e06c80b02009030209082c00340744241c840c00310000340b0340c2d402548000d1b001000100040c011030002d00c201040010034410020000c0c1e004410310042101c4a20160347d030060050b82010f034941407040d10070b241d2400380051074001d0000c07000b040502d40240200c50180044030302c148984201886c8205aa901080700303180164940f1036001499840840e4180c000c0481d0101a46400002e45a081c107c01c2014029500c0e0300d0100000103240004000403e20019110b01560701c902e0301d41002420071800c903d0154840800c0320076414566200003101059480909000940c0d03401d101803100d201640050749a0080e50f580188181d035500040c80c001241c1c801d03400c407240700d0794540310031003061407029000380815070611456100340080e50180000080c0c9e0071000c24206e05000c40404c0d6519031b508141c44d001801414030a545622524090740b0020046010f40c046242c14503101d862203005050070100340d070104034025110f1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 122132302 1250 122131052 122131057
    0xf0203040f0210261e09030313150e01200405060301050d05010f050408090a0902090d0204021e0307170a0b0306070305060a08030d0c110a030c030e040b061303030305070e0310090503 80
    0x5501c00c1c0b002c1411006040341c40340e204019185e80c8000c03512084460f074100704074102c0301c4c45075075240051811501c1d0000c07414007985004000300c6940b000c110480f004e03119584240c0310080e13007100c0013007071010717886014050340b42c3e4050a01d41c604000708000c0c0001d40350882141d04581c0180d9110b201c1e0520fa040060041000600300e480303150829052205100591025007400c030002c6035032804150340c0380c1ea07041c100d104881d01c954100482d804501c4c0540f80c154082c0c5040c0f2400e07901d100c0705001c240000b21317650b8003c5613500b010990001c0c0841c900404404025448821510100074520502e00041e0f520000140361130704040d211030018010f611991840801012410101c0340c485080424050150803148489400500d10f6401010354500001ea810100ea8250b158403081c11250b4808950344071100c00142e03009030310f4003001c03215600c401c0001d146903098841e001d60724600394500101a5034019006504028086e00301901a41c0e010a0002c55802600400555040d40385001c1c1c2c01c50 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 122133552 1250 122132302 122132327
    0x3040b0a1206080a0506011e06020c13020c0f100b04020c0307230a03050309010c0e150d11030c0d1b090e040212060403050d0b0a0b1c240303030f0203040f0210 70
    0xd0080d130b0300020411000141c4541600c0310b081e408400c8501d4070f148442068004c0c0716110060780800c090200030b0070038406420283d048044050700c0c0c094100c0c1c40f075140105000c3c6a5015600007280c43c82c1c144490302c03c40e0a8800211825850b12103540c2c1115940c0c041d660000c0c10740e4845e0480e00300d0034441040c8882e00c1810b02820390747d4400c12800d024106400444501d002c0d9400c0c88120103542e4441c2c0005c40c0360305401002c00c00459030654008203150024002800f41640c1c443c010021128071030050b51186403c40712140d5116200801c4006490401a8000510650340401100d494011b000c0c90107680d100043d00300c4a40d00c5000044031225101030f03024a44c00740340c05010615a0085c010003014159010030f0003140490428822581098401c8618550003800342c5031001d0408200c00c070310f1401c0401c1c007007a01c6000288801401920000004912464032401c004240c1c06001d822006010803100314154179058131010041003080d02c0003803103681c0588100035020702569800210 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 122134802 1250 122133552 122133569
    0xd051305090601030b0307090f0608070b070b04051005010b0301051908061603090b0c210106120b04090c1715040804090903050d1404030815010c020405060a0b0c01020d0b0303040b0a1206 82
    0x19030740c8d51084600400c90b00c605044000d003000d001040c140b80014901c0d08984114548518000068031122414180076008907100d0040c140c1007036001c56070b80100e5002c0c0c190001c00a03620751400301000711481524852041042802004002d100c002084c8107900520181160070740b0026000114024100068010b020705140c2c410320910078140c201a00c00f203041030344003a9042c1c12120054208074400d100304000035140720354164070300c55240c11030a43c400000d0400f242405d1035a40d1581800340c1c0d9086032400607030440384a1102c0908004141c0455801041c681d11801d06498450083c400c500412080380d0301c40b001e00041610840c200c41e00140d411400700240001d600c1d00000c1009c3c15181600025141c00200740c0d00d00c040b04d00351070341c450142c45220104c4001c2e07081c84050302005022540c00001804001030007541003008007007244c0384400040e910a4584040c00c1128500380545d40240d20600c03041c010411080101c0710f044105040c620342c400440c00c1198042d10b225003019030b2 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 122136052 1250 122134802 122134813
    0x607080f070c05031201060f02150613020409051510031406240406030e10050f18030d1d06070801030c030303180606121101080c0a110118030c050d051305090601030b03 74
    0xc0b43d41c2801c2c900c2d040c0c07147c66484682c502d134550780490f03407404c6000c18210282c0e5440049001441d0030000800f45244000c40542010355504101382141c800b110300c50300c410401d0360000810304e09030415107141c0109003000c00c0754a220980400a110000781001d008080881d08402034901c10030248035001002e9a04540c0c0d1a11058018058003102c07450721424418141c1070740301d00c40140222072185d0184040712115640301900e501c0b60b000100303501d11039030108100303500400469006040070300d2181e1803103000d0680160000ca180141c01098042003290450040c80020f51f40103150007281d815240c00b00c5d02d8188110003100c5102c40d503000600691a00300000365882d904205401c105001c0d001d07503503500004c90015100c80c80111881782038007800300f012840207030080749504601c80303036035000082200c01340c444405c0c1c0302040c05c5d0550208501a440c1001c0110400c040036a6045134681a8282710003c00402c48180031402018412010344001844e503134405c0e0b1081c5c5485000504551 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 122137302 1250 122136052 122136067
    0x2040f05070f031a01080c0d0f060f08070503010e0a02102109111002030d201803100e0307030e1207090b01110c06030a0203070504080601030605180607080f070c0503 73
    0x51941c12401082d102080c10f000014060300341c908500540050113841d002c6565850a404001a500c00c1403202c0d1010383d540d0b03549103040c4181c42000050000d04100080c4d5a081112161829a040c0d002d00d11a078101a074107942040040340c0892a0369056842d010035045205054132400411500c2180c2c88540f810544045821600b03c40f21041c06041c02428041e880c80034060003e403e03614400142e80204003a150641c2c80b0740c0490524201d540150303c00e05407029080c40d0ba075008a003d007a22100d4400d84c246645001d01c140d20f05401c1c040c0003001800c1640050365100d020301c09011b000d01120307448605442e01c96010240da005811403d0b600480c0c0c40381200c0c801440841d550314005a500f180c405807200002600d02000400140514110b94500c69844040d600080403201008014400019803050030404180a1449240d0126441c5000502d06080a032030813142080b95000806204841d5004141d46800c0566110641440e9a07404401d0390440c00e0104020014840040c040 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 122138552 1250 122137302 122137307
    0x1e0c032a050306220b010e010305090c12070e04060207020a05030601030c230607050d0e1c060c030b120d080c09100c060e0a06051602030c10180f0602340f02040f0507 73
    0xe405c03200c8241c81d00741c1542c10042c01102220000c40d043c1d030301179200002f660000d1500021038480c02d990301d01260400d94541940d449811004d880c111000ea0700465101c086207800820b03a00904030a4000300001c0d85141c490400d103e016201e2500011009401604a0008040010b007038820140029540b80103601d06036039640e44180c09800001c01500d80c92100b894502c3c0901e0045424030180442000740340c407020010598000e0310018150b984036529070070745030449400691072028015105104c051840a04030200040244614070070410000714103581e094442d03900040309150a41700e907032492911400801c8904007014881c070903074440c81c08020194201c14850741c4050700d000304000c0210f2040c0c3e600d000d58641c5030800d40201403011130010140c2d000303c0d882c0070060155036451409443c1d5402191102005584140c0c0005020924039181e00854521066182c071105a41550719001c451080e00c50000801e546c4080c03408009550b50360b0841402544140400c03c290705095201 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 122139802 1250 122138552 122138561
    0x2a020a1a031f14011115100e010b0405100305090106030605010807050103061401020c120a082a070e070309030c080a02060915090706050702041e0c032a05030622 71
    0x10b8820107001c40e040010070a460070480c104584441e0106514642118015103100c2041e000501d5103204d419001e03003032280c039443e01c580245040301022003610300389040c002c0c8c101d4058114030030140040000708200c1c1c44a02c003840070020315240001d000d8940c1c071a242d0140885500180c40c440c10840007068498020840408940c02624108109907484084a034444611054680035030460a01c00c0918208148601308542d80b90007601c040a0b026501c0d01c40582103409055000c0310700403181c8800c00c41c045100d48a0925210007404070301c2c03405031400203a080003869a803c0540301c55a040406003d404c840e004240c0c4a00503c0d142d03001107400030f6030307007908039007041e218440d806c1115490134015480c01c0c0102801405007103a64201403003a6440c0d48201001ca070401da441c6a003190b040c90700910040f00c103401040c0425400058400182541c40e60480a0700c0384503100100703c114602e4607020f86403080f00b41491500c0340d1703402000405641407034800c40e040c00050514104d6020b00c9500 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 122141052 1250 122139802 122139811
    0x40e0313090e1b0a031b0306090b0708070507170f0f160b13050a0204110d02130807300804030b0106050d14040203031215030703050c040501062a020a1a03 68
    0xc45001d03444880c0c4040c66010b000c007819130080c10038001400403034a60b039050141c44400c4400034100b1a40c0385e5460007200c40c01003003603a0a075444024040c0a691120030143c01c4221454014104140c54843c1460b80c80d180400010300c55001441c4005100031201fa20042c0101404042d141e442072859241c1d50f001007a401c99681281c00006126042c541e40190500381d001001060351078540e44c01e0000900c188140340060050601c03012007206843c0c0010303c0013a030100d00142c00c0c0c9141c044c40c245410443d4021045a01081e070640402007c032424082410013803202108080400c1c1c240051544990f8001400b00d000b079800110f8040e42040003045071614101d010031095010194800302240103540c02545a00100107115045030040d400c190402c464031720704035650310702400092800c41c0c00ea200b02c2e1540c0200c1d000b5503d40c5084d104150040c64281800d40317091800390b0040d03c444001b01d00007041d0803480781e0340100399102c4442c03d8014005000c0c100780d07691140d414104032a00101c5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 122142302 1250 122141052 122141081
    0x30b01050301110d110405130e060603060705071b1518060207060504140109080706020a0302010b09010e0610121109040b0409080f0c010e0a0b07020607020a0f02040e031309 76
    0x29960a052041c3c9200d288640e10f014201860841880c000d060010364000c004030b400d210124060f0385403020110074031a10300300060010000d03550310b400d000d0020f111621035040041040b4030280c200d400c40d005907501100c03110703480f4a2040130044280041d0849041402c001035403001580d00b203100f00d45c0340c249206072403416940d81d0500300d9a034422401500001070f414002000f8190071204800800300c81410450782c92902c602d012883d0503e00e074480401030740200c0c4240241a028032913000c1c80d44050b1010a165818101d031420402d40140455008000c81036658142a1294880190b14004540c00b403250741040c03610111103400070381c40140b00d18600450f440f46494144110781aa681c0540d001d410450480c0608080740c21641a2070619501c40c00c100304040b001740041c154031881816485490b051034200245005802410302c01076601404802e000b284440091113440c0c0e03030440c2c01144068900c0012030850040716010010120020070100d6140500e400520f620580c20 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 122143552 1250 122142302 122142323
    0x15131103071106060604090f0905011b030b0d11091807081b010f02060705031008060a201303060b01200708100c051e0403200301060e091f0b060705010603 68
    0x3400b15212042a41d036140e0010b4100b0040210509541003000b803402d441800051090080d11481c0c01c1d58020042e4072040e040d000302c07464005400d44274580340c14405850359511042c09540307021403c50720303d41b080c2c0721b400716200180010900c0c89141d074111082005543e02c042d0b58003e182d95826040060034018003007601d526070a941b1940090b0000c10b03940d130050200b52070380709041d00c41d41d00240000c14180b201a801040084082283d035002c0d4011311800643d034850030090302d0341d1827442c105459130300c8003c22000c02c1c20101480004240c5c0d81141001413103030500801070300d014011202d00300140780b058640344110070700441e62404441046040d00c40c4507054003107810484a8035060362001c035100b130208039039132074100c1c0c00d91001d5101e8510051500c0d480391103a00307203080f007a100403501c00410040c10b6501c1c10280145030040c043d000300c01c0c141d030401500304c0c2d8540400c2c0d5071259040b010b800c084030346200e0742e0700098600280a0301042d43c58800e070a282d4080c1c00c03680005e407500d450030b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 122144802 1250 122143552 122143577
    0x40513020a030602070303050c0a17070e030d080f06040b0114181c051b100810090509030c07060206040c1202030109020a120c1d070f090509010b0c0d020706081513110307 75
    0x7024115880c0240c40d074bc4140306a00803265150060a025200c40108448111241d8590310b082014407803220b016242c3c0301042c90040c0a44d00300400051410b030080b41030841503c4d03166013040e42c81d0a0b01c0030002e4283c0d200c1c0d207504030558401c0202032400380e00402c8041502288210901c20445541c004c00598001c01450f14808400640e800140c0e03420100206201c2d00c1588107582264210031640a05080d06581d0b1040340c043d6a4140c546400c26003001032200c90504c010000140100076900140540d482c1c0b03602c810409100c203100300380c20804140000c808541e001e6121491440c5d00414103602c168541d04e00510f007500281c022541c0301c41d8403402050f11b04025007042281d60b00404080165074509600f00d80c0d07a0403c10901062101c0c00070003107210758031380540f203010300740f40301555072a109040034191034030701c2c0340c1c081c42c00f035410442c42840304503840504250300c6151508a007860010705400314800c4007200c40482d440ba440c08800d60f40b088000d0000714010101c035611551880507 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 122146052 1250 122144802 122144821
    0x40324290f06040614070510150621020c0c030f01050709090b10050702010c1a0714090a050402090a090612050c06160f03140a08010602060a0b0f040513020a03060207030305 76
    0x45a00c001a8010800e11041162178482c400c98000e2486072110181444420359a40f490101400c508140c1103840c1d036115044044001d00c0b4034004c000038036140c2d403c0340c40400c0ca41d1104540e0700c03c076400c9940008060003440310403c882108103130302808030341801c1c00003400d0314020f1030242d0740100050200034000601c000359000b0700c1302d03d82e0000c20100e1fa0b05074084054a0135444400100c0c14400ca083c200360104140310030229400750700d103031500114513003200d0050202c410000004107085050151000f42d0b1107400500068900a40d0010780d49e00c504c030700107128801c603a4000c9500c5402c0c1140441c4101144d45110308280c4502c00301d94184a004040011a00403d428400d84002c1c0109142c041000c0c8023200341c6c014000e01b480c40c8848000d1083e100c0c00e41c8814180744c00306e00a4801005110f50401c001b550210941501308240f816080006941c6041c01400500c250744800108000341e034540e40b90000c565005000d69105c0d50b03685040780280d00281d5003600881d107040c001030444074 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 122147302 1250 122146052 122146069
    0x3020406020613020f060d0b09180a022e050702101e0302130308030c090901050906030a1b120f152d1407090305120403030504032429 59
    0x124681c0140080755541a061418041843d406036804081da004141194991030010700b10380b15540b101252a420b5042808403c90003d0150000d4204a110b2030742c10580208a00c1d0b040d5030304039070345203603510f2000e283d040180b0a4924204814298520281526000401010014403d0301c0480052070b940406603000204603c03505a05100c08003001c84541c402da0042030441c082c4c020984035a41c1b01d4a03003c41e617400072100d8a4192000180814aa00d0036408030360060078222601180ca00d0200c000c281c4442040350020401421000790003000042094004040c0401d8201d140b403403212810500f8000442c5102175a000c00c01d04403554113070400d03000e61071003c004030514000c1c91107865200300200f542085070403109561007100407607d010311380e22640620f00c66581c07210380070b056082c0141020001104070354040380c104400c00010382c120742500c048a40090318001408144684140d807035080000100f01103140050302d40c05003454180744200c407a40810340d2101510154140711060 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 122148552 1250 122147302 122147309
    0x506180a1406030312060d08040f0308040e06032b0912051e01050903041206240f050301060806060f0a08070303031d01090c0e09030d02071a0601050f03040209042102010b0a06030204 80
    0xc0f000001b07140c1d03080030b86080d80400c0c0b003940c1c11442d00d40c0d5a04009140d04264104881460300020204080200c2d1003415400c44130440c0030f04401e01c00d0003402845607049494820380540481c0c5091801800752500000402980d2020350310303d4102e150080d1130304118114001c000f00b04001c81d10103a10144140d074410000d83d002507141c031381406600b5a48400110040750200c5c1c44001c04803076503005d9148890b00c0700300c44a800e8000d81c1410300b20905000c03a074000d04d010740e241c00004c00807188001139090300800256110601c0c00801e80220705881269005500d251044d01400010107505922103840324420301100503a0000700e04600d030a885c250b0384060242d07004110103000021070740703140300d0f0408030385400c80349804180969141a60002581075400280b20440025424285440258080e030246000780c40c06088070000b0000c0c0c000030744040c0c05498220002010402140018400380000202524400e00740410083c06081101c501501900d04c01000040d4a8068000c3e10140c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 122149802 1250 122148552 122148577
    0x203040e151f0804060b01030b031207020f15070201020607141b030c071403060105040c1704020a09020d050702010605010801052119081918090506180a14060303 71
    0x101d449031240501801d2200d60841c1e072159984806100c0300c96007a1034003030252555100d02c1c6061925090240031900d0f80322002e814903082c1042d0100c1540c0c0820800442a203602c6115200c0002e0300104032004896601c04ea0071440c1080d034450740d2a401000382003994030076800c03108195160201200e1304030420a401c0c4071283d092001c1e080700100e000724109200c504804480c10400390300200c3e45000106d0340032001c4d58900e94134110b41030509100507401f4060654092000d500100710042c600e940e45201d03529921040f6002c1400c660320203005d079004100038802075407503400f900440780c0200340944040000d0361905100103811350085156074106d5800401000004c80b4003811000891040c1c8032041aa005a0f5417480c81e02c1c891445208845005802c00d544a261130b5400b180d108a089182509114085013409480320482e003400d0103403a600503000c1865100c0304c1c0480c04d00d40c4000710b02c0f842c00803103500b0402c24110580c01003152308111118030300da903191a414951a0300c16004800741 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 122151052 1250 122149802 122149829
    0x13030e0402030a09020a0b0408010f0e03190c0506070509040509150a020a0e0904050307030f050c071703090a0311032b030c05070c0815090d0801140103020903010f0e010c020304 78
    0x5034a01540555402101c5203004030f51411154002201910a03800c0100350700b60119060000c08001d2003101d00d41843d4100402a171013000040c0384e0399004110317200b002d01c040030ba0780c080300c1c0d4402c00b000f180443d44503040b0f9203641080c5101400c15000241e4042c00f4a01d0040024102000004c0b0302d140003240c44a0908a80c5032940c0e103002035440030f080c900034094803043c0810700d0749507203d589200701e000ba0065515060f4601d070040014070100e00d41e0781088401e004405806001107811021150010485514403185461040c15070007412a419030250707030ac180000521000010800142c20220103944072801d01c441c140400f01b0b40084160039200c0c000c07078601c1e0712a02039440170910300c3c80b90501c94104031881d078500000c0000f076002104907070401413150101140d0807096a400c010b649014043c11141020018003140c414812803e00c007500346080d52080e40241e04a07008004098024800c42603508171403c050250b590b0742080c55031a09680c50701c1c2c0c7e0307c04001d51741600ea81c1d416070714 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 122152302 1250 122151052 122151077
    0x30c0204020d0908070f0303050912030105090a0e100b09070201111206032806140402180a0f020403050c03120903060103062003010305011407020f070e04050a020303070503030f1303 80
    0x10082d00502a0400d00c50f80c0c07441c144010a05800290218074418291030a40f60b0341d515006050302e0000d070143d081a489180c101c0c80c6a401c0c4010b49055a400380e85800302c540e903217654000580b12210300501203000d040501000360050380c1101d40018000d8518450603181c89c4c004034201e400d010003100150005000c4803401c0006010000d030014402402c031600a031070503280b03011b10240301504001401c018035403002000301a0061030074480c0000408441c074901500071418a01e064115000e00484a20001d141155103603c950201c607230301002103440e10703143d281c0b965a811070440c8a500c0380c030480041e0b50b055450217089600303204003d80a04107a91079907a40c1000707008030300084142010b000c401e514030b0000700303000f540c000c501400c00800c1c201144130008034884d1020f4050011900920b0540c00f04140024030001103c001e09110107141c1c0e51400c200c1d0030080081070081d41400005025428024004055401441e20710900c0406031a15440320364008800c00004010807410030480 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 122153552 1250 122152302 122152309
    0x6140604030807110306180705060901050d0f09121d0d11090c0d02180907030c09060c02060403020603040308010e070521070c1a07020f0c030a1b1502030405010f0c030c02 75
    0x82803c1071041040001c01090310000904001c401c6942c0446c10000144180741c0c20380030010701c00240300a0766100e2070010300c000024614416400744007111a1940c1c0141c0350700c0840e034001001a5080b481461112180600041c12200c44a00f2004c805414451000c401e1030400d003c944896445070250900d0751001d41406440b1500801044400b03005102c829103490780f50004000402c0c0320b42d0700748501810042048001c0101034070780340130075103000c50100000d900041c01d101601c0490500d0090059280b00242042c8210b0708020340100010040c00205a00701c6402410395910002c582810780d919101100d0034041d0a00001d800b45541e00704c02d503104c800d00380322034000d00c00380385c01091a00039032126200703d85101d41c2c070410201510104400258140a0303009148c0f01080034098000100e000240d5420081c3c101034a540341c007078a07034000010b460003a4001441c0b101070180a8041150019490390801e100d16800300f2800420404024801d60508540355410f4441c2d01c0264503035003d0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 122154802 1250 122153552 122153557
    0x901200d18080d0203130e0712020d091a010501081f060f030e0a030206090c0109030f150e0d080403020c09040b1603060b12040611030603120d020417030d061406040308 74
    0x45001d24074150400304010a09011a000c40c0f207040d0020740c3d0760801c2203041c0c1e10340d0000c0d034040e641581e20841448441c0d43c1c0000d448a04600b5940c01688441c4514040c00003011034450080c4501408200f07000c01608000c85241240e03024cca641c1096619043c1e81c662600004d41510340b020769000c01808101d0007046644a1125140703400101049044082071800c11540c1c3c042d00541d1140b01040710701c00c420010205003000038681550401c0c40c40c0e4030a1502c0e295414001c1901c0c09591740304420b21310591004104948003001c41d0220840214094003562054500b500180070b441c80003009428010b102e10b008035404442c841c07856450b00d42249540104402c140f0806d41c0740c01001580800c1c038005402e0082034500b00c50014106842c2040803035400d0709100325006003d0003084081da4010074407000c03010260200741d559040c0b9103442030092203243c112840a0099904018031040000060880466011000c00c9031540f41e4180380000b14191040c298070200400c81400020340f024007 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 122156052 1250 122154802 122154827
    0x50112080a0c051608031819060305091011030a05010503150a0513050304080c0f10020d0c0807060501140f0108011511120c06060a0b090102030403030521040501020901200d 76
    0x980c0d07081842c0e554100104040c1d41d000b680c8a40c00401c010140303890301050405001800c94100c108820701100e23050700c0d10b2503441032000381596000003071050354050110341c6545055600c100050ba18480c60982d1682050f1450b00d010f038030b424000304060400140000c1103020305a41507000c0d07a03440d19414054000100600076401c070748025503000a00410241014201880151499103510704c1840400d1b00081e501c2072040c00b945090000f160780200e801400341d00d071840d19003582000390415000e50302c6403020040070b0307620b004000240d0401903080c1e01b048490483e4910702d80c0c4501401155424028092240d1032081030000540050040c141034610f480d0a00a0f151034803c0c50242d0407054002c584d03000c145400840400900380b600c62400409805040b107243d0400c1c1d07400000070740d80d010f03600004052140001e944241c2e054154101010303805030049060b81ea10b080c2c40c25034040d40201040b00d0200301c0f086600e09110303221194852030078580d00002c01c0c102d941c000302111004203149 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 122157302 1250 122156052 122156063
    0x10e250f060e060d1415190506030a2c010609050a02031905070c05150609010605190309020a0305060405010c0e04060605180f120c01021513030c080c070906030501050112080a0c 78
    0x109441c048569809178070784180040007004891507000001e208010180007400341d200c0a4811041c003042d5540c40950b0740003004040005070a06810000300b0041441c152100710a604100600903140015040407099035211a024445a160740c60441c2c107034001a1030f42421602c0c0b081a00c01080e9850b441503a000c21940b0f80070381003500700d488241c00c2040c00841c419220700150308001c21030600c1441240108414a0321619104400e03490151880c8814203400805d43c442c0c1d01d00040d5640c4034802e501541e04102541c2c01410180350290003132014002500104d40e035807880d00303c0c5140900c40c0c0c0b0211103050700d94034604508048915103101132151035662000f003065418030292036803800b20900d481750000501c0609001d1001a1405030480828022070101c4010003007128414005ca80b24240d142c1041c1020446c50320b400e944a000d800244841481289000503040030103070008021213001d90001c201590300c468500890700741001c4040c0c20400d04020b5410224858070b045210030f400381 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 122158552 1250 122157302 122157311
    0x60c0504090906050402030c010c03090e04081308060a0c1805040209041104080601061106010515031305010f0911090103110d0f050d0f021b030709020c010e250f060e060d 75
    0x5114003801c030307040e1030010f841c0c060340c403401c11046050030060300b00da9100c01d082c650202c4e0040ea4008000e01420b002d00300305c25100d140858200003102007a2081d003000306000352421900d401000340e6400d000c40f8180c4989060510701c01406001e51002500b0030108d4990b000c40714180070038000603600c0b0b03003541500a566403d0079884010480e000e48058400040580040d500d4000010b08a100300f000c1c0754800e80100004122654030700c80481c0b40999240d551b2a203a039038442e4001c0d080011000080c00c65400d00c0001c1e442001e00e9484021005d00c40d9003ca003d007021001440041c0307109000c014454100841c40b00140d06d00140c1030031545101e064600c04080c51030ba01e02c0d080013440d50483d40030411460b096458150140904800a01c424056010900980001942c3c501c420b2082c041c02c2a40007400441904081d08001005840c0c2401c45808a00340f024180390030041d1508080c089032444800b180c01000d40b0294012a051940c2c0c5428188069040148580c049404103040b1a80e4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 122159802 1250 122158552 122158559
    0x2031b1e190303080f100f0306050408090d0507060f11210c011107140307032a0609080403020405010e070503040618050d0e030d020a05060a051b031003030315060507060c0504 77
    0x148030800285200e80c0c2d4480c84d6080590302a001c00501030310614504982510910112018890600841360490341c0801c00e601d803403c3c103d02d00e118160388242c000212100780c905000002489004481c540d9640e0031112052450444107210556080d607180d0b04040141c0d08800d0090040e032524000300c040607440c1c0480b0031000c5085801144101d00080d2020440c241400702000780e61b6802a405406503150002554000340501040610f116100b800b1004207603004455050151071554484020401c0c0225410038818942091204920072424170340042900c01044440c640190402d441e0542180c549035103020281900150b003d4072520501401800710300d00b01700080b008070003500c810401000610030b1609040c000900f04095502110141002032000a64aa404240c0100000e081d84440001510b494911f50116400320004001c0c0880410f1484006c0120f9100352410880d00040c44641e0054051902c600c0700440e80a020200118902d030b08010010506440d229180507107 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 122161052 1250 122159802 122159839
    0x515120a020303270613061d090a0c0905150403120201020403200d06020a11120a021b040b04020703050c0f060618041401050907030314090d0f08090603040f02031b1e 73
    0x26006e044041c0701b85e004200c66904a04810354840e1041420284108248082000500080d000c00c02080c2c0c2d56819020703d6100c0e030b0001000c0c0000615600700d25036808140c4405400a0000303540281132400c0030300c00c0c18014821201200d0384099503d116040741030038030101c0100b0029094010701004144000134140b0b01c02414200308a44801e80700301d4140e40d0b0149850103d40c1818031080d01041011020303600010102640b4900002122080704e000c0c0200b0040c1000c502131540050010a1040806400c2800f40542800c10402c03101d403800d00b5800303166105001c0d20311580203c12110705540551541c040c0c1d59000e0b020303016005203444095421821118103ca041c1100c0d04942e00031300c100740e40038840c074494181c000360342410071807120002003103104950360040010902c00c0c0114100412142070721440c41c001000c01b40c4074602403c201c00c04034078104080f40b1900440c0c41c0c6241c801c0c0640002a245c42000d0046440341a0800c400c0c03100c125450b41c1a58801496a80030703171070702c4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 122162302 1250 122161052 122161057
    0x18010b03040f0b0a2403031e03060f090b1f0503060d060e070e0a15080d0f0221040f15020c06090d08070609170301030302030f0304030903060515120a0203032706 71
    0xd114032000035490500404a501150580b00100c0100e15005c0100302090740300ca078804500e100c0000720150101c004906600804c920361040c0c40d20300e0010300c0050b000045a001d00b05c50003080d20101c1c45044e0300b11940140309461034500d0082902070020a41a003425980c00160a200e03c034001100101005601c0c40e0600c2c85e405a42c809180c4400c200e105a1382d401040c6072030403200c0f14059010700304400b180c1c4031400000c2d07507c100440d011354134410a20810080585201400e5071200d9980e2001c44003480b54024054103942003c1450300080c42940d40c1c29010b0b61052a17409483d05465000c100b01041e80901c0586900003a10070888001c111b0300d0f0020480c0e9131040d00b001170100d6861401c8900c024040d00880b5441d4424801000070170780100850f4283c103000441c00ea80d990300c0389030aa915641c2a00040c24842c0f030901008030003035401030f0382d0000100c02c884152101c00c19200007a0f480041d8000290160014041c00c0b980010902007402d660803a400990540e0300e43c18040345c0b40c1e4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 122163552 1250 122162302 122162311
    0x1060e12030c01060312051219020f03010f03120804030e090c0d0c030f0605031912170a0c030f021c020c03040305030c030304061503080a1107051f080618010b03040f0b 74
    0x3039545600c2001000010045d003820110030f404c1223420306203002400384c490400103140281041d44032802c99000400d99046520500d01c066405d43ca82d612041c503090800c415010841b0289140c03803c80544500a464580c41f9962540d215124812070070305101c1407410203048102c10107804d120014260f039840c003809003001c12503500042e5031145102d88005450440c2d01c0315010760403103048409002502d0b101620042c3c1c221030050500401003c04503510f080d03040f891044980010240010000f2641110b00c0ca0038455a0070b00c0540d503840414400c0f84100414910400f102c1800405c1c01ea80c1500944040b14940c001d80e400c0960b80d0321000c0c11680141003143c1c440e0400810042008001e100f440210014241c00816240c11a82d8000ba103105001100d001c3c0440400c0c0c0b92484241044000040c1c0000703002c804908030450f2020740106859083c200200324078a00007600c07404d0207191050600c43d054a826000d910b800c0315020150702c0030300141d401a03040400e11011030301400d803070340c080c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 122164802 1250 122163552 122163577
    0x1112040f021017066f03010b040b070305040306150501120509031c060e010b030f01090c0210020d09021915080405070303110304030b25020c03100c020f1002090906011701060e1203 79
    0x80542c960071100703c404503400390b030140003c00c6c0014040c100c645400c1e5810b40302412003c1e59505480d090030713a62030241c4c1e44000c1c4080d04003202100e94400340992501195420b0300c070000400c1c510f800c105c058038011034094180c0d074814080c03e41108078607040789111044900002440c00e4844c0076002c408642600089130001c400814800098600050280105140d0604100c49041084000c0d107648022114043c0c3d143c0100d02a149102203901c8411200e500400142600402080345582d100c11440b0b095401d1410030304408240f80200701c11340c0b040c0d0f80400078200e10340c00c40e5810b4070503006005050102c1d10040c1f00c080009003140c1c00b0300d40075503540b06064150740040c0b520b100c101c481c3c10382c2030011500007a43d550f48640340042e41404c0086007020200d42c411035207604924096510700c080c052840b58481900701c0e40361540c0102441c2c1c5040d50449802d0b660f550041d18800c85003e5003e8100f00801300401110f0b110b41d20f100302c4201e004000920040c0041e116515603000320100420 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 122166052 1250 122164802 122164969
    0xc02280e0106021e0c090606040504090b04050601050f0a09050703020c071202130b06090f0f030d030902100f021b04020d09051606031112040f02101706 67
    0x9441d804014000210350544202c0041c0048040c4e083d031142c44015042e0b0180f0082070124403195211002d481c0504400781041110501a080100406005840507150f60040c4400801c00c5c4c1024042c00c5481c40d40609800121894030080e0401480c0080010040541c00e028100700400240116401400c0d22043c0c1c9940b1800b900400c0144009412411855403a00c00b01000707e8984000345c0d46140001c440c1d4204144654020502108c5089040b560500480e59070701101901a0320401c0194002d60300c0c10311540c00f02c001922650040300010016130701114031403071050506400303c90080c002400150401d085203c0740d006072615500b0454050b00240075230140c49685200c1d46005101c40d1505018891005d11400b5180c401c5000300403054041c54001002d004200e070f001800281d018204862005000384010075444004560440d44811003010500500e0146640241005890006d034032050888140984502c0920488a43e404491403c9080707014030780100c00000c03080d40440742 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 122167302 1250 122166052 122166059
    0x609060305010b0a08040609060b100306031104020306090636040b070201090809040b01271d09060f060d0c0303050a02010b06040e060108040206071e060b01020303070c02280e01 78
    0x805a40e0705030802c1074500400d0108130185a0f010400700d4100390040070015072040f450030004094000001201c0d0440c4441340e500140d03941c142d010608480c042c1c84180f40040c01c9604002c142e120a44050f540581540c0c086401c1d4541001d841860041d0420103113040b03400001c120012099244410864892110400051114400059034031120070f100801c000b0300d07a541c43c0415400356140c118091a40c82140c030b5010f90180c0e4500c86260b080b160f190b000201804c182607621111401203910540021003040410500a80d040f1b0050508078007070445560b450a001d603407180c004004a0f4071544036030701c1c00045520700d203101c80958000c1d601c083d0340305120b0303c003e4203607041c3e9048113028500c1048104000d41c100e90740660010824680700c120760b05c850000074040d002c1e6502c05003420805507400c40b03858101000c440d821502c205410b000281d800401661a400100d90000c08501b20350300c41001861300700d403050140f20341c111180c0881c5050941d002d02c650065080128912011001070 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 122168552 1250 122167302 122167307
    0x2010203180105060108040813050d05010b030d0807090e070306120b01030b0108030903030f0a0203040f0e06130e062e0602010e0f120d0b1f0203030f060319030e030304050406060906 80
    0xd4100d01c8401000748035904182c40003c041e61801040a440205c01085903500392900000c00001400002c000b10003900041c101903008000c90740c0464882d104030800d46502d103008103211841254941c5801d0115460221250700480005002008243da100e0000c41c11600307007603091103d2401001050441e41c15854103400354034040c0c02408580d80140034038a04c59034000212006000d46640343c54640f07204c903100389e1039030180b90031410f00b0910304000460a40c00903040c09106400c1141c2c40d00100da152444075003260b41c0781c0e01590f0982c12032400140100c0200742d1021581c119a242d46810046a440b007504100c3d95400400051351545c40c0b44880c1c1808000035a40310940d400981041c007810748001c12a0720425100c0001c80e510340440c0c0c00990381d0400b00d050760030802014642d001c00560700c0203482e0790088034140c0c242c40d4204086600c41c203002900405070040004480e80200041d181078451300406803405515110170040030480381c0311405890003c0a00c0d44900102c2e40c14020003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 122169802 1250 122168552 122168581
    0x7050d0615120b3007050d030203071208060a0e100306050c07020f04020a1e171e1602030d02130504020c0105092a060703020a0b1f080106080604111206040302010203 73
    0x441e441040042000d1390b8030301081c030b00c8604074403d20190801100300320304660f00b0082958002075002000b20350079001d040c0c0110081c40070031700c114102410303c0c3e058030040e90255010b4a03200e0700f006c041c80051014046000b8615080103080b004031201035603a549640503542c1c1124a07034441240825032034110704006206e070301d050801b1981541400580c100c0200300c0f464403000311401501c1e040c0058001401564412a692050b82c00314103d4a02111448030003101544008a60343d4550001b61310307148003d503139401c030306115400386203812540d80c5e030304000c0c2d0400301118030a01e9080c900018982e4680c4000d040b54520b00c0004201e61524401d028107100c1b00204102b061804080c014040c15595200070219500445205850b0300407400e049145c20600c6e04010400c0d21000f040c0000c2590201e184c100605810303140549480c5c50f096000d00f81c401c0c0d03109040f01d590088011030000b500002d441c0c156024094140c901c04480100d20a01d4484140d400341e0140c0d50000a101c003100c19a43c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 122171052 1250 122169802 122169821
    0x3010c0e0f0312030604090f05031306090608060901060e01140d0905010b0111190f0204090b150a0305070b0c0f06070c060510030302100f020c01060609091401050907050d061512 78
    0x1e841c440d403818510603183e104c01480c0b544241d5803080540c0400031800700380e1140641240c1100c1e16801c002010711001086409101d0100382c25080020304d842c8280d5865114800c0601107401c42d91911100f03603000d010191000341800540041c00701d0084481001d445600e03814100841c518817030f82000f900715400c00100a0420214417005c02d501c1000203069919a003511404801c6030f00d440c207000b110a0040c031002903029003801400303020300c2094040386000303142003017400340e48500703400c20000c0311801d03480024451340105208000c01ca03000300240c0b03802d41d10502900e0120007220b0100e8100343c002c551038000305444a0326041032041c0c5103d51580400702800044085040d03841c041e41c1c4044000ea00c282d01600c84013821801c1c1200d0b0181e0380302164042c000d12043c1e1300e802d00600000d202e030017480c00d81840c00d080f001450780f403034050324100c039805020807060351200c410842d034a0740401d0315103a10685a12000644103090f8011055001c0c071503403001c0e100240815a00260b6030b0303e52 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 122172302 1250 122171052 122171059
    0xf080105070c080a1704050c04060e07090e06060909040503040603060f0308040b0a030603200414040f020d3e0a0503030406200715020609010504030f140903010c0e0f 73
    0xc10410640d410024185581c1d4001c0b184a45900d80c1303440884460000107922110504200217100802074002000807440c20121428082251544500011098215020b000244040358100420030220401c0c1c0d80000700030340054034042c152000304030440e505440849440c1c0c00040c08100080e4035201d440f010f40442c404101e040c80c81c540319003482d8015401100101c1c0e100043c51800d2500980c41a8015a80800c032022840050120060318681e00303003060780130f1401d0000d00b11401c402950f8144c85650300102072140a002e40d002e00c00d00d00d00440045500a142644400d00d000f0302c40000d00410341001403568440280e45500411402c010910380e0041600c945c05200903074000c800c1d035044e04c03100d01c3c1503462200c1b115400006071055031210011402401408616101d40140c20200e0000b541c0852b807007500c420038070900b00c603c121400380000b000383c1014048180704866605500d845001100d082c4240000040e08444100d1510400b00703a0f86803aa420504220440c01c00d10081207 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 122173552 1250 122172302 122172311
    0x809190608010303050a26010602121303030e0303070507080a030f03020703020c060d0f09150506120c0603060a03050105070e2b06090804030506040b0604110405060a030905070b0a03060f0801 84
    0x304001d41641e2040c000142888004101041c0303041c45002e004801d40300c03002c41c20000d0190090004003210080c040d031310040c041c0d4191828280816030494508841d0044450030070303840c64500b20b408045030105180d042c0000c00002020a9080242e034000d40030300009001c030f04500303250280601050b06108822301d8018000032010a4011492f00011282030307400d40c0d620300d042601c120041c0f122643c0f9510003407078003012102340b004190120b903056801c0300e8100025141e034001c0150500110b0070b0b10b809503011b04044099410010051074000c2005005503008545a0380d54074207440c421241d0f180000d514001030b00b17442c90718092010b418108c00e0000d1551000c40d031582600c0604c00400903100c1500c909031801080050411a002035030000d040d03600906180c45c03c0e48542c2c80581383c0e144540d0501c0c020746100c0421404440c1140c600034005442c2c00ca018206401a0040c120b0980f03c0e401600000610070f128840184507061403035a00040c180d050101144445600d40c01248091381352 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 122174802 1250 122173552 122173559
    0x17090303040f020102030405030d020303101a030a0c0c020604080a05100c0c11030f03030106020a05010c02010b06040501110703020303181e1804150204060306080d1d0d020409020904080919 83
    0x220031290410740041c0302600012030303400180d00d148280c2c0d000c10b030580310b2038034041981c2e036010000d10301078002c002d00701510326926403460901d0454010840000201000811002002503200804000080c14a20350b0120389400081341e60304107078080c21507030300136034032640170001c06100b54280070300200c1041001c1009200010004e0b05e040c0300081100f0514004402c0070380c0c0c20403041c0c41100482e002c4030b0b078170340c1c40701d1000f502c81881d160f04035120b41c03e0901a0000380d006002d084440d0714003800c0e83d03090920301401100c2400011000d00e007207005011002c00543c4090006058060803803800048000c2d98200b44110007800368034071100c140c942c82c50704400303648461040e114600c040d031f0111141e865505100901030281044488614400034001410a41503080a4201d4002c0700598500202034601640c0381400702400d43c030b00c0e289003041e94105180200d91461518005000040c0058050740401d0741050151800d90340e940c00840d601060385006c00d01300c600c0220b65910300d41d000c0c0c80c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 122176052 1250 122174802 122174821
    0x3060504050f0c0a0c0503090604140a08010e06062107060201051b03060a030b070915020a0c09020a08061c020303040308040306060663050103020f07080708130806010617 75
    0x6000f48034800c0140704026541440030800546d1200e1400034101e62b51603661706051050002102c0005025455021000400c80010311841400010840240c00c20750b440104100b0a04034010116485c1c01c150082131051200400610b805009160000102400c10b2111065628040c044900b8141010410400952543c80400e01181e50090182400761a8a0350540308415550040040d00103008100c202c0c40382c0c0054201c0752103003d44450060b407500d0310815010380c8a8150040e0204100401140141c1003c0c0c202540304000c0c001110308902d801d60000b0f08540c01903000f56030a05010a050080c400369100b0a00201031034100303881802c030203500361680c5d418456050000041c000520484403404144202002e604601c218518403102c0c0700c0114180501e00f900040f411024100410103500900c21102c921008403613050078081d0507641c0500c1588104000c985c455014400c0c00012400100fa00b0003400c10000908459030411200800401c030804480362014106028000c1101 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 122177302 1250 122176052 122176057
    0x71223060619080703060207031e05180901030308150103020d060e1005010302040e0408071505010b0705010c030c020327090c0c06100e011503060810020406080115090b0d090c030303060504050f0c 86
    0x1b60700413000340c1c03203038010b0900303030f80c0803e60b031002c3e558500c11800d00860240d44503000300354900c119640c01080c0b031070000600030007a50900004001c00c14250104241c6e090040700b03614004014900945441309404008040d0340d11503000907130404e5560207200104e001000103030003500080c641142010710301040300210f01400fa002421486000880805002240541070041d0b1031114051001e969140d10311820303039010b8074094400d94600f1203907000d01c0b48a800f40310401d1455500441c10149080c1c402416075201917420445203000d490702c0109038840c004c201e0721a050140c0d8040e122022841e50341e0900c2d00003404862400300032441413142060411165042d103100212002c2101e2000340190000c14080d0070202a922130701384170344600b80c2c1e51780081c0195100c0d03a41e9407000342d0b40c030307006450040d0801c0408004a0390910051110300200d80c09000c48201c001d0700854611400d448944031481d10341c0041d000a91510018007141c01d041c0102e64000d409a0644d10091900b40030150150 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 122178552 1250 122177302 122177309
    0x230c120a1119030803191b0203190917210c0d0e0622080d08090316030c150501030611070c0501140f0316110d020712230606190807 58
    0x202c2c00c540c1e080440c0702d460002200a036900030041681c80c1400d85c00070900c900000800e0348410b003802016240c0300705080701c034611174a80307800a5081c44c4504070340340200480392443c50100b1440110001d812100c03a01920500c10704200900140c001d14580006040001c0d415034420341004c0007481c0c1c0314580050690380300b00b1285003402039015040c002480e03911809200b600d60a0810000c1e0f80324803800c030030200444004104443e02101500c00c20f880f090400c503000300c40d80d003091111036001c2000204a48181c1c0c460700c0c040c001a4681d584848226600d1002d40c1c0c4516070303403801442000a41d101c1c401d10700c0c03208281c003410010709640310000d1050f02d001c0c0504210144044100203401d020a94884175012000c0319100e190200c00003c41d94a12440c060008081001c240c81001021070040741210182c0d02070000300f1708200c500070454800c01c02c12100f62415240c00742c0249262900006001c1414000d4451410103904010754014003180c03a0221006c01001003042000000d0080100d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 122179802 1250 122178552 122178559
    0x11d1606090501050f0705100b04061505070605060301063303111c11040315050f0f01090b0d0204180303060b0a02030d050a020f0a0807120b061204230c120a11 70
    0x140c5001c400c1c884a54011b21134014400e10909010460300003043d0050045440161410040c42e503889011403220051070003404081042044200041111608402d9000b0b2003c2d00100300340755a800f80c040c0801400d4041c42c203955148a80000702010311480401410040c50140804505090302d01901c0c45400254035a1000d000d40a59403202c86030002d1101c0710503170440c41d8456641e801c201d034400c42c00c2c07110300c0c08240c40c082c00600413030729621040d13000f601745060964450b030030640c80c00010a80400a2a8003210310003003107005a89a00034002c681c0c06c0c0c0701c00b44400303d02c140740140c00e80395030b508410312001080c000d0381b242c103a001007903804c440254032010541e51a8056001c00912920030180c03004c140c00507008a2054009903441d001c1c102c69611030a0742500c242040c0201c8403074016080d40154100b045905014003040c0c8950072500410940781940001d0030840c0c90070540200c80c83e0740b900042d52006240c41c04400401f1304180e00805400003c0345941c58070414548845094403 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 122181052 1250 122179802 122179807
    0xf0c1e0b0d0c091a090a0815190b03030301030f020f040501030b0a02090d1505040309080a0f06020901170f1608040b0601270f0f060309050a02060a11011d160609050105 74
    0x40540c4101d030144014424000018a90130051018079026406a5103075406041e0103900003455120004202d00a00c174006419110b9407190b180c005110084801c0100c101a10b50000c08102d0f40d05000650003548111006e144818503072040c070404c1d644e1a10594899458840100003146024003c180c0c0708030011030040c0d0f00c46490f0b0018860f4900164003600f8501d003030b013044148554582c0844d004500940300d845d030460703460b0719040d61000c80100007000340109000180c0000d5494018148546050401d80c0020800300301e4007098100880d085100c5e41240c80034003441220700001c400146c0000d00e003515840c03810307450390000700d60301030060307410042d85c0140101201c0121005000541c01c1d035076006507081d07480111840c01d032424000d040003160400c0c00080c0c098000d101c2c103080103a000c0080d000380c04490f001c01a49800c40d560113000e02ca540c4c0c441540c0742100380308011030300b441031400801c40000766000d5480c025001003108500d41c0107560034003001d50032640440484200746007130399 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 122182302 1250 122181052 122181071
    0xc030610052106041d0303180a03050409110c06070915050a0e19030503070c1d0f0414010e07060216050901080a11030109020d0302061506030c04060e0301090f0c1e0b0d 74
    0x14000c14a040b80340c0b1701c0c0000d080f03940c0c606110101c015401b50072040910320900d20804000703602c540810310018040f41c41040100182e410b103400c4041d6a51644940da4241400485220b040c15000c0311900b00003401080240203194000506c0405145c90b403402d1424890081c00290410910301346091107200e1103509800c804601031040d4001e507520505032510303040d8600c2c2100d00b0090900480c0004003200915040500e9904000752045800341c6880c0c14945558440c140186640302c1e44a01554a401a051001e5020810301c03005080660044c0549040700020a20f4115241c22881c8181740e02401048041c100150311550b02e60003140c0c4051604242001074010001d1680003500400e0080c000000d040c0c011501074400c42c185003803200b00c0d0500303904101c0c01d40b200b10744404c01d55500b4017007400340300c1c42002250140c4401800024008466031160070a01090741c5044a442c11616003d10803500030130748000c0440341912103954680d090100540d0180100049000819513910302e00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 122183552 1250 122182302 122182309
    0x109090e03070c0f080705030a02090402060c0c0303040f081608070e07030906050f011d0606190c0f060c110703081602220f0b0306010509061203120c030610052106 72
    0x1030341c1032580040f440300f00959800b520309160066120f941072500844800103804c0c100810408041355005100c000f442e500caa0070800035400000080c0d03031601ca9400d80e48844e0f281040104050810b0703101d0200d07443d14140c1c629180210010b8206018005004100405c0100003071080c02c1d9035070281c100303190359100c0750200c0042081000c05482c040c00c00c0284540f01850380c0005050300c9111942c0310081020740690000d038001900c417150050010849641c004103101c485185160052401c81885c11440e1204c400c850301c582426201e00d43d81b2840c80c180e032a000082c010b440c08581d406440e120b442c60310340360124061082030003184101400715904559508483c0c042c4a400184400c01d49202e010864004191000c1c0250300c0c14940142901a4603000521134101c900082c0000400e55079803081c421000510402c0c40700500c0140042c1419880303034007000d41701d5010011240d03282c4c178042c0100440f900303007001c4030307400d01c401003108400400c42c010a004132070301c0d9241000e00940f29480032 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 122184802 1250 122183552 122183557
    0xf1c270c0b0f0d020715050705090a170f010203150406080a15022505010506010e0f09060d0f02060703030b01090905040b06010305070e0d0b0604050c0903100f090f03080402040e010b0109090e03 85
    0x1070401344000740000c10040c1107401c01d4110210700400300a642d540038016a91880b900d04126072280440400f000b0792984601074100402e6104c05507400444090380c902d003640c1040e01e5a200d140d0204d140805c5504081c03003420020710b1040700600690420351280342244403001141c5980c01d800192024071254030302d0b4071000858080011741414642400d11724001c11b4241c0d9014001800c41c107051004c3d103803030130a410300386100900540844e1030300e404208640d400400121228a08400300714096580c601c0030b0304549000307490104003910148001024804950400d0030014a010700b80804034040440069102000f82400151612101700580c0c508202d05807141c3c0c45020000480c080240c151415030040400391402e104948031451001b084c1d0080703010a0307170554031881160011145e01d4000001c90f4101c0000000c0c180044c0d1101c2013020314004040d00070036000001c1c041141068032909941c0407610008105210b00345c00001c0c00712500344100c446a070f441740f0000b071510206104 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 122186052 1250 122184802 122184817
    0x2107050a03050604030f0207050f01081e0c04030b07082511070807060e060412030c14120705060601232206180e0106080c0f1c270c0b0f 60
    0xc185215a24a821030b03455804640440c0040e141010303042c4918000924102600c00c01081d00018446d01c3e0011100100001e00b00815908940303904113581080c030306c0340d60260f052092466500e07402c60900c400d0703180340607245004205104040021610416900100301280030f06c11030302a0f02c0c0184210380d003000d045510b000500640d140007500345000a180c200302c0d40981c4440d0070301c0f0600380402949000c2ea22810204411401d05000040d01c5401c00440d0288250800310800c100c0c85007580c80d114142202c1c0d41184e80004854091020402003160300071024a0040104040c000f1007480e8180d1101c403d0200c1c46001c10340304841c005a800382c0d0042125960701e80b2520342d851400a0003200c906003e20f1a00706484004a00d0700124110b06040e990320703450325031380c0f078642640801c42d60b8002001910850010300c50400480b640d840c554491f41880c05001c80d10500d00a08a55100c0d5410502c088100307a00780d1103c00038008021140072949400401515400b510064082900c40c1c1c10 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 122187302 1250 122186052 122186059
    0x1207020603150d021009080c01020309060d0c0c052a091006081503060a060e0705040b0a08041a0f060910051e0a0e090f060f07021b01030209060a111002030402210705 73
    0x440c02c2c0100c42d440003240302101c5501c0d00708d50420f00380e28016030310b912881421980207881009200c10740e03034640e00044201c410600d05030b2020f408944a4501f80401e84010681500030b51240007009400c0c084042441d080c03ca520b000030341000d0024a0101c20140300795014400000005180600b6114449401400203001c0d607000b031030700b81407001c000d2055001d800d001e81c0114020a428a22500a98041e40d46840c221440c10300c024500b0b491003c8010001c80307212112400c84044151182201070185a6650302e01a00713050600070401c051400610300c21b08109060020407003550361095074003880460708444242740310f0b800041a49520350b5041852107030050003d104a0003400942401d40b003007050b040d0303400c50300d41480104a0500507912030005034803091941c8042500480d90b080450301c1410014504552680440c070b044d0049400c54010810b512020340c030083c1c09100f80104ca50b406c1ca011495440c2c43d80c0054032008190108040b92034400030f66920421040028901420008 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 122188552 1250 122187302 122187319
    0x80106022113030b010e0901050c030103030c240509060105040b010e040207060e010908030406140601080402010f17010b04050f0303040f0b0313061805210d020a0509100504081207020603150d02 85
    0xd06041d513180d0001e2003407280143d040000540d25110601c60240520702101e40b0b00d1075170b4655101115040007a080540e40b00140660170035440c02245120603580c3e0108074040b50514019032400c3c14024144e00160046051180d4041c0aa907c40c1c55250704071006c071001138458659050003802050010010b038210f62902c0400e0041c000487c000d980f02d60300c2160180220504540d405904840644180c0d001c07417100c00108005601480580a03011041c3ca0301940b1344c0300607a00052035078030a0b8132072840807900040c10301035070504182c140d01140c002d4004520b000d14108541441600e40c4c401e07903403445404404104c6000310000d11100c21600441305120f01c00034101c3d040f80c411030181c001c950034485c55001444145404403100c0c110201100c0031401c2c2a0f0481c80800a13610011050040003020040c020055071005100c80c1450000e81d2101d4036181404460740c50009440701983d0506400e103c142c0c010317a43c1008070703640905100003450020000501141d0132240c40c1e48001d5100545 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 122189802 1250 122188552 122188559
    0x2d0203040b180a030f05120c0c060313020904030f0215160c0218040c06090e15040e0102070c0b0a080705040b0d0b0f030d030b0922020405070e030304180507080106022113 75
    0x1c102c01500c0d86c1c020800e8401d9080c180f60044424070401a10714070b103030002c0c40d4050b40ae141c40780141d50310510500500a85580d5940000e241340001c640443c081a040c2944d5082d00340d0410051800448405c1c01584609140ca612000002180092401c120400703040c41e046440e80a280d002e0321512550411407801d0038540b40c502001203008040025003110300c0040d079105200c0116001341c2070b2454060b0541fa078902444007520f0019000106590208162400213241452501c000c2280408003034039411100710007451880080d180104001080c07000344003003141d11041311020309101c400054111401c3c404900c840e081021250380c54003840d40602c85541e01a000a801d094080340d4840085da00e2440c0c80c5032007074490701c0208005082d512880f0050405030300c0700317820071100d080c500d113585481e0300060b00e198490340041446811a100c00001212640182c130b030012074500b0720036410341c103060000359107c81d1794100150746c441c5645190a030b8152102168245040c00c0012040c0c00c0c1c8 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 122191052 1250 122189802 122189813
    0x4030c05150a050a060509040b040c180204140103060815070210050f071101050c070303050a02070807051006120b040807031e021513020d0206030a0e0d2d0203040b180a03 75
    0x20300b1103010290b1810036002403c02c0380e8611a500940304000d00c5002d56807503580303c3d440d41040051003254881700c02c0b040801d21040850072004084000000580c7d90f60400e41d40300c0d0004403c0c0d0456061600300b0406022a00000c20320001c0e00440f92450b000d41d54808504038941031060051260641c5002c0c14400c1d10b20170340480c28071404154031012054881103040c14205d03102200e002c0e8281d4000c0c00b40d03000080c0302c1e4021b9900268030380c001505003202a110307050683d00920080302d10b0750081070020b842c50f041d801108014071000d602ca40d0f54074826101c05038000750050005002c142c00041400825000300c1500415071443d600110003071207078400180d43c4250309107040a1885408000883d0782032130710000c072519a40500381c911480038580c01c0c4511030b00080d1003244029103a0186802050080044410707010305541c9417002d1260703030b50102c0101d115044030704070144540e18000645030740000c21103003100c8c0c3c9440c8250f036812a8960708040d840034018926030040c10700a00006106 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 122192302 1250 122191052 122191093
    0x3051c06080c01020d0801090906060305030a08010614030403050a030902040e0a0c05120714060f0d05070e180601140a0201150b0408060f04110904020402070f061407050f04090504030c05 82
    0x150000101ca160091042c0160307a91031845c1094030024131144014000342d04150004200c0e241b00e20408030302a91070303039151401e58000c1e184003000107a4100040002c02d034041c00c0c5117031000243c181c0c81e00c1c505294070020102d100b8816814203064841c400c01c0115120f50b80066a48050481502c48610710303890000e0203900c291040700d01c0340303454018074405050003080c428200c540061040000b10310340010301449800c68010a006040c0c1031121441d45900381c040c032403185500ba590491824588410089003042584140c40d0400b400c40400c00340e40d0b080504c1b40d20392144402d50781d4131000f603414103e0160294808031001c09100e4040000c3c4102c500015200b590300000988002e0341d02c001c0c2a03030040204070307400f401e0164001c2504505044c55441541c0050005d40003624103129134076041070121591404440a5a940c00b0f0020f040c00d403c200c0a4120750145444d901d0105010352100c05401140150481144d4460100c0d040601074402c0700115a4410165400d4a80080d100450300 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 122193552 1250 122192302 122192309
    0x50a03030c0f020a30050319050f06120102040906080303100909030c0f0804230f031f020c070509130b0f0621100e0a020406050a0f05010c03051c06 65
    0x3428180e06074056800b81c0c1c00340750202c0040d0b000300a003900ea0f40b44d008504100c607600c0003d4400341001c030402c0b45400f908080e040091030319440d9503801d010700d49114102154070300003181e40c030707140038000d0140c2400c0c0c031103811000442e1041404000c102c410780c0280b0503603000b414201c0c5880340c0000d1004000c00035500c42c0c96200c0000c00640d17a201400d0096680c02140100010300706018038000901c503441c0007280c94081e01083d0300f003e80f0f66020031200301881170703040650014449001c1980c9070412080702021340075405091324032001c04c030307144c86000c489112905180e004108800c40d01020413080c3c1c01400000c10380061800c0c02d01c09180c03610341608041d943c94072041d0004080114891440d03008442c041d00c00b190350206407010b820b10540d500c0c074064450049030b10050035030019002e0b585040d5000c4010b001380040e280304000403180039600c030b280150940101000071a01000d510b0048900a082c0718a000f901d0b450111001c1c41a03042070781d980b50108810040b400866444030040c0d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 122194802 1250 122193552 122193557
    0x3030c1b18070503040503130f091d030a0309150f06031403041a03130b01030303052406090f15030a1a120606010e0a03021f020d05120c1804020304050a03 68
    0xd0314102051008010a4220203400d500d09440400e140600c14030003594400d0150098a040c640314182e901c411000780d0b030089000c01120780043c03080a51034812107200c407224480d207070846104001000e4407070140001d1103052603074a0320504140012044d0780b00308449803201c00c0003843d0480e20004000c1034540000d440c80c2c403900c10714000f00d640c00001c58045d1618900c40c502d0347c01e145689840f29a100801003540f0341c2d00b09061300001002d00e40c149010314401c0d1000328081c5031546024419007103602e051220340071403001a012a40300c2d60100d6409141c03d4030215288180c3c0c0001c24810b900c3c2d0740e05400301c0c200010401101c518160302204030444503845003882200160104000c00040c0d80c50350503c0e4100a0105079958001e20410443c0c900260504041c02d541e85c0003d0f039500302180200c0c2e000c81c0100303924510320350705106113200f030705c010b0408504080065102500a00008048004c03013400082d41030160ba241501c841044040108195600c2c585403901c00d460b9030080000710301 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 122196052 1250 122194802 122194843
    0xd0f03020c0f030309070f030b010b0f0405031b09090d120e01060e090c01080c0a0e0d030e0d080306030c010504030305070b19020406051e0306100c020d0609120809030703050d0903090503030c 84
    0x100c0d030380702d5902c2c07508903901314250009c00d03405d042103c0f0f4030364041c2401c58031400d8100000105514144050350400c85494021900c4101410a02010340c000030004440c0ba080441790026907500444581e404d001c1c42800012002419030405005042542041c00b24145079420084400c40001e240c1d510140282c0e103020060701c0b54044240f06e0f01030380304087c01103408180c250209051084020f0125030081c034040840b82c464101142c1c2502490030b00752040380c030000070000c180c101001078020350003082c46c200c1c1c50103107145c1b0018881c0c06036030740040105000c1e5000c21020486030b504a80c1400002c0004c5550740d03030b40d140180c0f5680c0041107c0d481194090b02a81c07040408038203480c030880000c0e2030100a1224580b08984134002c44004070f038000f00b841483c4010442c0c0d4442c0141640c480d00580c0b40c0c2501070400034281d11001040e00410760300800113480040d41c081c0c140e8050f00710740d00340410003104624041c0c034603426607007105c1e07003502c00407490585a0b0400561015650000d004c00320 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 122197302 1250 122196052 122196059
    0xc06020d03020301140d0213060b27010507150605031c020d09030c06030903020102160803010518061f0c02030610051509060304170f0a0207090506040b030d0f03020c0f03030907 78
    0x20160f01003480b411200d551032494030400c07800d244500003a110310080001c0b00180c00902c4500171222990455002d2040c007003440201d80b050100302d010341503009079010100748201000200f9a100d082c0c001806255002a01d00c2ea2035440d8100401901c4004c0c1696290f0124488402000f696007450100601c07440100c43c48003401030207040c09a9070040203003031905082c1541540a007002d071804a045650811000034401003d802d001c0041d442100115039a5240004012901e00310080410b547c0d051075047c0326090351003d100b12040700c04901c015003800700b440380c151030740e03d80c10070065094080c81c41080a084500310070300c800d0758022552034001d46940b91548542e4000d0400c00d580000040000c079010500c1804c403000d255041084151914881200310070700340e00450356180c05130b403000006108401c1c103806025400729083e1800c1000d0050400003d95a0255001c0e17001880b00c004011456240700313804a441002448080f960000c5803210b5260352a40225401c40841c001c508011 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 122198552 1250 122197302 122197307
    0x190806040204051e160212040b070b0609150f0f030f25030201020304170a0c08010e01051b190203130806010f0503070e07030506030109020405042004061802090d0f0c06020d 76
    0x10302c2150309a4842c0d1319607901c04003280d82c45c401401e000001c5d44a01401c9154000e0501d000b0f0001e07000c0300c051280c44003c18a0103051000002d00100d1140e440c4404110f600040d4803185c8e044401c04a03103001c140c1c246100450102c0d500c1034406070705401000840d82000c8000a1000b040301e0b41d0700170483c4070207400d501d680c0c1040c0e01804000d005800400040288090000300c00412084040590790000c0d8250303600c0d00b4041c0164407032103150751682c80800c5480000e1090aa110600c0d000c400300f02400303020707000c000e481018203d084c40c002010b200301415100300140c8080301e210320900d503692925410000c1e41c40c1000d1151103641c036542100842d02d0305000c610f66040f43c00030030310b99020b900c0c0c2030780c140c01500c40105241d42540d80ea5841c400580c1e118083c5501881c02080300001f40d00b0020000040c50386d8442d04680610f08040d010082d8041e54450500304071803400300140c54111405c0020001c550030030703018103b000c461070b43d0b03014000c2310503000d01111555000c42c2c040c5080c1e88001e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 122199802 1250 122198552 122198581
    0x4050f0f01051f080411030d110601060518060c011409010b031c020a0308180a20040c080127020d02030f1609050111030c0717011104051005070219080604020405 71
    0x31698220f558400312007a600030703a580c2d90003500c100880351400380701d600400d01c0d1112072415200041d00001440050b0801031004601504103454800d140120504444004516071080203015000003e00118800008c1d401648904c0280d2118065070410300d0440d4068180c1a40c2a48a4010340041700c25901d1641188400c2c0708a5401402c4d5000c00c0b9201030306c030444002c003211a0844a1420b9104040741403110341101d030b06c519502450240400c1403600c016107003400032401145090440381c442130b0401e44041c1100d8040c4028490440e4074401c018040e41d9503107041c03203900c1c0003090036440301c0030703940145210301c0300c000d0040038a541c0e0501d4078401940003d405400300d01084002d10072548192007040080700c0420480740340542203038860749845005e902020742c402c203028515002007007e024500107483c003411000d0a0600344000101c2c50162194a4018404005450003c64940580c018940a0709001c0251403681c1e40061365107a40d412a42248511300c0c0400140704040200d04 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 122201052 1250 122199802 122199829
    0x100b060403021c03020f01020705030a091e03080d06080709020d1808030a200d090c0902130909061112040201030f020a0e040c230904050a050702060a0b0103060504050f0f0105 77
    0x55101c50340c603010b1402203140c0c1540c03c158210300038030700740004140c3c0900060511a224200841e0399825402008010582c03d4010000d5002c1c90300b22242e948180030703090310a40707810003629503441040361495001452586c0c8040301500481000241807541039002e02003104010b002485404403010301092443e0790502e006003004414004909034071076651091181410f02c0340b40f5032201a041e003155060360000c1c841a0344003601e8038001c004200c1e11204d80f10003060340c907000350b0400c50340d9228110302c551079008014141d0782d43c0e0525014406a5001503181c043e000365517641c1c0d00036a400780004040c04440680c0840d0a000b84000e40d41482d108450303416445545200c400c0c903192040002620300b22a204e004c1000d51040d445200b00340051521514114151803951080a80c003400150f0313a008005840c00d500d86000c01042640200b031442c2e0110140c1030000310158200f0041e401004580c025907001b5180c042000304034403200200d02c4c068692561442c105030ba8503c1045600c0d0b03031052 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 122202302 1250 122201052 122201059
    0x5010903050a08160f05010b0a0503010b0f01031503060204180e0d0903020108041109071205060604060207210b0c07060e16171203130209011a07030807020f0f100b06040302 76
    0x868042c081030360fa60140c01d0411032184480d00c403144644030000c0318945001e055a20741d5481c4003600c214a816004400100401d400911400c040a800030341e5079075520390290305044d1214131003000107101d000c2c1c1002a50f4482011500c0d01d4442802d40d031110680c42240901da0300e030000701c569051000441f1034a001040d96449a800e0940d801160705440243c01200c40303000320b034150a0140d80b91220316201e040980d68180425807000c850b8802c4d640301418040c0030b05410003080c448a0303404502c900a490ba880c28078102c1980341c91000f041007050400c0039082030301c6002401540174980008101440c01001c0c14400c000d1103802c02d54541b410140c10203031003a20308604121800c5405c4520030101c1c1c40105a640014150b440340d040d50340125600e4070030512030050402145019440140900f001c1100b400c8d10321003074494144144a0b0200184c10300c242c0c0f00003e920b0a10030092600354601900589240c4070765413128942d911443d400c469102405c11009007820f042a4080c0d50403a031b00103 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 122203552 1250 122202302 122202313
    0xc07020a0306020c030c07081f0504050303040b0c0c0610030b0604020c0706080601050c0303010b1b0f0709020313050d08060411090303030105040f090b1305060709031208280f060501090305 83
    0x169144402980494910130715400140040b500449050240310002c0c401c01c4090018421062403255500d64a91004c05034a8581020b000120344000b0550768040d501400800254540c442070550601a4030042ea00c1c82c481c103c20840e00e8444841c065048920405883d42c0039212101000180d00450080c240c256100340810080d2520507009981c0000d81030600c1890140c082590f14110b5000f600542c035101c01c001101c2034641c0c440324507103100e10051400b425098051200980d01c0712400c0c4149800c4076008008101c20301200e2407841041a032000071149001c0208002610445c0e0441d01d00b4402ca20700700480070400700140450356105c100401540c950381c00d21003080010031140b10f0100c81030b5a9000001e002460a444a0703000b031880301688201241079107040343c5441c90081c07441d010406510001c000240c12005a40000ca00d58140500d0790783ea64803640041c52652403034101811104240300d021060070740e014070f4020344031500a028258407100107480c501e03854440180070b40d022 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 122204802 1250 122203552 122203559
    0x40b0a02060112050c0d11040204090209190303020303150604090204031103010f020406020a0f06060902030106021b0303120a05040f0803180106080106030b070c03030b0a0b0c0105100e06040b030307020306041a0c07020a 96
    0x3e8046c40f15544204551510112000045003ca801c08c0c3c01c800c16199000030040700c28a400301000d85449100e0341400f00144c10b5035002510382c000642070001004000c204102e9603950041034502900c030440741151903c0e501c0c1000141b0311500f43e840d034020b500e07000304501120424000c450a491440d0001d08002c80d0307030340c0c036000400c90031181a10055507076034022034001e040e0300080d802000154000c00792100000700e900c01c52900c0800341c600ca6030041050803840203100d8500e5a018000740e42c00a0380b07940d02c1c10141c000140ba08801071010200000b00502d1746110703075000e040204020020401a52100602400c03984c86c0d00000c0c05500c0c403040000c01c02e51041c103207c2072a03072180c50080b50014040c4045000c180e19500034100c0c0b01c0010400740b6996000f4440c0d03550016442e06904036040c0383c401c000d1131a00011b000c49000365100d5000d0042c6480c10402c1b10702c0503602030121040703482c050911040d0660342409100c0403002c524080740b0015420810345008a8004001e058250314 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 122206052 1250 122204802 122204809
    0x904020a0c0615081c050c010c1e08010810020c0c030106030302010c110606090604020f0c01090b18190305130e0f0103050c010c1e0f230c060438040b0a02060112050c 73
    0x502c105c1e0820410101301004800c2400c2c080c5003001409a26641d0392a0782028180c2420700300713649a4020000442c00410000710001403030b203044d0082100043c0d9030b030356090310141040f512221417901036081c62400000c2650540c003140101120342d4401216440e084a1030340c54060544841c2d81c000c00f001c001c92481d103001d038001c060040c1980c1c006850040f41c041864295055804113a44811070341c82000507076031a019601e915000500050320340a110260382440c0c0c1584c911010b0200b0802151000401c01c49410354000307801b40034a940260f20b811048c0400b0030030309000894582c096002680c0495006d400c0b810140d81d4445643c00c1a180713030898015600030b28050a4031499025111180829040c80429000c06048040c09ca07076000c0c1244002d20b00b102e840030750781c02608104410002426000b130700718072a222452840d03180001c13007196103002108000d5488440c002c0050001400c030204c000522000c0c2540c0c00383c0f81d903a0390b644c0701e0071340c0b985454001510303a801c0f42d82503c10031718 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 122207302 1250 122206052 122206093
    0x142a180c0405090408090103152303100231050303030106120b0d05010506010807080903040b070503040e10080105070201050c030a050a110a030c0905030f03040303140904020a0c061508 81
    0x164006181801d642e9400580302d090305440c02e4070840000182d81c0941c0d41c2c1405145016140b400c9000c00c3c45103049003590201045d052900e451044004008825a03001d10800f82142c0c0403160554444000000001800d0703d13092407002da4841000301900c0089000c4113107821034030002c0103941140e04e003040c107552103842002e00c0010319690340000c1d030350b0381d07a00003140d0740c3d19008400000d07080ca0002d0015000c0480600594140031130041040406800042110b0946000b070016a84a203e189056480c0d401260003203010900d201c000c20040c0a15141424200c44c4058024002a250224281e00702c9009030307010f480d030190030400180148407a810454101520304c10010700c02d00c222065008940040c00803900080d00c8510940c4450350007218240600001c40c0034180310104034240e180e40e171085100c0181809142c40500d500d101c0001d095859541c070161007599555030105d0010b04a0226101c105d400500d400404030109070710724240c400b9601840002d214002c200000e014541 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 122208552 1250 122207302 122207311
    0x203041502030403080403200a05061b031e091003021e0702010521060406090b09070f020a0503030a090309151713020a0b03060109050126040f142a18 66
    0x103102c10840040000d00c40002000218010b0b601c60181c0702035141034030440c101a800d81441951180824041c07942c414007110780041ca5002080c809045001c10070382140070f690710340218401310151600e401c0c000e0380001c041507001100c1301565441c49460076002c0b4021210025445012000384c40241c076a11300040c503400d40141440e9007481a5140c41550500c0d00100c504903078105102880b01d581810700500014001c0c001c018005500098041a800f04008000404210402d0342c44590740c1c0c000d0260304041608401034990f05d2820b80750140c094030402c1421000218001c0e80011403030085042e0f5142c0c16000d943d815035522005401c1b0042260240041140c0280e203011640180d96040c601c100030201c4999041d00c03403401400240000d9801c1e4030460600039003605c030140744404030f0607840410380746150b03040080c0c995042480c0741d00342c0c030300000380307030b20100080050200f00010b80484500800c40c0701901015070309c24a01d503021451a52250040f0103152074016a4a8200701c0c42d078807 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 122209802 1250 122208552 122208557
    0x3070317070c0506070c060e0c3703080c07050a0501210b031608070b070b0a0525020609070602070803040e15030a03081501090510080402130623040c02030415 70
    0xd00c103698070f80c107040c001c1c191940310101d094203d803002003100600440701c540007180080d200d20341d03500000ca4110f03035200200007a0465080d102100d5030303000d11542c222100d280b620b40780840703490345401c41d025480b03a102c0104038414444002403d1030801d90540070345c1c03c10b035500c1c0040441540420710300400c000704045059100c1c0c110b00000e0320100b2a115107280c0c1c9000f03000b180761502c00741c030b41011029040000504402c106003804244a0103000b42c00ca42d0b0414001039a80c0d68440500c0d41c810240000b071000e11140c00c81c22852a40024814000d08100090340e410030f981c0c039000d030303941d0002c3d1042c58000d8205010030400183c621640302e500511041c141500300750000700084c1000da03000b1084011400700e07820f002001c500c0064001d0030070800c2c201881258103041c0000c0f004808228075104008004001504540360b1110140040441400c24444240c803a03030021140810020950758401300c07200c10710745c1c0c2d24160141c0c0704400200c0d00031b14640342c20080000e112200000c003000a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 122211052 1250 122209802 122209817
    0x120221070c0233030105010203030613061a0702180f06040207060b190305071203021009030c1b05010f080c070b040503120405070f05010320030711060109050601110307031707 77
    0x140e100c4000c00c0c01c1420941c1100644024080d42c103030403480c0f00c074140c030403118000e10040c822640c00104070307600078904481004c0100241d10540001d40242d4000c41c43c903905212001c0400081d0354007804c261842120394411061820000400540b002c0702c99049401510010900c03a003040c2d4010542035005010105009480d10040b07001103922454105003441510010404c0c41801c0c016000a07041e44804c041c44110a07440c000d5071006081e4400100c42e42d64a1280c00301401603020704019a445182481c48080c107105d4180c11075114458140412654884001c000b84240703903541c401d00e000a0410304022980e200e03036844890041c0110b480d8803003000350018000d950150b00f44214031a000400f0b0907802c0c20300021046820f90702c211306050802c0b10606081040d20f1000250480c00b2416644030b50310117404442c8080a41421034160082c0c5002003061402504224401e44007038036150b4018010841d0140e0348d10541078050b00092507a80b0301401e9104141102d904040d040c5040325 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 122212302 1250 122211052 122211077
    0x7020a14060d0e0d110a050c01081806070c1209030206040902030a0608030f030109150803031605040f0b090306010b03130f030c0b07020109050601150e04050406020c03030c040612022107 82
    0x2011190034000f10034a0b41d020101c4800d4a903840854409a039500c00c0190818210300e50f00d1030752301c040108205040c40f0060300041d80f860300242c02305100940c44000c951b10383c02c2c0860081c2c00701b03a03803010039603420540313614407440306008100301d4040302e034080c22441c0b40034605000311009400282030b8014003034451303000146029081000d40b8201c0c014210a682d654075080419080341e04001d20035200c01c2060b003040142c1100841030300d07403000203a00c00104540c489403003181c4502c20b5800440fa006d0b18080d022407411822400f81080010580c2151f5540e43c842800c2c0c1e185001c1155282d40c2c140c0040e1054000070030725840340100ca482820000c9904e0943d03503c644196808881c04401070f9034030300c54241802070130081203005204c4100c1516854181a5004001810000c6128011a1198082010071a840e412030715141402c0050700d403203003086c000c0090554000d106d40c0000903c3c01444048072a1940300707c0c0d020504a2809108500c4034000624034804010215428020100d5510 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 122213552 1250 122212302 122212327
    0x80c01020f03070917010b01080703150e0a060306050a181419140d0c02010818030c100b1f0c0221100b010f081006110304031b090f0207020a1406 64
    0xe41c007444503501c03560020b50800d4000c85e007050f5107104405c0c0981c10640403440d0399800404144c0c118945203000b18003d454080050440003039035200548041190080140f000c1480d0300c20030070b60f8820340050180380c4030010b00109682c94021030450a12803c2d0300d40e8009152004a11034051003607041e82c0c20b034540d042c3d0303695020410800a07a02c05000840400006d04103102001540c0028207002d070840d03441c1c1d000207096003401400d6074001c0e409080d00ca041d045080040d6000c010700e110848820140d03480c240805015401c5030b29008000c10f5004000d18000f031808055503000e6681ea00c0100340d490f808104118802e0b20b442c01103000c0701d84118690032030900294041003051500800c0410070300b800103200d9850b54042d0b07010807a40380300b0b1100d6004582181401c4901d6454060420560400428154405c40c1d10050003107003c0c0c1125044000001a10002c80d4030701c03a01080302081141449060344210b6038000e500802404044c09031900411405040321b502500c0c080c1400340400c2a03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 122214802 1250 122213552 122213557
    0x71e02070302120a0b010b0a030f1a03070e01120303050c0d1404030917120901140309011509060b1209030c0f100f02040803030403030209062a1b030703080c01020f 72
    0x400060300308810610075030034a4644804800f620380020b040d040002d403100301c28254103000d040d140c94000104a0250341c403a4000703900358444c0c004104040c0c1d03040182e482000c49070101a40c02409407880018614810481c0d1030b04880d0801038194101040307680c21001070400134089a1919820300c00c2141a10843c81032071499444680424180c1c1050305000c5c00c2100c0d08d42c0702c0303d03d0200d04400420130544c081003c0465065a209203500d61b001000141d03109100032080128002011040111108054000b80100501d0413840c0007116292240b060a0710428000c0ca0705410041081d141e014113403030207080d48030221805990030103040c04003541c2800038404455038182e020700c021054031803d074814940c140c44607440c114502441c00250680340c0c0802400a000d041d4003241da00d030b0f42d48501e0102c507140d01d044900c1c5140e28120302020140c54a2125501700c061050340501c50902580880c101e14400008000740016450740d036901580c0d40c4240d44040680d502440592404940c5001 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 122216052 1250 122214802 122214857
    0xf081e0a02030a0509031801030e01020706180b0601030908030612101d0f0a0f0308040c0f0303030e060f060a17151005010215010506030414011b02030307030e060108120307 76
    0x3016960381028600c15040c0d6202400781c0159400400c40c2c10f00d01c00c0c842c500d85100794001c4c01c02050224500003454028011030300e000d4401ca043c90349480c10a83c90000c0c1900161181d4071840480c2c41e003400440c21101d1000c0001c00d1403204001180c228600105045c0310501d4280c215405180140d8408064a10181c1d1845e24280800c03030903404074609114404420641c032004110503c01500c80c41803040c252840507082c442010086800d011111040382e002c0c1813440c0b41a10703196540c0c6030050007807445500182e4180912030202d81c000c2c0409542c1da00030716006015000603401c2250900b07148040400f40c0c2c01d0f500c100003041076100000c6091522404101d8204002c5901c0c1000290410601040d040c1616a9000040c80b43da46c800007902c0d005600030703108001d00d0270070f04d108034014840c404890410344000c3c54404002039000004602c140c040e0ba5003070151020b40740c0e0031980c1c2d0400707001d9030880d03030000b1180c40c000541040c00741d5444040e9181210a5602450510034216007845 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 122217302 1250 122216052 122216071
    0x9020d0309060e370b130609090213090b030f0714030c060319050601210c030b0307060207090203040302190b09060c040501051603030e030a030204080601090207030f081e 75
    0x3400c010b00c81d0008a401d400030420740d5640c0516002d081d240300780240e148860300300781145440350544880740c00b12210250061009540e034400490320b451411803105d110300b000240014402052485007402964221440702c00300b0070340b190601c1c8052019100d4a86420340601c50001c541d451644100041c4008008401407a900320701c41c40207040c1000c0e03006442c1401503000f0410300c07140e00c94042c4d81d062002603080000406482d00030048070f078568034001c85010a83d0709460480c00d0a81c035406020040d50717989080000002c140c0616845010301c1c032a110243c0c102540070000c032015030700150351151003071059801000368101c0521000103004015529140003d04101000c0070421119400c0150106a54105403810000070b048e0301c6041421000c5007070040300c000415008ad0041404540090180c81d1241d6882000400940007072040075101e100381000050200801d00c00c40f6010381d0199956a18100c03032030400d460712140075140048405903d040c410051b40440c100900403c10f18 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 122218552 1250 122217302 122217317
    0xc0812040204150b0910080405190f080301060509030d0f02120304330c0306030f110307170a031403010303050a050c03070503030a0c020d09080d0315090504030e0307060201020f070b040609020d03 86
    0x8020b0107010406140396009010f05401844040307840000c032414480d040c840d0300c4003040d026251482c5405180300000b041c2d24cc004c800840d0980e0418007800102e14150100e480c1c03610001e4044841c4407484251001503001001e40d009800040001545d0140c021012030070921810280460080040191a540c11500c40075002d0003000500030106030b0341d03444c41c0501c08113045844103a801e800c0c3d203800412030340c81031032000c1c1152030504c881001042610305d090700318641141243c0d150680341e1011000100e4910081c0104c094000949040e00c0c0c040d030300c60342482003100c8240c7c0e0b030354084840040782d8802880240700241c001c00055101e5904913030041902141480b011b440c04071480d80134802e200200006110413500080c150101c0380c0303146400301d0701c0725092503021703281c0760940c000120b50b5040c6001c0000f455000180e040443e5420b0701110b00260340c0d0341c4124201e0241707101c050308401c5c08000c1e00300861030040c00c0039002406100300242070901075000480034180d000044001c180d20 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 122219802 1250 122218552 122218567
    0x209121623130504020a06030905030306040b030a0501050708150a0b09010e1507050312091f050604021e130e0c0403020d140303040f0209010f0605030f040614040602040905070c0812040204150b 85
    0x49046e002041756040511a58101c0d6554a84038000217140e14000c0d561500b800000b650108034064506030880004c222a0418140091000a0480d8072090f0401c104800c040142030200502e0100d400c8826910f05203005100111500080400c8156101e8041d0144902014035030004244491180001b565940468400d500044100808050f0503421140c80840016082c07c000001800c441c034001a903540c50b0b40000e0002d00035800c0c1e0000391a202482508504107501c014000c2600c0303082b8680b0380c5690390200f03a85000080b545100c040c4400d000c104011f00b0905c800c211100e1244141c861504205200076107182c004450594014070703580024000d41c1460f0301841e01511800014034801800d002029100e031001904800f038580043c00000c0601c200c0c2e5003c070980990902c1040001e0516041c540d0203500203000d0810300c24a490007140b82240150640c1c50503a500100030f50510b040d410010906030070042050f0303040f039121019515284250742444020340030312030407640c48444 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 122221052 1250 122219802 122219809
    0xa0b061e040807050a12110112062c060a0e04020312120a06080c1005030c07050303010e070806040c090510030b04060801020a020705030d08040f24020912162313050402 74
    0x400d580518040c017500c1c40700340107940d01722a2045003280c012800d9450082d11724012134502c0300d51110021514136008003c038049101203014101c0c140c002c1c0385c18079017040c0400003460400090b46c0840d84440341c94000c00000c02d48040300c5601500081c15100090400010b00c0c150303074400a1110400c07901c003410802201c6180c42000003400c06400148810b030010f10100750740146107461041071020102c0015110080301c5e00302c442c542c0d80401907a8880d42c3d035041b60300b00c1a2003516114049036203000020400e040602c10a04802c0c403580c0c40d03003031551900307051044602c8007203039910425844101d142c200d41c890f4011a0000c007181400141c0e1070548400080c141161600024483e0300142e403c5401140c1c0114401e40150b040742c10045001540d292404011200c03103203072076801d44030b20702c0c580020400760702401000005686a12000600b0b607038454951b4103600c481c2c182c4030701c00e1005000600b40502074200180611603030318600b400420008011034071b40410801070780e407a1000c020071801c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 122222302 1250 122221052 122221063
    0x6030606180501060504050f040905010608061e0603120901030212070f030c02070b09060a11070e010f1415090f03070803030709150203040b0a12020d0606091a030a0b061e0408 77
    0x41e00a1030030000e030750602030020000d20452052500c28410b03102c0c1221580e0b66503001c101d4855004000b0000e0942e41d040e0700c0d403900802c449038245225011030240c0c0d150fa104030010301c9010001e001e081c0c01d018019008900d80c00c00104281010303404c0c04610707140058840c003180070f901c1e1905c540c1d4030f50404020050980c0c2c20384078018110340043e6010403d03102c110003a01c4072424101c03056915841d05000c02c40c5d00294444007e0310a11a44100040a64140c0c0580b4162201c02040701c01c51a19403400c0c144407003001c800e0503040500301d000a0300c0170f42c455000d000511401440000c0300019080040d24162b4542c003d4200ca07040082800152900007006000030800240a861008164a00a5103d00940c440e103141d00100107080c024091045005400b40e0074840011502c40764400b400600034542030080d80d0104041c0f10000c40c0c121041c03006100b00c4c00341d003c8964a9944d640c11044040c02031415180d070000e0003400010404901d58174042c64009501180c0c50319640790000c120b1810 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 122223552 1250 122222302 122222339
    0x406050a140103020d172803090f03030b030705030f0312070207030c030f060b04060902090a0801111c060b0a0503071815030209030709020f0d1505030d110102090406030606 76
    0x141c541110207182507440a5018112601158a2803004001e824030030004201118a81c0034150000b0700174101d200d0f040450b00caa500c40d0700c41c60300d206569400603000c903508074201400b403001c1c042c1c000300043e1090700580b2038804058191540c181c0c0c2c1e8008280b070b2030401112500d844c2c10115060342586640e980c4103503c03850610041042034519296500c001c1d4182c00702074a1502490a011706000304c0d900400c039000c4028004125103542c407105c03100250020340c00148217400e503401c00030306003205000e042588030900010524080703102001d541b40304680c0510681c215100c0c130000820000b0103026224008194803220b07030b64078100100401c029a00011a610200414802e10180410031030702c1e03002d2940c900700141e40b100702c400001c0c0703006416486080c02ca8000070700b0050740c085503230250600340c1c4142024480010600410169404a030041070741503800210300c5c4036654410b506a00d4081da4000005281001c400003242c01e5603107035001a1801e07030701c496040150750341c0c44031414040b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 122224802 1250 122223552 122223571
    0x307180f0b0a0312080c09030d0e0301050f091c12020307090812030106021009060b09070f02010c0c020d060b0109030c1d0f0403090e060105090904060c030b01020d0806041d06040506040605 83
    0x142c2c1c0c195a90040701c0d1050103882c108200601000400142c50442142c416050040807601c0c030745a404d0b03008000819619480c0d000b5400d22001c40d00e041014403030a8000c020041c0908612622440140000d610700f000c010704100440084c0400e1113040d03c02580500703070540d214500d141c100401d162610200c1c0b26032180c40c11080004202865020a601409050f4190003080c00761042c10000e020301001034000303a0241102041c880c03125001036401020030002d070000c2c1720a200300796040e213103070403c150003030340051110003044001045544034209418050601142540e282e40b03907075810040d507800c0185c1c5010100409880303101401d00c1a41d21500c0c0248254103807600c2c3da402802104540b151050000001c0c0100c0c2c042e81c014816105280c0b00603120340d45616080c144500031706010800a4040303840c2c038a982070301d948040b03058240040183c407000c899481e88414880200454503520a10500036111100c011000b402842e001d00e00070002003113a801d05040034011034030007420100a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 122226052 1250 122224802 122224819
    0x50f010306110f09041a060a0314090a0c0315200a03060b0a051e0903010207030c060c02030301080304150912120909290d050609060106080106050304031d0307180f0b 73
    0x604a0f074000c403886280282c070041668048800e800c2d8003840b40e29640da9015074007103083d49919034036034015800c0000c07102c4e111a203034950f101d00d00c0c0c540c001c460028107031624035072041c808a0034040480200e10a400d9002800b000d4405000d404002d44103200102d500f000540651415454000e0001610a20b42d81d6450083c0f000300c041c11910070ba201031220341e040b00581e420008406826101200f40c040d00940d076445407490000e10004d0b10350b100f101e07594038100b1005042d031320000580e4140c82c0f100d4000e518040c00c01500180080861086400300042d01601045e140000300c14240e246101d117000b4006007219200140c00b80b1411b070050103030145840070580303502c8007001483c0d125554803101d0b00b82d25aa10700101c0c05d026061900030381148070b14010b000c6c5851001034101d04840341a03440644907602c0300400c50302880107983c0139000036003914a4418800f10000598041d40300181200c000030355404401640080019260741d0b0b040e41d414920070002a00e0042d0000c1c00011642c842 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 122227302 1250 122226052 122226067
    0x809061003020d021807051e030c0a080901090507060c121e0c0c03141509030c060f0c09130605130902060a1812060902012a150906050f01030611 64
    0x8044403144000303441000340c01034500c1907441d2800800d101d640140441d404070300e045c00010b801e540c4120f00300504410307541544a01c071106070041e42c1c0902211001c1d1450081644400c036501c000180000f0015584c0e450160000746e07007001088020032107a1900700030b0201a0405000d00250110380f1024004840e004184d151094a501e511488003030819001142d02c40c1018500b100380340c0c0000700b03000d410400086c141c20f00020050003440100b44c115449a8903a00e0b0541c50b40559480e0546a51200c0c021031001c21612498a0f070210b110701e4650704110064000513950507030840710b03900340e544e6000c09100d01d040c02c81e1040844610854140300082003540455454412044000c0070041da02e0f04d02c2c00d203040c10485400080101c240500454252418400d000b005c110703204a010911030f00c1101c0600c103625820301e101014180104551001944a003101c1d00404104c2000704c5513036000003c005500e80c0f04450082150065254480d070461404030220b6092101101e20003a09019a070b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 122228552 1250 122227302 122227321
    0x6090c030605180a020a1107170610120f0201260402100e060f0a050c030a02010e06010f0803030a0509280203060703090b0a0f02070209010b070201090b0a0504090504110907020706080906 82
    0x40d801244c12800180d80f0202a0341c11540e903e0882c0000102380200c1400241c260401c02d1071000060401090794000e4603130804182034948144a4107040c1c4ac03400c14036102081101c01e01c00c40703441c010304120180061690f01001b815200c004a00c40b400c20500170f200c194146440e45810400d843d0412000050fa610001550303030040615a20080d200003d5010089116405480c0e241d522030040b240c850755841c0010340a003011070548030491091074000034401d90880c449804883c41c09001d1403070b40d2030f242216009807000400750081803080089107000c86003c050203040c0d955a07401c0c00e42c04030384e1034410181000c80c0035003000c0406042683c0070380801c40c142d80c11a0000303d8400c0000b075110503030204002074050b100011754000c050000000c1c50003000f00041038002d100b640c80b45d04954480070364550030f00601c0300d441c001900502050002c0305280e4022904a8084e009244507911402d0015010440850b550001600700840c108805604104c200e500071700503002401e114501310180 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 122229802 1250 122228552 122228599
    0xc01020c061c06031205040812040f0e150a15110d050a0807170c0307022e0b12010e030a020d050717031305010c02070f09090228080106090c030605 65
    0x250b21007070400040c1681d0300341c80d99224000030f503030044201c211085504130180903500948101207132802900000301c02082d01c881250107a811840103d46c149080c002c1944003240020244c91201c0300d01609884603a03543d00c010001001c5028040c02d65003040003000789903641004c40000154407002c10b4480c10343c0c1003415100000001e14241034036640c1e02c181114840303004001c000038264150144031124207140025840742ca444d40031600c0090040c8070010907484031101c883ca00c88804008001d8005c1550010014840010044900e500c940d4480d2400c40342c040c488000c159200044180e501a0180b11918201810b0300b002420000d040e1034510301c0b40d5214001c003504a2000001a0200d40389101c10405142c0000c0204480725040c0b074060341d21a80c0d03004090218002600c001040945402455121940038054401940a0800c0908031510741c0f55068881440010b001c120403609200b03400051000b05408641401140340241c02c07035005070001c80c005c500318043c101048840940307 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 122231052 1250 122229802 122229817
    0x2d0f05010e010201091e2105030f01120c0b1605030c07030309050904080f0a120f0e060a06060e0f030a120206151806010806030c180f0c28050d020406110c01020c06 72
    0x181b030141d64080f45498051241744409028200e010322000d03041d860303840800756209200030380c88207174241d88810181a40311003e10008164800f020014007803840450040c0140d030700c645000a6071052140c2d04c0350300755000310a503c85260300c809002c00a05510010000c0100000e6840c00b009003802e8440b061544a00000307c00f03c88000900300c4a050700c243d04100c1d000840080812001c1c40020854019110140059406202c0c3c0000b2503a076250070b00ca010200c50054492000d481e501605014009200c6065903130325014104151000c00c1400c3c2c0c400301d50800e10342c081c00071480d0034820284039154050010340190100060b00c040a03602d081490782000003401c003200c440c0c7e04c140001c0c3c03a000504035265040aa4039666065106031149454004c0800c011903041d02d555028030720003a80a510108030b900c903d1107900d2546901c00c4441e1014a00051400c02e01e44010035410000307903803040e8420300c0094011801e01512140500a00704041c100344090718039030740003400240c0c8a005c0d940 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 122232302 1250 122231052 122231093
    0x170307030302210109140106030b03190213020a1e030c0804060b150c010204181b050f070506180114010501050418020715050402030f010b030303012d0f05010e01020109 74
    0x40d0316214904014030155080c40f442030010305943c1c40c0c40111000e40394a180c40300b20b1607030120000c54994041e010f003c0d44090094002e01744905101200b2043d0160a80c040e40c10480790891800201003d000901d00c00c4201d4642200035003a501c03200c03070450140d5150350200361a0045c0c8104083e0311050850b0044d41000010941c01210000103e01c007405003840f022040c000070790200348070f1043d00507001b184d00111031481c100d0490300860b0b040e22808034801c270300d00b00c3d1040c4824503a806000640448500510f607a81401c4641da04c040c030340700c0155a940c00400e0b5108801d4000c44090003031040c0c10600c1c24a140441d407404001030085c0c01180140c00459000c40030182d0003a1682d416640c0361500508110032035401000041c0080c04203880c01c0c4d000b80282d010550101405004241c440003001d0025403071a0b2800710310384500081c466050886802c0e0b41c0e01d1550a000c0c09244001400c8001c01c00c50084d0716080c005804420280300301415a41008600c5010070039000c185421030380c080 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 122233552 1250 122232302 122232307
    0x40303140c0307030e041b0305070207050a0e0105010305070c0b04050606151309021c060e07090b070807080702040b0d120207090b0307031514070504030606240c0c0b07050609010501170307030302 86
    0x180098080c00564100030805400400060547da6054202501071030854003900c4419855405000d0b01c0043e5000303101040b81483d004100c554480e0340225441003003803400c070003000c0c3c25580b510f510000988080d04d241d40410240803141c40d09150310412520202a0689070402e004400c1c819100d107880307421070041c0e000c10b07200144c101c1e0100206260400200c20030805403200700c1c0c00801d203026148000056114500443c84140c0322044480e07480c5c01c1119141070548956aa1200c2d5014010498105e5100c64220406403521203401215910034002800110346d040402454402540c4c4021541810001901d9550710042800d1082c0d81d04481c5800c0700000361011030001d0940c15204040588050b0104005664400050419a4070651017801019a5038062290410301070484075000d500a40655030740c0350140304903100750344c81250049103c0c0d507510060700598000c120180c400b90801010009143d00a128081c054080302214540c0100c5980c0300983e40d0080c48802400d06600 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 122234802 1250 122233552 122233577
    0x30606041a0a0b04080d1b0f170f0304050105101d06031c080114060f03010e09010905010204090b0a080d090b0a02030405030106030f020108060405040206180a030b0903040303140c030703 82
    0x9128a10884050001140d0b19a910075281e2aa8414840c0c2402800b41c907000041e01c038440c101c061500700340860740c002811919203980c80c02c0040c1e15400c503641c80e443d6100880010019010b045c0d5000071000303513512460541400e60030f58000070030000004601d0a801c1c0040e8690900b03800c055a60401800481da03601030210786045600041c18510000340144050030603484500641a10388040741b42090a202c10140035290040c29580740720144240014018103964001017540602c01d1000410002c405407241c50880e8403d0300003407030301034588940d00d1141c108052840010009900240100d204480300140000d1640c000d00e13400e0f0b82c0000d64107041321310800640300542030090003006030503924a8442d1b40030840350422800300c0c1c50f2000040c0a4034041c030446100f15000f410240ca096200140350361309a0f001c006042d44142045070100114a50030305180c805d14104008558440c11420003601034080200804030f158020816040700e030801105031420194181495400b0108 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 122236052 1250 122234802 122234831
    0x30712090204090b100902030108120a030213030c0f050f03060126010509062409060f0409080d0e1912031d0a0f03030e01020c070e040305070c03110a060503040203060604 75
    0x960303500195125040055034404c1c02041e80c03034203000d11130f100e4100d1851569042d540042e800248540b144030703086400f103600210906001022031005030b1800614050000804840441d0f4030b40003500c0940001000b4040a032031819008041c0004550f0f0303605c00c0d2341100000c0d58600050062101c400e120000c2d848866414804081e01c2c11001d44c000d001c1c0c3d24010007000e83d00c8008540c401a015142031007072074071a202004905500030b02500045040d981d0b4800e024039000f14905064010790342e1840400890b80710703c040c0000861848000c103003404c445c200c2900c0d040042d80740c80181c0c0c17594101d000004022400304036810b14142000300e001801d8500e640701c0844e01c00c07010030a40c0205090082001f80e00804104200d100b0f071020001e060410f8011800c034000d0074901141e903800407006000052001500075440303032091a040d80303054040c0c1d60303111074501594000c4a841c50100c8891310140340918005000c0c012a01e0001e095152980010342e503550090b040300e0042d992500510000c05c2d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 122237302 1250 122236052 122236061
    0x16051c0f021203070312020405030c190b0f031006020105010b030a0908160302030d0606230d06080a1a0f130b090c040e0a0209130305030103081b0a120320030712 71
    0x207030018071862a281212034403d840780e1180408030000340601d103910191440e240b003a14107803100a0000c10041305081c09104a141c619024581c00c54400c2c0d8001502c48000d6000703010200300182c4941c0c6908040000301780c81640c0ba0000700a5904240c01440101038920549a018198000c0441c0008450600e440700e407207203403034032800c0741da10104542c24140c0000c001c240700381180c40e0403c13240e5560380f0200c90101070780300740e0f1400003141c9280c0c1c1007800c0143d02030b0a48158482c800615541d481e100310b4030380350f0b0902c0111019a00d08117801c0820900d081c50035030100040100141904d4900344120b04141140030090a6006d11004500c603c581086254080000035004110029661702015030301d0003079507412889900d14000007001e0075540c42c10b05102680c10b071129407c590031551820010b810200800d00400e8072448541c2c8106001c1043c24001c0340120040d0012005207180242503d0701e00034520b0311502c4e160458040842044102d03540b00c0c803645030240c2114400b1450030050f0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 122238552 1250 122237302 122237333
    0x30618070506041a03041b09090b090c0102060a0e010b04050103030e030d08070e0111030c0d121d0a0b18101d0102090d0209060109050a080d02060610020304090b0609040c030e16051c 80
    0x4103c0e010010610508c7c80e401142010300603c06040a60f8641d00da941c0e5503c1580006801a0401e42c0881d903202c01507006040c00700c10395030012900380007110109086a000340d10075000078281d0400d00000c2e040502c1819482c08051406440b42d10341504050190b000c405046e0341000503032000d04c000b0007424000d880b109d011143c00d460a0440004001700640e895081915000f0b1401e41580519682d50306c42074440444c101c00380061070a2511481e06401d0000c104500c100d200907940b40c44c00c0800c1c8954503c2c460a490700280c1c20301085d890048a010355801e0014580c4108800c1c1c1c45543c5061080c400701764116600000366485500488000c405a8002d54004d0070b0b511003c5003180010070303003d00240346903003150141e45e82d00c0d0400030f01140300e10039000503030001c1000f0b000480042d000206100005400c051030007200d074020508a07140094104006036451003a4200c0c4041841198a0001f003a4040a099410503000500d08641e036109010040800340c220750801c105400c896001 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 122239802 1250 122238552 122238593
    0x403050c150105041104032604030209010e100609060e130e03070f15050403140d020f1c0b030309030717010b061606060504020f0d050a0902030618070506041a0304 72
    0x6028603074020340d4800c2080c05154815810314044840108150050b1000c0f80c1d00603810703082e000b070344c9103154110141c00710074003018000c00c220100c00368031114501707402405041030008103454089100f0350498002e8229500300f00055004100c031542c030103a03100c2c07905400c4808107603090101e9400707001441e1070005203400b4080460f0396424041c85040154140d802041c81c01d080c5005440b09a00b290022580100403170b0700c41907416280c0031848081c1031401c40540e001440c00c20b1905000205030000b8114112241c2096071010159900b40120030030f03400142d008508012040700003039156515402030110840c8140101d10b6124001d412901c11800003408041d030f9466040d984030645502544150b400c0342c10143c0000d010305080c1700700c414000784140081c0c1026131100014001d001c0c05001c28950301e4403280020056034042c801c0502480007003d154501e60164001642800d0440d80300d184603035024070007000301c0c022010000034050341c8a1201e03039032540c0700d00c1d102d00d10f00c1c008540a4038 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 122241052 1250 122239802 122239813
    0xd050d02030703110105101211060d0b0f030a030807050a0201060e0f090d08040312020703020a0204050a0204090b0409050703020f060c0105040602041a0c12130503060a0507081e0408030403050c 85
    0x45a60007000410185009a40340c04102840f04803050991300d0035241c4d5041d808103044104040c00e21512a9810b02c0d110b040c010303400000c0400040d072250044402144110381c3d80e0100c040c0307443d240700c078181024003e501270700a040083e14068000c0200134405001d00000040300b0381040d00c00c0d80035034040c0540c081c00c641941042c1044000a04046070030914500ca01c500c50b6aa06001d032400c1742c40b690303066940d011003c0c1c0d03008956001e90445801202544640b0400340010ba031280a00c1d4803a20010700010b03129072424a105003a42c1034488558000c030301e404802008610003269410a580c3c041d0f030920300d0041c0000100d071701032050300c0c4801615440c1c0010301c02001580e400a20031201c480c10302c0398038040040d403031031264841c00c03240c844503a01c000a0807090000e0140036249442b0a445079412040da078101090074124100c40c01101c0365942c000308600c003038101000c65000744060745101c0200d0f0045018003140800503001421505002c400602010b2140048400d007001c60300a544 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 122242302 1250 122241052 122241073
    0x3060a0e1504050a05072103051809070201090501050a020a0c1403040e0403030b090c210a0e030706020c07061b03050f07061a151c050402040e120d0f050106050403030e0d05 76
    0x41d10b13008159000c0740c0c2801041c2c030004002005009100c3c2e000c680c034030038045084095900340c85a0340040060148d81444140c03680241d541c8a510350300c40c14080d0000705030310341c2e02c2c036041c1d084810040403200090b00c140046003546900400440c011507000042d00107074044c942200c0d1840c0100d0740240302c005805010481019410341011f19007003c150760307843e103d48480c80101401d0140350ba50f0716948055010101900301c1146440b5040158482c00040807100f0642075402c50340700c280c0540b201c5400140d0100049820001c0c98024807061815618915030380c004150000304c144405420402e01007982203a01f1200000c4480c0c440c2e011004200703040c882a0100c10f2050803091161140c000048212a405803080c129521510900031100300c4c102200311a000400f800707041642c1017a505d0500305505803042101000070401c01285130b444481d142268002d440850a0000c404d5040200411080341c206054606590341400c0c0f034448042c2d08004a409030750030140141c031902c269017418 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 122243552 1250 122242302 122242313
    0x4062115120c08060106050f070c0806090102071104060521030909010f09050901050601120c0507020d081209010c0207050d030c0510020a02010b010809070e04140105150a060e03060a0e1504 83
    0x12040c42e00c1541241d1103582c0d00c0c1050703a250780007440345501084042205031052850240140803061280094450003512049003c5c40d1840c00c0342c140c582c44e940040c032501404800b4401c182c0070481198280300140c00e20020420000816081400f10b2400e4040d10034205014815600840c40150501103190f944406400e4105030341d21400d102d03581b41001051200c04103000301da11400d01a10381c4040c2024035015007004151074012441003207010f01c81c6600580d91580381061140c050311490361222108a01035500400180501c0641c1e071405400d450340640101d21401122001c80b0460a4060340341807c1d02c03101c6100344021f08078007034481d035200400d5440e4094084440194020000c503080c8600540d40710805880c1c00a513540b00140030440c50661100082d4880e00c55551502c100c00100009800c0d20b1007503034002204443c81d0030400c50740c00c0010200001300024a000504961b110001c079031070700805410200c901d0f4417030420100300d0504100c8841d1440720031048450714649802c01 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 122244802 1250 122243552 122243579
    0x16120807121b050c120d09030b0c070b181207030c031407120207030501051f030204022808040506060114160c120303050406050f060105040902090f0405010803030702010e0304062115 80
    0x3405d110310f20b5208103991040340010303846030b410400c0d281c1c82c11a504507100c844505a000300000050340e42008064001645e005041d40a41070800d0320f9103c2503c01c03041c150500190152a1a507510103200000101e50301c14003a03443c1035014100b114040540c1030080090f84a83d42001e8548100000c5003089240e0000b041421030b4003501c000c02c101c0d158001501ca8103180c6030013070a10607203a07140c00d10141ca020344c0103024507410385114040202c600c5809040c0701a00f81c0014011034040020801801000d001d0f49600090901e401680c0c080300e00318980c0c0c4da000c0c030307860500c140101596903003c020869003410050031014040e01042c10030b40c0340090280c102120101d4940d420130340441e24001125514500680f0161245230605003800c850030029004020b40b254441c18006290040740ca49210715406460781401855803403904c0d15003c0d096a00c6480c040c80c031076008001c20851399612401071130f60070144c80980b40444008803001005060300b20030020142080980004058056506 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 122246052 1250 122244802 122244823
    0x4120c023c0102030309070605090f0a12030809190f0212162102010507021905041406030c0a2303010f020c0706090b070f02061c06030516120807121b05 67
    0x80000203205400484e220702059a241b0010b40c050641803258a010720060324a47c0300181080e40c20f41e18210000e07442d11100c0c0d002c04980c040449486081c10752010106501071004401803414410082e084004580b1094010b460015540c03824800c566564000a20790350546045508050f1280c001c0d0620703100600c01c0c040c244004041d581c001100114801c0d00d86070301619a1800d261054080c4256600e0070344611009043c40c5501040c1c61345c0d50304c5030020305801401440c0c41032401c0c00506240c9001d16181620034480400700300030310581c550595075801c6841a039000c0d420310120110303014001446054200900100e04420f205100107621802ca0b000b50340c51000740b1365180d0100850b0301c110075025040050984001003d800e06500030601c010740c1c81402c4109018132007420b002c40d2a150000c07102a00848440d4480c4105070341c80c0800b03811003655035140d14141e035031a081507102d0302d0f800070f00040442c2000b101440c09150f0341030000e5810a0903600d014160728005071034120022 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 122247302 1250 122246052 122246149
    0x20102030717040503030c030919030e0405060d0b04120c0b09010506180103050709050705040305030c0a06060801060b0d050603011d03130905220602091c1401020304120c02 76
    0x1d81450b44030807a03641c0c140220b81050181d8a1503c45480407909a48000c0c1400c0580c441c040070f164540074101c0030601d07054000d030f440054145041d0100801d0f1040a0002c0780315841d044118000f1807900d0f00104d8119074800c03c8559041d54422059880b090000c9000e04146801002c00803c110706400c031a1080000301c5404c5400d0b40d2038010301c02010b00c01c1c0806052503020084c144030f030318042e85c0020b403c600d01e0704043d404c059490b6160391641c1e0248652624039080044c8050401100c1c0c081c140141100100034400039041c010090f055000740c4515040150300c4601080c0305803400e42c889402c495446e0421500a81c1e010740c240d030b40e940318680d0301094580c40c080c000b544080a100f140d0059031035804105080c1c15000c410207044041c1407054031880d90800c8105800e030703209840103600700a854a04c0c41c03105240d0030581004000040f48d0510759004004100003c0c0f0400003891072010f860a01904500480c0003141007403e400c621200b00c440ca4081061071101c11900501b40c1d1480b48 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 122248552 1250 122247302 122247317
    0xa0f060b090a090c0921080c031206060c0d27030b01030b060303070f0f06150f03140d09270501120219050a050d14062d0403050702040203150306070201020307 70
    0x4001500803a0703200200c2c640040c081c41c80c2880b030071000400d2004409012048181e40301140c7e290300300b0540c410450650b10f50300000e010300b00710702c403a0740e029403041007200c080782000c20404465032100c1d801e500c0401000442291810b900c0181d21600500440c0308101c00407050b104e1920b8280c000003800283c404010310800540207140010854201c40d503c03400320080c1420b580c0d00c0c08804000520308071041764840104810b884001c0a5010085c00b00448d10700d522841d6003041110820201c0e100e0a00d50030013035441c190a5003200a1004560046100c02044c042c0704106441440c00300250300e40780c0341042c0001584600000c80700501a0003117450445016401c90a071140f6000c2d40714403030b048002c54904001c586001803080000501aa028108a003e40200141050812280c2101a0403c100d0002002011449110907030f00c0310300c122011810325440107802380c05004030080c41a83c0000004500362a140300300221020054111509400d00c082c010b8081d4004862400009101 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 122249802 1250 122248552 122248559
    0x103061e030b0c040b04050f0609030d030c090f0311010c0309030804060302071401051b16050609150f0903090d150203040c080105071d0607020f13200715050a0f060b090a 75
    0x210100c40171100e00c4104d10340b5181c80c2c8806e00c44c6e460310440716558412424840318a158806100e0708020268986d00051100043c2c14064a04911608001c4007520144020700000782440c40c006203426090030064400e0310030745021200800c00350002849404089800a040e68040d00a00340440c8905016026112844002400c03240101d407951000000042c29842d590fa003040103001c1c0c40c0b01f00301050002c2d6842e0716150300d0101e0503a8841e09541c801c056551810300002d0382c2c580c20015114000303926041090602383d490045085452190480c104464100b064021480007a1101144199100d20309400c010100c08014441c0000c15400d0100043d0b4040c807030b8440b002c03005042d6100703070800d4004009000c0d103a00451401c03a0002905070501149036030300c00c04c8010010b5800740109541132140107690384a03204d440422810107050100b04002034201030114818501c009001035159113070160040648000320565400030f15280001c54000c606000070402c1442c1500c5085e01e00da075 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 122251052 1250 122249802 122249821
    0x2040504111903110d02040f09180203060106080703201306050c07030f1401050c0d0c020606131a060a0e040509030a05030c0d0905010f050a0509070807090b0103061e030b 75
    0x40003800340c680005a80c008403201d003e07500c00300d240300c1d0244a107070500ea44a01860100c1e4444c3d0800050141c0d01441000381c800700c0d01030850000903041c10245600055408030795210010b00032801403200e5030000941041c030030b6000c440c05d03011086070311581301100000448168001007000f501030840d0440031494a02500c11949a24101c0000706000c5e49952180d64407000c240104450030486880b1503200410240603240c000c500411100755140c0b11f2407602d001300c440701c0c83c450065403c02c0c0c0030406d07103560700058411003541c80d120201d0410741d5505c40e115030100806410f030340900c0216541c40802c0d8840c8440000d000150742c05c102d142c464004290703513409820b80840006008000180c14220804081c0032460340000001c544c40c04180d0b11142500c1c0642c0c3d10401490f9a4401c2101810441c0101c58000c1003001c0030f0501d507400c00c014191102214021030040300c3c1c0b55120403a45034440e500003070003031010700fa4511881e0111700c940180011a0f20007034940205081c0824003091 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 122252302 1250 122251052 122251057
    0x304060603230709090204022205011d0604030803150307080304060306090524060409050f0609070302192a050109030e0a0f03020f06070605091509010902061e090d060204050411 78
    0x10002c4000304819803500180740c0282524503400c0787c00c19004c1c0041c0004041c0c4000b405044c10a4090b020201030600f000140004840f083c828164800740c6035008440c0c4a04044400f81c0c0d8011401d60350301d41e141d501d180d801244414506800d0f102d14100043c007140d02002610607034010360b80a0108582d40d804520582e40213827201001c1c1c0d13070301204402d208403030351050500540000d0505c90400e680d82400c030007151000ca80c001e089000300003c0100510300591500da204040742411424181c010541ca01a525141984028400920724090f11010100c001c2c80301c003c40c0700c26400c000ca00c1c0e0701d042d40c041c1030f40360801c50104600320343d568218a082060403059402c40840040002e01d16020460500115503849801540402841c80410391a0003840d02c15900d85000b00521480714129400d4104001c0c0261903d91400b40c01c10010317038400c4d00301e5560341002d003844208030090303a520781603078801e030041c83c4d0340302e28800c40b0f03c4c041101c950098000c031801118200001e0012484180c03607031 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 122253552 1250 122252302 122252363
    0x1621051f1a0a09080601060804030201061d0403030b04110a0e0301360c0e0403050711031f09020a051008011d07120509010902040c1d04060f121103030304060603 71
    0x5048034000810403207503400644180d4040c1c0c034003040300c281d40e05100d6003820000c0e0401000035a4581c104410b054090013a807008000c0c440010032182e01901d4010780f41c15000d08014101502e070990a2520750b0342e42c11900304991103980d016500c014250f40506008201c19803a40207500300140d8951661700304409000d500c041105042035624101c4901060075001d0340200d955140c199008034002c40d0441c60340d4403451103502c0b03190f81c94036103062200b2146501400c442c483d500903200e581c00c0d01c1c00400c1020240f0442080403070301614510001d4040c070403541000b5049106d2000c0c80036001c0c2d00c030350f1081c1203941504d030307001c00c0b020102c10000c140c001c115a090b01043c06a5608030850156511955011241400005107a5180d1f070004003981e107460380140000e60007158044103100b1160144003141c00880b810050079107840907525106005100e00d00c0c52401c99004070061010051140071010300003000e880c0d0b68542031070004c1c01003075280429908003540000c180c21040f525217412000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 122254802 1250 122253552 122253569
    0xf070905010c08120f010e10050307290f03010e0106020c030606010f031d010c09060503041703040317010b0315091e0c040b040f080607050a081621051f 67
    0x19241440010344003400d41450481c0d034520304002c002c8801c4407080c6401d0190001242e082c2c42e55141c081e48104528002e450041076942c00d44081003d80c0d40011084211400e801035130326405205210010074044200032111402c1c000528641003000070300003181600c404805140580c0d80703410041381c2d03502c0301903074154055000001003071240d805010f0407980c1c070100707140200301900702540b0340400042c44502020740fa915040d048004e0b0307822084000203090b035850401c0c290714080c0ca95031268206c44000101103a0b0010100302410311458180c1102011603010750f815503940d50602d5603039031048074400d240c02c14880c2000801d2800115050240400854001038540d4910081c0c03041d02010b0328501032a0f42c1040300240002d15100a04010410345c020340124518100700d150528000070982010005c04101d800181c503080016103030010742403880b4242c07510b45071400340c83c0c004280c0d141c00340d80070304074501809030710141c1c1005100c1c0c02090786002011040c1c03030160b0944581800703890300 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 122256052 1250 122254802 122254817
    0xe07020703030509040608010906050f240405090312010b09041503080306040e010209120102030a0c080106200c1c03020d030605130203091216050c010f080105040b03150c0405090f07 80
    0x428480c40150100b1140108000307206e0380c1c0c0e114032900f102c1c0105000c80394180c503041004003084606c441c46500000c200c10500c0700205864106104624134205280710303640d01d0002c240b1011003001030b544614072140e010070355940c40e004562038542064030168829410100c0c0405580c6c2d600f50a0340c00c503a80306807468150703110001080090800085074100303d41d402e22103d45280d45101d416032151103504d00050f075a0800b1880141668900c0e451507060084040040100310f0b0701041071009026071119242d40381c1e02114040d42001403020f81a035205519107580d03180b0700c102060801600307200381c0840b500c13440c031060150159031061160030350040d000203800104406c80d40007164010040d03400c1d10b0706c03029103150b01c544d1078214601e010003c09040600501704582003000d103040715002d0a2291000c40d500d00014100341050046501903616080d16003c80c0c4c4041200108800445886019518112130000010380052103a20b00c00c1c285e0101246403059a5148940504082d55801c0d0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 122257302 1250 122256052 122256059
    0x60806010e01031419050105060304050c10021c110d0c02033f120705340b070e03010c170a021303120f030509011812020102040803040e0901060e070207 67
    0x110074151518a035414561180342150200c9885210720f885030359082080c0d01c1c081250b404034400c40c0c82c140c10541c041c12040080c000468000a040d03494044100c6128203030303d03200d00c0101e0410400712140e511140a07112203013035580c0c01296016600c100710044901002110804440254420001039059002070045440071698a6040c586416510031103c0c041c4071281501c0b05019007692900303c8480001c1410300143c40b105a40680292507486c2c59800e201c0c0506400c412000395840344095aa4540d000105120380c0c0401e5000403904004807011524200c0b0303000d00b100e5072881905100794a070a80c0e200e5058042c00d0520280780c5028980450b07503842001c060001c0d40013050010014084a038000002204c1c1040e2300304000e00341e942c980014040c800c01800383d40c0080c10645040c2d041210303070780d24400800f5800c240709410202d90780746141c2c070f81c1003030b80248142d422070212400001804188a10005005805001480020030460382d940c80b031804c000d034050b0380c00d50040e0003004040 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 122258552 1250 122257302 122257307
    0x6010219030f02011104080309011106010303080c1318050a0506120a0b10120503040939110f0c0906100203030a05040c0e07020d0e0a060f0503040f1208180706080601 73
    0x51000b08203000000b40034005000702d4049400c580d20010466000003002025540d1212a0381483d98a05000300495410755074081c003060001820001000070200b170300f40800c0542e1241c0e0004019003802c044901111002c50400303000c5c12100300b0151814000031884a040c03070241c1c3c03038184803140003601034440d059443c3c016154000e000d4040d1060502d1001c00d42c0002000c030f141155104000440d5034920b481002c0041e1001030381610f11503903043e02e070181d00202401c0805c0e040f015078a0346039061000da041c1075840ba440000d0342a01781c440d54240000e15140084c90302d0384d039441141c00340e10603074980040080c0c50708100520001608240003041410103550080e5401a200700f443c0340c00d0907287c00031400c0005045a103240145d003c0c0c180380305050313000904200204000d81b08928101e0a05201a004c80130504441c420020001700007028804404444c040103580994ac080b104180c4840c000c4c03140c60203642596001e1020700c05019070304800180c0ccc0b4100e4200d40c072100754541e1000d005 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 122259802 1250 122258552 122258567
    0x40e0f10080d2f0303010b040315060501120207021912050c03031305010c08070203010212010509060a03020a140a0302060c011b0503010609030b0612121804090c051203040b0a02010507080601021903 87
    0x1010039020001c07503c00e401520900196029007510398a56840d1461070403c452000501290110800c1c602241405640d13488810110203400340349000da80d40403d8800304810285072042c1c6043d0042904000c00c00b4100c2d20b5020502c42c3c051021244584802c3c010162280b041d0104101a115124008c101550040214645e0540110301c0e0f58104001a00428207a030700241d40410f91104603801840342d03261102240e038214109490002080342540e0108000985034000c41030031000d8400c0c1c404c0103503185064100956400b402594079400c0402c0000c1c0030700889402480240d04142e07503540d4141c4181e0649040b00d0996450b0b0804d189580c03581c03110030001400300c9802c0140e4110342503003408108070300000140401c450710341e20304203045c0f007403a48802c030f0f4142c40c86603081c13544800100d8404001101583c008645050380880298070441c6940b04035070003450842d00114812140c180c041d84101c1c41124562640704030f40d40d49100480c3c445c80e0810081c0d803581d842000700302c04603215000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 122261052 1250 122259802 122259857
    0x201060506090901211a010302010908030c0a060509010914030a030c050c0703170c06130c0503010204031a09030c060f07170c03150f120309040c080601120c05040e0f10080d 76
    0x21211000c3e030348903011b403581344050b8000901800b0004008550784407495400520300d0201031410702d1640182641c445007242400b62049840f0004108044001e510003804141e100d1502c0b07070a064160007154903504190450380100e46801c4408528601a03001c96604600000250400c1411075540140d081041c94007000003800500062184200c1044486d0140030500301c4c01179000380c60310740302994141c15044180280d005100c208001600d02c6268400019030302640c0d03040390303580140e1602d540518030540005d4030608081c4040e005000005a026161541d990804040002071a810401c0152524072051408000150001c4001070030003c443e0f030001c09007600c120030500000d0b9605014007003202c0582002809142c603203864490404400d000342015030483c600080081d00030b42050400380d030f204d500d038005c2481e82031052003203c014001c00d01d02d01c0c215082c241100349500310122054903c01034041c1001c240000002885000c405480da203488030200700502e041c3d0030414046 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 122262302 1250 122261052 122261099
    0x61d0613110d09050f010506030f0a03113d0903050f030709230315040c0302010513031b09231302030c060705010507120b0105090603041416060201060506090901 71
    0x2d6040d020140d00581c04681c3c0608020a40b080610702c00908603032002e0702441c880c1d4811003c1c964400804101704420365054101540300b02400005d00d801c090b101940c12510700010030160b111103005407071203692071205a2008405007544075041c4101c804200340038010070410300c0305800100b920801154440305034508038008694540780100544d07090060300c254001c15a042c0c0d003541c1002c03c6410510200c15003c18840e0910f6100c00c1240101d6001c06030400100003030400031007006c1c59640303000f194402000e03034010810400d441050480d500810006c241803240130484841c1510a001c58080004030351900b903180c45204403008140b0042c1280c040c01b0303145510990b580c6a5000e0490300d40a01300101c0d00e4035042d500201700b90040c814020103a440c1000c0121182da014003510442c10381625210f581e901e4a01380805280d10b5403046001c280b140c0318880188100001c122412100780d41c0003480810344800412041c0d025051020f6040b00652004000b040c06000318183c04030b0303646 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 122263552 1250 122262302 122262307
    0xf060801140301180605061003050417070f1203090309050301090507090e0c03030f07020909070f030f03030e0a03020a0201032d09140a0c0f06030227031f061d061311 73
    0x55049424100ba504c420b4170010b584104100b21400d04110705400c031411854100200c1c41e0a9a511441e010785e2100d0603011000424403100300320001442c45c81361034003c0c04141007281070340310040207422500c0c4204e00042e500d010004180c00e050180d018000e902c94054000d240c10660ba580003030030800500b807114461442d00781ca598806100a118012845a0b01a0758180c18014003484070005080d44080c1d0b4000001000f60951386042981903982c0080501240300e8203003400ca0252040010030b412500416620408264000a13210040ea100b030301c0c2408454100314a101104801d84c1d05a1100c00a51149000c14401c591044c0325a610a03072031482e8214004d0125442c3c6542014101c40c0f03240b55a07818031800d2441071075400244031515003946802e0f0242c6420f549603a90640e2100c08500d4005601d9440d642480401c0c2d0381241c0102116415031001c1007000500603601c03d540c11544100c410110304801e080b106442100080c00e0b07480007064030084d500040002a00080c600c42c0c06 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 122264802 1250 122263552 122263571
    0x4020406061403060f060415032408060106050d0f0c23030601020d0804050307050105090a0c09020304031202090a09021c0608010e070303120608030d0e010c0806150f04090905070f0f060801140301 86
    0x1c0b01c0307101d241c54230035503000400000609028000c04807540389510905030158003000905000220f07207040d1411440c04c151a60204082c1002408000441f6541d044c00d141200e01101e60015a1440841c51601000401c450105c2d1030511444141e07401c5006030410092100d840303006854071a045440756044038034002c1c00b5100d490841c1c6082e242d2010b01d4000d52131140c140005460f481c0003802180c40114910700345036030050905000804d03d005000c6c2c0119000c222940e40d0003c07407004040f0410705560b648180146032450f0321121016040c2c041c680140841e4081c4140301d20702c5101480c5008050981c00e5032010b58021000301c04004403540c41c0c500200302504e003400641929840c4182c00302c4c0003250a0415802d5030b040e07c501c00d04000c18001009000c3c1d80c0c0c1984440d0006076600c0141ea03858003519030f05020301c40d5800034001141401d100d5010030500095034401c88540d070240070840c0f512401d240d0503100d070314401c90001881140c0103201801d040c16101c0c10882c0c000703000150038080c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 122266052 1250 122264802 122264819
    0xc020a08010905060c030c090405130f05280b040b0603191a1501090303050a020109020411040f050907140a2006010f12020a0311010201110f0304020406061403060f0604 74
    0x525008009182d448101c90000c00804004240e0440340000b092811890aa050040c0501442c1c02c40f03403150384c9a03030105188100c00e03c040380046400200f0868a81c031103083c65641c2ea4408622250301200c0a250001d101c682044107943c580d071300c20440c101c6502e07281c4402d0320040c00644055414040d0b8009413541d0154800e80c06680c0c7d210740e82c22802401c1c44c044182405400605011900c407c0d4081d11100382ea201c2d140380d0a40f5030600b0b10a4944200400481c010810410004d401528101a10a0a44030a0080c10449580460ba41c280c9911541440b0a131041a00e11401103004020080380382e000d00c030b020f4041508646081c000180304d141d052950024108034034442d61300040e005101a110550f1843d01902c400e081d0703000341024a41c0810410280c030701c0f001d0001c0004100d42c030b4842e8400c0d042501740100c801030407502c461814940512a900556040b0b1040d8640000016540d0240d08800141c0685c001140e080d5500c210902040f80050030056521660800c8007103030707054 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 122267302 1250 122266052 122266069
    0x9050a0303030b031219140c0706020c03100b18090c04050f040605010512033010061107052b02120a020102011802090403050a050f1b100603210c02 65
    0x40c0681c0c0d001c18545000c2040c507040419005e00001d00b40403c203c0d01d010b0b0100f106403002200103601e0f006013480740c2101c020710300b80109605090341e0300a0040000d00302d503000804020783c00044040d1015440724500380800c8803080c0701c1c141e4211040102c0a1084a420b503801644482c0e100203503014002d480002400326001220300f094803442c15000d200510100348145805450b0540300d0740ba2400124024660f240141d00900080041001c0c84070709440d00310f21000f200d450540c00e482ca150600310100781c14120380d80201c000268010b46050003100c400030300d03030307040f284042e00c40280d80801500c07015040f60300b040c05040305020259480016202c0070b00c1110024440005401c44070b410384002429200381c1c107000180c0c03141c4070610308003603038951202c581c000f40e06080c4641d586560f480141c4482c00b07a5255040c0c1c12502207400c60005081c0015805082c003408152022145441c42080440f90140006003d4500b4bc41200166403102940078030007248038106141c441c1210b0f8001240724 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 122268552 1250 122267302 122267309
    0x60c0515010902030f090c0901120804030f05060420090601200706080a0b030102250311030415031803020c040c0c080c0115062118060507030b01080903090603060f0109050a 76
    0xf5400000c2100d0048071180d00d0350440f062002030701001d00c82800244003c4d006000b1052800700395a1540104000c01c4222002103038050411102c40f5418181a40c40c0d230000c0318142e444e2070104010880301114116501b465040043c400f00303164481000464404068036540308080340001c811004000c01081004014403440e9106c400c1407a0109114041e1818041c01034003981c0103008480444c032908000b000c100140a101401440d40c41c2012111081d402041209074000014046041135580c400741d07060108a89051102840104440040c40310301c82002c0d0040c1c1209040407206d00d00307a04180c15051280ca0421541090307502d5002d001c0d4070034011000960354072010031140c0140040d1560003403041c0e041c24114446c011401d400740032401070303880ca440c0c1c0d07032480310300d02c0712201d80c0c44062100d0b080942003240b032421500140062048520356030100d106440011800e22000084580030705000c1c01d03441c11900d503041844460250006098180b001000000c030b6181c49000050000303 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 122269802 1250 122268552 122268569
    0xf03090813050f0105070305090622030b071e0507140115080309040f150e0709090218010206010e060d080c010608030c1c0504050f0d02040b060a021f0507020601060c051501 76
    0x40b8641410410303144110308060341440018000100482d400c0000d5903080f0a0a80e1000e40d104144041c0c58250101c50300f100f4890703051311034080240f207014244580700e034200c2d845803c45003c130401130010408802c60070a0010b24104030766000521141201c04403032084a001040c4500e0460817288043c4040d0030841166002159040b070500d0b20340907203040c450202070104101d0b071105040540303401e003034000c01401b4aa101c0100e16510703c11100907009023801c0343d0840d11800c038100d0104240202902d9a0700500c503040000c0b802d060041c40c01400340e4402094116203007a6681e99405942001e00010019580c4d940d00240c044001c0c070060403a50150004ac00b00401038240d80e891014a103800c10b0100801880140b0107602c2c0c642d180100c0d03503021520342101d0301c11840050003419402c0d44642d040500415400c1e02c180e0001039a590307468684207940c544c49040c4040000300c903412640c0c240181d02030001040800c2c042c0104410090051081d243c0b55210a4000c02c4600d81c00c4c1d002289 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 122271052 1250 122269802 122269837
    0xc0302010e0d140c0301050c03160f0509030d0309060b030607050a0c050f0a05071a0309070506070f1a0a06170309040b1302030906060906030d02060f0a0b0904060f1113060f030908 79
    0xf528082c031440348d0140300246214203605005a0041d00e14a05d07614044c284114444007450550049064a45524005003158240251940010060450554112049400c09000b000700e8500410003911039205a56000e08000100004880e15288114203031658042c43c15035490615050000c115114018001003203000d2401411980e0b0100585000303c01c900b0610901c010944003062010444104942250b2900c8440c00c128045100741100204081441e8090340340f840041400944102e904c1a4100001980c41b0080100405281c0401045410401c80c002281ca415408040c80c1030018012600d40055042175208980c030680d071144840e84814204151841c0c001e8145d68000b00030f80203802d0040110718042d5480a014040f40b14003490440000e005c0c11084c2c3c010001e41a00400e00401c0f07052508010008080d200010002c590074a01010b9114071644211600e0342c0355071207000c0c2464908241150b00c02c0a84074918101038440c004d200120301c0b04005403566100c040b10611 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 122272302 1250 122271052 122271073
    0x60a050402070b180d210b06030414070902090a05060304030306030503070602041a0c031c0b030a140c04020702100804020103020d090b060f01020106060f2d0207060801050a030c0302010e0d14 84
    0x44c2d006030004010886521000c00542e2142d03020868403160000c410490004014902e05040604034a80d021500030f407002c0100010300c00d10851070300101850784243c41642d9215030504c0c4c1640705d04144280c2024030400200140c0c01c04d10300450b4001d0180c940060390940b25a0740c2801d55105030340035280346401003800d10403480200c0d00482d80ca540b4440043c07a010440c60071580342e025400c0314507903014150b580781d4196250341d0402c1407019802026288410070324130382060b05c4980d1071032900181c4030306540a550360901c1d1085505d00364009107003080c8084010310031950540010000c13810540c00340183c109088480c011001c3e0f10303100d00407003e001e01d072203402d00c5103041240806904583c108a02042180e4001100a80c866190716203440803860328000794032084401e50030b80c844881c3c1540740700541c03540460008151090369072080c038541d1342c0300c0400803410740901000c0c1000301203060400040d030048041d00c020303c502030100001800302e0f0300c4031060341854040c5144150003c031b2008 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 122273552 1250 122272302 122272321
    0x50a05150901050903071101030b0316061206051219030210110702091302012304030f0c0609151713060603080a120e061b0403080a03091505061503060a050402070b 72
    0xf903030142c1d01d00c0044d42020000d880324134030b00c3c1d40400040c3c14960745182d8401f060b14140041c3c51000401c04500300e00b1170b900c25008108402c0c80c15641e61252800034085031501d801c00b002050940e1000c014509031040e0204182d6680310b54400700d056104081c140380164106014258040e04108141034a4403194018850b1103400103110b850600460920480142e0304000004403c020b00780c00c4044100c503000c0c100a162040d9040900340c0048501c00c0704c2086404034501c000d480f01c5903680c1c038103550f881d00d4450401000e2400703e000301e07090588200c1132103801c1c15400d500c001107a01c44813841400362100340c00c0740c1c0c2075041914143d40002c0c00f05c58051b0000b03c420741149000300c040000f01c83c41d9920036198900686207804000c13807001c11000d1581b024040d0b4002e9900310422315514844100040c2c000d00200d0011186035861301200320500e1400c0c840c1c1740c42540060f01d54100c480d0380b640440700580c4001d020030340c01043c0400124035074841d417021340406841091811014200100300c0c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 122274802 1250 122273552 122273561
    0x111606080c090d1211030d020405011803050a080f0403140d021605180417040e0108060601031b0c03030e01020a0e0a080d050706270506061504050f010c050a05150901 73
    0x21030180801003081c0d91540d20f80f00009000d42d500403090820f0003c084900b1204040314403140f544034440424041d070318140e03a600400480b03800342c80790b59640382000d0403440c00310800c5c03001070500d8101b1009000803507181001480c400d4801c2c0c010702e14290300c0743d940108000840ca01491194030000036204400c0c5c0400044903200b002004040c9514230b01400906490a19500c03108110940d80c0810200250038980c0c10120600c0100709488545a84101c1500303c0b0901c68142107100707520104000c0e5009212303042441d440e410f045c0032840c0c0300c90f4040d81c45082c2c0d01c00481c02c160f9903004c02d1080003005e1001c0e124580c0d0540d5100074003200c0c03504103c07a1070f40740e0300802083d8200d10245900d464020b001c03140c0169000768042201400031540800030081c0380c140294001d240c2100104001003c20a188124070031a2045000391031074170b121009000c3d41c01040d8200403005040c41480d0302980c0d402502c01e01c1207007280c103c40c00035a5041c0c00c00c008503030301c0b402c400c2643c014403004981c00e00a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 122276052 1250 122274802 122274811
    0x70501020d0f050c0d09150203040b0709060e0a0e040302070e0a0e07090204060915031503080a1715060c03040306060b0405101b0303020c0c04110901030b0a050604060f11160608 78
    0x6080c003150502d41c40f01d0303005104100698004540e500030100800400910b100400942c151085462b07150500303080040d10012a541000101000b4010850714016542c8081c4404050440c94005041c0007103400720f044064016010740c490400000349600c403800c2800d21a810a0781c0201e0040e00b5a0250b910703041d8143c000c9541240140014070405a2203024002100c801d0402d908450a1821050380140f500001c0002c408025400103c140007440d07008020702e095640c0c9008a400040c00c203489840c0081d902c0340c487c1c40c121440c1100d24646440500001c0d0301206c03d8900e40f643ea60740315000c64425074040c052401c4081002c024038500710a50711003075000c500b48101c1d00100300f202a2881d14140000500349075020030404609241006a07820140300600208017100410548210035089120260b00182c20600702400c181000b00784141160800382501d81828149201510b944045000d0031003000301d102400d01484008102003a480e42444c1c401c13100d020304000005020090050 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 122277302 1250 122276052 122276081
    0xb010e010206060306070e0d0f050105040b0f0f04080306060c0f0a02031507050412142a030102071509020303130312080a18111c141501050919060b070501020d 70
    0x82080f5054a000c40c141c0d5102220b0303d0003006031134030203000612507400c05101620b07804840007141c00304001580a10700a40c003d60341811749603100c0b800303007900400440c0d030030780701ca20305c00081740020340ba0201440d0002d1006101900701120742d43d5092a0001c4c01801440303e40c4511205030035810140240d10440315240725034400e03850000405000c501c01c3c2d10681034021160301941040c0444080c4941e15890340174140d0300d4001d41003180048400310091400c0744006000d0702c141192a051080342c601aa0008210654090000c80c900051100b18400d0303070180010001c0d0011a80944880c0020318070807030700000544074900340107054010041c1051a410b01d0035800e141c03544900c00d0b142d03004c01e40c00301829500103003e2000c60b455103d401c0018002c0f16601316580c0800000703c0f10303808804400000c4441103200c4c00000d2050340028814150410707040408110a00e408a81558031080f0950b0041100703039565849040350703800000107603030a075030102d0061608900ea0241c0412a13440f41d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 122278552 1250 122277302 122277313
    0x509010b070209070c03020703021003050906090d0c020f0d02150c06060102032502040e0709020d14010f06050d060503060103110301050708070519020106050a0306020a0809060c09040902030f010509010b010e0102 93
    0x2e40c0410705858003c1d014a040c0700a038845442018800c2204c0030141d5805403076821201541c14000c1c015002c00d507580503040c09200c0c0040c1d100c4034001001c1a1910307030396a801c44003e103c9e800340a505032540403440d0300b010f11449114096100c0400ea01c0900f00301906003036841000c1d42490303080c01405070050341107410030091809400323803666107503001b030601c0300710041007100610006004180e2491418910b01490b4000190340100d40c0c045c140c2403121941c1070003019001441c40c0700d601e03400d0040d040c10041000d010f00c104c0e4807500150040d0558020001580c0d9183d4001a180000076801110751900142c1072030840e09003801a01d03044009400c04031541e040541000d40306005245400c01b021540b0522408070758400d4110200602003d82040a00361b00c9050481c0654400c0b0840d802044980021810745840000e100b8071605004a81c9803c003036000c0204809030074824000d0381c3c03600c9480b02860412400b8840c050156408600005d075146500001400882024403005d066401030b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 122279802 1250 122278552 122278567
    0x5010f0915030b0f0a0f080d0507170f12281b0f26062d041a06220603020c06161106090714060a021005070311070c0509010b 55
    0x400307540e5840000c060070003040001e80440411100d0446010301940643d41400020315000040700381420f1391a02010303140361081640d81030f5140d10070488020407082c1c0392540103424902d100041d2070248050311401d8034001c4c0130b46284140b04e105582030720b80110500c04040c91100086039915165201ba102485480000c0c100000c0b191914882182404841005200c1d25403141c10754142c1c03c140c1d07904070350301c0303226055050700881d2045072154003030344585400d41d440600f4020310103542e5400307000ca203100d00c0207041888080d00340039049100507400701018084542d02c1d000a001e00150345081800313040a00c610080603848194806006c1c1441001440d0881d0808140140d00094410002028400b101c03400c036540c020f020851044e82c01690180001480003007001822104400f80780314015901c102004003900c200103121000da800946120b4002c4240c0d04016072100c098240001c400409444030310f8246e0000e2700031249046604018441803030000c48007405403003000c8045007000312 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 122281052 1250 122279802 122279819
    0x6020a02040f06080109030504140303030906010b090d1505070905061303060506150a0c050705100801030615090c02030904050a20181f1d0102030d02090d0c08030405010f09 76
    0x1204019000d1601d40c01c19440071903143e0001030081161400030840c1d15400d0138010b03e02d812034010011401c0e80409615801d18000068900410206010b03000030f03441c4c1038505915921103640c02d60030910303407425000424a01001500c24130f40c40c0b007000c169441c1c0000001e20950140d0000d40c0700d1441400384030701488034040e2003c103032644110001156118600055440c0c140c1021610f050b0100269410a20b03174010940b044151040c81100c206544810070000c5040e0030f10704100c00100c0c0d9400410100f181e0350004807040e0004c4180e0064a901c501902040e00c2120f561940582d000203101d0380d00d41414401c2c0fa40c40f12450408025025850506484880c0d141030840144000031405a40f850750510308007a0f07600005000715548a00d104890441b4406030401d034001c6040310707040e290014007000140e241840160701940c41c00101b480100c000b900011541900811840765880c00500b08001400203403400364001d50b101c5140c240018403410341c00d07030340200f0042600003c0182d0700 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 122282302 1250 122281052 122281063
    0x307140117010b0f0d02040f091e020711010f03020702030d050408101107060b061603170c030906042a03080c0601060203191b021309020310020c06040f0c03050a0b0712060602 77
    0x2081100380c0e660321800780c844175029000700c0d0400303018244010340c00200ca03c0d1039072080240400d00f00c40d01881841d034484900c100c0c09640e801410740c60144200810640c800c0502c8405c0c80902c1c01c005051582c0c0c2d401280ca0010f03240b5a100215400080074001d94404102c04c280d1800800c0c2e050141008041c40e50059026410004100a84507466158035a0b601e4040d6a07083c1e025643e400036544507400c0041040c2a0180401c120000d4800810000c01c007030302c2203d00c100f041c81c000380000c3d101c030764821596061409082010500c120a0a00c1c0e02c0056604240107500590003d51030b090a8007030b450404106034450750955008000d5510003175082c0520004040b541c2c24038041c0200f10040f0300202c20040d4600070b500000d598264030320812940c2c40303550807a0080d02154000d00e181034405003284101c514514131a4041d60008001900315211500700c40c2c441c0f114180d01729501e071385151030049412000c441201103070040004055200716030100d1941161001c1c0110352800001a4603076 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 122283552 1250 122282302 122282317
    0x1140a06023d022d07170f0f070c0905010f0e2716080102250f050a050a140604080304060c110d0309061107050c0d030e0307140117010b 60
    0x1100d80d040a10341c0908002008459108400c4649003548820700c403400951040070003400b603000c0066440b4451a102084d400c85443e001c078828034140307454841501d0043c10000003101142c1c1005925102010366003c0e1035100d120310000e03501c451091030003400c0116a504030280b16407038600100300450b040c2c05a1000c5582c9903401071072a03140c034603030342210b602d0088100c2c80464005052061201000848082000c100507500440c60780b01e03034440d42070344280500788441800419140844443c492b02000300f041c071174510414022034503545d041c101285004251229084101c491060014011034403252042440c054a050f190940d51070310240009040948944e030746031035021440d4059410710b9a5500c00303008444600c00301c514014040c01155100300c0c0ca490818445494001e20f5806860146a10030050314503a00000103001c0d216080701310540070412a41c039607911036141440500060601900784145515122001401d0581803004102c402d04480c2c0042140385810350907294031 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 122284802 1250 122283552 122283583
    0xc0b0f042105040305151e07020c060c010f06120b01080a050613020d05100501080c0603150f06041205030d0507051908100f090b040e1b060f07140601140a0602 70
    0x800740c10004440c0c0303000ea0341000b00184a0f40b0052503c040e07100b4a401d1103105105c0c0c6200803007501203802011124151107180140e80080421201da1030002c028045143c00d4100008030410b20207662025110760380e200848444c54080160207100000f0907070f6014010a1340240340100700ca681c1c09a036400b00070225400c48031008805001c5580c2d03094014103294201c1c0840e0b41408803006020010102840780c00e0041c4200203189813a4107250041c2c0303200c0c4280b40e032003074000c4080c5400e0140c406c205500d00c81d0300410400c03020480b442407115890005000300021a1030303100c04031281044400c00f4080d0b0040c050103022855440040a504068440c0140b810155039280d40315000540c502c2a00f10140301c1150407008507281c807442d4813803c40080c00b2141844983c1000015a80741c0c0c120321500104a280702d2044078103420114014038618100c2c1000c1c5262039110b44842003903004841040b0f0302c64200c4001001107100b090026200b0b00300444541d4221407038200003035603421130311103070946 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 122286052 1250 122284802 122284853
    0x1080f070815060705060a0b0a05010c15020f03040f030f03110306131b0302070b0609060d060c020a060c020d09210605060d02120708060f0c04060813080a0c0b0f04 72
    0x106426010b80c81e5004030805070205488620f10b1400d0341d1681ca0440d0811040c86ca01700d810411407600f1450001144c0041e16543c81046541d140c1c401d200c6810403014035095001c1060304139101d01c05004510882c041c0f184040360800138500240b1000e480280c030020141008503e06a29118101b00e80d080001200e103060441c4200c25684050891f03a488003103000c902459224020f501500248041071188410000380c1c0d03100e50400031043c4c81514001d400068481419000585907480281c4020250044031440381c05551030b9010b943c407001a010060300705031111500c160b000381421020f0880040c02c64490704281514560444800e98003424040d12031003c5503154513040506100aa00500780700e0341c1c855001c0ca480c0d5501c030540f0425280d4864600043e80d42007a03110128000c0140a2005141c54a46038003200c000c40041c082145000704a01c00100103005000203004005c0c25407201a008a140d091690040308000d1140f41608154020032000880d0700d9140c0042170b000803c00304 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 122287302 1250 122286052 122286061
    0x2030708190603080d02070506060d0812090712030f0f090b0d0b0d15050402090f0403050304060e030c150603010c021902061c1112090c150901050f040e070e01080f0708 74
    0x8000e0702080d88064120140003e04040c0405d19400034080140074100300c0f41540c5510b800d0016aa0a40384040c2c02000180101ca8109a0b60602150041c0d0540704549110340c555558102c41108000304501059442d406040d0039a00714903511910907050901400c1070b03141c00d04421045c4907045090200d540d0313400b40385201c0e0307855008141c02c1d0782c1c1103d800140d100750490391a000340b1082d20180c0c45056440e0008102d1100903016034450f0b0360580d07480b42151101e549000103040c00160b19440e078081071114280018007085211031010420440d00d41c0360400c00b081c9400c684544400e001107400c0369411304000b113110b104552050754150381160b5911a00380610440c0b01d880394510b550305080c40c12100c0e1154000014080030000c081103800d60307407900d20316569951500400a074110690f1b14507039591402401c0500400c90040c10058502411300f24012010303401500650740c0610b02c5814050310710350140088032040000c7c02c0c00501400d0102c500c1d182600010024000c2002e03200005 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 122288552 1250 122287302 122287351
    0x180608070206071206271b120507140315090c090607140f0a0809100503090a0605061203040602061b040f0b030a020405130b13020f1e0417030c010f02030708 69
    0x8002482c40c0001c4d8000302d480d90f2414000650709868106d1414101005000702d82071010041848616503181d0007400044030714179002400001b17081e01c2c107004001c0b192030300d40c0c91080000c40c4201d01c504030000c140d03c412002c00c10344c01b01c041c00308000c1e86004d0014241d251241c0301160134070303074012545101c44507032030300300918010a0402082c1c1c0b50150742a6141000385602c094010820100c3e19100729500384030045078240400c40340c552141e404032000c0360200f17005030703c82d80d0428400f6241c81103002038200c50a10b1a8016070044006034030010400901500c040400702000600401c00341c0b42034501031b4000020469400744c0f0215041c0040403d0001c081541164010304001d402c42d41c802d149084404020540d1079049030280040c0381007490070072b10038421510380341241c048090030a0340c10b00304038401e40008618030036500400c010218401440145150461000c003001f165903190804007203080da0505c2c2c5d101c0b01003d0040c42403001c0c9541060320709900c411042111001c0c0705151a28 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 122289802 1250 122288552 122288561
    0xb030c072001020312100b040e01080114100e04060b0603190605030d05270409150c1e030b010c0b0a020304051506010206040b0603150705090a080a050705040b19061806080702060712 80
    0x7c6009124002800a0103030740c90b0507081d0407039203000c2c020040440703040196414041e080720300110f41890707481c040c880725030462091500075005460005285000c034011034400e52080c1c80c601d005505000c0c4998040d00140214009004103401800b10f1100521020700a402038002c0c10782002001d41003e4414102a2120024200000c5c0240102145402c0c01c1800194084504444031b0906004410f914000d0110f1205507007410750003012041d065500300c0007803440088036410825401c141c4004600034604003805110b49080040c1d40c0d09207450090303e0b04501c45111010030030040300308030b0181e030041500c1303038842c0d0407120401c03035640c030000007071309080e11861f110141c1c1c0c011009200d812a4003102400945c00c095582152041c0c03100701d079680d941412003000b40142c1c80014240020704050f01310005401002c1c004102c0c9405111350500178840d180c106000283c8499000d078410118040004000c120a04012400e4109020025180d41004140c14144081460450035000840d4007 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 122291052 1250 122289802 122289809
    0xc2518020412020f030f0d050417060405340902220806041e080d0603120c113318090402010e04090c09060e01050307062d0201060b030c07200102031210 67
    0x26031f003101404040c064240d800c5400741d101d90300d440a2a40e0b81305180040d80b0303801a41c00c00d00500e403500141448809000c258030900c44022510140701009443d1f0161440244c0b801403000b5854491030b0340744c2c103003503207800d14000d44100c01a0000c0102140c00f0418a400070780000c9244061408480f540c8040c021515004140d0340000804510307000c499800344064a11070701c0e035181c1c0d054441c00119040301020f40050405031001c04c00c0310ba1460300009291589d80010110f24070b160028054210001400c440c1521555000501810a000c0041011070380d0900311141545810150002440722046502003405195a201e0b036006010110750000010030311b100e824801d054031420b089501e51300030702c101c030300034480c040f800b1a04601a1501e000c201c40b28400714598280d00d1007038220310392001304056007035540c2c0301c00c04940f40003204001c40c842c0c003a64081c2950f50441d45815550900c51a0380f41220808c440c3c54400180e9012044404240303c009002079580c407084101840c01c2a60350 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 122292302 1250 122291052 122291083
    0xe03030f180a05040b06180312071b05040c0e0d0c0f090212090f300f0702010e010c050d032c06040309090b01140c2518020412020f03 59
    0x30341c5001c0705104414000080340c065a038900500da4441c240015208412000c541c4500d0a001d4084400514600d1b01c651f19402012511500030142d48a030459010038015502240301e100340b95000141311000400030b01003a1003c002110799500c000305014007280c105ca202b011046040c45c184400403000c00b000d452402e50a220040da1071202d00002c2d840401e004440310080340c00107441da200030842d070420400610241c10b541c4891020f030404188441855181d4000600f410303e0381d04c9080d0003408004004102c05503450340e55000260410f00d6040c442410024803208140c0007400c080303981c5402c05024100403d80000c40180310640c0b030410401c82e041a04401000d2041c1c000000309035000e54000d84607044001d0301d030107998042d01c1494111901084400e1214030200314100024a188060881a5504c1d410450080b949904840c003c0e681c0030345e10104180804108500340c10b100c00580d100451a05162003045a07040044d0440a807042c2060260304405407000d000c0151030b0702c0c150 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 122293552 1250 122292302 122292307
    0x3080c0f011d010606051204060507111005071101020c07170a080712080c0315061303050114041b0e01030f051c0305010905070e1309140a150f050103120e03030f 71
    0x200c0c002c000080c1d60b181d22802e90300385040011428010301c126031400112a0700b0b091950303540e86500019100182c1381504000d040006005c0c018400d1241042000d01c104c0042290300b41904000d000301094091800903074410004401c014070002580c00403541d0140007803042e40e681c10009030501c034158001a2562400041c40f82c00c01a01c2d00c514820007040d0740350042c02d0b84803071940310001d00088071100841032030007a05041914296010301141d0b00010f40c1b01d980e094490b900d040c00e440081e410150039110381014801007010b5041e1443c4880c010350300c2507521718507040f02c1550080042c88064250801e000382e20701441410300c0003074101a01400b50813403c400205008000741b00074802c0c1d0250368600008034120520841011158500003490904052011078130f4800500c0c07900011640384c490042010500d000038000403e090340144a4945c41150302808038040d65001100c46258034545001800081d00c201d8a0105244030340c42c04401022608011914602c41c07008001ca650001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 122294802 1250 122293552 122293571
    0x3030c0706020705120d020a0b0c04050a03080a030f0e1e030f0309030408010606020a02090a0e010f0f02070c05190e040302030c06240904032001020403061b081005030703080c0f01 79
    0x10b55001110010b07940c03180e20744030b1000100e44610041b8090801600400007503008140609041c035041090302d06600e18140d61480025510b0b0b001d40e204440502002c40c0401009815208150b401d20700c0420034020310080101c038980b5820702c2c1500c807102c11451450f81403c0202082607a61000c520b05a50fa40d0341008003505540e90454854605070f5030070480b0105180d8808501c42c10266409820076000b134a61981642c080d0844010101b010340d40c8440d641c0046c2842d000d8011012203c52005030389460604000000003a00d8016600580c40880007100164540b0001c101f20f445900c941c420030741f0f491404a0541c030075030300500041d00c1910309011a00d0040a5940c04030284509480d100141c107105200001d0800c135800380200782c1d10280d407038054818001050f10101207400045c503254999031007108403212a00c290a0240c200c0b000d405006420800e41504480d841d13141c0104240f034000041c3c1da484141c0401000b021010416410317800d02044003080e43c00740743c0700070300c140040b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 122296052 1250 122294802 122294807
    0xd050f0103020a06030207050d0c11040f0605041103012301090321030515032104030204060e0a1415010e0103110a0c23120304020f060f04140619030b03030c0706 71
    0x102800306920550307075443c000421038003078401c40d045d540e0310802078044d6661428041c0e60b91042d03440292520850b0604101c45652a44a015041c0040321000129203041c1820701c001c541412400c2d0704550420001401a001c4681c08018a001c582c0c6610107030081260040701c0780009584010200c620040103119203108400c442040300019540c1000140d880307200c1d41c04000c40841b403068043c1c020013180201c110700d041c40e1080801c510007099250603600d50126080758141c4d40702040300074030182402041c0540c0e0007a0108510f8400070b0b640a0300b450124501c414880c00d2009051042c03120107070f085640a600407081142c00d8000c2030313440721041c02000d0700e60310300194201c88034485050181009081d02d03044a4841348400f00510181e080900c005405a00c06401030b03070b10001003401900171f030380e0f160000d100f01d817100380d0480c0d212490140c44040064600c1c3c1220300c03c4a0a002e02c0d44070707a030080001182c0c1101444c020614400d5400424114400c0c00d05104150185510101e07402c0d4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 122297302 1250 122296052 122296081
    0x60403080a120c03020301050d030c02120f010f0609060e1f03080703020307050d1d06030c040801020a170604020307120903090329090601030c1e051804061503050c150d05 75
    0x218074540c00c3c4408004400103e04902c004d0103982d41c0a180695203c01180c400c2001c06c96043c4081c0240110081c0340401c1807030603070280b07011003107607448203404c001184550140f40010169094188469824484404042040100000c0c041d001443c1c04030030002d0302e00d0079040115004520103964504070305000303440e5408441d0541d0a031040004107106684103501904610015010000308051080100002c41d40b003d402d07000c81c08818000441c0d00e11081c4000e1414080079104c8000c1d000c0200608110354100900b020710a610600801c18066006414204940400103001604c200389180030b0b210688640c001503d024122044950b07100807004140703260250110398a1004d81d0ba0000c059901c6da403d010040418071030030010864041200011104090388210a10107183c644010646100500b0410320b041c6466030144418005940314030240e00704c0710401c5a0200341951181c2d0390340c02c41008a180a00200300c1600346443d401801c0c0c1e003803004504418080c60501c40b1080322410f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 122298552 1250 122297302 122297327
    0x9090c010807140d0501140306010506090103020a110d090303080f0f0403050c031309051812070201080405071208071709211e15060907021902011125050a03050a0206030402060403080a 81
    0x24941c7d0307881800318540026081c1c12103070000e11103490b007d4240d00450203034100c82c0c4400c09201c0c4034078240b54100c405114003010440d199482411152441c20024090300000e0042c0004154400500440610020755140d000350107007400c66031200401015455407007014116040c401c0010b03404901c610250300214000d001b164a08005429020000e54542c0060000c82c4180c0d4401c100400065021b0031076160302c180034406803840690b880301600c1068080c903c0440e10361100242c0d04007007198810100c3c5880e04c0d6861143e041103080c0000c42c1d40e14980c103481014401c2400340e03a80d5007850810002c6480304040c044107000040364950035545469180700030644c0540c1d10f0006181781070600300540b242910364021300c1d40300300d2000501110302a401040e410031900b0410044410003c11408100c1456041c50800154400c0800410f66040d90443d62160005400400106200141e40746000c3d40407518203640c1d48851001401e188625030000b400402d0201c0d0091515030048451040c4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 122299802 1250 122298552 122298569
    0x12021f03060801060f0e01030b1506070501050708071e0c05010605040c0c0c06020309130203220f11010509010c06020f070203160306061a070f14010501080109020f09090c010807140d0501 82
    0xf02d45c1c480600100b46045809034105091400300104003140000e10b1040e082000c100c011040c160700c0601080803075001110036252603442d802400300169100400503030043d52890304450700208280c4171000d2480d605c2400c010407414102880078030800307500c51401050010810000349100303901c00307441064283c0b81a50300e05d00c400c00000d031841c004402c031255010020100c1205010007074031640207400107440040550000510002040e05213248005810b0003a0b110750b0941ca0f50780340410100005440340c60401c40207011071441070740c00c5196039040070b600035009a00d403840418080068069444041d50500c00c002501100e1070140340c5000a40b805000280241d03910389100110f031184000040311a40d004001800104004456208130700703110310a41d20f100d2800310070060a4070360a03003080085954900d884011454884041103c2810a894000707692500840c100d40701c24042c003034503050000d02c00c001603070b0320301c280307a02580d0101402041d515000c444a80100820090049824 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 122301052 1250 122299802 122299811
    0x6100506070510151a0309071206061a12090a03140703030b0303120f0109020403020307030b04020f040603080301091d06010e07020f0a03050a030f0902030a03030b010504091806050c1312021f03060801 88
    0x3002c40040102d900c512000d1f0014060b8a25254401e040003052000503a503e60381c5402c0498000c0c1c50f01461182c443c1d061000a8450032007020b10884c0600c05006909940e2040703884070002a00108107c00f00307520040129154551800d003600540071404003583d05007c0040c1c002c0c1555841e00c0424000c0a5000c2d501e007540e81c880504104920507400301035030591103184100001100b1000d119803062019003d0746860076507202040959200b40c02c02c55110b0404401440501403510400c134100c140d0840d00c12927819141300464940c2418010807030506519400194501e000f08401ca030424201d42c02c641c00000708d03050042860f0080411840080e0070100e02c901114043c0c015807100607002400391401c0c000076581a00108518200a0306014083c8030010300200c40e0700c13907610141c1007406440d6403101103203000d40c111103005001004040007440440c58641c0c4900c13808055030743c0e88410358110010390001030300414115072030204a14003d00245000350b855003100c1e0844407003c000b41b1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 122302158 1106 122301052 122301089
    0xd020d050702010e10060303080606030405120a030917270a0518060405060604030f03080919140f0d0509220608070609080610050607051015 62
    0x40941d56540e054810304c6001d0000ca00103440701401000120706699000c0d20350305010300094054000400045d04001d0300300300e0181c00741c41c50400562111781301c140040141031403007001c451080f10503603480208903101058403400100d44040503240220071000000204144107a280c1c000100300001800c0c1d00d420600140385d044201e051045403a05d0020301040c2c1d01c0c080d118a000740c06c100b0042002c1040080f40407805541403a200704103443d01c601d82031401c005481c54001e0f0101c00b012200c02c2099590940c203640500d03070261401c0e92240d24529403191445160003010807400c014914072490002103d4844924074008a00d0014070b401c0e600d8101c2d860f517084a0640e0b445a20140070b000d4000d0310071402004c3e0700000300307030600d80003694109464091107014010318021070918104030050011070031510b040c5400f0407a4010114031085912000c0c031650801040024942 = true := by decide +kernel

theorem cover : BRFrame.Cov 122122302 122302158 := by
  have h0 := BRFrame.cov_init 122122302
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122122302 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 122122302 ≤ n) (h2 : n < 122302158) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
