-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5428
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:50:12.542678+00:00
-- url     : https://prove2.me/submissions/97179c15-402b-4e5e-b0d6-5e5ce8081e3d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 976079136 ≤ n < 976258992 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 976080386 1250 976079136 976079141
    0x4020a0e091b1c15061d011706010804211e11190204090b0a0c030f0b06090103022d19020114060405060312030a0207020a0806010e011719110f04 64
    0x500742c04a2150303040125180b00754820344510400e0964454640800c01d0401c045050340310090101a2030b07181c080202240c0030400c076518154a03a04000c0ca080c90100b040e400f18042daa000582807820601a030380f68204490749030292000d0982060460105410a990041c03c00507080f01e008501c00b040481c020048801c0c40300c0e20341007107007030700200100003850380b1241302208058400303070010a080004ea16002603009049032190800c43d03c40ca0311f441541da05100b00d224084c0c6201c0104903031a8210701261250150f042c400f41816030004041c40440d5504000c01c000c01c0e031001142ca5402c10401150741c8a400200311000a03d6071846507a250324010701039124818088109400c1d5a511581000058140030341001d4040c0556250308244500103001980b140c907a403140560344510a1042c0480100390758890341c9190407100c0144241c25584a6440c11542103502c100e100078140c0c5242d40c10265038a07946580140c81c03881220400c100c80905001a003011104010040e004800303000a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 976081636 1250 976080386 976080421
    0x32004060504060804050f01060e0612070b04050f130c02210f070305210c1809040807080304240f1a030a031101091506090c020a050d1d04020a0e09 65
    0x20031018041805880d00c60004941e209014400300e468087c440044503003115565007294030b04000080400c41c1c5814020318108403906224000c0c100c051400c00801701a004501a0a01c50400d4070b5580320160b0318614505040605903404000c560b40a140280d95040603030305406840b00c01c0e55040141030042400d4503001c8a0401d2010f181c0315055030210f9642d03100707901e09031113404400d081642c00d030b880720a400c0c420034030100000d603500c580c060145522200b00d0103841c0300324822000c010000f0041010b4458190b402060740f600ea4566142c9020f040d42044403180300f45180c14010b2030201860782200d2601660079004000b80701007e40c42c8251941d458080350b4041c1d01007804c41c00004d11070442c4040d80001b00300001008880c1c1e5a61a60ba2503c0001100b4441d4491a09004030f299601c21001c070b5941d0303400101100800c95a03940d44502c0c86280e041c080c895038440004000c24451500138000360001e03c21951011003100c090004916030603401d02801c035038800158240320f503852004 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 976082886 1250 976081636 976081649
    0x21b1e030315060d020f03130201030e0111160501021b010902014e0903050403020a080703031e03060905090303040c08030306010c06110c0d020607120501050904081605030a032004 79
    0x211a03114680902c0116400318458060f51384c2d082100b0b0301c1d91201e00b8080d6004040015410440c0041c40c00014140e410800420880e40d1418081e000c8910303a040464010070315045030b40340150b2042c1003d500a010b00320b840705d42c4a041c8100300904c00c2044d03000016032403003600c0d25050400740382c0c4081c0443d000b800c000b0403110030000c4d0380041c0030071303100d04604110120f4200305000c20016154400742e0343e94a4007100130900110b000e0045140980901c0040c041c0380740100000d928549005101c0100c041c400c1c07003403404c041070403a65548a80c1103003020741000001804182410309100e60740e41e10458040c0c1c1c3c40c5004490204103103d0100480b4005d140503510385030703182e9003916401c008141401e00784030500001c00582c01c00000a10280c000056640c016004034030b00f080d8081e0120310300c200300d0826180b50a0041c4620340d15044042e030070640142000381c039508010f00d4204a1102c01001500c584004168a0b0708a039140d0000d4983c0ca04411300f8080507000c3d108800c425008074062207 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 976084136 1250 976082886 976082911
    0x30712020f1606060503010e0c030f30090402130816050f12070f080a0b070801060c0b090109020a03080405120c0607060e0a08130608090a03080403080604021b1e0303 73
    0x100400c09080d1600382c01405044009645562400042c1c2107501c40d245000d1030342c201440c1d20b5a107250a05c0500030303000c03070304c009001050585400c6001c8000c96005500702d8071840d541d40c0144032100801d40c0c400841c040d10440d039440300421440c54106051282e0401441411038492071220b0240d1903c003200e101802aa0710711498904201c49060301040f49501849080800070750b450128003a8401040250003030440c0c6c00117402d05851402000340400103010001c40100815030703000700320900e1a07400c042c03400c1e880c0d01c50702c51302405440101d03400395025440c50404402d1007010002041150b00490300564040706040010f611007408190030b40d409401880ba40c0302040c5513030845881d2600e04401e80300704039825994586190080100c20900101142d024091290400d028071b4111603044014140c241c040e96005104400040c00201007224032404107041d0344590301601d01500c058000c8881448104c4d0200c1e5454820500359032200b410302c490000009408000c84c0d00460300b41401 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 976085386 1250 976084136 976084147
    0x1b180608180d0305370b030c18040618030804080a1b03021506030c01090506030603071703121e04060f021905030907120b0a0e0c04050a09051501180e0705060f030712020f 75
    0x3007100400515403007a81600031151880c00c5507446d81102e8130381065642441d27559044c03d061580407200200c400368154000c803c07080000c0380c0c010340c00c10f41c040d9003e05403c4c0c3e103400d985011542e01d520320b40307050301c95041e014400c010990040350041d24504540c000302025aa03420415079200340604407540403070170841c800d00803800d00030f0085500440180407154400c0c3c1c0d4180400e2000d00041d08031449801c003088903220401700040d0703130f46c21400361250080c200e0000110f5188a48001d40004e003240d9032a5130b04202481030307405848110703031001a40c00000791000000f40c0503600481d103030003c502400402140d1214040c2e2300d842400d4004d4241c40c0d590780c40c0c3e10b140e8010324180c41d4030400ea10422040080d1035071540a4580f1403075076a1808103221506240c03440c5054201e800100b48040e100c0014044616429143d5251036034200f4045002400d010a0f40c1c1002c1d220781285811450000c0c120035a00e0244d8011030086d00360f43e40746009138503d01d101e841240a80114240d862004101 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 976086636 1250 976085386 976085491
    0x20106050a17070503060c04090510050603060f1f050403060b04060f1a07080304150e0a030e010f0c150b01081006020d08150907031b180608180d0305 66
    0x10000030300c200e20ba0407600582d0311240024503000045071882c504030340000f802c1c051400d541c09200d070031250801015840a04040004003580001420103004501c0d0380c55914103a44d5003c9809a4441800700c00440c08014030340027026640a4001a1a011709026041220b4201442924111266a090b601c141410302403200c0700d00303069403101404502c1c28415100440c4040e001140030701c0c414103d1500d030f10200b200000580e10418040b19240d0001020180401c2d00500c007420120000d1802401014400a05882040000e200540a1800c07050b881c1c90404042c1d1200c07a1a5100740c07143d160320f547c1c48003036240d030428901582e0b006030405080b0b2140c807400f4440031500001d00f402101503180306000810391100040302c680001a032544c859400030f80218080300e501088a242ca600703555185102d681d00001e080c070452007000b054600081a0846080010b00c401a0100c20340d54444c184c2c0000602915003075902c403040d000700b00480c0341c0c944c4102e04e0b9109099500485801032548400c03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 976087886 1250 976086636 976086659
    0x31104140c1909092c0a0201090b0c07030605160e0306100e2203030c1d1507061404030c050607300b0301021623100e03120711010507020106050a 64
    0x111a006010b9030f81c1c408248070f03904d030003010003601071182c20300012291008030b4803a042903107040320000d0b0010a110005030b6805001e910569841c040d4003560b07000d400e000f4500d418000e0313001900c19890b00081c40064001c881e02c103495480b80b503403804080f0028008054170703004203494034030b00c2c1200004104800c0003c0855150321140030000581d41c04101e07038005040303603400c81b81240040daa943c4100421078120f249104c2e071b4030002c82e8482c030001150300802c52511801d0f040480404012980e8000c000da88d412030702041a6440c5903181c0f40c2081d26003e050b011046008440b2401000c0c00540120b1141e00c0c10b012085080084e200540c1400614004a5a07800c0da10300c24140c454030f4a2000341c0303003400180201c0c0040e480000c42c1c00c001c4d080c500b0091802442c842a5032040305100c40d0003d1000491264200600e03000155061442c50001c0c950f12804241820440c01007042004107600403407415841c9a854000740002d43d96607004038200c48240c01070036030090309104240a9540c060 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 976089136 1250 976087886 976087927
    0x11413030606150f0f20031308190b0402150f040608010605070b07110f060c0406021011031f1a1210030201230c0303100602150f0a11090a031104140c 66
    0x60500745542c0300103152103004038805400c1122140d01c0000c00078801885d901450004020049c090700100c4203000d4840520f1000391400352021240402080035035a820424544000406009554404440301d107684950031078803511010842c520b0001800c14001c1088400d10b40d0700081030301c025964904e043c0c030035410f00b0560030520b11079540461100081044000c1c0215002c2015070b8855203403c000a00e030504400b10701048508120f00e0414850110013680e4003c5000518014004814002c203404030003507502018004504520017801252240c0042400d0056214050541d81d41c02010072194001c3c0c5c40000e00040411035002c86071402010350038050014603848a00d40400740e040189160030a440400070602001400c015180c0c04201000040f80f040c8a0110a032038503401c1c1d102c5a11008100003001510b9990840c050400301007210441e500007461071103107603102d0404281d090742020815010314942400140c04101114030f41f0300c95a001d0b40b03014a8a151040e4a41c216141c4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 976090386 1250 976089136 976089167
    0x9080d0507060f1e0213121a1306020a030b0a0b13090203060d05010e0c090708070212030402040e03070506010e060f060d0b060403051504060c0f02030a0c02011413030606150f 77
    0x22255001e61220504042c0004ca191010300542ca0380d96141c031868404405502000a0070a44a50000041c048006c20503a10100101d44041c1d69144c01ca900e980098912005010720310000b42112160740541c450890402d05450041c42d803511081c042820344281c01e961307031b4100c04988040042000301c0e0001d55000002400600d00181251350303031401c0d01d007514100301c2c0c40d401600120341182055500e01d5849140c1e407422440c42d0800030006074a501c00000e140040b000d0000024040d034851303400c0300a5229481c41100d0741c400a43c144652616000c1c0640c01c0c0454201001c01d410346000b14900b07800210040005182c0318200125400401050070101d4000c1014840040400c40070300c00c0b145101410030a8480034502894130504030b410400c520424880c12014020741b03141e001058071141010f0381030010113001d141c00141e405600b2103141c0108000e0001d4060032454800442e942201d11a080c1402000e449030b040704200c24211820718001882c1c0440e008510b4491120020354010 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 976091636 1250 976090386 976090391
    0x291206041e020c0c090609010e130c0b09091501050901050d0f32040b160309080c0d0909020306090c1806072108090319020106090e0d09080d0507060f 66
    0x15040c0707520301e180401100554580c0c1d021519011190090001443c03c0b902218403402500d054400604800818000c0c00038014084000840390044100800010382c0c1015080c40d1070340d511020041c6a41c44001034500400c400c0c03000c503c00c140c61840201400344161112406c00803200c004442941146401040d080d07101c0e1a4400c040c112031056520500041c40068071808920940c50071503480e028120390460700d040d0400c80826120391141d80c11050b520b01c0c41202090340c407000c038054004898040c109200c0011a030011603000a0140d8a10780c0c00d8a6114110781d41e0b00004007240000c5800700d400084040006080c00b003102c0c02840b00610107082c0c0700404d07541c00049803541e0004c0344201da10260b4204008030700d000282d8001d54440c11490500c40529001da40c1941300d01400c9442c04415041c4240c00ca41107000f07400400c0034012000040040034030040e60140e44159440d050300100d4203038100456942e4011072150350511180c0c03501e52410801d656810006c0545c3d076101405c150703 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 976092886 1250 976091636 976091651
    0x7060212090a0906060509010f18051507150b030c090c0f09060d020a030203010e090f070614120f0106140f090d0c0b0307030501050913170a0c0803010e0129120604 72
    0x143d4520985010b41402e81d1000e0712888440005040402044008028094124501e106054410300070f18161881641c400c40501807100702040e09004408000301000094404241890141e502869102000701c0c200d03100400000180100300703d0694802035011030130010045c0f0404a00002c041040700546198600903006010400300e811000d040030000390000010451180180001070700410010060301a0200d04011030f41da8500c03e100320f800340401ca03064114822010001d443c007421720b111040300c1d01c1c64a102840303c070660901440d400700d5500001e503c6040204015918500c4003403401d00d2900050301c080000034950b1140880300044801d0000c07170f95400c004055400380c1000c1d100841c655040c6002c000c030282d0022720344450343e4940013100000c00c0c580c0ca03540407202c42c0d0664041da20081c0480844001085440c040e2141070f0004c00020b6410240d111b440c120b4841080342400341180030f4000403610303842c0e040030b41e82150501c060b1f0035010661441035001b0400610004030344 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 976094136 1250 976092886 976092899
    0xf0309050a0b03010f0f0b0d1505062a01020405100e0409080c010c1d0a05060c10060b1803070b04170c0910030501050c030c0415050d02030c07110307060212090a 71
    0x1d9421040da452030103c01041810080058880540984101c0850480c10481107000340e005409086507250f841e040540c6900441c0011200903042c0500220b6035010410b110540d2000c2e4110100c005000506402201900c18820340f03040c0d9100030100c1109038151841100c04801c049a1b1903401075076200b40700e00191040008100111303d6000102d00c04144540103402240f41c1800284d2003540402045215565054102d0654804072409610f03040340440442c134010070b8816440c046072405001252150b01c080c00350054451080000180105c003805041c1c880341039205000702c034101408280803d800c1c5001c06c078690f02c1440f04680000280100040d40003105445082ea462041c007428420300c8001e001c2c0a07400000c100c4c0c49441d600300310501448134840c1c1d1180c000c6403a2506050440d00340b0480480d1111507000a0a5442e8100b040d1340070010303400000100c46001e8280c1c644038030b40c200410791500300c50b1250080d004680340544030340c00550184200580c1b002803a02d000c03840 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 976095386 1250 976094136 976094149
    0xb041d07120f12030f14070f0903260c06010902090a0902040315180506070801090c020c030a022e17010501020a11040b0109081606300c0c0807050609190f0f030905 72
    0x980c0c086c0f841c3c0380b0385410f09000184c46a5002d0503014200715808a00b0300110b500769100c5212503140c1007400310079640c013010031000c501400d00c1080a500541c0000103039070141c0e401604000d442103403003015169035020380000704d2181c0c1c80010f140800300c3c800044900b44552106150004001c0c10000360482551042d08081d022a402c1c0c022510340b43c01071024100d035119201d0154940d0008281c0148180b000941d140b41030400240b28206900001610383c075604d903264111000840040801081444044c0032a8a00e038814140c00080c200009003a41c400903819210075000154901d020306200b051101405e42d08089034148550340600088042c000c201c28445101c090807000141800d24000401400940000041454081811140d4643e02c5e464120103a0704c24030002500011002007911b5174001428007401500307000c00c2170018004017055083c8a040020141c8002e802d0031a401511188560009041079006040c0440016124a4503080e034501a052046815545500155a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 976096636 1250 976095386 976095401
    0x30602070303140a020c15090708070f0302012c040e211b0d09060c1707050a050609030f0d091a0c070b070f051206040b041d07120f12030f 61
    0x43e94030340c48510004240079450760041014242580b4103d001819203558210605803188058658404102645c00420010300201382c690b00342c61340b650303850032b030081c0071034181c07000381c0c0861136010a000c000d40343c0050641000301e501203103c080c2103105044c00000c101313042d180ea20a105071340c0a407504101c0c24240800c04911185416076403019040c40c4012540c0000480c20180c4c0809001c1d8526a00642e0f031009a40c030921304000000202d00708503c0c0c1d00084480c14049050028880040c0b0001042686902e4081c0c0104d070070316118175800c0c65032440380351001c0704a40428002c00507603800700d4100e8040701e8004d000c1406000c0c1e40b000801120f0030103454405007500c0006c3c44a0070402582e074056802401401c10103442184d585019246200d850b083c58540300d6040c000403080da03a00d40c0002d01c00a000750040001e016100d0890504a00001400105c0e2080400020f040d0240808c29034465900000000400860b981c0340403420f103804040c00103058803903a02c5080c1c2d8100384103d00 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 976097886 1250 976096636 976096643
    0xa0605061305130b030309092d0739170d06030c15120b041b02010608010f0510050409170c10050601182102060c0105070f050703020703021903060207 66
    0x8422032402e0204680403100701ca400c0011810328140c2c010554020054540c8107100382d82e4a1800d5070b400c1c0491500c2000011210340e164003408180d800b4200b05070b5801d105d12041d4990400c41111002020040319124102c00c450440c1e040e9800c0c041c00f1982c001c2d0455910595000400003080c3c101c0700040d801c80034164100b556904000c0081c01142c1002000411f0710f000b81074032103540a84001c0c50900400d0200359165150203c291043c1c64a5200000c40c43d00040400740c45d48040398004d01a080301c0c480c000c2c0560800b8102540b050880c421300380500c0761001310a402618040030321002d002207400645a040c1d4005c8a04100c0480000801c40404060068103513402030381005812620b0240255042100c0740800900000d80f62001105880d0740c22411101e804094141c031700c0e14022090300940141c030109400d001400c0541005000b401e0304d4440c2c8486500c11a4106d505014044000d80145d2003083c0820140c20680602d144081000c00c001c684103869031260030076a40000c4048 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 976099136 1250 976097886 976097917
    0x306051503010b06040605030703050c0c1015050a0602031603050408060103030309060c08011214030409020a11061e16020a0606080c3c0f0a060801030c06020607050a080a060506 78
    0x5840345420701c00e08440f0b140489120b0f0805051440003006400b00900c0c010034143e40d440410f00346c00191042d10b0452069104850b910351501e242e14018100d1940501e00d0609102000309003417030048032050645100d0f03801541083e00d00313210101c2e24274904505400341f0004000c00324680741d003803107100d010b50300948000c100c4271154541031084800a0025404202c0d00400510070805140000d45100360022501000058242c95a6040d8440ca42c00b1508032032000a01000c15034200004004424885007520000d0381d5006443c00c9150440302c3c41c8140c04480400a00f05403000c0f0451807100c07000e03104a4150110300c6d91521b00b1142c4603006440303035501084c40101b80340b4080c24a86484c20401c95030000c02d403181a104500c000c0c480e40140989056901c98000310b4440e0045861005002400e0341c101964460015203044400c0c0070a4411010b040000300f000b900018216004000d181d83d018584283d0b418103d88054004d08010911515640700191a03131b24140038101c041031542d140c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 976100386 1250 976099136 976099171
    0xa080601081002090d030e1f110c150a050d0e060c1b0a110d051006030b01080f0a0b01060c0302210d0605011d2b200616110a030605 58
    0x346162548002d10820b441c2e0040041c0021620b440101c3d6145a0745410044022a8640000742890302450121007070188881111402c40c2e500c244945034446c260401d5465251045042c0994594a40b42c988c813640c00410030b0481403403080e4010b01a69904a8000455412000801303003131480541d40c0d802094030124030310112507400c2d039490380083c034810f0003801da0340380d159516803548282ca04050300c1004148080c0c403d2101c1404900d2002074182e5041200c15220326180850640a01942499100300c012541d4806400680c16901d036801401507280caa1030003070200e554a8082d1422011402107007001240307001010030046500001c070340b850342c45002d0000382c0700c1190120781c012410000303d44000c000101d4200c07420884604c0c156482c050140e100d164070058944081594003207004100228024000b680d40508a8007030743d044140c840c2c9407048204040c0c0d019404c0c81c1130401c03a000c81020b0003c2c00e02c5800e002e015078041c1980c41020340c1c0f40c680b80704444003185c02c0141340781c03203409 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 976101636 1250 976100386 976100399
    0x60f0504060e0d0905060a021005091b0a0b070206090f030303041523011403030c120a0f0504182a09050315090d05211906050319030810050a080601 65
    0x1485941807070801c020082c028080e14010001c0c01c04c0e2240034060b590004021070303c9842444145c40410b00b07800144103074100a0466a42d07160403c400b6a602a00d42002c0850751070813000e1002150b504011807420064640c00300f01080c0e1003040d107294051000c81c2c2d0070789552020f002a602c59801440128036000001241005a030b006010007444100c06000c1c0b070802074854043c480c15140c600000c016051803910119241d80300e0982416076078414801c5032050910002c004240c0601150f680901004490b03400f9501c41c090f500a008401c401c0b161000c1406c45654400055800f8060a10641e07103200e00341500d40d03100c8016400e0005500c0601070046060030405905e11003581c03400c03c5c1040c0f40a0070030390b031509062050300040101c00218821013084a400b0200c150f4075012a002035400c000b0206281040003201000c2c189091200002d4240780c040380c00750711603464101d01c58400c0304660741100c201c0d070010710401d461441b04801107219102d00d05aa40a04a80d20007172546504141 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 976102886 1250 976101636 976101641
    0x3180a240b0301051e1005120d1416020402090a1a1803191b0509012714061302040f260102040f0e06030f100b130b030721060f050406 59
    0x1c003103000741e0600c03081c00101e040c01700e0015401c803813086121780284c42c0c1c0c1c2e41d14640d02ca85036203e280d2020b002d2070440144000451103445038003440e2201d1108800022a4010350b0003517000c00509034004040000260900d07400400c0c2d1184014042c98016449000c0d400c0001c140c03a05081c01745c1b6010402c00e40c44517498008041c00340c400c42c000e1001c036084500c0701d2003008191200a0244c0340b01c0c1842520f094104600320080c00c401011801c0d43d6840da0100703041c10141400030920b40f9000320341c05100307811612940d40d0007580c410100032039540d24818441140ea51000d418401607003000001120076483d48010003510001003003640c0715045a0b41308041205441041e861a481000100550012208108200d943c686000c1c01c83d5521140040e0070012145d1012441e401044903801c40501c0d03031346c0800304a200c00c4405200c00b10240c0c44100854242007211030309503108183c05c1c00f01000e003000010b1021400004521403007815540c0c901681d841540c01501030b916407091108000060 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 976104136 1250 976102886 976102901
    0x2210403020c010e03161418090115061106010603020c07030602070c03021918050601050913090506011d180316030503060a05040b09060d05010f150513050c03180a24 73
    0x22401080c0031003840c05940942201b91081005904000c0303500b440b1520340000d240404500100702d4030003031400005a0703010b4403010185544c40c0e103100c00c000c2803142c0542c0308c8119448044000340116820701030705600942c02000c1c48051446102d400200160150008000b440d2145c10042d41c0e4a1443c8140402a02c0c804800d40d802540594103002600c100f080c80d421072019114042050b454000043c0d482c0c1c4101c0302442e130400c465501503001e01c9841e4000690b034a2060040300c51903a07950300a4a0f00071461703200c0c5203541003000007294004284c510080c030b500c0c868a054a14100d1038025264103070312028000c0b00030910202c200440e91910b44288401800103072000d100c82c08040b40007840009000b0301403031042c881c0c145000d05004003540b0500c0c881200500403c1542d001650000d001143d1f442024072410b000c01c08110b50900300e028441c000d20760180b040381583c1f03618040c0c06e028464801c04005600c6080d580c100880c1c0d00c15250b803510a0004001115510041081010394110 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 976105386 1250 976104136 976104139
    0xb061e300309130513021f1e0f2001020301030c06090f0b030c0307110102131a16080708070b010f1d0c0a030b0d020301020d050702280602210403020c010e 68
    0x248541c002c80c0e11154551040107010342c0c1d0015042c0d441888940c1c09220b06100030f50049841842e00c07a414004000c981c1c5010070a45907880e10080003040e070b0100d68960120000001d0920303070005140c601504210100b844000000c22800c2400c1d0020f908a0300241e00948210780d00000402030740303402c005100040c0000c103201c00c4105003000c04500c080d12000e482c07060b64410010000e00e41c144150003032411101144001c3d50340384050050f41c440e01d1058000e02404000c0d00148000c9801d01c8170499211301c0c10300c0c3c80007402c010300e0b40306d080c0386030002030040d14042401c110250018266607145c80c081e21000201c0b5080b541400d117085419800840142003205000041c08a50341042007503c404900f02d2030003107600f52246011416a040710756000350150b0011a81c031880c40115004188501c54550840f900d40d8a009081c0341c10340d904810040d040d654a076907a42c042481a001020440c815030b4aa04041d0071450040c0c0044408031025401a0068202d82c441581e00200d030030b400690 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 976106636 1250 976105386 976105393
    0x18021c0606080f010c112a0f0a0602010e010b1813080712030606080106170105060c030d020304060515030d0c02010e0406120b0f0703020a141e04061e05070b061e30 72
    0x87d1050081c1303e100c60220214071a260021901d42c1a66511080a039411001c1c005c01c0b8200e42c2c0f184068003038010303e403460002d542410040130003170070074003100c222001c0c0070101020715849582c00a100301003c1079007914890010098400400d400d060240300520080e6000518a890040c004008800c1a00444c08000a00d003404894400c00d20307102d03042d11802c5581d40d9842c55014041461442f070450600d002e47d0000c0200020b011995209a21900c030700d81c032a06400c0181d804150301c0b40742c3c108600740410408903004000d0f511540c0c0c4011054000380002500030f8071110605030503100d0003400c5400c458080300f00a424103202d5040381d00660541015401e290320740c3c40143c10b00d40c1c8281c26043c01da5010500664104086c10b50072480216a1b4416555540780c040c000c011591540b4243d450800303104800d5003541c4603901315082c040e0058910b450548030001080031403089110020f80c07101c10100c80c0100da585040b104c0b08021418008481445256a8002c01019070391050702215003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 976107886 1250 976106636 976106653
    0x1030213021204060b030304081b0f0406054911010513061110020424020d0509091b0412050f0601060206011811030a0204050418021c0606080f010c11 66
    0x85000ca25107800c0707130f48a20701103420303d40000802d1035400703a035010701090b1084151190b503a11000200f070000a41c26142c0007e4032144405201c01d0350050b1050740e1704800c241060b6181c100c03004010300c01003c50040095000c2100a50340303031135400c560036000d00700030554950004000d90141c0b48403d1900a0a045090036a42c9413502c0c0c1c4000d141c402e14082c000500380100d114202030084030402c200903082192115100c052a8480c00b188040c07540c4c0a40c40c84000914560000680e5009401c03d0f9940503d4506440d0500424081c0a0690540d103005903510030301944016010b080038250040800740100103504002d0b140400440c04228a0b4110400511005901080d0b060540b569030500e00360141c15141c00710024140240c480e100d40c00003005204403980715400074011560220b07024010900010b10280404c25442d1000350701050001d2410120355610310f00c802414020000000c0c06541e8680060134a444803101c21026556104484202d5400c04404451884110300070490302d03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 976109136 1250 976107886 976107907
    0x311010f0e030f0901110102030403020619020c0c0f040209100f0e2205090f01050c04030b0115020a060e0c040204030609020a0e0106050706200c01050420010512041106120103021302 80
    0x244150100743c40c224100041c1020b030780c0d000301c1417000040000d0340215600d1405040c020b460f45401e45421080100000ca40ea610600d5030090301e1286090002034004404c4500412001c40f50769690180c1044d001c3c0441c40c92661042070307000300c0801c1c03611600000310101000401c504c050360b4842e44240071400c00941000c1da03c2c807195020082d545c00020700ca8032518005842d180000c1a241d085600304020085042e00420280003224401c00c100c542507600c5000340c1d40120747c4c08000500503448450a00c0115040e138000501900704c0d00c1c2903030b440c10301a1000c60b060340e000390800d072401c4e602d60324903c00b1410030344e030400003d09030f4041510b401c0d4100700700140240b24450001c2e1200e600c0c0c5003400382030444c18100030b401c04c481c5280c42c0d6440c10034996aa01a140440301a030344800710304500901c2c039544040326004810169180c0f80780030220310901503c10000f03001074407038031030729110420140c5480c030041c03003e50305000702d0840541c91481003080240c8145400c40d03200e0b0051029407003d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 976110386 1250 976109136 976109143
    0x20126010611070605271009030302011407020604110a080d23131815060215070e03031209010e070602030c0601060f091203030b040c050d1112180c0402070311010f0e 73
    0x80c5a1070080404404c445591b5880c2e0180c00c00144035844010b00c900421310320b170003104000c1141c0c440e40003444030808204004814007011214170025800100c0014002800301000e4040100e00900e402012354503098014071300541c0302000300104d00403480490f03010942074003602c0300c0c529000c802403905110324082c421507039040c800d0700c000c503070004208005413040d604030741c10340321080004800c02c641d1500001c2d07036003050300e0302c0b400c43c036007520040f0b2007041c0306056a2020b240041c004502d4022903449501d50000001c16840e44d656035107254483c4960180030300c10040c41c40b0703030095441d00000b0b00314505003501a4850030a120400d00006034068100c80d04400320b541c21801c0440e00929403c1c103078060080c03001c81c40d9015142440c0c1400168100d07018110b2880000c81c204425111440f500d021441485918510380d49c16000042d2000700201300380c00003511034000d40d50a40c3c10350002c18242c0c0c0003960200c000c03a0074110450500a400d03c01d1a0911100d4202444401460742c0c801c0c1e00c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 976111636 1250 976110386 976110397
    0x21170a090c0519060f0e090408090906031b01050706090b0103140d050a0f0309021f11010f0e03070b2a030403030506030a020d021003061205010c08090622020126010611070605 77
    0x6010a103000740c07454074066103a4880216000e443c6030341f02e251500d004c0f1403030381c0801c4815100e1100d500214207203040001c0c0d031001650f82848846076158011700103580300d820442c1c0c12101c403500c50f0790110010f03001d11b503154000c508c00c4010140404075055414242900f010310036080100a010031300c4410750011042150581c64100001c2000071030000c5250601e500d03c0f0040146103190444d6005940201000010f0b19904000c00c109100d11800e0310a54212020510050b4424070071030700406c004020150b0004005d5140450104269000007101e15468192400c80140401040b081c9074050050540c803031011005080898000c0e0300168082492150190182181045220102d0f0196100001405544290255161aa00d0131a020300b44049000002807816030100b034a11400054407409541a07005803003003c5400c3d0f6640b03440007200a400d034104050700e0420500d4105131100d50327400c5855403a01a03c5581800c5010300380308910000005103500c60031b820044158440309452 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 976112886 1250 976111636 976111649
    0xa050a0b1812090a09240902130b13030c0308090916230c01060906050a050d02240405061602010936060b04180f060321170a090c0519 59
    0xd4881807a0f601041356902283c0140c260f2902c1c0040040d00210426030743d45800c2c1e00d800c81d030451300c0d495003644c0341170b800340d030311282d00c10708403100103100d0002c040b0060031081e8083c00682c2c2c07402d0b550362150441d8078001d91040d1f45900000510b0340050a081c0c60507980b0021500d444e80d0324441c4c6020041511100c900d40160801800d4101280a0820030454100000d100d0081c0105500c44418000400b6907201d0136105105410000030300c1c0c100400d030380f00c0c040d8008000000c00907050310408803028841d80c403442001b03020080440c080d039406001c0c007a5078000c4560b04900401c548009085c9600039044054040100030f0641c4010300302010307030b1406040da40c860001c0b0f5656401d480014101036000a80d280c0c0b008200400c1c00c40b00c5405600d900e80e2a00014410440003824a42c2283c1260001400c03428552400c26401d10001a01107294140e40c07800e07031040c0000ca0320000003110283d544ca8880c54840c8400024003681101190150400b01c84000240400461100b100e181911400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 976114136 1250 976112886 976112923
    0x309030f3215060109051306080703060501050306100b0a050a020a050604080a1d0d1e020904050c0f1905091003060c05040f0918060f020c0a050a0b18 66
    0x1081009a041c103120300c800c90314140300d03048008031126503804a004010440c454440d03105501c00c03408498050500408060312041002c82c1401d05001c280600c4011403180360b41c40d9000055103200800039a0700840c0a603030700284035410710782050300300f420207022456a42c58642040c0039401580d401c40e0f040c0126410216511401d1020aa04040c0f81c11005441800ba050030003040c400e0310001050700c0c0e1030035379030180020294030300000c2480c041d0091079040f459440b46240007514580c1c01c1403136540c030404161410b42d0180d0020384001e800311000c5542d40c11088812000e8148800c481c15412012541402c111451501400d419600d9100c0d10388035203450303000301d1440301d10100b00c0c0c005180c010400b0300540c000c170701c0050000e5100e4800d03681e8000c1d010100098401151062940c0d5001c40b50b00c44e50500c8090721024060051000903800c155420410311202107401c04c4511340692198001d030084a0507410a001c181400404502040c40d1012008603039410100300e42a4260741e026a6 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 976115386 1250 976114136 976114163
    0x10207021302180118210b01060f0225050d03030e060901110d050a0e0a050d140306030d03110f0c0109150212040f050a0210030b0a091a01080c0f040f21030903 70
    0x40b50f05c81c1d11940e1001071041d020070f0b5442e0903c0301103904208028000c10201c2e010380d0303071041c0c220340d0280304161900058202115400c0180c5022945040c0b180c0070907103d404540d2104000351010819510441c0841e50740d4020f103090120500110703600c48030800003000300700c03c2d80c800403615105101d540300c000c0c2d0360b40b40050f183c02015403040560f000c00404580c81082c06180c1141d071400c5d000030301e0f004a0307881d400940c80304140c2c208491140202a000d002d603c0e414040a8000e000d0703100050080300004d01a041e50181d00c0c0d0090000761980600110f1900c80c03608104036408055100465814010451030546900460803140c000780d10070010b007806c00f21405c1c118202030300c0000007507100e280540e103a5003c80e45074202114600d801c481a039602591400200c01326409021520009095014092160b601401c00305034030020482031545486400140a405a84182c000351090501810280010118200602e442e10140d2a06d020125281c0c0c07009405128184402420f01e05070216 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 976116636 1250 976115386 976115417
    0x80d030b0a0806010611120a0f0309020d12020129030a26030c1b060601121a09070f1b020603010b0a03090b09060a0b061e160c080102070213021801 65
    0x1c0006040300c0040d140c1c2542c4940005000303182190021031a485020030580015141808a882d0341d541d6899801c08100d071100c09401070646400c0c180e85c031880d070740e4601012540500100c280400f2a5000150784140d0000420030812980040c02501c03994001c2003170591800101001c1840d0009625581d00c40c4d80c004c0403030b0004e40c90100c1c50140501006200d01082c1e01d4001c0d0a01c114564103800760f815821345a503940342c2c1c0171112140094400d00c4c0d04000c41c40c80d07510010070510240500940e034503804000c64200d047c2581c5e030b800042c070f80c5041503990990001214030704040c402a500702c0510190005002e90106000724540d0b61400601c220716030340241d0001a0b003992066150080c2e01e03004206c0364540070120f80814420341000d00201a51400404840b601c082011400d110905410001e41c9141c0206030000303450291840034401044c3c1700b50b070460041a6590000d60788900c0c1d88103100b4a0b080d14100e10400341c3c010720038000e2404c1c104800c00e800700380c20710b042046012a0709 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 976117886 1250 976116636 976116649
    0x14100b03010c080c09090c0f070c03020f0117040b0a0f05040b09060609010b0a030b0609130903021608070b2506200403050c190b040b03064603170307090609080d030b 73
    0x421023000c001c0014180f0400950702099411280221403550402d01c00c0b00054806580030b800c52004440d0a2001500091070840d40ba0340220004400060340c00ea42888241215400d40382940e20840c2d10040000400701001001ea0181d000c1c1e031600029450441024113034024001090241915400c0821150301c0b21f000380d840152008000b1207840340c0c0070011078028000e0a80c00c0c0c0050084800c90001c40d00c02849103411203803120024031041c7d15001803070003150091070341111310b90b00312038001d410514061480505c060180c0b00c00a00030090088003480003405000c0d501d28a07106103c2040421800300d0205203500041d50f40781c8203008800308015001109401400044901080214031101d42d180503610450301034413041114000d0a80c020006901d070748408038141400151180803005080c1d58100300c1801d003001d101a113483e2b60780d00d040d1044914114880307003004000c01c50341c0382d44800640c000340070314100b4648850030203aa650721400c80900000905440d540003420603221003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 976119136 1250 976117886 976117897
    0x819060b130f1103070f1b0b090715030b010522082a03010207050d20071701150819051c03051b0a0e010c14100b03010c080c09090c 58
    0x5015a0307490740c40c20007080042505181d500b50705403074110804a07480400d400c890044035940c41d0b0410740c0c00404400c0313079000500990003810215410021001903410a182c0b40907040310406852420b081c05c002203070001200804800305400c105080c116648c1000485004001001ca0580072070000030480b02d03040071a521640d071621903d4401c51000c80c1403052803102c141049800010340c5241002c1500340d0040940103002900f11000075140140121045c207109450b8036080e855801140720450304020f070035400034180308081114071030003882c00e00c14054602080d01d4514102403d008219a450f04142403502c45c4a88100c1ca00c010301204020b6415030040381c010032100c00010351b0008011300016101c03000359124403a55003442c6850041a81c003803800940d1032440b916100d100440b039074011200e0641d0f40703140d21091401901d805002c80450b503002d080303010410105200a05086071540382c41d44080220000901880c2804d40c0300b126410079040360040040d48a0144c61020313817151 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 976120386 1250 976119136 976119139
    0xf05040b12130b0a052d010620101a120a02010f03020f04030c0501080106020a170306010e09130308010519090504020415060833040e010e071d010602070819060b 71
    0x2036074100a044c03036940c0c204030b100d00203040b0a4495405400d04c0c2c1c0c505061344146e503400c445c1c498001404510710070000ca08407600c402d0410109202d80a54180c1840c4911005026054942c0580603410b42558141880c4240c2a10303100d02003004407040c0d84d00c0d075040d0740c40281000081c010038694184241c05603031215902c402d0340c42d600c80d62072411a034030107101d114079804203606000001e90140045818150075030004002401480180d10541e059400102100e050000c3d05a10f00041c0e2662070015125040e4003074014140b09a40c1005842c4444c141c0c8090f202d001405200000580344a4800c811500c10b80d40101d040e8036644009000790803035426a0300303542d502c0e2a0000d40c0b5603020b8502402030f41c400d40c690700d240010030b00300b5a0501040c6c801e02c00d0011540400545420a07501511201c4110340001a03450446105541000300a41c0540748129400014944124880705091300502030b9000070b014480c03400e0649a100d190100d038029003901812413010a2004a420a100201d030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 976121636 1250 976120386 976120403
    0x3070b040e0406050606130e0714070b1b040602100f09140a170403020d1b0801110405040e01200c0f0d0807030c020c010e220f0902010f05040b1213 65
    0x4441e003212007a403904440c10380e4614100000f040040c201300d0100c6400907108511074144504140486003e034202406910801c03010140300341c01c842d407040180805074802c003e60070311410602a00005851803084001e803510080104010458001440f0180842c2e10b0b040030030780c01900f01256005000580c40a070600321100901810b152022400340502440395030018445110144001d08601850000030340240c4404440c0010810017003800c4450014880c404400c1e948400281c1d0035604904541d9011010100d810701181c686400b41a44034103009008025441c2c501000c0c00f0b040c0c158010303c03034200e00300098a600240007800041c18103030160301190030441c4200d0000300700d10130031505034000034641810315028510100b1078041c0c0701d4050b50350510422489041122078600181c1a603802807080343c1000d250580ca0082d400b6100700b411001544130464000900000c2d01c4048139010480100428400b09841206803016860701c0003106500d59580041d94405a6000402814680d0b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 976122886 1250 976121636 976121639
    0xe060106120f15030c180203010e04021309050f0d20070603090507150203040e060405060108040b09010605220e031201140406030f0c1404110d02090f060a0804030e0108070e010e03070b04 82
    0x118203400c003146e1110390306146146800302c1050403804203014000c3e4803075208000c50b025103040c660180c0625100e200008201c001c0d59902da240000c028940346280c0c000e40b11803102d00d0307041130540c194a041c010b28102228403a05207991078642c18090101815338603001402404010406000646074000c0c0c41985010740a001941e2a0014843c49418920050025403241414002c09020f400181c58015103030710380c4c1c0d42e5004941c01c000c0c4a030400e5940ca020025041c9d40301010856445078000d00301002c6000812200242e8000001c0c1e103039654400c00102c094041000c120604440e102403610611038801000200500703203d900c00b40480000703103584c50a1181b08071030101100c2c20110a1031f8081030040c1800141d41c08103400e0b892515040c02841c1c032078859500103050317421004244060110134000003a000b604030220080c00640c0c640d00b004200b5030400d840131594482401c14500614101c8401000081c4240d0318504114114200550a80b010455080600f04085000d51101d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 976124136 1250 976122886 976122893
    0x212041b1e08010506040c17190207060603050f0604020d1401150803090a17030409020714011b1101060b03060d05010b0301020f0a021002160209040c050603040311010e060106120f1503 81
    0x200d501d07024a607890b518150203ea2149010711900070fa034680e07511010642c10261801c00c500c284001d00100a503110320744480d90900f00d602c02000341e035210364000548641507081051500c070100c2013000c0c0c940d000c44140005070f624448a0061aa80001c2d40440801c540058502400e0042417030340c0041e16011000c80c5641020015000503001170380c03c82001551042c003144a501180122a400e07002000b0038440d40314950002e00e40079019804c4156010340c86a6100e00711610f821040000714240040d44584603808801440e034036120398020320600c0d0030020a590144009411079200d850456034040400c8000e4200c00c0503414020001c644401515020004561201c0d003540014010b220105042146910a48907449009082c0303c0b90b20700d06500307006940130094001c2e0b50000610400007090f584900c0154400c6100c1d664003040d00050401c0142034800070307020b10107a40c00900051040c00e6000300740c281582d07140e441c003090140d013030304090004003003a206d00301c00424004004011b1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 976125386 1250 976124136 976124189
    0x70b090a0209010608191b0c141c08010f03020117041a0c0307270b090111070f05040b1008041e020607060204140a060903030503060a051e03100212041b 67
    0x1c0030320141551482001ea0101c4040fa0700008081500d070b186807151903501d034824480e940808c5d1207a10340d80a1040e03015085840c0106510030405604000451981c030141d00104940c0104100e40d5080000c500b198000f0300407900c05038200185072140360000f0203024030046041328120180040700d40c24141138074020305984c411540c15004c100040f101d9400842c507518080400d0241c0381d4040d0000d4104a012026a80040d00307140c100702071035407105403414050007404018464143c1d104042071405082c07009440003c21554030806400c80185001c0383c0019001d540700c1e6001e94580d079465081e419281e22107403000350103908208003113800b13400c02805038010002e0360b2103040d0680764204910100219500e44c1d00464002821401c0201b001902503000395400c0b0400070000240c0580714004903e10218a091040303c151361100c2200f00c1e03080501c40740114881005003580351045a8403000c3d841c5030040c00c014124405907202c02690700f40104035030007401c0188240c400c20500701e007040701c5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 976126636 1250 976125386 976125391
    0xb0c0105010819020906060a02070b0f03070314010608040308042d1506030c17070b0a050d0e0d0e120c0d0c030506071b061802100c26070b090a0209010608 68
    0x300c0c3c070a00c524244007004043c0c0701280c2682c001c000c000c2a649134010300061350082d00d4000c1c29441800408944220003102801018031440d01c1161030780f4110320010280e80700c070140301000c54000300051150381d0303020f90890390054060401000d00e40b21f41c50316000c1200708c0b080010100c4036003408640f400c00505101c0c00d029004045200c180c428001021045503260301c001402c0c850140c5003041140c501a0109400c056a9426282690794447c1340c814154415170310f11001560000345920110001e00c24030100700d24400007821041c2c0240c0001d0102c10701012264030462207030000100404040200d0a041040980406484492460100349040c0c95010031a454080d410024403528400d01c268120101880000134074100b154561100401c07039192241c00d0b40b40748400800c0540c9a141c40c00060583d2503031410142801c7d42803c400401d80c000590701c031030458a036102e205060040503100b07400d4001461030001c1c0c03a1201650714003140c40f10001d4100304403d000044880d003144003140b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 976127886 1250 976126636 976126649
    0xf0112030f0f0c1b05130c2001060306060b03010501030515011d060705011103061f0503070c051c081603110901050c030d1a04050f0717060f04050a0b01090b0703020703020405040c0b0c010501 84
    0x110382d01c1c10306c0c85841030301d010240c00e00003d0354904280c0d00c440d40048004445111301d400018640e51a911200c0c291a0583c0007d49503020000041245590600c9155403251102012003220b86080700020056100f21100d2001402e0404c80303100207035500001c82c0c01c0c095003c4000c000c80c0b0045002e40318503800032100b2038803c40d0366020603541540701c1170030900798a8a9a03191845d55607403400035560303449101010f0b50705201d00c0c2c6c0d490080700310300c9000c41c0540165413a2072803586000040c0c1b242601100d030705075007050705007008140c40c0c030002d0301a40c6100e4801d0030925104d1100c100d5651070740c020700f03094024150030084441c0707104074081c12035124044250f0301030015a54030b410f030981251080c1d41c90400200044540010f040d581c2c40b009030455001400c5612203415400010144c94007550059003c1c1c3d0f13200501c0005603082000b1000612210003518101304080e04d01945407941480068003464403640050704100c0c81103844070203041100c042645504d20808114000c1009000d0318 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 976129136 1250 976127886 976127899
    0xc0f190219120602030a02070519060e12040902030a2405031612060b060c0307060518061003110f0a06020a0201090f05060a0e12070303080f0112030f0f0c1b05 70
    0xc000c06140c4200361000d03101914400c1030700901c2c80e41c070040207600003400040896400d004030000541c050007900d840401441d5212842c0f051424000103c40c0d1a0445070140d0348001300c404d000c090b2502c160b800300c940148006880b07590b01505032010b00100d040f06035a034510783c20350345420039500080d041900c0c8141c0448070003100d040701440d2410100d004140410104141d040002036064106000520000c0c00d11070074040309070b041d00d240d50880941200d0746a220310803c0b4481c1800c01104140140500c010480c41c1840030004e55560000c0c0005407084484203140041500d0303032040242d03d404050716074041c3c1591210700035226014048203d0000352000030010f000c4220343c1c0c080c810ba610040c03500b85031034035041d030680d0340c04000d0b4203150b00301001c40032201e0700b003d0034000b07000114026103450089150401a1a0324281c0c160846000d46003044a084040791b0b001001002020750f608000d10700c510150402d03210b904070030000401144412460f420701d061001840412a0402c1e81d11 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 976130386 1250 976129136 976129159
    0x6070f120c0317060904060b0112060f05130207030806060313020d030815040603051c020118060b1c030804110628090b1801030b0a090507050426060c0c0f1902 70
    0x1201c954000d689050f80b02069401080116086500c039000032324050504110400e51401c8003015101d0300d62040380c9140000c981000f4508058451040000000500f14030f80021907178081e03d01000540014021280400020410001160821002600200440c20745a0f640c0380c000c01c480b00403249900643c1889042184904141c000d51060b80d9121380a00303100d030603001c408052100422542c904540d21400480d004031401991100c032a4003861010581040c40c03014404c1e1030180c03042400c40d01d0f000c104603202080e0b000011031341160740003480051440c19440020351038060820705c44040514080304140c540104014030100003240d8850b01d518503900c2c0f0809505002d00e800003140b40d070341000700082e10340c404d5000075019800180341c030000b180c40d0582c082c11210100c80840c00700f40002014402c03000f10f4181040154003600000e0386040180c070029884510150490001820100b6140c0214000303000079468090b08a08483c20700e07080400f440c08245400c0010b17401040701058 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 976131636 1250 976130386 976130417
    0x12040915060c21050405090a0209030114010303050403110f060c2b08180304120501020c07090509031207140a0c150603081c060e070201140f090a0206070f120c03 71
    0x701d00116035085800f6580300c100d5255800a00e410300700d00d490400038208404a8a0743d60494410b0150808030307001602c48900340241030840303103c0c141c91084200004010000030b0b0b4008100e4055980c0580b41284a080700008509000380c48100e8030745c0400d01141c46038090074001140d90840c02030701c0d002e140c881e03007a05036900742c0508480842c000880c40d5001640020340b40c1d1025600c40007480888bc5002d81d2500d4410310130041050403213441e5000900080002401c010f0000074100e455000c000a040c00403981b5624070482140744030a5406800281e00030f80141d450807a0108080c400c16034840f2038000040420044050898144224030908034400c0e20522402060b02da20103000b500c0d002628076009081aa0f90707812100d143d454003008281c150110099070300402c010b400104141d1044e0a0050011200a200314001c0850310104075020200040c05451240c060710130702d0741d607610350800e40015116268090101c1c624070050032403065004080c0c0c031a403070003999500600c101200 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 976132886 1250 976131636 976131647
    0x3051603120b0109081005130203030c070611012901020a0c18050a0203040b2404113114060f130302100206040c050913061a15030105090411031204091506 68
    0x14110080c0c1c02160306e82000104c6030300a5411411915101d00b03026070302d0740001d00c1c41d4803070380311088680c0219404010168018610f98034880341c0d18000c1c46101ca1410a0780d07140541c0c1184001d40000745088850300f0b0f4000d003e07106907160400c40c44202da54036034041060380145a0119a485894600051140c04e154801d980c000d5901000c40b058503200c1d0603031080e140c0041c0c0700e04440100601d0f00c40d281551280f041604901d032504600d51202190f000c110000414662800f502e865200b06210035243c03181094015a032920010607a0070161001080c9540204401d19040c0d001c001740c80890044a0250701c82240d200321190401c1c0301820307104a0300c4540035640100f2140d880b00007401546050040c00d0740c8000d5200c0d400030000d00585034a416242040030b030700714100300300c0d9141c87c4074100036640c40300e005c8072142042d240d540742201080542500410290a8400100b44e04803d507500b4490144810b00030704075940c44984400091005001110400c000003071004030004110b4001c6 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 976134136 1250 976132886 976132889
    0x20120040e010b030910051906080303091f020904020c0a02040b010c1208070e100c03020c0d031403130f2f130c0917070e10180903051603120b0109 65
    0x141a840740d991030301c990401640c102074070b468101c3c01080300c070040a440600c280c0740f1603c00744484c0c0c41c9064030400544101c3c0c2007504122610340040041001460000072180b1840b100000c22017510aa00e10701400280686905198002e00026a241080c00001440448680212000c100300d10000005558800c13a011001308024807031490703140c5960045520300d50010050a0010181200c640060665182d80c41c0c82c6011a07010b0400e1414503504001e0003c03200e00956407816001c0310b5403405030661107101028900070310004005041c0f1507050104005d141d902016103544441c880c5444c04a1b54803007030200301d003201010141040880c0c1d0b4840c60020315006071070f0030900080c4402d904007038204007004000303200842301300041001c210044950700344a6400070317010150804078280007040300902012010009180b0501101c2326080406680043d602000200d11800b80303420389d614012124000c0940340d0442d40c070030078540c02c6042c800000c40000e070308200c0c026100005459000300b5 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 976135386 1250 976134136 976134149
    0x20c0a081018020a12030203040f1205071a0412050717100507090605030402040902040b060a020732010f090b0307030504020111070324020705060109140f010303020628060602012004 80
    0x1071360401c0040078000c4584200850092041e40c1c03406d81ca8400410084910ba8008402c92034600c0d840018090180070501c00f070310142103481150054100380900501542c0500e549402e0075101c250200b0004004d084d00a0450031044130480035222801900e50b20400384044605081000103a00d41d4070842c5407809035091915a141961225000d0200824041908a0308150344608000c102d50303c40c4090701a402c42640204140d90600c00015039910201408101c500321200a540341000360038108506e8040a00c0d0910181000303178021511004107600002e0701040c004207000032a581038009921850003a02d03814514040ba0002943c0c80c00c0c107210152404000d800070340100c562501d6142400081540301502b0422039403509401c0c070200b0303030040c01084d40d124515680c4592014002c1d0b40042102004815580345032006502c81c48000c00700e04186d41c8601140c0319103070000501c40184c074400c0300200300680d10b98101034001c01980b400302450001090030b40d912180880e0481e030075580e4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 976136636 1250 976135386 976135399
    0x406020f0d08010e4f0b13022b0209090f0d110312092d0a1b080613020102120f07020f0103020918060a33020c0a08101802 54
    0x6858036410340c403100603205401c2d07100c1203180170400c040644070120f201c2d500c0c0000074401c3d0002c1441030318880c2000d41a601c1142450000301e0124004d1095544d01080740d60301101e51810520004600e840000c800c030710b54180d6003002d482c40840c3c200c3c002429910940d22103e65441d8800c0059540c044000300504603401607050011a80c0300f2020040c00e0b5040f08102c9081003000100100726000458541215074400c0807084440d0340e411902c80035007200c0340d84080c48180904200350f02c4000000c030141a1001b816441c0e80205641c0b812070000704815002d1340c042d0700300140a1b040455401100b80d006106480e11280d080b445241120600440310a4852801c2e411f60300380100c078a3361002c0319060550911400100b41c880d2071180e40b408101400c07041652070103008100c5200490b03004400c04110b41c04151010004070840414030041c548400c80002c07030151801c2380b81183c901e00050300301d04510300000b8100000910740043c0c81000c40103020f61809002c0c0c010000c24025170107540102c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 976137886 1250 976136636 976136639
    0x909060105090c030c1b0c060418110a0815180901050f060906010c15090b070f02012009010c05012d0501091b050a0302040b071101030f09150c0203040504110406020f0d0801 76
    0x40d06c11010740c0a50b2080246c1d48410820700004050750450b52046417402d405517034400d001c3c140340c070401c0f04842807469540d040100c40d01004000240041207050b8040741e0b4140c2c1b518030f5965412040d400c82138240041c885103004000140a0002a10101c1024100308081003151902e45501c030b10625040e5038071480400581c4230346002c0c003003070442c2d00c200703513550540b142c04240203c0c0384510640294941c0d80440d024810004d01316840500c0789141c030034a40d85500e040d1704c0340e44212900903500340f900c003a9a003a9030501300c5c01044500010b400f4014188208040000d00001c1c00c610b21203000010403c43ea84c4c0d145070002e42d00090502c043c064429a04201d2040c01000070308519005031900604194481d09560016404070344280d940842d0036088480c0d5680c14050050044441d81c001d10108190f540e400300c1003910b010131b00303082c2501c0e241d20640e418400c005407402400010428802050300c20302c0f00c00d640d4000e0241380c0050040390036003894000c000400c06c0d03240409941c0d50901da07 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 976139136 1250 976137886 976137907
    0x806010c0b060d0f05060403020717030a0503070e01020f011410091406040e030408062703090d060b03240a0b1002030d0b1f0305160306030c0302060d06050909060105090c030c 77
    0x203a0000316036026080d1340c0280494401c0111510491103500240422801d24040070007044460058441c640c2c000c0285043c455407040503250040550304142c40300384801da00603801c0040c5443c000d1695845c103100ca910051544c280c1a0141e4a82402d03400100e4480a100068614900032035980c5050f58010031410b0411358000111210301c041500d0610340c5843c0240d0400d401035481c80b0020080500400a2000180354524144404d1000f03514100400c000310350b06a808400180032503941740c0324a0140d4905000d00b0305e500cac040342c0da02c0780d13010034014500340314500c01d550091203207240c04011815424980184c1c070800b070443d001107040c501c50b00d08403400780c15a032180039007003047c40e003d24041c1c0c8a4003000d00c003009501e4801040358030749140d041503461500000002018200401000410000e1300e032102500e0301036900d2952540074a1050700580801ea011355001440f0300104500740202089840c16690102d4841005e6111503c07600305a000690b1410002101080402c04ca03 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 976140386 1250 976139136 976139149
    0xf01030b03211209070303030f050405061b0f0a080103110102010b0a09150e0109021c051315060f150909020901270510030e1507090b0a0302190302040302010806010c0b06 75
    0xb202124402d10707103031402c607a84030000c030042a40c2d00c81321036000c480b05004041d054010380501d050010740030010391030310361106036881030041c00d1094200c0c08244d03003852801006080b10000840c0040a590fa600b450a0042024009100a5410034007078840013240d0b603c18001c81a010700c3c020a0041d0050406401ca801030002424000c0c1c21441c5100005991040100701402041c4160005840382c0d405a40486244075007100070705d42c0d600e07202c2041107442d150f85486c3c0300c3c503400030101d1003000200d0502d54010225a001900a0704050100103030f409a60800655001c681d40e03a00d5480703d6890b00c1e48410ba004001041c0c1c007081d0184501c10070404544031742c000003610120041c0e030080e52a07010032180d000080399400001d03122112040968002c000305800101030324481295842c0c0090014400ca0300f6006445c0745100c009140d9888500c0780d0145c2e4070ba4005c40041444400e44c540b4040c0080d800391104a02060010002511960264071140482500100d00020955442d01004070 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 976141636 1250 976140386 976140433
    0x1f14010b0d0e071d1006050423090c03010f060509010e1201181407061b0206030601170702030406122307050d0e0c010306150e0d0c050603150f01030b03 67
    0xc0e407035a6628100500d240c1041281d000f4000007000088030b240518502100c040300070720b20f040769604e801c8200289580300c000c9808885000c10303002043c1030501c2441d1108210800004d900c10200802d21403040380c1c010003141200c044000783c0500903a9034209461034001c00a41c107000c200e90b00c0401c101400c1124100f2410b800245c0001a40000500e9003460900142002c1c0c0e81c5104616030406c04031410403184010300400d05007a1070700c04009404101340305071401e000b8002c0d4400f1004c6100b50b400340907441600c5420103084452403400b07990003544c0340c0040c424180010031144510801180038802c001c40c204001801c20780241800b140c500715540007034020010800c0c100480030250943c5d00c1031b4194011a0b0f0007030308052031a48001001d494907604148480400c0000070104550400d0050702b0456095400c1d18945403541020070202035603502864205d6000420810542044248451841d008581450000b03000d40011402c0360009014a50142d00441280c3d4000085200ea41d0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 976142886 1250 976141636 976141657
    0xc09101a0c030a0f09080a0209010b071112030304060b1804230d030e01050a05010b19050702220c02071214030f07030203120c070218061807021f14010b 67
    0x61400901d004828659030000d800000082e5030181000e030210b42c4940d00d14014540e200c002c05410b000c03a00000d240d280d041c4500d100c5500001480020020030f11001d040998000f40142000000c0940b906d4a90317200701d0781155014030302800000e1902c1c0c480e1400c0240c901800081406039625074030720501c10200da00300c43c094028045d003070200f628108401d028665944d54007240380034004034100e094410261002c00801d003401e005005160940050b660002c2c1e100e6061507000d03421200c192400d10540202030740042a60201c19100b07240c180000c01c2919004108118001401508903200c4c000c1d03000b81c880e480027000040c000f01c3d1102c407030720901c8116402524a801e4038004074481d6540080000c03400368201044c2c0500c8882c0714121503900c03080044d10f45d89050201c1d80090460000e1040841460034408041401500c030106840b07030192440008601d6420245c1c07020b9599150314801c2c84d00d0b81d44410802821b01c07514010400b030200d1420340f400e516405c12b882d4480c0d41c1c20004004 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 976144136 1250 976142886 976142939
    0x22230307030f3b09090c030c15070501020a090305100c0203180a0b03090703051b1815040614040b19031106130f060e03031204030e180103080c0c0910 66
    0xc8600c0c81c3e8148189038101d95802c01c600140044050100200c1c00a001604d42d130030030074600d40183c5001c548001c940100701c40c02e000c904e0640c4d039901113600510744082c041e90700c04076005103c140c106980d00d00380c070b00680864600400c0303c115001a181580f4801005800600c4102e884141c0e05d01c4102e83d84100a05c114400c42e2660b03d0342c0c4070360f0270880740b41510b40c0c4401c00400603c0310500003405c1e904040c0520f03031024481c80000c00c0340d50038039900703041c1a0a240c4000800061703000410740f0380c060b8020030501000303a60f1500c408044e4055240320384101d2030f04102440c42c4c5404c0045040304448002440307100c42c83d43c2ca4404001505140e200d82245007040107044414000c113840024101071810100594103180004100001e41c00e10180280c0c0304108a01c118440103961075485507141c03070070084540b20900454515a24200c0d209095800303200080104103004000d02240c00002c401c076080c9800d00c90412007100c2c000da80c1150501503092082c0500103020005c58044620b50a04 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 976145386 1250 976144136 976144187
    0x2010e061e0d0c090e0c0a0804061e060807050a26070e160206070924020c15030a0507080609130305090603010e18011e0522230307030f 60
    0x50300d000d6000c03101c88a9400d40e07500260f480607803c00100710103010428820242441c080314a0071051140c010800c080c8100c141c0001c0c01c102c020b40001c24a065403018400150703c1c0c14050b0300240c689030146202e81c0c010310501080030300744820144111100b4040340c1d9842c55004071b16108001c0010740d44c880310701583d100495080790b04050306000e0115511031241c24039088500070b007400384c042c0403503080000891040194203480041118048103000c1c0d1841ca8102d030742e00070380c54841c0c40c0300100d42104040281080141024010358802c0d080040140115543d0050445402200f01e5074039500c0044000825684101c17401400040c41c0b0a0500510700b11180c0c0009000741c20036440700c25408458000c01c031a030205d21805698440d080c10081c4085040320f111010528001082900b60a42d10400160843c0790f890b10b42c0411025408450251222030416448219404043c000186948001c46988000c0042203070000d6030161307200c0384507001829040b1024000a00380c2249441310130f00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 976146636 1250 976145386 976145437
    0x1050c0904091b0e04060b0d02150c0c120f010b0d0515040510110405120115050f0a05060c0304080601060908212101090f09020a0501051e120a0605060702010e06 71
    0xc499001c2c10030003410130354901d4149403c00c01c3d201c0000c1014068001c0c02030308401a100d4143d0400042d05440e851519040a90030084c5071001410314203500142c0400700505002000c5807403040c08001000a2104213180c0c4d0902045c1540c0480c010645e41c04241682405850720139820f81061251040c4c03080b4504800c2c04400340d96032188100102c400000d800c22840c90090f111007000180d0304020720071042c046441d451020214800c140c0030361150078403001030307030741d02102c04001d000300030812030700c580c18070450955036003141c05002da45e48a03000c008100140507111303c0085030390301002040000c00881d403800e80b4200c1c82081451240c0d007070210300c0d20710003903d10001e0300004640108002c0d40c9440981000e0b1000384442800842c5400725150140e00d90012140c261030083c28199602ca07000d0f400c802d0303c030715000800b103071210003ca00003503010111141c0d1401450b05810601450751038908200440c424001d00a0105251002d4030100341001c4000d0011040b5a803a400c3d0b04020299 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 976147886 1250 976146636 976146683
    0x100806010b091c1a131a010f050114190c12080403090b040f1715040302010b03071d0609090102091002010207020405330301091406160201050c090409 66
    0x811401c9050404202044642031802080c000010400c12420b1801c4954540d00e10f5940b02e460f042ca0703d04540760008142c5004c914440f003140394000f421030542d40d10160050081e0b40c1c00c1c003404903170200701000010158825a0303520324603c900642c9031701d0322140e01e1010000058140080c018405480480c101217600701c1d6141d49100b10a84600316a854145001494031016400106681000340005c3c0003440da0041c40744103880160300404035104c12444c020340703030142480c05c4203421451541040101036043d0440750840c601501113030101622400502c4103c803072494007400c60010103000980c0380c580031194603080700c43d110005191912260105071f05154904114004d80c1d0002087c0c0d0440c01c040c0f060360b40c0481070b001c0000d0400000000080481400038954001c08110803c080701607400390f1240c44055071140c0445000d400c0342e41a140c8070300b01102c84e0500b0188003240030346064010301900344514903154140389000d50403010880101511901a11455a0085030034160117031003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 976149136 1250 976147886 976147889
    0x810020d1b050a0806060f0a0302030a110403080a02070909021804140f071e0f0b03040c080d030c020d02010b100f090b0c06040219050d02061b010f0f0c14030a0510080601 75
    0x3a82c42c556240c00b1084013514102026010701d0044c041080000c00c80d100c0f2100351155011586000b680c0c0380c44548000000c0c1180503000c2510440019000003000038500007001c442c0b40603002d80303000d42da48202c143c0c104d50403040081e40108020102ca4491803200c0e1a50343d20900c5106001c90080e54440101d140140030290400190f0203040240a0004040d032034440d04c440e42c01da2a002941481514441e080d06880307085103114000c008242085000784140001e00a0102183c0040c007030b00000401401c05d0000680140c02a0b001044001d80306003d8204604006021144030b9500c150040314000720480c084070070810030102c08506804c06400414509441100806090405004005143e01c10f41e034031307002e03003050544100080c1c1c954644903444182c046541e29200c0d035131a00d0b80d0ba040a04500d040519520b002130380f50041681d580400c0340c2c4540c0300401c000c4200748030010f80b00c0340c005400c0c48044020a00000e48905c010b9000300760310034407a6141070b1702c0f1603985200b245001403e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 976150386 1250 976149136 976149191
    0x1614030102071208070318080d0b010921060501050108150f0312040906050306090303070906050f19030c140f030103111f0f0f0503070813021f030605030d090810020d 73
    0x380003c3c402180d031b0500828565040c1e540c5034820720b180b65950040148116401d0004030b40c0c44590302d04860780103c054030300421089100060b41009130704403200c0c5201e00307a02102c149181200120315548a04001c920494420314180e038140582420050700f070041d00e0142c0da02d4403516581e40152042003000e0801000a200c012400341c1c1030404040c02e200c4d0040680001b54030034000c1000c1d40d0303440407203941101c0c150708240360313954028500d07400c41d4802c850a40c4014629105401c2c00154198800280740030195560314030f0300f500921010080c440d00750385004201c0c0074801030002c5a4404a20940c0e00b1000f0f201c000d1100f48081c0c0200410744908250000c501e9646079101440e4002c295446917504600c2c100f8918900202e019000340000b615012030021080f81c80c40854032411245140214881e28040c0d1074658044028007401075401405c0c0a0300034004602c0c031042c0a02c01300c40644030010041d05030101d00400c0d041c02900545074500741e250301c4403404a100c40c1542c0c42d810700d032010f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 976151636 1250 976150386 976150397
    0x605091e06010618120503090a050307050d03080c070b0108061501021606120e0f0304030302210a0804062304030f02060f01170c060c0d02070816140301020712 70
    0x1061405142402030040120300451aa00100016698081a154159519810240c0301108034407100c0d0078040041e08041c451805c0c100030141801400800307403943c520200c80303904000d42c9070802c0c0340c4c072034240b03204c0e647d00100740d070841a0010707004a06d070702e07808050300110a04007081a01e0b00c03031203e5420791144801ba0450801c2c001006006605811072580c04c0c0000c0207090b441d6400251501a940b1030401006182120700401d4600b41d0403084000048008a6280c00142d14810f07403030768860b100132400344c420140e1416014a0007966880c9010341290703843d080c42e405c407000b44c84540380100100c23002a6203c1080c1072180501d100b610071142d01c211400c0e01da1910f4070b000351140b192410725000f0b6501080411031540301d0f0f01061415103081c031500e4400d100c10030958600d000140b015550b40040c0100d21041d001c00006007014201a00742c0c00c6403013003503885400303e80b2040c08110714031580301041c1e001d004424200c40c60900008015000610701001600c80070340705107040034014009003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 976152886 1250 976151636 976151641
    0x6010c26070c030b060922020d050c13051f0f2607060c02120f0607030b0105070209010e09070b0a081315020a1e2607030b03070806101202130b1c0605 66
    0x14841002a030009180c5d04a4101c4092107c00214828150000a00c034140d6400c00d5410403e0a1042801969014095049035a880041c07440078080459013040241c1c01107046903105000c1e0a120011a8451582403440307a0038030401220744605a406d140004a024a80c40f000d400d00300715250040c02c0355030b13440f18113003800d02c104030018103c1c80902640fa8800c0440c0c254081000c16815041061400c0c0010004c46c05001031300c2900501c0d10181d030040004c000040c4400c99084024881c020701c400ba10043c07030311915003601030b0241e0420080013071f982c41d0000754501112400d1820031802106ca07502d16101000004e0241d9000d0201c003070004140b0020492850f0388180042c116a0140c180309005000d0100031048005501306c1100d003c41117140030a1306680242d00061241c00041c080c3c464054403100d1041d41e485054540c50071139424000c00007081440340001540c3d17150b0091203140c20402000b882d00246c1101d664481e400455840c803085900c00c2e01da00000720342d00c00d510201e060b2 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 976154136 1250 976152886 976152889
    0x5070b09010f1b17040311030414030c1c080c0313060e151e0f0d020301030308070809070f03021201110c0a060b030d050304020d0c03080d02040e06010c26070c030b06 73
    0x7a06203900d810030f0718580070245801c5980143e202c45108a01d00c0600007140e982c3d050803106060808031001d240d00001501140e01c0318582071700420000140c0c210381d50300c01208180044c0321b040e1031700414120ba050401d14002144000140084000c10080b203007441c10012540c41010083d61003c400300300d000118054074200712104ca10a840c0387c107a01400d00c0840d404044020348a04603411080c60005400f6151318030390400d6a1243c04440011901c07580c403454060304c849419129007000c604d0003400142a00c400154171020707561240f840114140ca0f5500344002d00c0b040d101080d45035500d0b021441c04a8841c0340162240f00100303001004454202c1c100501190000138101d80a070b0401814038182c50381100860381c02a90564128010b580039041461580c03e00e508000c029078000620201702104680203081030b1100360110300c1c901d0b00c0703410040d52030140b1107000804044000000c103405000701481600c0394060000180e141441703d6070740030442502030b0130843d01c464107941406042d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 976155386 1250 976154136 976154141
    0x90203010c080603063d08010e0102041703031b0f0910120f0209030a0f0807050318120a21030914010e070e10050d08040905091b030a0f06090305070b09010f 69
    0x32004090041d80c0d408040f400c0c44041288040c0324a44101c1b04040458440c4001c40030350083c040100200100f80704c00c600715010754031500c00c41e0100145003280303030314034400407045230301070f21b880c0806a0003241100b002c1005034000c003042043c43e0300c047c0300191264452001400709020306a41e07500326421346401240407914850101c5140d0761040c444442103440014850341c4064010f240004860640e00c2c0041c144c0c440c85800803e18000071a6a4800405006049092900458440048140c008940750f0384045204c1c000c0d0555118091001214070070b51003e100110140c90b02282c80c2c50203403502002d100c00790002203e030b80e540b1b4400c00e0f00001c1c2172203d08040d06802c1c00201e45814152511654040c090003198480c11001000c2d004108040085400078098014207200c2407030618121502c50b80c00e001000340300f40d211010301102c4c0c81d003ca4220811035000c44e8444004049464a500410340c0308401c90600c0001c000001c0841d400510191251300044000309440300104a00700a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 976156636 1250 976155386 976155391
    0x50405030f0706200733030504110405070203270d1b0f030b0a021309050a02070209060103051b07020d0602030903300a0b03010f060b250b0613090203010c08060306 72
    0x100c3c025100d00040305038004501702080310340d442c1c07441a00004581403161281c0c400405202d603039502c118840c9165805411040c880c0b805120300c000c0a020040500090725400c86103000141c108010140f0740c68000c103c08005040030303a8640c10507900d01030100303084074400700081c3d480070880c80140c80c2c40b0000400c40006041610840040c140c07655441c200b0709a0080e0403025110380114160b10002003a0342150003c1c1541981030040f802c04d480c1c03d10081d88076920071f9003e040c102000541c554003a000e114068544807200f981c101d002c60141c0811707900108412071748002c0c4110940c0c0440c60f240040c0d4000c2c00326a01941daa00c45d5040701149121140700c80410b605410240140783c02d4201d14200d074442e01080c03020414885031000a401000050480c0548514194001c5903a00340304e0080d03d60201444142c10700304104038041d04103501480b80060a041100d80000d070182044803103c61011050040401e50012640c0020700390b440b0080d801000034805002c0100f9883c2c104202038 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 976157886 1250 976156636 976156667
    0x8010c0203070b1308040501050309010b09011d0a05010b031503030403150608070821091206040605100803040b0d0c021e0c100c0f0204110d140702010e120702040c050405030f0706 79
    0x5404d5501d030349410141c0102d12035241845008000681b030040d0070341007801441402807118904d90b0316415649a40382031071580380000c290031070005002e1b5890748111b0341030300d2002c49a0b0b820f55071166a92090821904503142e0140414080000040d1601000e01c0c1401028400459883d050a04061408400360b00c03600e419801007407010071035071403c01200394542c00c11140d590781c2c040d504081540203401000c0c00c041c5100d07500070407081c0611703036100d039006062186140044135656410590b0700d0281c0d000d0040161800c10851551100302d600030900c4881130b0041c0e0b0f51901d030401c00350900000030f42100c105a045040d01c14001d00e000e4400382c80404032800c1883e29a00551900103080c540c807040207000c4c56a03104040c014280c3c903c10f54034245005c1e40240309040803040c10303c441c0c070415200c030005503080001d54840b1b603c0100300800e1400d6078408190810310707180c0030003010f0400f00d200081449030400002c200b41e141408100c0c0e150407007000514407285010030092001018034080d0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 976159136 1250 976157886 976157911
    0x20d02030f040e06040e060403030f060602010b0a050d031403070c110109180e0106050303070c0302040c05030103080d0b0d060f05041208090d051c18050c060a0f120608010c0203070b 80
    0x181101403441c0a030b4098600e410022202c550798a00890006e100108400001e8842c1e0070400080580c03580040d10312404c14070040c4882684c40e0000d900340c0300340440d1654400520003090106061498100c24154003030300c2c0c18001c40350f20b007801944d0741d401903610500141c0d4004509090000f003048070383d00c0281c2841c0c103445162901c125040040d90307100341180341079211310103040e80001c250880310140c400202602e507500442c0c40c000e1203da0080c44102d00450506001c503e00d030b4012810f0f0380c1260341007402e40780340100c6425000001c0506032005a0b000007000e2064012451510642c41e10074800b440c00101810141410b80e01001c401c96070508001d0200208001c1d2200456060003078502414a15102c080c2c0300d55100131b25844280799181daa1400f070000200401d1115484215030041d01a640c00104c0003003405040c1c458048000302286400c450f402e0302500c540b01085480c01032420010b54982c0b9240f54a080d0354100b210b81c0c0040e400811039401344000c2030a66034100c0500c8512 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 976160386 1250 976159136 976159147
    0x1e03100e0606030406020c0703080418110301030f12020f0703030c032709230a0510090c0203070b06240414032a180103050102280818030403140d020d0203 68
    0xb0300922000780010b01ca560046000b0300c880d40d00b00180005141e01503001a156615442051411642d1002403200c0741d05159507140500b8403138048038180c9800c03c10790480d0880d0380d141c42d1083c2144c464031500314800c2c407444002d0004240441c0300035500c41c0d9241e03681c141403410020064514480544900305466106a860b2901f200d0b40d0000c640c41d40002041d43d88c00309480c0380001d86203440590f403000c260800c005c26500c0c280c0c46548640403c110001d1625150031164040390f481c0e0001901503802040307048041251180d07044d50001000704681c0004224101d20180724a04408101600d200401c00740b2501d4403139213001c21941c40c290300500c9007404062006107500113400f03124001d000c03169004405030301c80d10345413030080d1981e00c14050a940d4031710306603000b03500c02c054206841140424113055080c480351204000e440a540d0f00e2403c2c1c650003030814000d90203074840c0d45180300030031000001a14000b062111144c00501a05080301582c901a0400f04080011021034004100 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 976161636 1250 976160386 976160389
    0x140d12020d080702190312020c06131a1302130b10090306110f0706050a110711030118050d030f0f090f050f010e030d0f060b0d0f060506130e040203031e03100e06 71
    0x42c1d900c520b41502d01f07110002c8980c030714034009111700403182405004500c204080c45101082400d6401d2091291a881000302101c070710b10340d2001d607201400f81242030342020141c0303402000c0c00121000072200044415900c0c0000d030b80f091400c680070000c220300075000c00c148016441104500e00b2600b15aa151030020505c050052207110001003d03199214081140002c0c90791106c810004540003455492910b4200607400c83c94800034180710f5030a01c0c0c903480d1684421098a115164044001d00100649480a40181c020350103100311890b07403051340d01041d8205000346d007940b42c000c00c41a070b180c0200342003030790910280019490741070f07041020f91090030000000300d42c0740d01c00f104000510182c901c981c060180c45142c2c080c811075440424206c4c030725a020b0f03007d40e51105c0325480811503682c2d1754050045902510507000b00c200c2e42040b040040300940c060207a800343c4001d00303492a0075000b04940481c0c00e03074610340c0754450b8004001c01c0000307403000f150f8001500625180700070a00d000300 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 976162886 1250 976161636 976161673
    0xa0608070507080f2709181f3314010e060a181226460e030706051c2714060f070c0f0506010803031009090c140d12020d080702 56
    0x800080c060070100c0c00a00b050b6903643d00200945200c071400c0545a1400d209010203002743d000715040340303058080d00003491b00c00c1d2410740d1880c501c103071140c60140c2180c00402c00b46400090300c600500051000c004040305619403e500540600b65502c0056461418403a1007034030808281010600b01209261440c100e10050307030941c0f005213500301648100803415000744c4800150003040f01e00c4015103116031340c0ca000b0340c01c04980515691070440300c0f0240109640c440542c407956000c68010031180c08009a400700009010180d0b9101260110070a40c1405821089601e42c10901030710186590400003001190705a49030400018661814000a03248800f5409414042030100090100f410805c2020501200c1500001583c80643e03461a04a840743d00450f00041104002c46010401d40d440f40b2600a900d030300301000181c2a8180800000c0ca4420500010f501004400040c0005461808501000c41c2264081d100e00000c016002e0400c0740058101020364100070100e42c80d48003541c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 976164136 1250 976162886 976162903
    0xf0311091e120d0c11090415020f0405030a05010c031113060806180a0504021f231204030c020109050f0105030a1d010e03090a0608070507080f270918 66
    0xc0c001c454090640c00078040301068a85844180200074142000982100b084118203000d440d010401a03140010415808400c07a002051904d840d80c48858510703107580a009916040058186003944540c00a4a0070039508000c8a40b6910f4000032022240c1c94028041c44442002c2c2c0300d41003074806c104081c0b00d5146409401c0410054000040031a5514070340da150003d5100c00041290070842e40f0079010b004100d030181e014030310702c2d03c01144591442040341040d018941e10005003030b00c80481c443c181c6080c0c0a030240a002d081c41142c119a00200c9a14090b40c800c0d00c0364903440050340700141080d0710940c001440340282c0d4a89141d0ba90308803003101d0f07228583c031030005190f000100e811502d00b0191082d808a80d0b2a10000780080e081c00030007028000300c201d0340400740a03619a01200c07190300c02c0320010f00264050250000040c00100034002080c5070503041ea0801d031240c80200e80c1d464104c070708418980320340807102c2d1440c10288149500041c2a046840714404903c040a5031407d18 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 976165386 1250 976164136 976164169
    0x206060307090b0303040306062909010e04150e070801090501050423070c32210d290f190519030b1e010611101a0306070f031109 57
    0x40c3e030001d00c0350b0398091003100c0145034031920803c080c64a410004c07081c04043e007009518249401c4030448400c1400003600c09440c2d050b59210038404200b0103001c09800b4180700c800000c8111000031881d0340404150350711403081952007040710341c940880c03441542c80617401240100d26141c0140744411400c00d20703035040422a01410230644410340100d4039240f501c800a09440d0016a0340c406100c40a05040c1c82000e00f110f00c0800d060000d42c50f03e40340d1b1250b84d00c01c07001000410040c0400300590380074181c5401000340c0000d0407018030921000c485403441003081402180a0048038034a0040400903000750103641160403524038501041e0326a05078042d4030300c1140c0058200a80c1d00300e6065140c0030350340c000c0914402e030400380c0310700304031180b0701e48110300251240001260140c03041c0070b0b00c1219629140200070b00c68182141c500100720700e0f420280b0700c0748207550b1504592001c0040d240251890782e580c0c0c0c1c0300d2121050050440c1e400c2e451400d4224800c000741d290a540b6403d03140c40c25680c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 976166636 1250 976165386 976165391
    0x3090f0602030f2d04050a0e0c03010614070501020301090501061e0806120115081e1501150516140d02010c0504150504081902100c020603040f0c2d0501020606030709 73
    0xc42c000d00e52007507006401c0c80e2034001d003141446000c54142c0c0040c100306c42085e6811001561164001098040208c40c80760080342d041c0010810f0a200e11883c2400c0101c0051580c5040c229807141e07400d9034000d801031a105900c0310010810740c0e50000325554003511070380c0300c04051600710400400c05580904030f50311030482070a03840e00300d94080d0b0000d0014102117400c8000282da614501780c48101d94213031408940801845112903010101d0520400c82d03290b06440b040d603080581e5408070203110461001008000d000805240c40150440d110540c0101981c0309004054100b082c545580404508116410084044401a00841030380c0030780b001101d1020460250983c00c40e0107020b1984200702c10f214080c80036411440106041c003040c0d0080d20380700006400741d80107880300d02505400941007842000010046100c2100f041e00003032080307004810450741d400103004041d044014044000780718601d094103040100d68008024402030010f0491450440d000a44910b003a1090140094 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 976167886 1250 976166636 976166647
    0x303050601050904060f0503010c0c020901090203070c0b0108010e12131a0705011b0e040c120b0a0911280903141009060e102c1c03050403090f0602030f 67
    0xe02039001d60b03d1540014104000c00d942d5035481619800c05449030324080e510300581486541d2080750b002e1b100e1178001e4040030507030b460581020f000b540014045400c2003070b03a001c41e10002c1c5221420b00c1c000c1444500106134014a0305069050480c529902c4848000c10001c200740b00b81c64141d203900315014100b00e80c0f485080480b0780c07a035502c43c1c804003c00035444d108150407400c2c1c1d00d00c42c14042d102c1c01e40e141c0144c2c2141304140412034030281c02900c04030f41070580f156070202668002c141e580c900602481c2c2e519560303041d10760a5500740e4034902030300d81c00850381a152520301414074900f000c60701d804e1039682020150107020070300140000f610841e004001056001d03002c20181911821051040103011414280b0300b004013500e82c032103115805545c030405000d028500a0248203280840d0004040701c4608a60300d01c0500400c805001d800380402c02941e0408410008900d4801502c011610340b8092070010400181904030b48080341d40c0f900c080c01400d9001042e501c46000c590900daa0b2031 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 976169136 1250 976167886 976167889
    0xc05030d030b0915030c0607050d140a02190303021e041406040b04030f21080106171b09030c04090c0305060106090e0f060109030b180601050409050c0409032304030c09020705030703030506 83
    0xf00c03081b10704580000e80098050100030001450440c58a01e60341c6000b060a51000364418611070408800016401030030800c42d07101804202c801d20a00c6418018505401860081e01c0450800740034031141c40c0c0400c003080005480402c0c0f0b4004401160064680343c1801c2c0210501c1c0100d020140900d503003641c0400400c40d8840003500307208011880c000c200d24110900420003030b02400b9200000f046400342c8803441c4010000c26002e06c2074280ca40410aa0b00a81103800f070b0070100140da4513110f00d5800e01040c1e11035100c4c0349000d60040502d040010700b5400c11520f402010707031248040000c1401e040052211a0040c56001034100b014a101a125100100c84915035600081c1006501c24103011900c42000c8400b00c804000e0015528039a0740d034010801200c110381c2003c1c1058008280101251806030701c820851032003810824161038000342d0401008541000754540c01c800000d0134024840d09181d51001002c40c0a000c0d03182c640c4550b42d49440707008203080141810f48410118000303 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 976170386 1250 976169136 976169143
    0x1509181011070b1015091415040b0a0e03190c06120902060d05180726011407020a1106160602030604091401020d15060206070f0315030c05030d030b091503 68
    0x183c10241c1c251450808500e4241d500756548501c46455111100c2c01c120b00d4000c05d482c41c04c07070300100740704041441c1b0401030111031401001002d0f02d0b01c0e0100804142c10340388401500104d0410340c5c542e41c3e100c4196080c1440c10039030128070300c0e0070130b044080380000409404101c000e0310041c0c584229600300c009d001101804640750020360000d0041000c0141d0f0700c080d03000c248162851110240c8842c04d040c1090b440c1c00f03250080b02d910200d99107078011503070125a00400d2100c0810000104041860181003507044207640610050300b00c82c3c0c0b688240b00002250726170031b080c120f400038500025040100c883d12001003008103d5038004c80020200d5070f599100528043e040000c605c1c8107140720780d01a000398000028080418034040c00d140f00105200240ca064a04070b0f0000d0080380c03110402aa81841000f07442400c142d25080147c505004480c02c03080218803030540b5200a50a01007054100005030001e1b80826141055a420550b1210051600000300c8849008958444c1012904 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 976171636 1250 976170386 976170397
    0x302120109051f0915141b040b09010509090702060f0c1303060e0c0a09240308070219081c0f020d0905120312130b0702060f012c1509181011 62
    0x145c40418440305442284c58200c11440e00024649003d269a61800302d4052540362401203542d19060005010f0020050018492008141010781c10124428002200e4010480310580160012030511075080d03511042180c012003414041418080541046079011003140b0001e0219621022151000d110074843c43d40c44420280881404949800c03c10f8040c10f80b00d00d0500700c0348610035510122075a4104501e0903681d01429291900015408102c01071217006803540b2600c005074000a070a40c02044840c1441aa00e041c01c802c1c00c80006004e45601c2401da181000d54200300a0855413540c8580c3d6201038460848540d000031080100c4140707140907808c2034000040209090020080c1f540c0a800c0c0038a102c0d404030701669440c49412a03c502d810348941c0d10203036400c8014004141421b081c202d074800c1220070804070203040c6451100c2c008042c1c0d03400320fa411446401201c1405c040380c002c0e0740100312901444652401d00e9042d5507803580107201b80d041d0780e0b488100c0700382500302208440 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 976172886 1250 976171636 976171643
    0xa1a031009140106020d03020f07110f130f0506010c0f0312060503010609062409031212050a02090a08030c070303050f1306021f05100306022107090302120109051f09 73
    0x509480030509901010078044c07a4050722030411070003d150301c43d0003140d056070001c81141c0c1c00d04d40d00d559080c00b0012030140c42039010b80c0c0060005c2068550201c80300300303503c0400010a4410b050188d200844001a103024104039003c59440f020450381a50030019550501d0407915034499203020b00d0040c95560055a855420300b500040c081d82c0541281060b18814078a480900c002e01803001c01d01d200c85e0b04a000402e04150307081000c10225403050880c04c6580c01c10341e00411540d0601c40c01c1300e5040b114820119804200000340e801c0c013806620141039048011803800352080300c0f582d41c60085100c0182040340000d401c0030700e810207006070ba42d0202003048002c1d0f11519020069269200c0d010001045102d41b1818101819103004a83c018a082401d40c40c0403425915450003a6000d080507c40c1c1c0072410b60904030a0134082c0819108045950350148298190310401c00c0c1400034940b00500c2e40e05207005000032501c0880e6000d4410140903d00b040c0030844644070028204091028 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 976174136 1250 976172886 976172891
    0x604090c0807030203010509152811040806060109081e070e18060a05010b040902030c1c2310060f0207030804090f0c1d040c120e0d0e0a1a031009 64
    0x36001c40c00101942584d108500900841e5a01d046103641c5240c003041c1c4420101c13411001c2207100f40b494464601000345d54101c5001c1441080035201590a9551030307002103a4000780801100c0c5007842916080102440c010361030500d00403090b955144d50110b81030001000000b200c01d00d440402c1804018a20902c19400b94a03000f2007650444111500051107402444002212043c9030303c80d844c141c0300c1c020112424076082400920007504001c0c220441d0410820110701e80b20040d803441030f045090ba001c045000317101143e44140242042010714048250101444020b010304043c803800d41c2c00030b00e4601c40403800d440d8201c1c07420050380c1c0040c1500400140c086400c082c140c10100c440318140c641837040d050007a000b181c250524045600400021141c4d015032490940c11288071a04c0c00e1812000c0b088956074440d00b11500c0e0303010611198081c10a40307401940200702c0c5480c81d00110307880241d02c7e213080d040e440d4283c1d903600a0b18101c02e00000281600d4030003841d0402920241008 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 976175386 1250 976174136 976174139
    0x120f140a0c02060127090804120606050307091503080903191a010e060904231f23130501110720031204050103110d05070903060e07030308040b0604090c 67
    0x24000203010315418400140540030010072948140340c412000d2100790100e2441c0352075800c0d05c04000b07004400007207900001c2008005003241d00c4030304281c1294000d5100040c118a040201860001550300c1b134542c160820381007503000940448000201d0740c000c17001954030740c4400002400c2c11522410391100c0030b880070480c01804400c0d0f0b14584084118021000c541c2d0700c0e0040d500154400b242c100f80c0c0011030b00e00140000e5040f040b000c03141c949116007900110302c4904101c2c2002030341c25051400400302c41407040d01c00194000d0391528141201e00c0d4518060745241c081880b1802802101c204441c2c00b01d090811800b58000306203160400341c0540c651307095103484070a44901140068030140e98002c180a949404030b210407030711544911b0545072a180000550282000b0742800c21079280c240700c203900398a900c0c01054410707100d03540c600400314118034210007283c01c1c002402c0140c1d0701000003400080e8001c13005981058002e03180545035a03035940058091b0404090003000324250307650 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 976176636 1250 976175386 976175401
    0xa03060c120b04140711010e12180a03020102120c070e190b0f030303060f030c0a08060f0108010e0705090a090f060204060f08160f09080304151e120f14 67
    0x40824580307a402060004403403200400064443c0b8203009042c011596004c18905405000000c55000c024000412400c2c1034041a908200c81e02c040c035040314500042001800404560218034554201ca640344141c0c111740000703645603403816030440a1140018504c03c0c400c42048020021711400c100b0083c0340c50301020050038100d450400040702e50404641e01da561801c0041c150070054003400440c00c40da1914100401c2e010701e15840d6070035008400100c0402d484070034214010f405400b0040225050800240c3d9031b8100c16881000243d241c0301e480128403001003a10002c4031001c8607559002c0e141c820b40c8200030076580c030000701001d050751221030402980b1780241c001c0f60766a03282c01a91007403500d002c0ea00303050100c40600301d02c6501c080000c0103034000c61040b20424810300d40002e0054480d4005442d551145c0c00002003481801851800c1641c031482030b905c207110031090082034404044010b001c000480c200181c0041c0c0b202c00c0800d01207241d50020700380120640a0031070302d003031007007 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 976177886 1250 976176636 976176647
    0xd0309060b010203031902092b050d050406090b030a0216060603030818151503030c0610090618050403030e1b1905031203060a0f0602030a12050601050d0207020a03060c 74
    0x100d860505000310450150b0010040ea4403030141104110709041003c1868802507000c0792a07958081084000304899400c00f2094a0040b00c41d0006080703120014100305103020b6100724100104081000140800d1350300040c1c4008803501000a90344944030030b030005c0c010780030304116118a00400c0c1c140300140066034011100b200c0c000d4803040250b480d060b4a48680325001c401c4c2146e0f51307100c49019080c0c204101e840f030387e00c6409500041c0140040d100000d00f5940304440200e46035004c41c0c2401800f601d07000c0028010500850308200c03e42c58558907124003c010300c0040c02c440d503660002002e040c0a5003015200c4844c410a4462014204040c9814494002249805900b500b030078154544c3c00440004251381c030080007000c810301000c0d407008117035100800c1d80740c002e0340c0800f001802100051034000a0644c60b0042d41c5ca500050714010151240381b0121004241800d040c842266002421612103c151000142c4e44403c0c1d400402c02090fa41e51000300524a04030411200c2980300c0c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 976179136 1250 976177886 976177901
    0x307051c1e120e190b0f040e09070612090f0f150609020d05090a170d02130f06030b0901051c080c07080313120314030a090c03050607020d030504120f020f0d03 70
    0x1a2190882c080c0810f040c046550f00400d541d41a622080e42d040c00000c2d12200a00408503030300550300d00c0c0a498140d54440c031041610040800c0d801b5640070b00051341c0200c660070141c2c01c070318802c0201c290107840341d0b03107c2e03501c80c0e5025000c0811500528140694842050340203021401c00b80300703569590307202e000203501c80c0220400f01e80c500f5022511f0100041092104150040d40c541c90041109030300c20515801170114212082c1d0802c02c40c0c043c03600300110705004040d00000001c2c01490600302a0503120700c3d540c44c41c46006c1e102c1c01072000c0e680d190004841100c0141204081d4101d41c80c04800ca071150144070591482000800902408008010311a1480e1000030308d00c060741d0b03015100c0002c10980c00003004180002981080300000e1405140d2042406002088500d1191202d001003003c54100780d0351900480c1c00c01100503010850440049410b10b82004203181a8480448100203021a5001c00103a245c1c0c08101602c200101c404007510721050701c1c0348081d440000380080100 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 976180386 1250 976179136 976179173
    0x150103150f1410080a0b0f0c07050706081506031b0c010f020315184510051803031b0714031c2a05160b0907050307051c1e 54
    0x60404584c0d02c002040c42c103440390740b01c441c07204292101410074502c6c0030004c2c00400701e01000e00200c000720794100018070007843c054030f800c203990904c4140344020b004603421941c0901070800074807502c18000e030510501450b084184544565a0380b001c039000d81044090700340c00354008011303c0b100a10101c0c1c03c92099004842d207013025840b1451f00b40390074000b1030f1812000d00142003038558004040b0200101c1c5a5000b40c2c681c5140300da81502803800008242d8100142e00c4400c3d1118040007921401e50400c40310019400b404581d103210664910008100340b105d4074440d010041100c0308102569a810350003085000e00806008401e5030f40e4201c81400c14001a4940a0007458041440341c0301c000082d034040440f80445c10341002c0096550300208100b0840c04204d1080034080290028440300d1141c108000b103420902011803424041e50002c03442070300103c0080203da03484101c88101c8010030040c0c0e8034400d03110b00703065400400300e03014000c04142d80400340c800c001141450810b008003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 976181636 1250 976180386 976180411
    0x3050709170c031009150e031605030a021b0609130207060e0607022a0f0310020a020318101b140307030e040c030504110409051606091502150103150f14 67
    0x50102c4910145d65040d90041d02084044c9141c0d8985255904141d141d20000300031a86800280c1070b2000f200d1405030000e0b03038190000701c5d0700441940d0500244840083c3ca015404504103d00005041445081d0a05218a80d03e04480f900702181d5010303281c040ea0448002c00600c08512085038803880c3c120390300030040c0141d00040090008014031007016100d400d541c00301c41a0030300e09000300140144440c60789132081c03400c6007045c91070f07500080521a20a501650310780000083d40e046104010b07031054410b0344101d66100c02c150b07000300c1180800000369000c4040c40c50300d0a00e8402000901c8100c86140000100300090540107103111080d41000da90070008442c403510102c08882c420380d00201f1200b200e4080c0116450300c0e4015100d624042c206403503620410012880d000403155001601280003504204040c0c42151400b070070000450002e054100000c0e0368160800c0014080100039401030540650b2400c503d45c17101640c4100e080040008240410440180c00310481d45180a401c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 976182886 1250 976181636 976181653
    0x6060501021608060f06030a020a0303021b150d02070314030928112710051008011a0a09050d0c0f0807081f090f06060e0f0106050a03050709170c03 65
    0x40d0b44a4448084546503000b4002507110404045a40300020788101d900d4491403080b0030241ea610101d102c02180300f50001c1040307821800c1008540d26951800502c600d100c200d56024140c0c08204851001303215290059450303e440c68161000e20405500d000d0940e004420864078a40c002098442031a0304080c4050228290320b00040c0042e942200502c51643c00f28421001d08146e1080d010400c020804d004908039143d000d510295000c035079601c00c00035610001c1010382080d200031508940c103454070040d00d604001d80d101e04420030003038000c00b1382c400003010502d207440f0381d40400240c03138014810b520029541c1840c18000c81c250203408031071310302d0400c005460b400000343c5404840d03a90020f0001d503106c481204d08182520703200101ca00b45c03a032720100002000d805112000500c00c483c0010b0140c2407840c500c081c218020300c043d640c40090030040c4071507904074041d038202c4902031034041003a0381c174440129513081e0a6400314800000c0707051128080e0f040852891b01c2d481c010340071a403d81 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 976184136 1250 976182886 976182913
    0x329040c0837020a120b15060901080c070615080309040e070f0e19021603030f201b061501181212020304031509030809060c030a0f0902030102070606050102 69
    0x1840700319040e854140c0701403a8520440b00662035000c58002403882e0091990b508400140705082c410171100c180c64482000350042940425042c5c0e48010b4668a0401800d00d001030040d800250000c08001d5000c43c2034000c2084a4014518000650001c00981c5646000381d41d074a421100c40c2c03e2241c0d0602d8650b414141c0001100021203500032040c1c40424640302d6508800f80c0c020b01403001002c01e5011680000c601400149004512000c4c24110f00301d50741030003000c603200c4d180c098610508091141d0303030030001c1c041080341000d454408d0f5540c65841410000c0c1e0104440e02c150518003030307442003003144104400c2842c2940c0c02130325080e924091007039001d6518030003401a20f140341d262065003408200401803075072800000307004507071070151a5128400342c24480028456625140c5840c4e004050b4031000154005034120b0083c012400c000c05800000e000c0280440c2603d0b586001520301c000d090341240d466550050021942c0b50f83c0d40c00c041000d4005800b407c0e0140c0b083e401d900c00070 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 976185386 1250 976184136 976184173
    0x4081c091217190c02010603051506010908060108030d0507020a02030d09060f0513120804030804030807020f0301140a050a18080a0f0801080c13270605150603010329040c08 76
    0x14045400d02d100da543c0500d40f2000100a0b4520040456507070b0300b408000500100100070280417080758046503454500c1c001003010040350005905a0085001000490f6000054480e461800580850169074140080389030200702032000e5414401e0840403140c0b507410408c842c003550000e40c2c600b2182444d085069a483c8a00e85124582085001e010480c65141e401d040510301e100b015158503003590390726403025507007164000f9a680c0c1c03070004109086260020078248602c400b523009100701d5400108000d2001c00003008083c501d91074074000344d18400c1c50350000d8800d42d83d04035030040c030144a040174141078100c940c02c01d01092030307020000c09041c000c0c50024101d80d811002040b51607024014400c488512410003500f040d140d440307241c1000704159006001c0d51203404a03203195407550405505407000a4106202c40c504102c2010300b949814007201c1c1580d401c00d0100a43c0b07400303e115101c2c03000c003405103410a03c904206110030001080a5401102c1400302110742884d5200401c808 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 976186636 1250 976185386 976185391
    0x5070f090330080f24210610090605011b0201030e0102040503030406020f010606020606150705011107060f05060103020307051210030209041a0609060d060c0e030f0c15030f04081c091217 82
    0x900c03860189521700e034546410130780d02c807020f03408161074405003001103685440e000369480500c0d210702d25070603c03e2107041e101c0d6500500c02480c0c031740d0420016020802405c8005170001c1c2c1017544500341d8801e15042501150014503000d001c682e03907995030b00380c001e4644035080d0821040c0d50a00d4000201103100203000d43c02242c3c01422000022a007020084241e40940030488841d529006e0148414003010058040d041c0030350b0001c504004040052130807078400030f00103810300d84103005021007164000c094070f0718041c819289991580312400c2d1034020810301d0348002d50241c086010401002340c0d1031102400315103039440403c0c40f40c80d1601040020a41242c4154101034a241d510300820b082e038111410034000307800c002450211103004642400358801c502c811640c401e440221041c00c01140c101001c039400c0c6412425400c0c021042d030640380020b400500b02550200e120380340002079020303104034102c0e03c6030208405840c6242c40380144201c0e203200000300e0924041c0051100d008070080f413 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 976187886 1250 976186636 976186681
    0x1110a090f0b0c1f09020d08120a061511120f07170702090f0703090c03050102131e050111033006030303040b04021c02040204031505070f090330080f 66
    0x4d049001030304080301c076020002403440300d1500c41c540075000d62143c07050a00c034940038980702c950b0368801c1c8215038801000036010341070140c6402d40401c80042940000e0b01e0a800702d240c103240c050f01690100c0d151800c626222840c40400099000c3c011060100500c4814800c0541c0c6000c050700216071046030242c4c0102039045102c280000b10402a03151400794041d0340d5041c00196008103480709209034810b0b81040b10544e50000b1000094911120071800610718a40b40103814210100c0744603500c4201d2048a06201004031240103440080c000d030b5620240441c1a440349440520803008402155915000000341400c04112903042c01700c1100e10440e00080a45110344940e0f0038411891003101c10218200c83d200005001681c69000502c0114003078120320594000078142102120b002034008418044030507030904035107070406a03120841e50007540c190480301ea00c0506955820740840c030850f1158951005487c1b2582001c4068000c41c8500d2820f4810368500301c1c5c0c0140c144480100e071 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 976189136 1250 976187886 976187893
    0x1140a12050402040e0d03050f0a06031a041e08040f060305042001110f03030105120304060906110c1c0302060c210c190c110a0b0a050c01110a090f0b0c 67
    0x48010000380e0400740c0c1051014000081441c0c0c2c01c103201d801c00340d80120810000341c40c3c5060020301004200f031aa040309404034100902469540c4800303590039a2201510380e10403080010703091040c10b41c4603401408d10003000340002c5c589441e2140c1310fa0b000b402201c210741c0d055100413507040c6c482d106940c800c82e4040b000b150354004070006000c406502120b45810402c03004943c150000e42072140700074000c5840002c5440c0d505200401000e5444411039a1040d40248400c100090388096880c0464841d4100541001044a8460f0901100d07100441e04000c0f000c510004985540c00301c095294005c0d400c0d0340d01521418841015840760004482d144c001c041d401e0581e60f404140c0540e0070103004ca0101e807800d01138140407100503071400605004a0031039060141405800700701c1c0c105d0807404407800c0060605000f54490f60380910520f10341005800708140341e03426025070084940508c18008940c0b1100b120703600511042d454000c8078851000c003030340041c010030240d0544d035680541d500034 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 976190386 1250 976189136 976189157
    0x70302090901031b0f090e010506301c08010305150108070b130905040807020306070e1e0117011404180f020d02280927080d02120903030601140a 64
    0x1c041000018140b1513840c0054080d00040c00b440c028040705c001c1104107804030b003c1d10413a10184c00c6540082c0628040d5a0b07440010f81501121031804003a188106840c2c00903440401090b407624001a441e02e5079100c2d62003070410159040380b01c20b81240c1c0319400315540d041800060744c804140c284180356255000e14070a020b00192100506110321000c5400c400c15940c0707403128170a03504140e81c180c46261000440005605050206680c8141e56080c1400744074480400301e07110205d440c80340000c070780c49a0700c401d01583c405e026440c80800110403a0313030196140c00681407a0210000000d21841c80c003040801e0650454107800140c60b0000c180c030b076860310b654081c071800341e07401281244d00500d205603a403100100c8040c03041344003d56580190080d410166202c00300c3d4403002011010b00ba80c0110317042800010748203c40c0280d442104140c03681c41c0005800040e00641004103c0028103100b000040c042c000040c6100d0002680e5403036043c464081c602100f80700304100d03840002d001c100f1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 976191636 1250 976190386 976190393
    0xb0421080f0a0b03061e070c0c0504050a020403021f3b0301060f0905060a0608010305030913020d020c01091a0108100c0e091f05030c13110403052407030209090103 72
    0x941d50142c01c00d5030100d06a8074510001e424500102d0354036070000700944e000742c400c007841c81c505603104400e0305091040101c640c4070300704d00e480701c0e00c69107101c1c603201d070001244864a80c058800550b4007524034219101501e4202442c40600241c0500244450099100d000880c4030700160890300d1000c11170421901007440b80c501540e03125519010b640b2000c00041c07901c0d20030b420a00600c2c0134030b80001c0e039042c01001c0003035141103079000320304200b0380c00d0042c80840c0020045a00e9010111806007240d10b005407540080e006422240703404910200d8100440d840640090707d504c3e1103028515032041d04c43c5451b41c40f01e5801c0c0208485584075110b000155405a4400540c81c5440e042001800f1551030002e0030f521800c88030b0941c034041d9005001c8180000c00114005004110040c0205401d000045440c1640f119121107881d512a0a1030039500111401c88010310342010a40d40005050036030180110784000d5000c0906140388000b41d0751501c24400e50303810140c002e0001c0d030164130711344 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 976192886 1250 976191636 976191661
    0x3060f060310120305040906080a0218071809061a070c15021f1a0409081806070f111314070e0402221503020c0c060f12040b042108 58
    0x202840d005440c0c2d084045203102403080e038040404d110742d07541a075440c1001100e4013a68115030045196900c5000c1400059840003d01c26220041003100412035803014003c48086549558030001c6201540c0c000c00c0d00d42d61508440192850304290720818480c140300703644684654140a00000c0001e02c050224100f50070f14003200c41140c0c4112014040710303079960004072070080d80320250f139940c58400c4a20440988920001c40d841258100440c00c195114645540304404c80b8040455000f00d01c100701d40d880a09444900c0d030000c1101408808500d44034000094401e003551003010240701c140708120450081c1c00311903801021038107594a540d40305542040044402a500c290207015405400c81c3c02c0c07038807120042038500300d0383c0c2a030b150640c00b00d04140c0d0039180804150040007580745004000401c5040c1c404182c40c0b040c0d40ea4201d0395500c1141c01040a24407480300e80c0b00c02d00c0280304012070750500850007001301010180e900211250740303c0d0080400b4000c0760784100020041c280d0f06 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 976194136 1250 976192886 976192891
    0x1015062303040206031306051609060804050604030e01030f1404062004030b070c080304060603120c1e03050702030f030717030106080a0e030c0f0f070918060c140a0302091503060f0603 81
    0x114074821413060140e562109443d011a840c02c82e2700014545840e02c10303070040302c1c04000c20603401d0107045810030391900c5488042c0100b007d0300307201603040c0c0300c8040e0b44640d00580201e81c800008010100e60f5600880c0d00030f07000d49058071082d041c148201820165115103000c000c0108140601d0300c1d1079983c40800c031306401043c02c414007200720403510108000d01c0085104030701c10304001844d9400c6140c0a208244604101e50030020004007410000b6803c0c1d50502c500302e181500764201c005c06240c2102d60b0320810b540250140210081e8402442002028003001480b403240100108400000c450a070b010910403031000400740380104404540d01d501800c0030b1442c00d0141ca00e0100191420341c0307041040c144024103548204000034008400f440410b0143c09801e07014004480710f4076421000d11244080904425603626040214074001c1d5034030720345444038061440e11019018400340c000e410100c52940501903154a0a2005100c001101d00c202002003c40c0c411901182c18041180c000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 976195386 1250 976194136 976194151
    0xc03011104090b191509081225050d091a09011b0c051207091a09072106091b090e131a0c0703020d090b0a11101506230304020603 57
    0x1035002c2d504051360300e6400d07240a0800060702110100308140024200c500c0b5505c40c68183d0401c40710340308100f005000300c4156103000d090780354080c0038000d002080703044901002043d41c0304003040041030075004000350003240d4140091207007608040e50030b40c1d800e00c90103032802d002500d58000d4034805035a030b2007035001c0d6070300542000d05001e0f03c440220f20305034810514040d050344100d0003086a27024502540051841070300300c45001403203031070100d54031071707009400341d0180a00c0c02e00070b42803075134a2406411000da101c0ca040c000180e903840c07a50020004050030300300661880100c81005c500811860086421120401031650754203441201412120842107400c490003c0b02c1c00080381e50792a003c1e0060320f011070701a82c6c85910385070103440c1260703800c0c1140600c0b140b0303101000010b040ea820350b001903c442c2001c015943e0030140c510304007139490704200b074128984072003040034205036103100050f07842603101d080081d9003010f0120320503840c3c00e081e0307030343d45c5130803c0028010b0400101546d04500b0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 976196636 1250 976195386 976195399
    0x30903090a0b03060301150305070e18030406030507110312010b09061309020301060e0a060e04020f04120c031403180415030b1302040c0e010f03270c03050c03011104090b 75
    0x12003000540724581551001040000200600a0070300d0700f03100d816040d088010f0750b4038040b4550b50b12a0780340c20072882031a80b24081003000800b03110144c0090291118400c00b582d5440340c58020190040c40251901c00000d0320140d074030050b8003800411030f000550707440d400d00e0290f032038030001440d01d5001018054001d0014400c00341615001c8a08601400041401603107940c10800e0003860b40381c584143c1807040c0c2e0302c00020060583c0162103281c40040540300076a99070740d4403440c0d541c1c034810b07580305c1810700d069481c11109000c00c0400090942e0311403050302843c0701031044565079074010407150003120695500f0306000e0340f40650010011503038490b00c51400c540d603500d40c03000300c040032101c44036404d901d100410704620309485500d101c0341d82c508240d0300c4d51aa0b032000a000d80c2c00300544409155030b0b942509070305085401c0da0a5011a1419401c00085941c034104000d59054401104d03c2e1044a45103482071906000303566840301414401420189030a82690240400580c015048034 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 976197886 1250 976196636 976196647
    0x7081b091815030109030c06020f21161e050d1410090e0a0809010c140d03240b16030e1f0806041e021b1902010212160602030903 57
    0x449610401d4441c11003000c04030a98a41900c0090b00b0548042c4120722a9140c10a5000061f0300a902070b5140785d0004801625440b24410b251158481c500c1c140d100004a541c0c41c21001030325041d200e104420403040c119001d50140c3c030a8444900500c00d0401c10741006d00c4c40c1482d24070420140000c2034041d40007040c0300d0900054561007820680301d60180e8503010a041c00216100e0041c803100c0400c1100400c540701050300c0c1c044003402642c2c88141000f1005081c1418010b09094209a03a924242a2000c81c91502c20140007085924241c88941d8405c140c9103442506032000c1d4030460301040322052a0032044104801e00801008088052182448401b940c584980ba00b09214800c1c080390b4060320390038054080c2441400030070031846503007056258801443d81103c007072000300701081d0150702e840c2000000c41006e28a210040002d200d6021010302802ca0000d028101034000c0e000c3d52080c0d40c1d03400c2c0c0a9254803501c0c0c401c0e0040020311080d0400a04550700440c1e0005058050340d0130325 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 976199136 1250 976197886 976197889
    0x30b130602090d0b070906090303020606040b03161e0518130503070c080c04050f13062d02030612072709050327030703030c0803070513080303011d07081b09 69
    0xd40b288881031303408080310001c101d400354002e007400c005801d0070f0905c1c401a80c5075680c002c3d43d40741d008002324040d42d101c6c2e02c9203000c0d44040005519910004015090181c0c94a0101000c09124039840d5440e103418803000a240c24201d4889030754002a9000391441ea45001c0d8100070f40d00104002c036550300c420840c80c0041001281e0700800f5000810160a07490b0345076040105440018103400d440c1e00d0032005218290000d980c95454266100f08007007a0303209001055240c030f120500c1e011411054252030038405000e80d40c01184900c4049802409a036550300c0d4141d51000180a02c0c109c54440c002d03450700c00c002d11040c0203002c9056190120f5a40c01c039550703247c1550440341254001604a40d20f200340141c201079a102c2c00403054006007520b03480d41e10010800c541d51f442c09000c201001004c140490322a008a5616540d07481e04401d2081e43c1d00b450030307a03940c001d22030f1609084c600200c3c1e207880b41003c0c28490082406907500c00c0b40c0d4445094801c04440451026015200208030b9a07205 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 976200386 1250 976199136 976199149
    0x110d080403030809060f070f0f120c030f1103010819081608030604050123090a020c0a05160801020f0f0c280c1d0c341a01030b13060209 60
    0x2a511a40d146001418420a00ca01e410380107041d00010007118003c000c21223034803651820821343d8034601207070300d03501c03543c0240c54403828400001901c5050030005260a9055040f4980c0400c001d8400c1221200480c071b0380e01d5502007070241c41041d8000c16240702054003001c0d484621580501011850940c80f442d41c1c40d0a20340300b110441d04101c010040040c5490103101b40c500400302d040101c024060310421440c020366142c0b003181d100e4800040400e82088466041d200782010400031107101c1551814020b80d0750300742d64074855242c0c00d602400b02740c0c00018000c0d2640d80d050000864140091140f198070940c0000b10301200034030500c20007040c0e510818508804500062001d40d200843d681407068000580d070b00104903103e2024446000040302103441d41c2c0c0140c641c0e4010b40c8074880400c0741307001107407905428003007140718007a00c07003005c800c01e0712001e91584545650100c00368500d0304401103a0702440301038889643c0900040350008585210120288110801450020940d000420 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 976201636 1250 976200386 976200389
    0x13061203030903120b010504060f110607020601150516140c030105100f0504021c02090a0b0d0f061203021e031209070510020303040b0114010c0f050f060a020901020a110d0804 77
    0x10351100700c4007080c16003012044c1d0198407000b00610115603400000b0f400b511a92240604004920b891222940c1c41107201d00c12084580041d240182840300f0000c2d41d41d1030030b0141090394007030344540703c0c0c515005200302e841c51500341254841c0c0306801d40b21034114840307004038410a0f001d01d500340f5620769001e1180300d101e0044140003200440c02e1401c078501c40340503600b00d04d015a2040011000c00001400350f2030582e5003110000d607450b203001c4045540c003030099001d149081e101007140d40e1402d03004d030460005141800340810056503110402e19804481d0344016016812414038036812500e0003c00d540742114120851b0726205519841044020003182c6901c0181c001c071400f403040b8a0043c40c81d8085603030500c01541103081545030828092810321a017889440400d0386400542d000d9118030302c207503400c00c030364007402d07101400c0c07143d01e07841b00e0a003c0101707008100025801700d6562003130b6030003a141070707005041b41c80707580d600d02104401141c80241d103d08207000082c001044900280f0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 976202886 1250 976201636 976201643
    0x6030915041a070c050c0303090a0905061c03050315040603030c0b090102040f03050c030c0117160c060515040c091215110a053f250e0f0a03030e130612 67
    0xc0100c1940c2001406e00e00c0007010a442900f003000341c40038940d2421201c20079200383c1107000581c2d072274110001e0300f0b51001540c6244404030b400402005d1540020165114844092036190041c51030000c000071290b0070301004000ca10f510f001d0307401054181400f1540480c040b0001441c003030b201c4807109803000c5170354000c480f10743c03000e910000705041c00e211603803003103100b82441d20f0030010000180b00c00190007041c01c080e8a11002419030f005218600282c1019040744082001e4181840300012003492003003440d0099040440c802030700c82c416505e1000311141d000c46c0e12011006030740c9154003030340705203810a54681ca0788015480c805c031901c000c1010009545a069a03581c4a00d080016114401c6011503042c030042018218a1604444841c6580401c40e4003000742d5a10908443c44604210045a51007590f241319001a6040081036070010030488410044110000401c0020b01c0700d80401400510b280642c07403070700c7c1088641d166005e0780c41c01c0045000c1d80c4417124001c400d4071610059 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 976204136 1250 976202886 976202897
    0x80313051e0f0f01060506031603181a09120a051605030406030509120c0c01030207150f0501050f030a15091505160e030c100e010917030309060606030915041a07 71
    0x180c80d0103030200300d428160360f4000020300003c3d15000004060780001805198448466041c4034981c921035808001c5284480804010822060030551404500f002441060000c003001050200d40d00040340c03e040101da403c41842c11074141400c4403d500080c0161807080c40940107040021400d0000c0d2001c0c12080d078000130503142001e071091524509030381d5400c10f9402089000f078640404a5080a858000c1c200503a80f900b007890030048184554861851340351501c4000c00032070209400240c1240c008171240c005402c2c06a08060b100c014440d4005c1050300d85d400d8584582c00d00390088542d03180544860340c0c1c108030b513038070b124150395040f139004501d16007131a155001c090b042010b50328801425001010ba400304103001c5260b11003072045040c240455a914012940c0c800d080c400e003e82a001d800e890314040d40d0200d50340c0c070380003962900c1e81b078002c140c00070b0b065082400a40b4031401d0702400901303400e4442c840c0408242c2d07019105651000c40c0d21084015a03100806985c019042541c50 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 976205386 1250 976204136 976204153
    0x50d1104170c0d05070308070804050d11040b010315050904060902190501090b07080318250504051e0c07030c020a0e0f0709140103051e19050112080313051e 69
    0x510341401034226406103d01440442c43d000308000080c1c4000381c0e588900110b540c2c210504044030030780281c2d8080c41d40540304039003180411101c111004850745080d101400000d12000043d008e40c4d622442005250701980d408001d03d00e0040f502e20342013030080200103a00c003a540c02103403c0309500d5031111091510030760104000c2d64098401d1004050040a17907003480101d40d682141440080d042c01c0710080700c86800e002405080c0220700a09044004501d9155604101c0c0380550b1050f2003210b10035480c0c000000c0e040c00e040aa06d14041050305041101a40e4800c100d154940000360283c04000d41100502c005880c4ca88040c006007030002c1e0840041d1821720400c0070034107c02009181002000f5204000c4c0005045018003480700034200490380e9035882200f50701d0042d403800c0041005617041c05002c19001c88981e0780402003d521010f02060384c035034041c911203041c41c80d4024540d040400004442100004c114421180b040c4283c2d404240c1c0040b4200310f00e030310b4807400651030308014039 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 976206636 1250 976205386 976205429
    0x20030a0915030501030807060507091e091d0a0314040b0d0b040c031a0f060f0d1407090f140d0506070801081006050a05060306030a08040f051305060d03050d1104 71
    0x4a00364103126890240303c10b6045a9880555001303e11000b01250740f41c0b40810403040c02081e80401070606010031901c2c0303e000c94444c450445441c07080d034101c146888191003110742c50724500c0210314468001400c9901266800300d03008108554120741010060101041c0d003550076000b425001c0b0109008a106e0f2281403c0201701c59044d0b40740801d040c549060091b221203140c8648a180707000f250110503005040b0041035481c418191080c64210001480145c180f80c0c51b8002c0c00070407400c81c130040159581d104181d51580140c05800c07440d031030f02c0d06e04001245607030242032841940034101a5050140e80d48803131609000b9560603010840940040c400c08800304110a41001401c034207000700c40ca80700118145131040d019031030003035070b00000003481501c0801080e21403541c0062aa66075980c0c0c2c84803030380c80ea108c44c000c0c540308020440360045995124043c840c0a040c000b40b22552011259609071001c1d4801d81d080c2c2c6201d91a9a0340201c0180c8101c050030060480e0b0502041080c0000c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 976207886 1250 976206636 976206659
    0x309011a0306100306020a230a0305100617060d0218150d0209010b030a02160605040201020d030614040c0e0301090503090f03150109180b0903070c0807060c0320030a09 74
    0x81014025030002c01006000b800a0b052a0304507904100700607901d0360303407640884011030b030142e40e640b080d050180c80c6000c04c0241d10082024401c6ca075001c0185445558580c40341c1315052140c0ca00041d03040100b903a80505a01903644c20890040182c4401e00095001c00c20502a400481014a60340d4003080031101d4000d00a043c0c0803000c54804112410b1640011881d10b4180291109101c1c0880014500d40496044950306a01d80c1c4500d0000c1d050307484c1520103400d003101c040f4014000d8200d0b841030039010703000e50300a84c0d12241d440e4440a84e00382c00d020081c04000d40100c2000b00358070115602c1d0303d0a1040c40f00050080d8044d590b10100003061008007180342000b5070107580700907400704840c0302d04111241920360001001c91611041400c11070b051940a90140c0400070314030501a085500100a00d091781c400c08020340055540d0502e182c540300d0912a80000c236451109402c00680b040244500003c0907030b81d0f005400001b0b254403440c6402c02070b000c8010400320a030a000a01100 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 976209136 1250 976207886 976207931
    0x50901060e0c120a09060e030c07050105122a0c0f0c0307050303031b090303040b030105091e15010c15020406090b0304020a3b10080f0309010c031202030901 69
    0x440c1e041a060800180d80c940302d00c07030340c0b50b902c001070100c01c0032580c03005498118414080d0490028050220444c011b291280c0c4450040c040324030038004002840e501075001c0d51580b10310100094419602d4091f416505908400003180000f0005034440074044580d001e0944403d0102c018035111080481031480c101502151900c20f0f40200420443c0b0365000040f40d502c4641c2d20840807c407100010080668001d000c1229070600020802240500140c0c01960480b4003c0b41e200340f01d40c60f000041702100c140d1055200c4182d49100c00200d80c0e80780c400c80710394961410b1409a0702106c0035240c0480c8851440d01055000c0d4000404203c900c0c0d100b00111f010705100f000451460a2a0b030000700d40c20f25074440c030510009031801001181103c42c1404840c1e00503e04002c40e001c0c08940764040014084801581c0002201408a1005400101810400081c0004500e0320240704015103000c800201d0031000c2000310000b180d4810214009140200c220800103b5910750441f041840062007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 976210386 1250 976209136 976209149
    0x3020c090c04090b1c030f11100b0a0e090c090606070f0f0224180a03020904030e04051008030d0b061b0a031e1d03010f02130e0106090b0f2206020105090106 69
    0x181105d0101010344d00f061300070410382c1400c002c07080b09500c042c1560102810000c5600f180076058500c03403240656040b44646030380c112008469903454040f150202c000a4440c6862707039000303040001d0a0704003e0200c9400440c0101400c0c1402d40d16035030380715140344851045481c5d60703090700c0c44c03030860805c1c41040d103803480303408445a1a000b40c0c1c941880c06025521501a018a640d21550b1031915843c82c024055900940f1000a614060130007400c4d01903d40c1686006038035100004e10035024000e0b03840d050b0f07140d680195181030391070341c4024007030011005080d511501c10004000700310035102e805540741c0414405018810414107015101c0203c807060b824800c5038480b04a0001036020551101281200724500c100001040c08240100f100509076a401d0f480011001c10b18086616030400f107800c031194005081e1f03241d800840c2c9811041c8541280104140502c0e65000450400b170304511260809a44181400304860b0b09007203000c1c0e11160243c0d541e4400d100a0300c1d000e0080e94040e003030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 976211636 1250 976210386 976210399
    0x5150121060b341101050417010c08010b091003021b0106270b011422060c290408030901020702030712051903020309010c051501260a03140703020c090c04090b 70
    0x2040340d8503010701c40c80c003900206007842801381c10074035a0046041c1d501520001c200c4103080005800c18500910314403040c000400e03022800080c40c0c1841c0007c98413901c01c050071541030080c01440980194000210005034440e050941260914092040d0070041401891403001c440c81d01103408509128110342406542c141a8004600d9030800303805215014107406159460400706946c00d02c0700d407240119001c080c000c0e040003480781e41c008400ca1501d806001c103d10410800c000e801c0c20b402001904284410300303000014042580380002e150b102203104005440d04030f031603001a0800c3c285070000608010780d0704440041c05000c025401c0000100d10700c82800c00140d45001c1d560380110308a032410031081b0f0b40d0341410031001380b160099000801007411074958458403241c142c030016841001c01d25401009403807152100140f851071003901900d441011601c4242070365456803090500340d040d40304800210f1081d0702c980c085240b00711400c40859031581d04041810301600c441e405498410398 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 976212886 1250 976211636 976211707
    0x10e0304030209010b130302010c050a0501060e0603160311060903160602030a080a02030f0c090607053003251b0c0f080309010503060d021801032405150121060b 71
    0x181090b240f005903902403c0440da803c0e032b980b501924101180000030102d50900e103001442070f902203e40c50050310304400b51100d184400c02c5003c074441191002a10040c10f013900004175042c41c00c02003030000c030041c06a464061808080c43c4c0611941d41c040d500580c8005010000603512241690700715560680543c618101303088500110b1501a10b05e40c0d40010019045c010384d44d0f03234400c1360001540603080d22408144481c010303120030420112140308040c1000c3d50402850b1407000c49208000c094611580807018055058124032898520818048110701403000490000b0040c00c6007480b40181c40a80c9062140d205000c6c103503a0301c40020b03a80709001110680c1e0f00402665030045054800611820030740c00011444401e02c0ca00e0044a10800d00120a02002d0300000c40f41c0007a000080710181040403904048071002c0340c04843d18048c958030200710358402c00031080500100b80e2111f0320031041d40d0380e11044881035800b41240000c00900b4412009140346004e15124900900d40d02d1607 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 976214136 1250 976212886 976212907
    0xf0602060106262e06020606040f200c010204090f0b0a050102120f03061f120b0d2f0901060c031404050f060309030f07141509032a010e0304030209010b 67
    0x3010184c255610720510454102c2001800e2507402001000d45411a0f519507a58001039156001615594000c2c0d0500c4000d084a480c01e000c0e2850140d0071000d4420760700d40d40617403c03410343c00c0b040150b002d0795000c110010307080c04540102e030b21a10481e000020410104802c20110910b85d620050554100521420600c07444d40700780e41071050400c80ca00e959a95940008035076210840c0f082119a80000481c2080c1364000c1588185250f9440100041c003000401c01c40014803202e4000c0c5501211440301451110402c40450004541c8500c0010000d44030300103080d0319000d81210300003454040341a401e25a00c240003100310110304814038500741c10a070124140ba003010704981d000d0300c40040814000081001100c41c03241124601a844a01c586007920390404011050768a510892100940c041c6401c0c1c0494010741c01580154901a94081c0c0c0c003070121601c0581065407180741318410086002130150620900081018642e17680c214030400814170410307045043c00910a11404044 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 976215386 1250 976214136 976214207
    0x339070605090d0c0312051b03090603040609050a050d020607090b040b040302150d051512010c0f0807030e06010e01090c02030f0f1e0d05072304120c0f0602060106 72
    0x540000ea070512501a441d040070600c52244d079000520080710003c002e429190301c1800b82a1009001551990b080006240690b90340a5540c403a68408020008580024403d43c05841c6842c4a041035401c01303809500e40031708003651107403040092703000311082042d46ca03070041c00e41d0041c060035000103091906180c0c010006000d00e0000a008010354007018080b042c4000c20b451664441150a1100303240c0300c580840c680040c909010b00414a0f01c1d520300a078a01070040d5000c021903030782c1e007606403410340ba011515503070301400c0c2c130041c56901d140c0340210510034041c8074082c04070006801055490184000d04540e0304038415002c5400602860043d40405000c8400c0c10007940c4403d61511035402d9080c4200d152074086545010002501c00c8400640745c00c101c5c1305005946404e82100550606190000752a0101a55003501003206100b0150449820001d050195501c031090645940010f00f00c01110b41002c800760340708100401c070083e0f01c203201180c4001808000e10b03031694000c091a00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 976216636 1250 976215386 976215397
    0xc0c0602120601260c0a02031b010618090f02010804142b0306080604031d04020415030506191e09020a020f07050d210c02041d01140105060909090339070605 69
    0x45c2c2c0900045c1d0136003c0380708106079000d15030700c071b44100d034a242e021030114000c080b1071103040d40c0000c1c1c0c8220180c0b203103050f129140f171950300800b41401c01c44040c2c0c011600500018021550b4a4100640600500c0100003034000e46540ba00268110351a0303e40e06140d00524684031802c060a00505020035007022625540050f49401d01200c81c41c0f100b4800c1401118a031040c81d013040c400b05000034010030f4000b0342c10040d0410345007004107403614010721030300180c14010400703030042e01d8104001026440d58546080b01c003008005c114a521440d0807402e07a88088040001a803110040503230680b414482c134001840708481002074400544d840742281482910807515810001e86800111401000700d40c0015038007d100f0030901d21404191241c1d4001103071000e003d03619081c40300b141d007001521450f0613180c00038001400c1c005030400b0031124603002800c0c60303020b000c18003403083c298100d0088504407079003090304000010184c1c600412401c0d0310040c222080da02440081040c40d030007034205ea0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 976217886 1250 976216636 976216651
    0xc0c0206030a0212360c01050d2306090f04110103020a1107091a0604031a2a0415170f15180108070f0305100c0c060212060126 56
    0x703840b6690000450024000d101030681d8014004e030400c45002d16104110b110451103101040c810410205800e01c10700c88a5642d400d1a170000100c00030541c001c05c041c0c2860301001101060703008000c40a40700012800c0c00d0081c620a800c0e003031003114a010110716601104140d0301c80782501d00380d01c80003001680d50b8840d50605030f0010b0310003240c2e84101107000443d01150200c4002603600c0402c11f000f0402c07000340c0d0340311000d800002200e5250810844084075000200f10441844e00195921a400c001d40b90382e0144036007100e03807081c41f001c04455a80510084076015201c2d8503044000c01c3c0380383c4011010041114045824844d03152076926207030080c10b4408040482d40c1d40540403180300d45e42c041a1680403401e408a195403039440200a81698000c82c15245011b540c3c14420a624601e8003000300303103402100e0018240c0c45c4a40c4095000300300d9107403040c100e0032261103200c100c2e80140c8000d82444c0d002401c1000d00d5030004022403640601c0701d0902000320000100e02013941d4042e1916 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 976219136 1250 976217886 976217899
    0x1021209010e0607021c0b0108011802060d020c1f1a06030a0b03010b12100c0203090307031b05060408010c0f050c0d1d03070f1403010c0f0e0d150218040c0c02 70
    0x141d1140c440c64207507440da0b45e000d0035000441804900035280641140d00440b4100610703400800c1e41c03901030081c41c20031204810041c03078162156003080b11581020703800d4078220f942440321100961080040f403400800508030000c0f80e201c1020a28240e81050400c0d0300451401c3e2005022911024220f96000c4410000095a419088006409003103075a240e0356001c813014504c060300c13800100355a408115072030820014040100070582c0c4a0241c4095141e140d009070104101240044c80d05866648890a942080c2e507120800150140c00030b0f0025865699551200c00a00d5005003400b1085044d0f0304050341004c8d80e4560041e500d080c9040824108140c10075014120080381d003100081301002015150042e46030180030040340c543d0b100c0c2064810070300403100e100b800c042c07294143d0074a1a958040220b80a1a82a11900c030791100b150b1700700d4001ea504002041811480c07290000c2c03501800b5030746005068040c0180c0d00384046003486a403404060650860700451912140e5a0641d82c6 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 976220386 1250 976219136 976219157
    0xc0513140a0308040b040f05040b01050a0c030c0b01180b09060634140607080403020a021c0b0c190302040503030301050f400c0f080907080f06070e0102120901 70
    0x4a40d80e0300207503000900341c03a004240841d0420070031011b0010f9590100d600c01c1241e94880402040d03800c030010341d50205004000202410344141040c0c200302c0e010381001c02204c43c0310341d1004c0c287c076026881021041310314500c0d180d84160500501441000440392181c150070a0f5000070303c18401d000501c00304506024070000600f005503400410031111441c0c444800c01c250625032540060030080d11094019400020401409424407600030750f010381c010b201640c03050382031009440e100640d400e100290410518009680707100103511840100c91082d03201e00d044018500b10410b0140e00e001810300500c024000c1da1000001d40e811100c00300e54005004000303c000c940c4611404200d581c0495154584145104456100e5401254050100b081140d03040301d00c041110f034a40d10510010307030000c2c201c0b9002c40c400d00440d80c000214109403888982e481491900d40f81008114603081d4021008001e0421b070070850821055000307001030180091404682491441500070550510000c0500c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 976221636 1250 976220386 976220389
    0x17010510050907090512010b060706060815100e0c0405040c020106060e06040e19090215071718040b0f030a05060603060115050d0c021507021e123f0a0c051314 70
    0x10f1124a019206950f00e501d2b504100c0e01600e0103000343c56103440b0b40c10019400940465034940319928962900000a092080180c030510025012803030302401400045900d8ad114401c0704103003001c540002400a28104004d07205180c00e0b15218410041400304200c4442000b4007203500c01c2404006403040034044a14600801d10440080e41080c030000c00b031807009250100902c11355000d52507036030790742e0581240728000e03125809020010f0500c5182c56101d508194011000000006103031300e4007111202d0120b0700d011801e40003950759500c42018001541424418603002d04a654507101d040341142c0e0000c2c05d1842800118040e450759540100c10b02407090000000e118000b07000b241c0b440c00d014000961758802c2e420703100b00c000b540c0002070b15141800941412010f810000d401c3c144100d80c0c122540d99410440c01c0c040d203042040e0700d85c40007c82c0000610000200402c2d800310744c1800040d0101f00c9007440703000e03000d0010411408040a2100f0b03000012079145440300300003c0407010 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 976222886 1250 976221636 976221641
    0xc05153c030a092102060901050c07060b0112020c0703030e0d030503130f02100906110a11100c05010c020a050f07050306041401140109061502070b0a181701051005090709051201 78
    0x6005403030540541000014481c00031001310760740e986035085415503118500e41c05c2c02ca6a0030b442101c2108020024540091115004401e50b01d005040a41010b1010f107800380a07a0701c80705110030542c100000070b1080540145d0051500340090f6204407a010b440e40c1e02402901c03010301912003074282c4125500400070b0144604901d00d5001d011603690a005000250440d8028020030000c20140003011004120001e40181d50300d411608140c000051141481651203e2008900400054104540105000f401914800300c41030b40142030708001400c0560504000c070300381c0303041e98002400411860340c001071500d80080d00505504090f00c2c201c1d00b510b0040200740d45070040c081031700b0000240b0b420325074000700885488200e0045001c0c00010101c0e10399134540144840031405000b11040c0600c2441603600640c04d07405640d000f581c03640d01c444100c54503d0800115a0344031020840080046010400204000c0c0c5914446041500000d01110312a0044a008860010520842d0399094 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 976224136 1250 976222886 976222901
    0x3040f17031c02030601080610090303050a0207080f0601050a1215020a0e0d05070323060a0203070207240323070e132c0303061c0c05153c030a 63
    0x42142d10640301011140c1c2c000380d0800c460190108801c1000039107107042c22070031594600039607036400e4096400c40d50207442540010b60301008601c42c001c000b02d40404200403102d032a42d080c0d0014075896140004100f4008219000824015403040c207810005540b400306c6451a0314070603015849021503481181c0300302400f0661036010280140100030b00001007040420350380100204448a02c005090003039008448c5000541c40c0e0100000803103012940d4061508035002c1c1c41540c020310741c2d90203402c030007000d03082e01000c1078005030881541d82e98051192030000001d82c503007203041c10031803100c080d88028028110400d20030a00000300f00c65560607580003148510b00b88c10424400001c01000b4014004414020a0b021110714111000400810350b403040100800c0717142900c0543c0c960514010182c2c000f102c00c21928400808e6035035462001d0000c80c0341c0c5420380c0d40ca5400074003d20a26481c00b101540c0c10320781c0c00c01c0e00d00c210101340d000001c8011401c2401c5940342c0310340e4580303001440107 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 976225386 1250 976224136 976224157
    0xa14030606090a090903082809020f06030f070e01030c140304030e1e0f090103050613080c070b0d0f1a04110903010903030c0906020106080a12020c040f1b0203040f1703 74
    0x3c0d001c0030641c04415408000c440e0b019545882d40c40d80c0c1c0c0010726074600801e103075910b1100d5000c0700360b01c503141044d001601c8007031001c0c180481c40450400840c04541082d110302114004180402c13407925031040f0084901c020920742031100102d00800034051900e0188050900030700040010300b494003a400400c5516400b83c46031094000a0610b48580d030610380c0440d01c15070080040c0c0d6128981052a9070580b07801102030f2509407592099003075107100384003088644035000c3c0a80c4200510030701040c4000c00c1d22542e6141e50344901d00551040b82c04900b0141b00a41c9407103070821404409021050140d50107541c0051200c5d2080050081070185000d41c80d407643c2001c2c0301108040c2d158019800d29410390305c4444a06444005c103a003a42c0c2607000c0c2d80740a5000c101320501043c0201a40c8410f450350780180c07290003100f08003060075500b00d80e400e0307504d2a0315400342400140604c0c419802c0345200c1e101071420942481c2c0c110f85000b081e407140c0b40001e00340040c0c20f21042401d00440c0c405c42c40 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 976226636 1250 976225386 976225399
    0x60601170c09191422180f050a0c092009031203010b040e100605182b0308090d080105190803070309140f0f01110c0a0305010608010e030a1403060609 66
    0x760400d038188088124064131400c1ca10060b44030220341486101c051058415102d02107514403250003a0004104e0041c5c0d8011600c03219440c40046008940c0081c1402e02032000b0341120403490806017021010f5501855103140380070510400040340c1682c0c610a0310044110958403160311000a1a05002c042680c18016002000040810540e0002e000700c42c0d0200484050303030b40303050b410b80b610303034040c0300300d8012030420004100c0071400048025034450004001e580c14080b019074006001078286a08003003200003135040001d05411030035095200081c140145100900300c00c00500340c0b00180304460203002941d2001c24141180c2017404090400740302240c0c0c54030940e0600828580d82d61103102009000400120713480c1c00c0920b039011000c02d0103050a82000801c4004540c140f0003200316046500031812105060364940790000c00840c0650300120b6142c0c10080c01d81c2c00c40c0d41010a10311154420040b41c5035036604540201059140c03090b80c981c41e07641e810042103581c07140031145c0d94000c8 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 976227886 1250 976226636 976226659
    0xf1008070e062a1b0a0e0417041403010f06080a030e0301060e0c040609060e0a05131e020c0105061906081503060c0c1b06031302040b030102161202060601170c09 71
    0xd982041c3d1481010354a0202e420300c403800e80811408014040c241e41c2c111840c180b090210081000320207030041d1049075031703a00325031030803030300540541041c0c00c1100b100c441d10386403100034682401070309c0c0046150401003200c145031030700540d9a151070740320080c240140000c010b00541d8080d0300000007806208244034861401c0074140c0480d0380180500d102241c004080032485600c80c041840d030b12080506000080e900381030070015185407804c10440403540f00c8030928040e00f0100310608210040c51805070301c40045c10a200d0940740e00038401e501462141494100400101404a040745c2c0d25041005107901c8801e030407001c4642140941d50107210740e006001908240308020030190060300c05030381c180d0402256254041249203407403a0304c003c060001c5040306460f26803100d8050b200a02c0003581c074080d10041703400d9030012a1003401c08166640841c0501031000c41140301c2080c030340301403c5107181803400a48116120f4054140798501e41c0300140281094008803001ca0720700901411815 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 976229136 1250 976227886 976227937
    0x90f060e010b27010603020304210801051804020a15110712030f020c0a09020a09080a08031006020f0a030e010e0315010603060f0f030809030a0f0503090f1008070e06 73
    0x90460074189400b80840d1215000400403030a200c1500c50f403590034100f80e036480d00e00304401a4001420031345a0b11000508c502c0b20154a42c00c00c070790007485846080c4a580342c5810007003024a80032286044c041540d08200069a50749142d209a60640100446600d180346c0d00311095207000750140e00300d10a0a002048409000c484031030854800d0340c0d8203030341a00c000800c0741c45402e00b408140d0004010b5400f400b00c004075401510350083c1a1900a442c07980e81c6149030310f41312500d10141d44550000051102824000446c0805080b07280003c000e901c141c1140544d03207452004000d81045115034029006a204521018174108000d0403181d0003003050034400840c6800b841650b0129181c0030300003d5040c18964400c0440c0c0384107941c0c003e1203143d521004400d501038040729502d80202c1c1100390001d05107680c0c14186500601c02140c03180580402d00101c413494100350740c800d8602c142d80002031ba51150b4040d602441e18076181a2000925002c50800d019100c1c440050110310409010407 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 976230386 1250 976229136 976229141
    0x10b040c17040b041106032406070b040b07261005240c0307080316030f0509030717120c041d0105130c090302040c030c0e09010e04230111220f050103090f060e01 71
    0xb6a03403890b4230481d0074540001006014447c5200041511f140180018045111104c0155024100741081c9403400c9491102c030b940c480454101900c0110307640300b4040d03401c02c3c0e15125400b1f00070941d02d141904070021007142003c100301842d040c0350303a00040d07050310160303007801a5070409030720003007103a1a41800c585900ca10303605107030b1450000b8030b031035060b16101d0f420f400307900c2c00f50701008051894400345880307649205103165170010f04013004001100030849802c4070a0720440c61415003c2d112814413540c0c06200c0903190f0002c00c10004040103000e259a0400c0090303a0f40c5100d02c0c0000c62121615080e80c105006a202a41c03241c6001d818003120381d0140c11048024200b9561480050440c0040000080003030191000000074000083d00048045e030710034400d0601d4408403031250808064031030a40f400c2c00c207100d1903071201042201c0e10500194a01c0c03070700301885007461110ba04140c1589015000f9105a50416894004840c10710054100d52107200d50080b2080c0114840c2d60f4802e400f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 976231636 1250 976230386 976230421
    0xa060503071b2604050d0b0f0901020a02100f0f0c080a0b012c012304230f060f0f071406070c0b0604110f0c010b040c17040b04110603 59
    0x801d22240c52031540545081d84410b14aa020191003a090802000000a000b0b039901d040c0440408000202e1560b85040003c2d105030f116090888661402d440210304c5060b0240c019901c81e80140803c01d9955008140328048015907031f0300041685a0301706000140181c11030301c0c0d040a10f440940b41c842035001c44081e100c0c4100b2101030058503010303030045900400440c0c00c030030005031603071810201c2048503040648182052515070400c90b40303455080301c499000800c240c2c0c1440000380400c45000702e0134020070500c03214040f8166040464009c1070b10b010400603254851100041e0360200e00401d0002e039412480c8207009541c4889207803900900d0030b0000c03a00d01c10700e4402c20740041d04180c400c3c9040c009043d40031b04c00c4809030301c2d84003c0c08040c0500740c2c4210031000c000d000740c00301040c558001e49600140e0f480041160304000c070501045842007501c0e0780c108020040554025105280700681066003c215400595101d05007501c6c0490b0341403450ba8002000002d000205401c1c810900 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 976232886 1250 976231636 976231651
    0xc02041b0e0406121a0c0408030406120605010801120f0602040f030302070e011e0311150d0902040b09010605180609060708030a0612020a090c020f030c070e090a03051c09020a060503 80
    0xc141a25291000340181c030f0850010104c0141740b0404001500c0102d0142d00700314840705160602e6112000c16003990480e42110700000ca044450a14420890042c400108401c0c2420340e0306504107100300809102d59000a01235104c0b0b007000104004183d81100c0041000445082e030701600ca01c2d000b9142d800ea8414031404549000001c94144034100c0c100d04102d00c14003154881500d10741d6103010a03910180308551040c0c661600070034840c0014020101030004040029480c4010f104100803a41c07820003180c01074040d080103000d0035820008460104003040e400514000a140c0000d005209000b105500041d010466804000e0b492000d14003621315184240a4141c58a0307800e107101c1c1580303c0c0603511041444003004071100d83d6108145050a51041d16900c03410f4080c40c0d491640030307503000440c55110141c1080311105058000c0d0b001801c503009028042a542c800400038020441d10310541880c0440040c0117400a80c41003403c280c0c0540880c0e4400e40e036030f6015019400445810 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 976234136 1250 976232886 976232891
    0x3060109030b012706060c2006030a050402041422020a0b1b0d030c0203120a020d1d011d0604030807090801062306090306010b091206090a0629010c02041b0e04 70
    0x1400c1d46000c0d0702964060310700039a01d4001f40509615030441c104000907112000707401c0211140300c2c984034440210b01ca9000702d08003080504051051008940c2040781307000c1045100003d11403103290f00718a40711301d180000915941800300d8000616940000d50000e01416400240c540310a6065108034040c0c01d09082903a900c0148040c003035040c0e409240b88030005801c10003001400a8034201e9040e0008001080141090403052800e412603030107250b1010140c0c482c242c0ea0805a009014510f505692155103e080c0c01459081c1942c0d00009013000302445500c03000205080d116401c00c0d001460390384000d00200c0c0c0c1d150411620394498200c4a0380f6003401d1001e0700101d042442c12100c0a200c05001440d581c0c0c07a1081842d21500929601030740312181207400c00b441001003142c0c50044221101800c0c08503114a01501100e402592081c0200c01d4482d0320000803160003a440429031b02800e05400303995851002900400c14101c4140302d4424000118040590200d070400f0703290020b4504 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 976235386 1250 976234136 976234199
    0x130e01051510051e16050c040b04060f0306050c0c1b010f110d120b0a09060e4c0603091109150114070f030c0c0b0415030203060109030b01 61
    0x140401440012010030120342d007003200031101003001325000c101540c0d64008a04003c03c20400b8030014000442c00e4503036500c10004030681c1d140a00c515034030f10354102c0d4104422450a081460f44600a10001e0b1019680e8400105164124400c40b0075158440f000e4070072100e482c4150180d0b507241c03132046600282c010100122454002c101c14003024081900501c0f2030f04030b44501b00d403c0e0104500c40d084d45078a507451250703941c490000c940c020700008040030402c58102005801003010003002c4401451003407a2425000382c41883e0101d1182503c0042c0c0150820861115a11401c0e514400401062290000b800ca0350603480400030510038440302c8003031029403007000f4011400b510a0020b2842a00c1c2c00403032980920710108401000c01c013114100f0500d07441d0107589a0408078290082040303402070178200b00c056000c0401400c883d038a0941407034100354140241c00074207920741081c582d000021030440ea005210040003158090301c8030200350785800003400d10000095101a041034260007 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 976236636 1250 976235386 976235389
    0x7110d030501140d03030b031c110a1212090b1006080f07050406110a0507080d0210090b060f04020903121b0a0f0807170406050310060206060306070e130e010515 71
    0xc1e01d040310b1085800443c241984000c11001e40e541c00d0040341030594550404019072414040349905a0070050103c942d00200b000c081c2070000d01810044007500040104400507420301d1021a00345c20034039048031400c85100d610307c0101000705001d41284ca00307208200c5040d003500d542c1c2041d1803491742d5000040d120381d262001400c0042e203100c004030700140400c3c482e5501c540f0040d91080a50011100328000c65241e40e030514541d60005d4019030058040e40751207a404000d40c0300700796100b8004004420b596103841c256280c0c007404092040710b8400042003542d03031b0b03034058030409440281039421101c2070401680580c0d20507002516a684d030811481c4a0440c0810300c8149103030080016400700240c1e5850030b04c640e1004030101c0d104204d1902c003101038143c88000c1c2c8080c105030b403103050350790418441c1c1003c08035090f40003004541c0058208012600e000c10f0036500f081850074460343e520070f0313180003484030111101c1081e0f200d8900000100ea04205404c01400303480201200c000030323846c840 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 976237886 1250 976236636 976236641
    0x1f2609100b010807140921100e070308180d02040212060306071416080c030d09110d030e04112b061715061809060f070f0e0f060f0307110d03 62
    0x181d41300f021038982050100c090403244000c10032081c3c000e110405a450780c0401503400900d0050703c0391503502c80360000440c1038103071150381d003004092030081c03e03c5480d40d5100203030b911030303c0707804152451141001d62580d00d0f959188000143d00038000e5480301c54142e60404426030446a2038464466240130407280350080d602e1b10356540701240c0a031f02d440200d5403a0a2038a0050f181255804ea040140009445080c4040c0000c001c12410200d80c605560511038901c034054041d07244a690000c200c400043c0c0c2011070070350355400680d00420010103000d004a0180101181090710412030403c1e80000803640686402c8840010000c005042e00d42011602e00a0340150b0f8040c0740d07000310710629015032244006540200014007840b132050043c8101304c0e00c00ea09640455055000341c0034010302c030002e844103030350100c0d003803030210440000b0341d60041043d0404042c440c01074461070001c0c0300c90b4803110708541c242080343e10308582d2030501d0440108840110141c030511070152441c1501c20303610a0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 976239136 1250 976237886 976237891
    0xf0608100b1306030504020607020607050f1002031005040905071523071e140709021b010506010906050c031909050114210604020d0501060e0f1f2609100b0108 70
    0x3044010041410583d040c2e008000141c4240c0e031002c001c0c802207006946660007004418499409003102d40b0342c1106040c68031001c903007000d00250051080003070060100b01d03c0411a101101e010030040e45606010342040d41c942c109402280c550040d40d04c100750411f9007244403030a00c6050440c803094034440c058103800303045001003032a00c414241500d41000780c1c071142002802101c0c022900a44860700502d8505113500c00c42485c1d0f0082080341c680000205d480b5120035001c1d000f44134a240c41c0c1d0008000c000b4900a2109110001c18402c00c4a01c081050751900c24001c5801b043c0110f40c0c1c400601412100e01c10607000456207401d8030003218946040d06c80604125aa11070700d031295150712181c014004200c1c80e04650700b07000c002e140d20f8407030040c1030003405142c60320350350207460038140b000340c41c502d80b00780e4041c00340716140010802101c42d41c0ea4020030b09181502090200020700c110550382504444890860003050145865020407001980410340c3c6007044240c041d40010350341103504 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 976240386 1250 976239136 976239157
    0xf1811181b0f0415080114061204140c0909011a191202010516060f0605060a23160c0603050a0e06040201031d12090a0803040503031b070f0608100b 65
    0x9403501070140107845000e88400742c1c142c40d9960805450701d0810041c0105454424001682440100322201002c0c12420311044141c4d402c078501404100144000348002c2c1c0020091612607514180c50300d030500c17507201a100c0003419100d95080000520307010f0b0510340d0362113030080403a01c2a14094501001c00b506030500a0000c02d002501c2c120b1600ea003804401405e9050081c00c116032070103072010701050580300c0c0c4280400a2080c1c003000c064000c5030350b945c0250380250782c10410601c0d540c0d04064009500240e00101c840d8101400c40103918500900308064640650344260300200403c51280300e00703440c1e196030200010340e26000b054040e518403e500c1103003038104a001c030703015512a4104080b032510000351185028401560356103410030005800380c0140d404a11260145480310360000100f00c08070045060a09140001e40c8a102e01c3c00000c414143d245200c030300c05d05051202400a1001607590362180b5514103000e01502022a10f4000c0d1000d910008261304c2e4038401601d00c1c51a0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 976241636 1250 976240386 976240411
    0x21040c05012d0903020a06030f1104050d08030a0902030114250806010509030106150309030e04020901021515090408091f021002070311010510030b090613060f181118 73
    0xb202022103030303200c004200481000007951000c4090b894051003140107090650b40001c1c03141d42c5024501c01c40b0040e0348051f01d00b040c01c0000700100c1d500c461010020301d80100c1120b58036203601e00c0030301c000d1216040c025015400d0100c1007420550244400e842071001e2050a984160240e007240d80c00c02c04065080041211800031039041c0d449280900366a6a020703000042c801d4548802015656001c1000400a9100c2032600c0070190300907130300105100300750b80950900300d1140010b92118443d002028210790b28000103a240141c0310140c1103138040c040d02c1e80340305090509200713050380d001510903030166135540120084040001030f8291804299406080010b01c0c91100c10040d511560b425020462007480000c0000c00030301c900e60041482d00c55400e411481c43c0b82481d40550000c1c2070b2045504800100100f10700b5101d40840380650014002407204144400e280080080c0b0000031013070b40d0384101c482c0c02c1251184a00c80050000c03148480c0c141c0004540d2412413500706c4240031341c0e54 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 976242886 1250 976241636 976241687
    0x3021e09030313090b01090e04051b010c0b010b0a090b070b06092d0714030c0a05090112230a0b180405010b0d05011406100c02010e0621040c0501 64
    0x40900240c504400c0081c140e91520429941041d1080c00f550403000e040baa42c0d4102d11055a005001c0b20024048030700c1c0c10f52285890703103d0035260801003094160b081a00c1c10103540c40e0703100300403844145030300c030300c000364596102c0ca00d002007500060308010104081c0c0102243c5108014240c90003103601c20306625650b0b03100018070000a4020f80300c00f03d0017004144511900107809000302d03500540071010407039480c00c454020411200c0b00c0300141e0544080050007e01c6081804076041d420315030621968801c1900d004880603207440c40c040006c075150500ac072000c03008603609c41d1601044050104000d0f1200c030416021110810042d83c1e01500d0704c0100f554010300452110391080c003810000401c55404d8012440c0007018000403a4140d545140c40b0341c659004000054010030305071005015065078441c0901002c0701005d01a0600940c10310103e00fa603244c00856002c1009002c00b1a51a0000641030005160036602143e800d640d105c80070415521500c18455690703220311100c0b6085 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 976244136 1250 976242886 976242937
    0x2010f060e0a3c05100503070314070902040e09070503030f1602060909040b0403090e10051908120c0f0309090c03070309020d0b09010b0904020108160504030f06090309060302 77
    0x1e240c9000d1044501c05035004a21500c0000389008040c550003040080b64103061000d0502100c00040001076400c17000d100501c001c0d20b000905100362503006110704280700004204501e40b42180c0d01031588640001000306003000310360006400386c00d04a04580c40c0326142d504054481c01880b900401500741444115032640300c01300d00010f0030340054040c45c07034504d1100104072000700881d000d85001c124442444201a44030301e00d03034001e011198103040c003401c200300c400607070054902c911441246207800040d042100d40d280c500c010002d440456804142c10201510b903504100c003c007446020b160b401c0390381ca8102004403000300301e00508000302c943d105000d6000580000d4551410540d07607002102c01170301d5030f804080300c030341c090740d214407a034079064030094250390700e00d14910b00451090b0107100050340c03c0100e85d900000801034408040d01818401c903400d0085600142105d021101c015041c003203140e0000041d01e000f80d40c0c860761180c45103019401c0c4d108000240020540c45240785540 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 976245386 1250 976244136 976244141
    0x60f0909151c0b1609170a0b010f050f0103050a1811030d0806030a08130b030705040509070c200312070f06051b0d050406020d1d0f0d021e0a08070b0702010f060e0a 72
    0xa0014900341205d000e919600c036540b5480f06400d00340768070f0b4440302c21a000d00440400c02c038010001c03029803009a50401c0081280d0600741310f4080c2c1859114004039040105a801c08500b070b092402181054401c01c0c01c0c04a107481d0341c0a00c6038000d01401c480c0d140142c1c4181c1000e4032079000a001410850101d0340c60030b205501c46d0010010407082c0c5074010482858003c02103000b1410b40d1b9415881d03d05040030060181c101805071001e004c40e04910400003080100e10142c03515000c0003120005c0658000700e03080000b2030400c0c0613640c00c00a1044108040c0d40d010049050284004010310381e200840c50a010498880800300c5000520030101c0c6142241c0141d03034014883d07000076041818921321007041c1c1c0c4004009841da802c5070240040c480404015190443c4101c130020b0a00900318000a0b4899a100b00d1415070390040b441c1d50800c0ea801000071f40350ac2e55000d904036603107003410b00b00b0304407a502c1547c1000c010b5003090403095900329140205030075200541000380d2982c0b00c00401900 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 976246636 1250 976245386 976245421
    0x2101a0907202814030a08041b1512020c0a0503030f060a18091109240405061302030907170f0c0603010b04140a0f3f02060f0909151c0b 60
    0x6484d94880041c82400794107001406000c0d15a8851402c80e003028034154041040c114400c01400d80b803080100880e0070045114060b6200904090150750401500e01002e03129444841e141d034070030035400300704100d0b000009610800004404400366110380e0108001d0308030710b200d5054030420740f210b84410b800490780a0503815200f100c44080301700d903000c04204412011501d0107107500c06080d91401140d40c1c9400c0d00580d070000c480410451510800048070154001c1090003180e034048002204694108122800b0345800b07140c021082070480c20f0242c0e5240c103401000b886c4e010f00e00c001295400c0c02c4080c0d034161104840b209080a040113110b140784c0c24481d0104c0d034003141a1400013450360500510f400640314403880c0740c01600000322001c42c001c50300e8541c081041c0708050695594100d0458141020b42e0480349070b5600c1c120007000aa00b8041c441920b6403180c3c5040900c00c004d101000c80e90040d01061710b454000517810151358450805202015000d62116400903030302c900c00556444 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 976247886 1250 976246636 976246643
    0xa02010605150d0f0c140d0902090f011d040803182416090f0504230c0d06050f091503250e100602101a09072028 50
    0x2032040d9460300059003400c0040700d500c409190000e6009000c01c0b880c010341e80d0301a00b9000a2054a410b079074020b2000c00f040c811080d929202003801d4100e00601d4000044e096002000d13074181c0d05141c101c28480400c20b10074402c802740c0d559000c810764007e20390058892904007400c5ca042d035481d80c007940c160281110001100b4001c0c80d0054039100d000c2c5560440c50307044019600003500e0800c02c02400304009910101c148802c0d2101000301d0000380f0000015520141e03400310f806802c80001c03200040440034035200d0f40ba64002007295a4030450060146890a0082032010903590320034800d84152508030a50448202000a220106ea50050400100028040391880c00c03410400b40c40cae0240302154680300d0140000200008400d019040fa046001070340300b0000d40d4a440e00c080e58822259008c418240d0311038482e49456039040074001d41d550700182c80c540079860311203c02400004d042e4000c80911503000200c8070701e0b505c0041c0b00c10120816402e100b1482002e0301038001079050181040703 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 976249136 1250 976247886 976247891
    0xf01030b0c0909091c0e0604090c020f030d02070209010504060b0717190c020a0b03010e040b0a110a051c0b0a0308070510061d072a14030a0c0309050301020901020c060a0201 76
    0xc0c0ca64840c001c43e40c0c4940510f82c05040d0b10400041980c080207205003d0500b041070342c1c003003600c0d907a0740c140c1210122418000300040c1c40d02024026420f00c65180040003079400080349416000d41e07a84c000b0049107108448900090f0303254020002101d8160240b44075000c070520106001400d201100c0b50030304a15401c450420090800b070450450790041c990000a074041c4d0943c0840c10310310701c01c1e4090407081c52218155810807420403490100100040c00420798070000c141411070690069070018040b2014a984500580000c0e02660102c0031104104018141c001c20044443c4155040b001e801002c1d02906440c64560b11401c1d001440182c2c9c441c040c00002d0410038056110ba10014207081c45403400201240e00e44005038880244000e050020800d660840100c01020b451182d5031404540701080000d81852040100d0804c11080c070342c4400070b0400f2080382c005c1c80e5225150710035070751030710202e4584003810300f40e00034500b01c0750240e803250841c0d9882d45031501c0503003000d481e1072000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 976250386 1250 976249136 976249147
    0x50a171306090624080601170309130b13020a1b020f06090402090a03050d02060c250f0b09011d01020f0a14160b010e0a021206010e0310050f0a140f01030b0c 69
    0x52807002d40801c0800f004c0d0070610042004491710602c5814018030550141c07203410694401c01c0d544a104001a02c1d12a01010311202d03208526540107200c940c03000351001607104d016140c0c0d40000d60044074050702203540c88040358485095840c1682081c0e03800ba1070300369040442d00074030102e504040c1d080c40e4000d80901c030105040c1c650705a000c0040d07000340010400c1411140b0040d081c0500030303024909142d01041095034a807419045000d120300d801c0d54400d0105058241403500d01c14407000280340707d21410602c601700e001500724800320580c41c50681c8100529188860803445070003c2079401003c10f0004a0980d4091140c842c0c808804020691411114000d0201c1d802101c10044400b10510001030200706c0c90082105da0002d0040b000310314081c0303945807521021400400c0903041007001120201a503c0600001c050014229018855828541d1840000c408119081c0b00b580385003e0750302e040700f43c54182150090f00f610307132041d20903420350301c2d0130010b404001d00904810104122 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 976251636 1250 976250386 976250411
    0x7030e0102030a060603140f010b0d060e130302010e0a151512150f050421110304230603190b0d210e0604080c010c05011506050a1713060906 62
    0x45116104001c400a413640c1800000381c12100c40030803441c20640d21a0070030241c00003140300b960540d00d0b641541074442d140080d0040113401c0c103401800f0a00d4614040c031042480c11100c0412281c0308e030300240001c040040c100d682e03402440b10060110b8903008580345080315a030780925152115881d0088040740c54000c00082104901d1044486c94000c40764240004907503c80c401c5100200001030100742899100c200790703a000c9030001503c00c200125403500ca140a000340700c14413400300c41500e4843d56100c2070fa40c200150404c0c040801500440042614a08481160320480c1c6030b4072150b501c0500d1107105801000d0080d001c0f03401200c813240400208100701c81c0d00d00d01d40d00c40c0c88204500540c0c101c1c0208166102070070750b802110b007440103201918021600d0000000300b0300c5c0220040d400e505100340909509805030681d500381c207201044036940180141a096801d032669103000d1150380a1b03000c0a003088400540e01c0e20f4a41204000440a8109002e0700f0b00500010614540030b0a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 976252886 1250 976251636 976251641
    0x70f0c080a050f0606010905060d240b09011407030206010e0903040f090204080c011d01030c03090b04060920010c08090d0c0608010503070b04050d111906020307140105060f0907030e01 81
    0x81c1d090750303254400104410850020040b01d03520604c00c0c0792081001c0d2402002c1001f40c080c80075022000707504c0d40d8040707e0010310051454502c0d01180040640f07280c1e41c1c1b00b200650342c0950120750000b505620300b04038003003400d005c4402c180d0703165000b001d0903803801fa402440c00401070208019030000304400900d15401c040b82c00081e1414035030050351945402c0d41c0500c4c101c0354504c00780c1070264207030b2544404118100c281d0007201c02800d0100d1a60110b0004500800700f03807800074140c0240e142800248036840d440214079910400360320b01d07850284030411228250030440c05000601c4c3c4030207003002600310b40150000150103002280d00b0312543d90f41001a00141c0c03c0704001950343c1004004a150801c003507001032103808241032806041c2000308100f45203201018241c003801c030400c6c91706d036150803150701d03002c5901e080340048103510b54134001c3d2290300c60681503039100038034000d1145441e41840b4042c0942801011032308900449000e02080d030000400030401d2644d81c0b0800440d001d07003030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 976254136 1250 976252886 976252903
    0x2120f0607200c030d0f0c0804090603020f01050c072102030303040b06100f092c0702070317030708060d230601080708070f030f060b0d030507020a09050c070f0c08 72
    0x240c5034500c142c110451410300908080c5074100c030360b034000d0312985400e403404110100c452217a031501b1421250000020b41340b21b0545000200508030003d4005541030880d071203401600e01c200c842c0904c1038150801185c80e40602c4601078010b40042d8410041151200240340f0400041e102c086034806c3c09400003400d58100f01d0302078840d00340b04401c012281c98694842100d216650030200f44945400c00004c05101d007030300501101443c0d04411a00c040eaa041442d1074030180d0000300034140c03615402c000d4a50141f403008480309040c4000c0f00d00d140e8030072801c0d2841f17150b080d074a0810f00d9030b81a0800c041a6000c1400341d07403041e482c0004540c1442120707444039031005098002c0260b54500b00055280c0356080d804010690400d031000c0c00521040b0f0300c150704403a040040902000128207041c0020841d048010b548012804950401c140d0000081e1124500172924000400d0f03642c65601c041ea142280e00c0004040100000380c002030400141420030350091410428150300d9108203403510400c0d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 976255386 1250 976254136 976254151
    0x1b1b06021c110c0d050c150c07050d0812241f080a06050a0f080f0a1205030405030c01020d06060f0305010501020618030706050a1d010b0d150e1002090109090b0d02120f06 75
    0x841b003500d0445c00c0c1407001a8006828140051500c002a0085a2104164018907115030070300035040c0e040c000102e0583e9040ca5445648444030b060201d0164620600c1034041e040800c03440104686510b0014400515400a01d4203940400703120700c8100c8629034014034004400f640e80b100880d081e200c814898020340110700e00c58a100d41002042882d10600001058407588666945c5000650070301208000c29000c2c10000d4030380c3c03502d142c00c0d0b0450182130041c260940c800f1170009185402a0803120850f5501e850b5841c08118183c4110140d500c240629030159100c440440c0c510001d00d0001c100c05c1b2001030030b0724141070040e99058103132102500c00c01a56506e5100302c0150701a95074241440401f000001c000100501001c40d1072900d601402402041e41c0501c0041494015080241004258000d039101c070380001d0b01c2d4000a402480d48240003403000c0301e0205405c0f82038030a030308403c10001c0028483d400c0590030412252404462010140918032201c00f0080c02086500d01803e02d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 976256636 1250 976255386 976255393
    0x150a080a02031f18270809060d0e010506012c130902090103080706060f0312211b111f0f060812071709060a0f1b1b06021c110c0d05 58
    0x5801e002007952071800340c10f50720703030030000400c5c4942e80802c0800d02d1241d072220350b03c0c0c1c9540000c80010325078014810b01c0b00206080030300c0404414419030003984602350903200e5040b1507100c5031074502d415502c0344184210710084072036a0054605915581c0900c000540081540740043e400300e810060281d1017140c40210204022003085514002c0d200500700f001030008816146417a40f180044145a01c030090162002820603085404c00a0441d6009144000d019414601c0c1040c0c10b02e00da48445080000c0300301b034074042c990303e001c1440400d02c61822414500603105001c2103000b4001c0c1f24030280140e0b510040000c40d1041030044400070b003c543c1c25141c403920f00c0c0c14012000110800050084002004030303c4803680c0d054180d41342d1240c285010741d08002c804c401669281c107070001d00d50060306001d45c03103010042c40e100c148400d008403110003903c1c2d996411059030b0300c00d4840407104070400c40310ba4007886140310b0420044000155002c42d42d1500581d8040b8806009001044d240c581 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 976257886 1250 976256636 976256669
    0x30304090c0921050304030f1e081804020310030b060301022a0c030c090f040203011509020c0f060105010f0c15020d0e0f0c01080c1c14010302150a080a02031f 70
    0x1c043e4104100c01445210400740206a01e940d90381c0c03241b045000040011070a1454031041c0b210054455048840100c0c1a109004e03982c20030b031600da0080520300740d16151070305011102e400d203402624000c509400303003031500a00b165140700b4501d07402000726405650a01410004141d4112a034901190051600701c000d9400f50a85041010803a0200e019504c0762880070603035100c2d41500c0d0f070b1010303001c5c2c0f8122942d200e51001a024200c042041c200202070480c0110b2402902e0b4002c0070880254400c440308011600c01454030b80c2070074840d050106000c00030749000c05000e60021604035100324801c0e082a208031150f1400c80c2c2000905010307160b91640000c45583d8200700142038890b00b0300060003404240c20000346909401041c549000b5000301e04003803414084c10180210007031740002031100c20003d44001203a00001d00c0300f0383c807590000003d000e45008000403212003200503030701c40600340c0d00c0061980c06544060310a011074000343c2030aa18903a0205605006041d1000d501082c09 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 976258992 1106 976257886 976257899
    0xf090b180621040302061801050f01091107050706020c04060806060a090c030f020721092103210510052209051f140106110a030806030304090c09 64
    0xca0110b01440300701a00826024130a0440a03503644802c00070099503402d8400958045200c3c0d50390100500c80f194107500132113003044a4502c1f403031424499941e00c6290040a5000034010381004460325001d01d4540030704401004030710010300c41d80c140080015440e0b14030f48261036003140e98a07000168170f4001d4102010104d5000011074641c0813505110f80c900c12151040305001c0c0349445001103503070044c510f28064071410020783c03000190b15a085545039a60040503402d00c40d0014003442d6082c44c00f20000150407207c81d003c83c5500f803d2021300710700e6040d5000941316414800381009a1004030340039805c003a08500d004500c00845080c5982408080902520002401020b81000e00459040002c0c606d4151020682a070784c1d07503804030348010301080b805429810500112011030f00c0b905070260441001020341e803070b141d42e84c1d00d04403c482a0794950f1001c50130124080189 = true := by decide +kernel

theorem cover : BRFrame.Cov 976079136 976258992 := by
  have h0 := BRFrame.cov_init 976079136
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976079136 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 976079136 ≤ n) (h2 : n < 976258992) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
