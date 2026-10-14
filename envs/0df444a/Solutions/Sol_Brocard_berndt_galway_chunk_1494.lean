-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1494
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:15:00.480927+00:00
-- url     : https://prove2.me/submissions/e1ed6339-8a0f-4894-b13e-5ed77eb8723f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 268525179 ≤ n < 268705035 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 268526429 1250 268525179 268525199
    0xe0403140301060c110621090c060706020d1b021b03070504150f0e190902061c0c0e06120c0a0207090c0f0305160f18080f030d15080606010e0a 63
    0x4064480c9a450b02801ca8407170030014404241c16103168461038080001a205003a6503450618111010404010683d1404520f80c200750040314130700d03001000040d00c101049000d60042449042035001008460101302c060001c0040b10f1000700c0159004c070400f4104d4400300b200c428030024000f4205d520701a2240082410358064070700205215504590078483c0348490786410740982918080782c48545040d85103548010314500c040700c0816603c1c1c001c1d030259150b08045840900c0d49200303482d584040010b0250040004002b84400228400c8902c140362904400706e42200015003504201910780600400113640040e00c450190300c0384200020741500745005101030000d040d15070040c4910748000113419228000c1c56087d02d00f1000701da040410750055160100c0054500c2d1000c4140607400c114900031240340c0142150388076024480718041d80006c010010f04440e1541800403003001c3c1001d40880751b0f24000c042d842d0700004005405544034102043c040003008040c40d011544d5165010 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 268527679 1250 268526429 268526431
    0x61e0403060e010615020316030504031a010906060e1e1c112b1203230405150108150403030f020d0f061a09041505030d0c03020105060a050105040e04031403 69
    0xa403002e4940d446014802c5083c4a0322004248800002c0c0c04503c1d014002900d0388299000302150f515980610800d140c03090b000d590140d0307444080c88901090a252048008909124000c40c4034180540400d9542c441d02c4c0a6012100107410b01030070240344100c0d02d41d0011004505c540044076086070b440007030a058004005180100042c1529070440001d01002d200045441e00320081d603070344000031400105021000700398120440d064402e000f400300314041d1200660b0044135891002202202c805d188120501991048040364a4030b1900209040e006000348120902500000042c0058035083c0058640c040d00c030740b0300040c41c10101041403049070081d0b458010800d13981c42d0b001450107514840c0c100500160300d40b800070710905800910341031188040340703801641c80b0032580c01c010140003504009080000d041d42c4800740c0565000303050054850003030b0019070030301c0701094803810001c01c8038003960010307900c0503d01410001c0c0130542c0380303010340700310104400b160604c0b5200109074099 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 268528929 1250 268527679 268527683
    0x512090a061d010b03030301050a0306020d0b060c0705030606120a0213091e050606010305011412100203090606090a090308010608090a0b01060504050102070602070f05010f1e05030a1805060402061e0403 89
    0xb01031081c600580840c2101c82105249000ba4020001030129540d540c9400c800c0b00e0303100740c000d0b0341c61044c1c000c080080e00f441040147c0081001c6426a0b042c0c030302042d00015203400b40c084800543d5035030108814a03111421403401d6802501400f130141c140740c108220304508400022440150558401243c1032044e8862040040140141020070109000303264202509103014880d0354101001d8002140c1c0c01c4507036912515051580b0030b0346000c00d01039145074034130030389045460f464000c0c002c44d2103401c02c6403554414803c840014031801010b11440081c16016500c40e15507a007889010340f40200040c0c0002090b00c80d4889400000c0d5000c503860b4040c0a05a07a0907032554602000a0700c0e25080340c20030780c00c2d900004400d1008601d000100422a03009203400c03001845000010f4a926400da45038201ca417899120480406400c075000303600032000d01c40100403003140c00410450b00009081d00411350f400c00c0c00401c004d441c0080107415a140184024a0700340941114085550301507401 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 268530179 1250 268528929 268528961
    0xf0a170102041d070f0e220e0705060a0c03030506010908011508011104031e02041103090a030e060937031109100506070602033c090d0512090a06 64
    0x3800340f04881503441e070000007629840c0e949420031540107403100c103035412590f01304450901d201c141680c490303240424500480380d01042072120036010070060300c010750100b0340318483c42e500081c86040c840203c0303200c0c3c2c00796500c110b64503041c1c0c1d500301c0207800064200c1e410420445804521a10300b17100725050b550103980c5400926142074046820f44107000e21510030280240001c00118010ba403c8075500440e41c00c4e15190401d0610000340180b500c078001c4800d000000c4200071800e10001080c103421340c02502c42070101403241c0200000c510405d210980c1241d80c41801d05404590040c030200305280c0400c0e000244405814505450482a441510307034480c500c2710f00742d441c03c006042c6ca41000381c01c00e03000a014204004600346104612004010036070000c00510450b04c03c50b84410002c4825480317510303840d05880c050b0700000046040c00b504000900201c1c0500f44e00160100300d000c443d03292a8142200040d0300032038280000c102801c540220032518000a8242c42030f80320b00b000f0210 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 268531429 1250 268530179 268530187
    0x10090c0305060405101d061f09031103060c0406030509010e1207140a0201020d050a020a020a030c030311010b011407020307090f150603060806060d02120604032109020d020f0a170102 80
    0x3048150ba0020301740c0d401c21014402d00b40004009840030b66800e031446c8503101c0580e12401c0100d0f8046c0032011500e80031600c20611210700d40d17440f8408204603030203400f07070819022409007003680340e5506454810604104110401009009400140d4441075110002450a080d1003080741023603000c0c4243e0550480004260040000700c05c40400500d110380010f2864402c59030010f5070303540ca0854080c0511502145403030540b4030030046520b500341e003c0c00f21040140d07a031802c1030f40280e0a0000318040f41074420800c003120b4052003142d0151505a6400141034440d0b10304404603400b00100744c0e00340c05815800f05402c2407601852005241000000503e100050740c0d5040701c1016400031001c01d13042480c200603000c400500150084002c0b904c0032100c00d4a840060a18688110b03000031901402040009058100c2003038645109441d86030b15406520081c01012074010550080d4032046806505016080c000340d0110061005052021070b1601d65a14a00b8010580100c1c20341d40c1d0005 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 268532679 1250 268531429 268531441
    0x2130203180f0a02010818010606032a08040b091002130519031505130f030816020c1f0201021213060b010905130b031e01020433050310090c0305 64
    0x9a05080d03405186070181c82d031210381050560312085000000390400c40c0200200d102d001c1114518000521050000c006590765010080c0240115455006850380540d124030100500c0d01107000c10b5034203950307990895564aa48083c80c0401c00f43c984980b82c031420410000b4640c0a1001f418040342582541100e02d10b030030108404540110480140c1e04c50803541080014581d0302c0900c0680419100440c540d80c403035020049c50b00b200000070344641c503050710030020300d03810041f6503000d0740b0b1140e80b4030020390b280c010a9a507802c7d0f00940c0c54108191020030030300f2465089054024560600c009854011482d800920000081d06d001410f581e01c50f0072941001494420400c1c181401e0801c4201c0a213850001900d000f104280d03d441076444404107001c81e5028041281100302c2070040101c03400b42401154000c4d00030b4041c4281c15000c030000942561090207020284c00301060110030380d1800300d8000c8609810107014003d09400000e004144600c490243d0089808161f4000426103072807 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 268533929 1250 268532679 268532701
    0xf120f06050307050301021e0319050c0702040b060a09060509030c101106160813060b04050a020904110708190e0d0f110d11010507020f0d06020310270e030702130203 73
    0xfa5001034400c1c0e00c100000380044e0b000d201e0841e003903e41d4001d5a41c507565240d440b2a000c5042c40020341c900380c540402c00980d0300384079004c2c1c503110380251020841c814140c400d1000c6881750518440110742c00060410038580b041d03000344220000078050303840c41e01c1400d0115010209960b414004950103480071402c62004004041c1d0180450404000605850784007404400b0040d00c04003141313440b07054031403d11255030800707038402502800402c074a04e44014940d0007500604a505d01c1a4100307858000e86030205030954110710f40010303041d4034207200c0300c08000001c082c024082091194941404001c2c2da14a242407000500804d0714030203a2600c2c3ca040c2c00110170b0807144034402d501040c1400081468401e00940400080c00c1c29942d40040f40000ba21126a046059070b01403203d490000030803a094014600070080c21581142d16911285d01600f15a9031100031807410b00348603495529800107400c4054800600350a8900d0040b02d40c010400c1c8042a202203005c0715000400d00c500800c031 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 268535179 1250 268533929 268533943
    0x204030b09060a0c0c08070201030e0d0f03150302090112020a080a0303050a0b01021c03020309151e0606030408030606070c0305010e0d0e0d0b0114043905040302100f120f060503 78
    0xf20810001002c48140c0a0710800440c030018061007408503d072821a400799000310802540401180c1c070003100c4d61401411402e00c1d00c14040002c1c00d0404041106040204d25402d50740e00819001d03980c1e00300242c0d66802c1d983c00200380d0f444280703e240003410903001d22038100c1c501c0c00781c4d07004516843c0022540c025a140726601e40d045500c480103000b007000a0a1401140014501c1c003da500c0e01c40d210301c11302d003075040440d003141c10303000c107007804030745503e40f903201808800c44402e801496440504001140c0000c075000f4140c0001000042c00e03602d00700e001001014072070f0311400080c1da22078031442e00b103409940e22182c450380148041040240c1011003102c21002c00c4034000300c0320a003541ca064017081c043c403403514070700d035640c00c042030301c3e40c40707402821000500464512420300c0c2c00c01d20001c4c043c1030114028000031003102d510300d510b206508507400d4070380107010001c0e031080340c00044518601e4110b05c1010070035600402c070880c200724040c2c4908500403c5003c2007072410a4209070030140 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 268536429 1250 268535179 268535191
    0xe0609060904020906040f0606020a0b0c0f030103080a0203041203030b13060b0f030603011410060f031b0e01090915080c030114060904082109011514040c09090204030b0906 76
    0x1a4850802440390348440609038043d80c1520001241d450b010080b0300902102c1c04210685400c006000c640b41c0d0340001d5040c3e900340a096440c8803901da504c0c07001c80314854031420382c00c0417104100500220f11000001d241034040da20480707240c0785e0360765002d25045218120840009498800c2405a0302d8407103000d070b03078007450200300300034580ca80b90407410340b4851030803c221041e4011001601959080d845510f0354044200800120710f03009500208200d018000d010100b0411110100428801d00c00d0282c81301880c1d021001d01c10f202d500582d1a4041c070940d0b1410080d00440201d0082b5040c041d50080200c600201c0c284d41d41001191424002e0326040c250103a03240c540b400780002d140c51002a0000000e803059400d0f0303243c43c01c110149100741d03200d8041c1c2c4140800c0310400700c559000218410400d802c000c00104140c1d0840400d807100b503100e94043c2881c00c200c0c1d00c0143c54507078400c2404c10007606001003c180c4c1c840f03850b404e076000307a48203481d9040c0300420400760301030500100b50700203 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 268537679 1250 268536429 268536439
    0x711120d02180901080c040e03161202190b0601030207060e0f030d0c051e161b03021c120e0604030519110108040804090906111201080d09080709051b0a02070e06 71
    0x50b04120171710f541c82944042d17551040c1d840d40444150060309200300c40c50219100300c00132621500381041d86043c10035140c1c1c040144110602058030940d560f21404005a11102d4030119468420046000c1d401c4110f081da02d59030f54800c03289815200700700c82d101c0301c18100051500d4140415502049408143c4448140141001040b42c80300f86000c0c0c1900c1005641301481d05c0d81c889030802a0701640400d4011f1204ad8004202c03022944405082e01c201c0c0c0c8200d070391203a80900b0311580d1803e0f10110100600c0c4094103803c00f441103011304c82c0c0d120294000741c14a420035540351075181c80c110030900d134442d0400348403076218280b1079440901c11080c402030900c071120b410169622011440360b4440c07110069560581c2e54100102030700102c1140101e101115160070003160341602c800d1080c41240c10034071401561141c1d8500070441001142d100c0c90242c00b81c0b0f40b80c098040302034a0300411030350348184042428105880b841c0c0c003400035020300d43c0c010412541043c8007000140800b6000074828 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 268538929 1250 268537679 268537681
    0x90601060c0204180f1b0506040306020f1e09031c0804120e030d0c11060715020a0c060911030c12070504091106040b0a030f02160809190b09190501080711120d021809 73
    0x1900c8c0e1504460407298480c0c0e0059640035115040c3c8068058011101c0081228502030325550010b50090038a0400031400d490b03035020098403440e0518040c02424020480000c0000c02103800200d00e02d4618490341072040484480c000002d003480030054800020488184040040c84042c200c05082c1a4095440300c0c9000695250b03155034000d240b2242d9102500011803860080c801c01824180700c0d4009400c0c03001250618140e40c0402c41500014040d1042d00768050052030314407001408003440002900c140d600341800e10020785084141a01d07084070109005510741c0701c0c000100014038212035040d40382c45040b40c008040d20100d0500c4c036040c2d4014044161a0070b6100d888260840c1e01c980e50990342c081000c0401c618002c9100c0030312211403040300004104624100a10b0455802c5914942a280c00124001844c18900500b80000c04540000d52041d008144203000d10000c81d04645c0b550348807036071007200c550001603814042034020946c0e601210000501540c01942200c208444d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 268540179 1250 268538929 268538939
    0xf11130503070e04140c151b0105061509060903030c0a0219060f03020a120606050322080304080c0a0f0c050f042d02040905040501051e090601060c0204180f1b 70
    0x110f240041e00c090945245c050409401e95010080d640038035101800e00c110000f56010760140d250050b9071050000c41d06d810b0080c00e105010710136203205090003130440ea0312840b5881d1007061600000c04894000104001e409132a41c0c041002d050081562401007220002038030600022041c1c0c0742c642150220540342c1840750b5034215018030050303040740c50010b071160050b4a0440d03002a140c900341c40514038094021810b241e00034000d5100f402c080c005403a2040c03105080884400c100100a03194000900200f00054003c100501c1c0b9690141b00700c4840101644034014115080745044603030350301080041006080880090a122a04a5040004407841038913aa001c400046607061084400007020451030407a5043c1c50190041100402c001c0c5444d2409074021f0801f030310649401c1103011500d0321030510540300103204110100151145134640a4181c4a10b02005000c990007034071108000216503090b072941c29814040c010170b09100e203007418590060500c0000c0d440c900080c1c0c1105000c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 268541429 1250 268540179 268540199
    0xa18050d030c0915020601061b051b2101050703050105010302090f09180a030201290a060302160f11100513030206090339010201020403030e130f1113050307 69
    0x3005041818080788401c03014000700c55507801c0340c010140502940c0d01c001602940000d005060390b419488014003000401414489582090b00041555102c0c107118054283d903410340c0921640064920600c481c1103d80ca0840748200906c07601c802d030b6480080140050f4175000d03450040c01c0a003000c614007905000480c04420301039030303264061240c5002041c007400d20414180c203034a00803820303108201064540240a0808041c0108a100001e200300b031500040791042071003040014400310030300c0e1510a0542c040d401441c031046c014155007a010011980003050b1403000c910500300036882036600750800c030b4ac12034180c0011041107000e018a41038083c0c4078008074256501181c20035200c085d940d0000c1d16092850b8117944000780000804201312000001d010310388808e07005204424003100c0012402c0380520b03c005030024611000000b10390800720081e540d144560000400c0100794000d400e0162100260700d6040800001994050340402c1c035608409480c0c2240984603040c64400046 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 268542679 1250 268541429 268541443
    0x80f0f0d0813080a0905060309030403170c06041212020712021009081b010e030703020607170403141b06070801180b06030f0c04080a0506060909150406020c190b0a1805 74
    0x3c010000000d034808185014082c001d0040c18010103940d902d00d0300c10760035600d03900640b00481c0c2b0031005460f14843c00d810b9005454130070401c68014405540d80d40c9a016a5061200903001881140c61409602030a00d00003041c01500030342c03008030780c14201500240b812102041408041d8504003182d000104501b044960208000380d0403000000c0c42400180140380401401c107041c0f00018509041580100c5c0c1c152107000b403a00d46144041001d866210002030407100100000c506051014024403080081e000c00c10159194810000304039207150300e00743c0180c880d240410300c1c000040044503020030b0400755a0340c480e80b0910010541d0b80c04202140009049126405050000512500c0da550700355401041c104089400b0503640f400d040c0d48604080da40c45000b0101c7c04006140101c00103048007003880035610183c055551511040c0094000904465490045000c604211212002d248500742d0080c00c540302142841d80304001210401d40030400fa048406d05440c0c049103010030a0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 268543929 1250 268542679 268542683
    0x90b0a18030e03070513060e060102060919080f0a09080705030a0c030b04030e0a0b071101031a121f0b240d090614010e070801080c0a030201030213080f0f0d0813 71
    0x10100c465402c00000e0501c802600025080303002100440c1000300300b90824404c4a880305003030038064030f461004a03120101111014126841249806003171241101000e910900a1400500b4000c0c110100101a441480710000040b1000000c1c07000080600884000f0602180202400000d0f6610f010700e1710458440503024059000c00a014140240348115408100405014440351510001112600000382c26640c45407000490206e5500900c1803031582c0c0b00350b200c0c00001825113003c01040c55600030021546000e00c1d107000c0350019402010700e0080280003c04603000c10440140000c288207021004030300d00502d000412a00c4078042140c1c0300e546000340c041074006550400c18050308092114058024158000292213110040c20030301400f801e03a1041c01036681c40c1400d80d618184000301650088030024200700640c020f50050213180d01c40030582141d290349803503050511800c1e01c0704c82c06682007092187d0b2803031428401940080703801d042c8440c030350525010540b1010945900 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 268545179 1250 268543929 268543937
    0x609050114032a0304030f03060311060c1c0f021002040f17030c060c090111070807090b04091e0308010e010b0301060c02010516210503090c0d03090e0109090b0a1803 73
    0x20504803400852040060b50f52040420001030307030f40f103058040f5402100d05500040c0c44940400c4040e00c20b004120883e5000703180b01c8204410181044110341c000302c400e154a1040c1803039803400501040d500480c103019505c589a80006186001e4141898000d040030b005104110500c110403541503580b0a44103980c1c20050002584000140f46d0311580b81401d0301441410100a148a00c600040820800c01ea960004410040c611940d68640d1801040e41507000f14005000d0000c09502802900c0c400400101c1c401c0d4080d2079100c4106021035060a8000f80c00f08500149070b081500a40101080e5120001c1989002c120003c50b0106000e0f043c10060086890400d43e84200e0581d24140000c042d09801c4000398a8a106100018560b5120682d07012a1440060f8080c00c03d0300c0c82485107030007801d0a800050308108803544411012824884801004602c002449406601810401e40c000803d5401c6050040d5075140013400c0c43c030701908007202120340c45250780c19050448c0c0d06081c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 268546429 1250 268545179 268545181
    0x50102070915141503040507060908010b0117061903080306041503050c060901090b030f01061103070f080310030507060305060f0933040207050a020a0503012315090718060905011403 80
    0x500008400d0b1303806002e40720080240320a000c030208420044442d95141c007800380340ea4840130341c00e82d01d60061450100795200e040c100e001c14882c00c2103070b024100504a40c1040414246100e034581945c0090786e90300740c00310030841942458810342401f50302144904580f2481c5941c2d003030751200034036045c60140d080403c44442c42d9001d2a02400549580306d01207407071345411008020f507020244660000902410030450602102004807003202d90008002c15a4210588524800c1d41c00600126155030030700310004086402409580d002c1c10140e600032909040510030006a80381103600c0c2c600c00c2a0f01014082c9100501c02c01c2000039604400784100c02601050b56020681a00181c5400c02e000080e09020884080745884001e88211102c0076816296000d05088907100140301500da00c01202d01015003101080d86680b107903400215601c0c101100010805128096a000700031402c00700306005480c4510725060302408151030031a0b42c1c0351412000070022a0b29400003221044008 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 268547679 1250 268546429 268546469
    0x9020114030103260c120f0d060b070b06031902010e0d02100f08360c0a1706060d20011808210415030b04090b0a06050102070915 57
    0x603034403100ea8841603107a6a481c18040e0607054100c12065180200c0c00c0b070703000c00d014150f084e2610781800b030006103010605040d900110b94444c500d0580c2c1410705100001d610300181c0501d001034582c4078001500c8121606c0c02d225000c1004c1d0a0610a0b08407030928010f4208034841d55409a4091800d841c0504032000491003841c41480044e401640483d846039010b0703005038141c92203042c2c0d40d03604407495448054840c0503003000740c0781841d0204021030081c0c80300c0800e000c0c01d0b000a140b0099800d03500e842000501c00c00c0303071640015400b60540560007401c80c0c0a01515500004c107540343d440c0d165082c0c1d08e50110301c4c00c20340300c00000d80d21000080c500d644110158036a80003060414907a0795150352100e03507608001445100d0035080040c106070700f45820000d440c101d64800046509030312140c0816806020506c0096410030340d0b40303604002003014000614000d050307001c40082d20301d0802c2d000908180c0c1a400c0140e101e818050781000221445601c241214280794404500d0b4803e0303 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 268548929 1250 268547679 268547687
    0x10c0809120615180c0a021e06011404020307020a080d1103090102120709150f140d0c030507050f070b071709010b0301050f010e0412020c0a0914060d08030a090201 72
    0x1403941940c2200044080803210807001990500681440300703040303e03c140340c00c2000050003210340b00907110078000c1c000c84e100700203c102802c072200c3c0c140140d80944401c11701e0200943c071109925044c1d507025000402075590b00d18174640c0d94a8064030154a10b00d0082c0010750348030101d10005203075100c0042c0384600c21026074072540800d1240c0c0e014a55905102d102c00f800b03500b14809103200200460301043c10940201c1040c03003140c09400403903982803980103041d00c1043e2a250b4a1041c001080034640d0489149001000c800d0342e82c29001414141211009080340c00040501e81805402c110042c2495501000d64142582c00700200e0141d40d603050040340c2d0403401c2d0b00c41c504040024824005038071810b4228210030182500204019580c611110524040031b210ba44d04a01c800720204d400300d401482d000e01d6a500b01c0c01143c0500501101242000319580d1110742595aa12202c0460700080d2281a03048042210300050704402c989510b40c261001800041c14680d554200c0411a409 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 268550179 1250 268548929 268548937
    0x3030815041506030617010b150a0504030b16080901060609030f020f03070605030910110f0c0f030f0409050a0c05040605031306020313020102100c02033108010204051518010c08 78
    0x2400301c0d002d90075a481d040a400340500e0300800c0040c01c0380e08440c6148800c1441400c29110000f0300d0041d0082c008014138589511980082081100800011000c03840c01c240300c2c2c1c084c5640c03100704407280011600040c07298001800441290b418020304114165014007403100390f9030070101c8491a03006038400a0341c00c84100341c449416000f0140700040f650341220180d48554007240a032000355044100c2503084643d003003180441c83c0003c0c002c0129003001c9201900d000c541c1c04040b500419900410300e03103581c20203145c14408a80c00141880b142c1100d02403181c2103582e8002c10f004031a00100d002d01503003c1c82c010300040000200000d003440c001c0d0580e41861076044031046680303051004103408900114401079015100d5005071001c0c0251034800c000c108400c2c1e602960821070300c08840b9405001c1c0544400860070391002550901d001c0108400003400700b100016629441c0206101c944804001c0c600c0f900541071041e81c0101d6440e0b140048900000d00c3c2410f003002e0750b49004111402 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 268551429 1250 268550179 268550201
    0x180603050d08011505030603030a0e030309040f0e010c0c0c061103040905070237110102030d02180102070b0a121d16030303050112050c120319080412090303081504 72
    0x80764040300c00301103400071540c5050f1061000c1c40c040010420400391883d1109480c656003550040100000b4688606410b03e00c0c1c41005095a242c40041c500160944a96031200211559102c0500c14509400d1052000c5000f546c105989545040d482d1200c10f907070366106100034040c002c040352501140038011034014000c0c100c0c08120358149940001d40c0e42d07202c16070100e483e0000542110340c0340290a2085a80c694540c420409044940d032010050a8407041c611305601c801c2c4903922081c01c190004d0104900d040100002c80b0b00008002898280540d11211000c0720400020030810362110a22b078000c24521030214828083c400300403400d54440c00130040310700480448000e1a001c1c0e42d064403c13a40666801e10503a41c079818141e0b5014442c1c50000c00e1a0302050308a00c1d2030174a01e0b0310b1507e542d9603005580c01c1c1201c0285041c2840e4841010500181d01c4500f000100b1010b2459004030001e1403601064050659130701800018014107a038840c10308040c4c110b40190344075001006604 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 268552679 1250 268551429 268551433
    0x10509030d020705100806220f1a0301110307171e010b070303050603060105030a0609110a0b120f0f01031e120302090f040e0a02130902060304030e0f030d02060118060305 75
    0x305101c08000e46511039405494490034903440000440c51007a80c1440c01071500900080902d40c0009141c22202003462506503030365225540c0c2e002038440c510131000a0880800c881e2440c4001d00c0c105800c6400030305e408542d8940601c18040b603c3d03030201e5541d031030200c00c500c0d0301840e42b20b904030449850304a200c041c800b080c401c170001c00c10380c0c0c0030745c060f18015100340c03800c3c0520b03150391040540b510130074011203401d94080003111010a065400c0030440e40d001b12125002c1c140d48201050030b000c15a000400100d40006050506a100003091742d44581043c109080d141071255560a4580040c0700141c114640309001c0350304d5440c00e41035003000950051001d101e8001030780c00980030313412070300a50b8841d5916a00c840b90380d0501d4018048040400386c0038101c000d407203500300200d101c0455040c01341c0981d40c0c400e400c016280c1d030000311b009a01a88440d000343d09020200b000c80c02008491074002d802545c2c9005440e500011400d0540b60508075006510060400800003003021784d002070098 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 268553929 1250 268552679 268552693
    0x909020a020628050c0a0210110f0f1e12011208030406020c011b020706020f0a0503030403030216050a0305030402040501090218010503060d05070f050a080703030906200109051506030a1e0201050903 87
    0xb00c041c590041240721096000d13202300c6130601869200321200200c141102680420446444a844100400c40101c04c44e05036403c10b082034000c010360510100c0210040ea40c00143d103080301070308080a070700410b641d0380c0b88003643d1055510b18641307000180004201039008250780480c00300079040058210003103d040712410301000300003552038200d8491030b00940034900c114a01000d011507078000c21074203c0015803464850b503408038003d40c0030800d0311024008607251600020000c2c0113800b003803400399407065100d090600403c000c07500180d0154400701d104208410032070402481903240d0000900b0034680b0f80d03407070001051581d00358400080241c0590302000c110b03403489800000980c2c2003994516001901d40720b0060340d5000500026010614895007000203d00c200d0109002c98206892800c0444e80d80e05210700307407807e40c481250a07420225064940c1c030203090380c1e6603125504800810340000c03641c4442202020f800792b10b580c1c0e5500c105500055900a0f1f04860b80400090100c07011 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 268555179 1250 268553929 268553941
    0xb0d110d090f0b2a0c0f03041502070b070210120b0a0f0f05040507050d050603070b0c060f0601050a09030201120e06010b0a11030a170601090906060905010909020a02062805 76
    0x103502a0361401c40d000c2034a43d01141c803c02d0030300000c40390b451320700e504490000c908800729402c1c0d801800c1c50700460f1042c001100c0c0300d050280050001030500e030041e91280d4120403c007900700400e9401c102d0790200c01344000c0700560380c0d688038001845c4840c10400c0c00c0c4a0112118400307800c80c1a0519008010032000040350454070183d441214000e07a0850041030b200d40c00c10007900d409030b58680011f141402030111500c610b41c4400d4002ca0010200d4a05503a0303003090008940000e040d038811034001d0801c0183c4940b010041036841130f42464124646010840013602d14203442c007000e41000402022296220040c1d4000234848001b00200d4600d982d43d407440e0308441e4400d40c814000242090007806043d0300c00026140300e40c83c251102c408007484d5850b42050b140d0010051030400440d02400200d0b2101c0e803042c4809091241e44001683d400c7c0030014280f11040d07030080401c0343c410403e0305103090b40411880d400c0070480e02d49101124a99001078940d10361080710403201e0b8900001d00032 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 268556429 1250 268555179 268555193
    0x3090607020a03081314061611120712030e1912020c01020304060f020102070206040b07050d050304080a030507030f0608060105311503080d060603060801020a0206011806080105040f14070b0d110d09 87
    0x100701040c0303a41c1c0327206007000500d0040d1183c016406401e032450003403001000090701955461a059803520700026031028000907507241c500b80455585104110980720414004030140610490764140000c041d01452034000179a86d10851080404001c040110b00308214401e404039101660001d08240d15591246184001c075884000226002d101d81592a10b0060162041c0c0e0300c181c6c1c1010040d0b00380b925489059000e0f00c1d0082c070003020140c1d22040013001c0c40c02803041e10040c0015100405840d03043c44140a1162100c3d01448481c1c60340e0b1010380c0030b407400c84500659400100300003107401d0140d070080c0a9000050b8200600d00c44002c620b210a10b1042d61100d8200d0b00c0585e82405810b41d44c50a8508070701c40c2e03134181c0c40160070500062084070030700040704d0141400400001081943ca42c125400c54605803400c40340003e050b5400d2090040e040781e452240c041050291070743d03a01d042071840031441644608600140c41e100d407403810789940816a02181d0b1011401d015840091421030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 268557679 1250 268556429 268556461
    0x15090f030f0d110a050a0321050a06030203011a0603060d020a0e010b0903010f021801082221110718061a031b160212012003090607020a0308131406 65
    0x20000303e21010180c1d202c20001501e82220741c1040c0548846d5200343c40c1280c108446403000b41e0440e6580c107415980d880f0921036103100781003120000a0460651040500f510040d42d8006803a9094101444c419503a6000b201d41061046802c0b2740c29111a05c0480d00c58032040c7d01408000440c04000101e02941c00300030f080c010400c0780200a005200100c0c50202d00407180148404c0f040d0611030313122540141269900181c15144000d83c00c072035080e0403444d00e003509900f290151480714101030100b14410300240004014200f0200c14244646869a102e00e548509800190790080d04500c000443d070103030740a0301e0b01c021180810030385c00d40464550791043d41c0703ca101410f001c1c501038405501c10309035000c083d00205400c5100f2504c1e020840100d5081040a519550310f0306440980340603030318015a040460035000f6203a240c03002d00a03040010040800055401020708000026888030b03a15500c50314280403000690403e0406c002144003181102e407240c0b14a03418090500020f8400c4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 268558929 1250 268557679 268557703
    0x5040b0a08190c0501020a0b040803090c040606020d0905060301081203040f050a030309021305040b0601030c050d091b1a040e18010c18080c240d05040803180c15090f030f 75
    0x102072980e4131001240e64950400d8060b010001060105000514078001075400078084c81c00c80300303280c1c1030380001804c90740143e000c040583e000c0d4607000069a042007445d002020200d40c80390456141605007a2150404082080b441c000000003034100032120305a1034420380c004085800d4000300c0d1801030300801c1345801c243d01c240c1840c2421201c154290052074841e80d800f219200c0c05450b14001500601640607002040c84401e00090049491620401c0805170160390008a81100360a840d500d040703841d00541d40d0340141d100280c01514804040350103d41d6422808089c0e42c0d1050b840c50315400901940348415403c150181180940c00007a62443c0618101d0584189940b895601d030740e082071204a540009400e164a800600144c0c05110030048014007146010702510070942100c1c02104c0448450402205004842c48040e208248418980b00144864145800010800d880b2203401040030795000801c25040d0710354210b80c00007000302804440804141c40b0145440e40c0703000c400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 268560179 1250 268558929 268558943
    0x1f14010306140d0210021509010506090108070e06060f090603090a12020a0203120304032615060403030c15020409060e0a0b0f10030c02071502250f05040b0a0819 71
    0x1c16020b40c1c01d544004036039001002e024110b4015070902030b810421581d51419801400c2004040d50b0a2001e17440c4500301140001032503140a50420915000c180c00460301c40e0b101d00010b12045601c1d540c0b90740c00c413404443e075503100c800d482080c030a01d100f96415580c0000d800700500c40c0340300d4000740004081d48181d03180d01d160644c100c812039440c104064003a505070321540000b003482d2848801550414020310b40706004040082c0c0c80d0204003a0035440d5038040700d41d0010050260f0059650421065007107600030701d05455624010700031100a01d0203055202144c0720309401803040d0703046500800a01405120381c540d2000742504085003102c0100000e811b01c003c48615281564680c00c00380c000400040103042041d400310020841d500fa130009522070140c0208258017080d501c44036818031035004080814010345051985500c810134080701140b0000700b0f202d44413400403271000340c074030640700040c08c140f8000000741c0c000349c20380c0182032078000c05a84981d0405045546d840203801000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 268561429 1250 268560179 268560191
    0x108240a090209011706060d0504060908070f0308091c03020a110609010603110a061407051005010308090102010f060608060609030a171315050d0203092d1615081f140103 75
    0x142005880c00721543c83d48208204025440c4074234075444160070a0090340002105151641c038410550b202c407030300303940c0d0030f404624030010150720401d001d6001c00040050003c680514a5220780381e02c81c07040d29000e040e00410061282c42c070850304d607a01e00355584c00310703106401c109072068002d000c240410356820505c0032050f50b441c20042c007490f04443d01e41c2c0d41c6182108841007882c5107908100022101405580c10f40c41c4900716501486020f580a5010710f40ea17510100e0000e800c40b05100540950981010010000300d81c0010f0917590104080e01c2c41c0e55507110407000a420030002200051280040e8100d2080030440040941032030344400c920302140a03155003154030172075034140401c40050340800580007031141c250003a58000e90890112100309420781c00a04100d01d00b407200c16070601c90600503000404041020030806041e500407013030701c0d41c00d0146289000c011121200c05000e010800714046100000c01d400f1202d0340f90b603500c000d10b1323100c800da161181524040c07503000070304010f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 268562679 1250 268561429 268561457
    0x203070e15060f1615090602032d060f01020a06021902011d0615060f0a08071b03170705040f060c060c030b1305040c05181e04020108240a09020901 65
    0x18080b0742e044402c008009080240c1181c00e003640501104c8101c4110842c6030085800300301c0341c040c0401071840380c1d00242c4c50f8581902c4194010350071a01001c04101c003441100b900c42490303180d607034001106075403101c81b00541100503498051600c1005048902c00514008261f051782901e214a0382c2e594004e102125815405c0b18401d10001c2c14290317240c0001001c03650301c91442610000d0014090901c0781080e04c400401c031303215084400000041080f03c020081c0c9554440342e01c1c030810f941c0500700680a0706548009000320390401d1001c28a0365100c1c0452540c80c01a07040d1b40041c1444458040816110314004100e50300e211403c8a20740e00b0b00d0f412603145030103030260307800889001d030188141e911465803a001518000e032054844036422035020541e5240c41c89002841d960714802c00d0250301f06034448440354500e103900d040b04469410705010050303030721001880c2c11039400801074000c2c41070b04104003450551414641c0e8441c0101c01c0024a140382030f00640b441e424262100e11403000c0d1a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 268563929 1250 268562679 268562689
    0x1500d0519020705190201120e011d0105010b0927070f03140f060d03030f020307090f08030405100807110601030f1b03050c150904020309060f1807030f0503070203070e15 75
    0x150041c00c90708045d81038205000c5039001c64461038014581121441d1000c060b100459089800840b100d0f5124072600c000c85080310356601c0c0f5260801c2c02003142c3d40c50f1904410b0907010b40e06505204180f40307030714a40c80b86040031041606065881600c0ca25003020784002e00003071042c0313200301c000c00d0801c0d201d41008078041d110715200e4240783e041d044d5603564401c104030507600000b03002c07418160f548881800300d0380c0c44d1014610a5000c0d03250141d0392410305984401450281d402240290703c20841440aa141c9240d2405409540d091800558859207815194108003030306011051003420000030a1020700204404070500602e0104c60604000100c20700b48004ca0101421030350000950310518107100d212004c940400c0003503282001a54000203051360b105450508060384040140415106021409070f00b0101c040007182d450801880c4041d2280c51a00c8041d02c00c10524030301e5000d01c00b090046404140d801019200819220314150b2001d90341901e00884090721011000c80e0b500701 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 268565179 1250 268563929 268563937
    0x120309240d0c1e0c0305030402010302070605010807140303040b0a050f1903020712022d1009050a031403041707060204170d0207060903020307090c031e05040201500d051902 76
    0x3c240d031111060304040c3c40640e55540007078400ca0406900f00440404281e0340d10505018103043c0028207505890321511244000070404990707c6500204010000300c0340f03c0044031048225400d01d0780c1c40d80741c440700f401d40a004803c044686640f46045440040e5131550082103100d22500c403c1c01101c5d0414000c07a510040490a003850070b101003400400611a58440240c80901004980741030f00c554024005030b400c43c0c44206c2c0c01390321064001081540040118070003000083c40c881c214902a126440300c0d202d030032810801400005030700d0044c0480354040f02c01030880030f003800000310840c00c0d1072039031000015030400060042c0c03407001ca050b0b40306101c5601100d800400030107003070b0305051110004200700071140d01415503e4091841c002d5010058415441d141007000425203054000900342d0503032007481d180c882c43d02030600b40345943c5001d1884212a07202458080c4000031001c14100001c45110b26410b000d4041a6655480400e406c414490442100310310501c1640030f17401410b81c01 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 268566429 1250 268565179 268565237
    0x1020d210b19050a141311210f0106030209030a06090302120a0509030606010e0d030e030c0306040f120216030b041a090d090e1012030905040609050108010b120309240d0c 75
    0x30300001c402c4105c1d8586e04100c040c15901860585070082114000449420011080424001141c200110030002c0009c841c0100f0140c1801e51a008a40d00000c0d04d03000500b00042c0126aa201040309040c0300f0489140e403400c08020f2350355611080c1e20040c18542050005074030138800e1a001400355441404502e8086502505034600e6400541d025a424108610303074582520400c500024140d50811440380030318011111008020b259050400d1100b040c0c03080c0400b5544160750551400c1608040700701220740040b82020b444d1a00d1074444200041050340000c2280c0c18820301c901c014001c510030300c1c121500d4030b4185065a41d03900181605400310354000007228125800c10040e8a44100c3c504024800e24000310401d485400184c21140284c102024184c0e4a0700148051502482464041d2200711a602c0c00e941104403101c0d50f0f8820720807a0390203006d400c5a841c01883e8100310307080d0320b210507200050b1039200f0210306d030000300301c0d4404040000c2c0140c41040c4203181c1d031251003070b8039007 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 268567679 1250 268566429 268566439
    0x1d160905030606361e0412080408090301050a020d0e0c0d0206130b12061206060307210501110307030b120601050607140a0c080c01020d210b19050a14 66
    0xa0380f508200070041c09080001c004251078160b008491400b0f0004040d103d250b882070b440501d0900100d00b42080709003140c0180c0c41c400074001c2c40040b491810001000d00740314503013003081e1360703440c13501f03440d240581464180c0560806e018800c1058a0703070003800d0940c050500402caa03540d4211441d80d140703640881c00d2f81200060410304058181000204103074109444042d40c000e0b41c90540003003c0e84000780e42c010f12442c40d02402103501d000140b402c00c1c0d603400c900400e4503081800029446002e1841601e80c0d01c401e110840035144400240400d0564200000b0082c61941c0010301c959075008560400000e46010022081d501d40140026254002c000081c20a60f09000500125901131101038940c84040c914100304070b5020040744846a102e00201c1e00c003940380000080ca08a02c00000d5410754210042c3c15252981c03000d00310701a21107072000110b000c49118082da0081c425011103a400000050b000050b00b00f0f049e0310381c2c08598003901e44000c015030300c03040342c004400380d24052a805 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 268568929 1250 268567679 268567681
    0xd21030c09050604170102040f030303090218060108060925051209070b04031410061e05012a1b0303021e0a0c12060605060d0b0306060f0d02090c041d1609050306 71
    0xf6071702140407541180100c000602c1e10780c072101c1c0e0400c211a07591040740000d03115400c881c21414000312402d0741d440c2c2000118014204000041c005000050110f03000d102014000782c3c1a00c3e16181402c080700c00851110104413101d0030040055014001400a41c40c0c0200030074203040e0300007403201c00c0b2050036507107505090550b0f803501c4a00030190303981c01c41030ac183c0815864a4140b4410040101140c3d52a540380710704140c00e82c28815070300d40c059414440407441c0e000540011a104665401600d041482030103a41d117006420400c2c0c5211040d9000c43d281404010950001a80e880f80c3c6806541c444c81200c0083c0340d6640ca61035000020aa103d419808004440b00e002c500c8420b07520803500400c100c7e813950040342040e004180007200e01a01c800c042c4442d81403e004003600403000f522500604d0b80f52002180c0003625201c2e00034003500064000960305045801030b1130140840c1c88502c0e03010080e000791a42d80402c16110303600e02020b004120603500c5c1c0210070310300413240050098809 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 268570179 1250 268568929 268568939
    0x6060d0b04031101020414040c02150a150305010f020c070e16030b0303071505060a0506090306040f030519020c0a170601090c0c0206120703060b0703020307060207020d21030c09050604 81
    0x112002074411002c2c03049040c6101007540007800070700090a00c041c20400034589210402c4240c4198841c81c60554002000000e4800e42010009603c11020074001c03a8401462804496200159001905039443c15031001c0c41300d00750345c0081c000d01e4904400c56004584507150040140000d50352103007020251210900d8080c082c0e0840d8a00f90001801e03281080c10f15250614010440603254083c943c1c0c030300c10041e4130300d000c42081000e400240c8100d0b0401e20030034040b81e55584090000b40003520f00c49161001c05104104407009181119420141410040030281d40c0f1001d2000c05031041424501c04108a50258621080c00c5809402401e0507464429548020200984410104800e1240302c4c405616074600030540b281014174450400d240c0098000c04503400741d08200c0301da072010014107001c254008107645c3c1c1350b03410030703001030f036542d0184000361101e5800c1e00c00500d959030403402100810300301c0e105a45a0b4000da00d06000032566400708450643e182d01485a1180c2c0a00084c04 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 268571429 1250 268570179 268570193
    0x10815060108070c08031e07020c030318040b0d05010b040f0c0509120c04020a05130f0303021203060f04050a0e150108070b0d061e081204030206040b16060204060f030e06060d 77
    0x1400c483d40d41440c4107610010748a0803002d07481150900d520090180100003162050583d0315440780c890300c042d00300c01c00300200203503d030310454103400d642500c100311001d210b035a140c0c040c1c03250520007170030400f0b0160a4a0300d58041e00f05103151500c51490b00e25404035108842c050b5084444a541d1824605180c0d0001c100402c03202451b81e40c02445910500380360303038485100a1035103894a4551039161101ca56440080403541c0e08000000030190004100194000644101c940301c2e90790503e40341d54850000c54280c804e2a00600d174401d05110910a02548580c0103c004031401802d540804201c40daa0510300d160030301ca07a813070070740c0500001c008090345035028100e407510404012881603514000c80c3c0c034051290640c2104051280410070000c41c08114085510040005260402d03145d500002c0d0103001d103126a5600500c00912007101c0c519050303030012031540c4204115283c0d510b514005041401414100e40400d181c01002c101c044400078220307105040041c00b9600d888460f6440003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 268572679 1250 268571429 268571431
    0xd140f21040e0c092709031228050a0e120a0f1103090d1103010b010810061d0307080c190b040b0c0c03070b1c02030f0703020715050702060403030516020607110709020f040e010815060108 82
    0x81042275071441c9001450400e40540c2c6c0c045c80d2441d0003c10b503849950301d040d01704240c207900079a030303c0410400c48030855009020010800c032107003080b4080c2c22a44071480c2c210f1185400581d840340d540c20a550401510003c542c00d441c4060340200b000601040054882403800d0f110b100c01c00c5030444040140038440c8410200b03000000303031000c00040400f0003007850b105403500104000e030071540e002510f500f0700c07004e069404060507a0150011b03141210390341040c41140103100f02000c000034107001d000020881650b0700e50014040300c04880d41c5099901c495004a0302c03007140c1e040b2450081103803038624001e0300d0180800700400b5071603442c1e1081c290029800320b141100d103e14501955050103103617208080c4181c4168000d014280b600e440c0c000c0071240001d02a030485443e4242140001d50300190031540401203040c09071402d5500503070a840c0080b15401000310391b0000a01886a03410500988203c83c148180c0341116601c408076151212001c4000900c56410440050307110341c45404c0c81 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 268573929 1250 268572679 268572721
    0x4150902030a0603080f090f01020a0f061a060705070f080c0307050607020114030703050a0c0815150409020f04030507080f0d0e0d140f21040e0c0927090312 69
    0xd50180d44c1c2c0d44114450300070201c088028440441c400742c042c00c1c9282d148070b003440240b002d440550b082d59508000580c40440c0504125500c820603000c4600d1001c5c2c09581c0d1400030029502c40607941ba10703aa541c065406900070b403d00c0c180001590500000e04248a000024041e050304d905100600a098000c1081a8108040c442514001248800c0218040c0c0030b10f940200f90743c6800c844400c20b0304c1c1d183c1da050007005091010082e001100030041c10071b112003200c6500b1180d591495500150103150030a1102d14400204c08043c009420000c1c01140e11900a60342840e03929040280ca034078012403245d8054000080b2564598852440c6500c05032000344a40000071043c1ca45d480036200004011a00d5440302c2c00182c0d0000080220400e0b09a080003407101c0c210712425182c82c03a000d42c2c411030010b0030030b00300032846140040c4c082d41e49501001e0300507400d020b540c50141c85000b00380c0e80111003445c019000310b1620324022084404180461503904556102c000e248070450302e01e4642 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 268575179 1250 268573929 268573931
    0x4110415052b020604060f1b02100f02010e060a060f0f03050715120204060c060f0605010504120203010f0c2106060203030c0d09050618010e0a02031020120106030b04150902030a 78
    0x600b0040c0e8400d40648041c150035619003122000c440c0026294251202c00d03824a25025035072800140e0b10314070500d40650103443e0440103642044d80070f034050505001010b9241c0102030030892020b0042d8082c03000c0712694030100d82e90a540740a8000d207000b6900000c3e12075044a1000e00c0700000c00c3d50400d041001c0c3c1d00d08119002c0304444a141284c005030000000506404c580f0800d01c820307070203610280c0290041c20440c807450080040c1051140f441040d000304800b02501055550a5102e414920903881092064203101400182055045070140008500256004510341182d10642003500d41c02d4005502d5901c400c0100c2901c2e0700103103124411291110b44c0381c0009a4188111801000020b404103410115181100e003924502100b149460340030015141c0542e4000520440a15125100107400c82c0540108100c030307801014510792140000502e02c2428400d011414100c600c180c0c2e042010b501344104000542341c01401c040050800780c1c0301031145501d01d500850b04200750b110 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 268576429 1250 268575179 268575259
    0x60e0a0806040302011d0c10210f060e0708070c08070c080d020606210709050a092001020c090103020d0b1f0810240e09150411041505 59
    0x904907103400d41c2210300b100140d440b05040700e450816001c42111000300600a000003102e21408112000d1b01119001c007000908900315103030200d51640b204a8000d00c1c1414042485105020340c0034050034400c13003499404050004e00303103038440c03115140a0942651881544240c41c2c07a4149103800160043e6045803045900003040642048a040f1081840d000b034069071409000700040102d080580c401031400c2d413681081e0020340070601c0c1d001d07a00004000685900c2e0040640f0040c420210018485846800d0b0071a09000d41205003441361001d03821181020007101c2401209007003880000d400c41d0380100c0c03590028201000d03a9501c25402c03a0070068100c2506002584600c15a01c03900894000c1b019400f9050700c240031f52a400041e080400e031740c1a01034200601c082901d4440c890401e04180b0100f4107002080c0254076245001c04014001c0b420a400c06810010340e103401d49100302d1602640c0b8110f00d03200403110013240e000038501144c0d84540c80c80d0600399a8211244400c1c400400 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 268577679 1250 268576429 268576439
    0x40b010f050618010e13090302100c020d0c06060b07050303240d0b072c1206090604080d0b03070902041e0b1c200c070609050d020111030d060b130501140301060e0a 72
    0xc1d0261b802d000102d601040704089401c0203814040c2103041e91804030304100d8000b09950300002c040a085d181c0707103005502c0501500b0440002e2109400c00d0030740950011301d52003404800406107006040e21001743c0101d0482003004a107e00804d0705803031f0450320629410011900c4c0c00c0700c880c0d0008560900c0f40c15203030107050484800800408980f004940c2500050213810014030050b05008103000901a50400040613544c5540080004003051000211b10111005640040c0b811403006002c5076251070704d0303d0038100030303402c2030140d40100411510280e4460782c040400b00100c80140700498034000400f001115000000358221850945818240e0f80c0503080e5502c901192803020300050301c90388111138407030801c001507010f1820026406814840c5665948940c144c884d0309080c60480c01c112945d000c0c0c2140140d80b4605206c0345002e1000a540d015007004040060841784406400c03902c580054541030685030b40d4418070442400180240c9004249001e0303402c0e03004040b50a110740c0c0d1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 268578929 1250 268577679 268577689
    0x7060216150e1f030c0e01020a0c030227070302032d06240304060b0117070203030f0a06120f0203120f04150201020915090405130201020a0b06010e100305040b010f050618010e 77
    0x2102003d0000303580f00c121480540c0c1c030512440c0445070910180c840b121090f1203080080c106404013074880d283e40c1424925102142e0040d802c5445400c0303649849242c08200a0020740007203d42e8440e0500031112061041c4e092000a140401c51003a80c03a603646486051010040c4a2040c5c113182c103000155506200807184c000c0e510607845200d02141e41d50b51b5800040c007040e15100310074141c0f80c415090214103900401900e501c07800c9405032055035a980311a41d005005183c0c0882c0c860050044800144030141c03c42c480400e0095048802004605c0d07031605945c801c0303040700340c20311703009010600c00d41c0040c2c1410040000148009030802c4000c0d00025079108c6040c0c0b0070b6007500e01c0068288424201405161351105c4580d0456580001580010b5141d0262120051803134480600052007603008241d18065080040c01d5071000500c0390101600030300c0140c5054980000328000080d29010000c1c240342580d40140502c0e0518001c2103c1c0b51181c00700b8900c0505001c440c22400c0b000b6120 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 268580179 1250 268578929 268578979
    0xc25020112020705070906050301150905071e18080c03030708160b07090f0807051008091c03020d0612050a0f050109021302071515060f02030903070807060216150e 72
    0x1380d400740c0070307941c9015000707030440e056036224a010ba414102c4030180410000441c0d0102c03103070001c1c0441e8030758a000c0c0c1203034a042c0c4016020400d0f034015410b0202513601440c1d010f011080c811030001501d813a20102ca0781c40e41c809241c1079040d882081080002500c05002d00032001030480070b41c406403030701d030f998000c4080c2c110f8440340001c10040003003180c9011944440c00605010000d40f0b072150411010820120102000c01d007030010a902084ca8007508201c2c0320459040d07108548507008032404001c0182d4805e8112880345070601501140350110320710b041001c1917001d4000e043c1d050b565a1101402050007006990b59581c3e0101100540c640055161041c0f521400040e030383d80d007034a4900a0700c2006031000d0f20140c034240c04130381c104450348012003d9800b9800c2030390002c001008120718600c80d00407540d4140c01415400600c042000420105807030311602980e0b4244c41d101c03d0340300c201c50588108010300c403281c204034445500550340c0100c56500904852000c0c0b00804925584180d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 268581429 1250 268580179 268580183
    0x90a051c09210302070b0a0203030c030411120c12070b03070c0c08060114090a090201080615041206140705070f17071b080c061c0e010e06040c0303080c250201120207 73
    0x40b00325101010140c3c1485000e000d8007284413124205140e00c4d00095682c0001401d035008644004049402c2c0400d80c110301b2641c08000b40270214500001c003504d515640a02c944500a070780c41456609480408607500b0281c1e00000070721801c594030300000b00ca035203044030419150100d5031a0045503d05041c4140c0f80a0207000c13a130301414100d650244490304070f0040221030040d240c08403040c0140c2c0d1100170150001070480d100c0c030089619560b032850394807440e404900e003461100d014904011094001c0101d01d10b500130180107030380c0d80900940e1035100380700c0c0c001c15100203c1d20303c07400117005030110a0001d80703c03407400d42030040690360400c0303105011540c0c0e84194140380041181d20400c01c28086808801d55205081c00313102c10b9240700e60385114011042247d25400c0b0b124040c0003d41c450111070050904460f0b6a050070704046040f50501e00041c0d000030400b80006d000c520001080f2010454030094507059054018003155604c400070310100d041100a6143c0c6076005107070700186c00014 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 268582679 1250 268581429 268581479
    0x7060e15010510030c02060402010c032a0203121c05130c03150609060503030d0e0124060905031902011b0203011d0106140a0e1504050403050a08090a051c09 69
    0x1d410b00b001c01010f800d9221200003010701700f2424407022076010840581095080c00c1c000012078180c038082d1111055021303400407002c40c64501403003070f84041d25040491070081e0140c5440309819001d40c10725108001030002c000300c1b0a03c0d0780ca001c1c6840d52000d940070303503020a0340840c04110355802100000d03540c4151031840c5e280000c002001d100d4401c4c803000b4510418100080d80c40c1501003034507800344070004e01e43c0558440c3c2840144000303411610003c074404a42107803030b94444041142d00c40c214000c00001941e4038002082d83d080000780d2080e0905842d0f01125058070540c01140c0c1e0096103031a0076940c03e0064940f00050f01c090240180a000b0000c0d00c40c0c558076005166800c5604030340c4000102e6070140c46001490302c80300c05840c10303a076041c026104107644880c642d9140404505031113401c98a0300007000f0501d5070202c0900404034407982c8040075a1160514540e0700c00b4110405011900601c904418001080484030891091030518080035955040c0b101e49113400003903081410307 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 268583929 1250 268582679 268582681
    0xc08120f090f0703020f0103020d02090a0603021c0c14090d15060501030b01051303122102030a0c18050f01140c0a02030d080702100902180403030f1104050f0607060e15 74
    0x803642480b640c44a00e01031001040094070750f40028401825220144d4103059000034003060780c400f2601140c900342c2c40500783d44042d03652064014025485550035442c200e10400002d0440099405480ca035100c407680c445100700041c6040c40e401d580900112548201c43c03000703810014029030b40460321001c00f5540001e02c54602000541984d4849180d60304200307041041550025400880c1002d590300401f42001d0a81002c10546100380d92101b001c15140728401c0541c840040381d002181f14a00c090824018645802010740d0709030300c00042900c00300c0a1070740501160900004524401005140140c1112012009100b262f44000350803000e50f0030111520382941000c1201d000d40c07484900c0e0000e401d00e08440300a46982801000c40c526540300c002800a66440701d030784950744000484402e40c2070400307150240c0280000c0380301000d9135090a0b100f6a411001c0004d5408941025282c91070800d42c5008224865104c0e6108846140e503811580d96498420031184243c0842c9600f00419 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 268585179 1250 268583929 268583941
    0x1305041419090503160c0b0408030d0614010e040c0306120b16170703090804030c1412010c0e09062e1215060c02030f0303131703060609010c08120f 65
    0x36600300d80c1501d80ca6081c0071100c0c00046000003150b8540403103c0010f8100c86843ca46405420510382c042c1100000200d0081038041000c000ac040e03800044030100141e81d80c1d2003281c03021101c03424400c0d010940341c880400503410640c10800305c288080c07800007002611114641030050b002c00040d9446c1c400003081140c080300040c00201540d4070b50401440b00303410312140801d4400008c06100070103884181007410441900c0c15200519803040d40a80034545400042040c0b12180f40c1c0b5901c40e0a1044016503540018407584401070260398038000780f403007004184211018061701c0c25803c180d40e1a0f0340440f404c00c00c8441134000c00603001c280368268503000300400980900c0d03450700c0c01c14a81001491201c10305600c00782201c450382400311b8a05840e00000341000c50040a2035081d0000008109000d28102200c8055600c00d4442488010000b00074200c2c0c1d00084a0141d009a010000800c107513005826079500030740314030002c40c5000308042000203100c00070b8030981710b00d00108040c091 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 268586429 1250 268585179 268585201
    0x807020c060c07030b060a050604030222090f030f140301140f0d111302040e010501030e15040b061908030a030209030a0c0603050708060f0a090b120f033001030813050414 75
    0x604991b088400d4070741c450030040025800e100700d00c80244070b110003258034608400ca4402c0c0c0090a4014201040390107110b0901e5414802440d0080700002d007505103c2c0c00c824060712803645000078450403281540c2c01d01c600701900c000483ca2040d4000b140f40ba26105580e01c4209620025100d04030012140d40c00405022480c0500403059520030f0060005010080e10841681d04468003468041492180c00300c2c400c1c14002d20324145c0004003015020841481000e01445001d40b81c00e40d00782c00104084a1000501441070140000c5600200500d5441c0d6110f42c01410b54a0002015181c00311202da65a04c500007813079102d900400c1d120000c00c601d89401c03400c3c1b1644840151581c26092841d580001ca4400039406030404442c0d4540c0981c0440c0c540c91080e00000f08041c04959000900004480ea2900500c8070040e8183c0d0503c103130942680201d2003020112624030200715140d01b9a075608000350451b52030f05d000030b82c503200e0000700c5596034099030710140e188080000306402c08041681e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 268587679 1250 268586429 268586431
    0x6020607020604050319051c060501080106050f090d03020c031b030d11030a1202090a0806011a09011b030c150c0f02070b09060913020a0f0e1008070807020c060c07030b 74
    0xd096412040800000c64404411600b4940c603ca02002c16418044030a580c0c03405241c403200454104081425424401d42e07000100b555000d0300c426895a99036441110f45129441409003500001d008800729410a001c1c03c0b600c0e0391090044e185e4ae40c43e00b1021030314001014580d44c00d4080185150900d6050900100c0100c2d0300741e2504a040d004811007090342c034070651803100c0c04c00105040d40d4080030104da040e50b002c100002c1271801d606a962a1071680d6940070b01502d04002e4007501d1050500d002003003100c0e0700d654107840345488010364440e00d4840c0854044203800b40700035001101c00058241c0720070307894404c0c030420000d141407004400a1224455802820965102680502c80c4c94082c006698030203a0881b05580e80e011090082040081d0440340c04003142c1c00890306010090b041701c0f9514880180380d5541c0300c0000c1c000200003c4503034911482c0003150440f0081228a0303c074510640d4082042d004841701446801e011807100e034000405460680c0100c01d080c410449100e6400f = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 268588929 1250 268587679 268587691
    0x9030d060b1201150201090c080c151306080a09050709090302190507090216020307030303020913060b1b0f0a0308011701110313050a0503070b01050a1d180c0a08010204060206 77
    0xa030a01c810b0780d000c10425030060081c410002c00805a42c42000c1c03003500140300303456008003219011175540c2000755a80000e0a00f080c85054403885400600546070143c80e803c0380c443c1c0d80c00c071403140750207415910104081e0100c000242c64041c007201060041280742c000b0492020005450490b07820024200702d000400c40d020f50040c01003c2002c942c00242d040c05071410075500507691498410304540900213508000d4149c0151a0700000380b42e010342c0a018041c006440e020800400e08016208440d802e001d0210680014400311048001005e0344000c0c1404000c102c1d0401060410028a0704117801821000a041c5100520080c2400c0341c40000c40400200240b000300242074002c0c9040c0802400c800a64107407049440a02c00d0411248075240e070440141c0355610725506250119217024000c84c0e01072560414001400100200080500510000a40b44544030810b8807044030b0200816400944210301d41c40c01d460b91607281900080400d4000165554a0000080e042070001081 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 268590179 1250 268588929 268588949
    0x30c0608130b04060b130905070807050604031707111305150105040608041101090f09020d0b091501030e010f0204120203010b0d05061902040902030a0905250b0306060f0309030d06 79
    0x4601c0019150034001d54210364040320200305000080b0104820b0343c3c00132100e000041c00e207241d59050000200d0000d0035030740a00291400b09407624240007141c440d03840001d0503582038038100c964030880311000d060010300c40c500320380d0010580c2000130ba070703082c1d42d0b04011141c40c1d4610500c0454803002203403240da10360a08045080030326003007019007072080042011b0b003031080800e00107000d60301c100541000350240410844081d502d0ba48110029004010301c0d000c0070740751203d1a0301c0c41c68800003441c130405c41e505074005115041e20045003c0d15490f040300020303640703030072003d0b81c501d81c20b0015001800b080c05c03060b41c00368184c0c01090300b528014101c460145040030f011401040340030a181c0da001402c0001d040410480e280080000d10965002d510014800700906c96042595040241140c0c000c5048458152180703141414840d00203e040198255861003003091044172809164000e10060459043c0320441000070b01781e40c011280c41c00141c00004102d11031040703500c6580054100014 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 268591429 1250 268590179 268590211
    0x50a0312030c1e1d0402040807080c1e0f0307031202010c030b0402070809060310050901030f1b08060703091407060309120305070c0f05010e0a060618020f09010f090b04030c0608 78
    0x2800400c1d03050302601c410204003c1c0b00c0c04c0b02031000804412440c0c11405042155901d40d100121619603409028046141c000e4002c14201b6107048503039141d01301c40224000c1c080e01c40740802c110703210051901007501030003104400000325804030b190200106054001048080003240000c0c01c0b82c040f410041d114034814811079012030101e40503508500f500f40c90b41992512018540e440000807640410303800004d4200100401c016400841901849040540c071075040e41103400120020601500000b61b00160000d10300500c05d8000c0031005024006645050b00c0d0704040f80d04001c00c0360000c41c0403940f22402e0700100840e180c40c01540040701e150400890910a200070000012500050070b0202088101005d008007948441070700080030b021a2204060b034540007000d000140710703204214099040440f150340680c000c80c7c817507000d00c003030702c52070301c015000152020310401d01180100303d407c2c500813811614900082001e180114004841c04c0e00c0d00d000240705040c024a20780480e48690 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 268592679 1250 268591429 268591457
    0x503090c01180506091201050901020405100c020f060904020c030414030d020a0807030e1813060c0306051503041a01090902030d051206120c101206170a0305090a050a0312030c 77
    0x14075070b2000d4920031602e8907a20041c1400190004030210300c101d2841d482c04c0300741b200d041d00550050048030b02c03d0b9450010451642d000380c41c10814420b000e90822100d02e07000e482454403c00800100100800040c24902ca0044091654000307401002c0ca0814103000343d02c841c5020804504070103213a00c002c0403107085556489a407070258540040a04c800d091680a6a99422000c805560506e0604082c1ca00e400c8100d0085d0802440c2c00340e90142c640001d46013040c0c403900654080d01e1000c0e2025441d0000010310f0704d116032000f0419900091180d00b820302880560079035070300800d1102d10120b1300000310b00426041010038810b442c2401030410026090350062440c480e4420003c42c0d0341c5991b01c0c8442d000317904121080c0009903000b4081040c01041c03d802080c107500e01c1c162034104014294590f02c1040c00805400c0c4000560b9011541c03680000b17214800522000364003030810120159200d000c1a070b075243c55003007111a40c00703001a0210150f81845098184100d034506104544110 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 268593929 1250 268592679 268592717
    0xd0f0509060c0310171002070b04020f0307050d0b1314030403060510050d06021e0d090c050411070209040f05100c030c020d1d1801030605040b010b09032e0603030503090c01 76
    0x140c07003916000024045d019031009000e01c90b6810100d04482c040d0340d01d103414030303200b03a20b81d5007120200d2160101403c080b640c3e040000b506029a440500064107a801d1915a000c0038240140004803140e078403031710f600c001440c40171020780640d200c600450b00c1d01d00f180780c04000d440c0010040c001ca00030f045070402c00d50f41d0702c540711004581c001d000166503042d83c008405004404003500f0302c0b128400540f60444085d20b41c41400100d010354500706070540c071541000151081c012181c00741d00018840c1301c0151a04828054009128044152008007903a641e5030401c1c14171080003003030543d24800f0415850b058000c68515010a05c090072080302c20201c00b80042e90b081d0307000c445100e5003602c041c1054481012460b071500f200d11204510b03695900e4240040d0100312411580c51451000000d02211410141c404044005000d0643d01c20440326075510038440b11140101512412841c03e110201403007068043e5000396212552480c0c049009440d1413614942c0c64100f00d14030300940000850 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 268595179 1250 268593929 268593961
    0x91509030a14030d3308060a021309050a0207030306060c020d060f060e0c0d1103011206020a0309020607030e03060709080a080a140c060603100b030604060b03030d0f0509060c03 78
    0xc00321664500c1c861510700789146004184210900c2e62a02510039502d040c1d02400e0705d0403c0c0125a64201c0f0312aa2642000d0074a20b4403515841d503000d50041030444040d9005412000001d4001d6150550b60350405801e0f15825076180300c2650313000460906040c0d15020300000707845941003128150000380e0203d206d5100700e035405030541b5070303c0e1001d4641110541000c4014010f000614000342418040c02c0c842e548214a0312030558a405000d0400f1030550003924104c03507a100406100f44059250303140607500038040c0c90205070780c0c0d110400043c3d03503500103401e642d03000390340d8405100c2c4c1c84001d041c601800a04090b06005210004100802000a4440140350310404003a260441800e058800b0b0141c0807503000940b0307010905500324100013469502c2520104e00f00c404000302e52043c582180c070f25101d4a5050b4111200140200c0d485810805400c000a000c07a0318102c20701c1c094504541c0c0088400b48426203603030078009410b00410047c1c0c0c01082070f5003411f29509008a803000391440c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 268596429 1250 268595179 268595183
    0x405150f090f03010204080a050f0717031801020c09070309060501050f0f2803210504030812060d0b090f0f0f06040b070905040c0905100c05211e091509030a 69
    0x7007000e0401e485071405e405030340c001c08480040364106821890000d0b195090001c5201c600d22903180c00280100f8008481040c2401c818080d40c86c207913054a9554143c00e02014481c10f600c500d84905078641c0b51841c00902c2815070783c3d0001102a00f0b45060410b40f90b06a200c10321680300c200703201c001c1d903441c1e4020782c031110380448000c0004240011680d0700713071a40040311000e00c10600800001d004000d080082c5201c030007140201c204440c2c41c0251964000c0d8007015255110510041100c0024243e0244c0c2201e001801c4110081c0035549a001d003ea0484050026030001462580e82c031004000e0071401503840d001070a004401485030710758403000280041c0c41002d446000c80c15039800345071544082c240140080c070035500b6100b80508440b500e0320a0600a81c0e501d0000001d00303106040c000140381e03111002d094019130300c100001c40d800301e00700c0801603100200403000707070914000e0000e540c84540741380f460b0703c5003082020800302141e202020448180108038900c02c594003c24210820340e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 268597679 1250 268596429 268596439
    0x9020102011407050f090d06060312110f0a020d06020d060605090307141e010c06020304030201060e0906040b01090b0f04090501050702070b0c15070509030a20010c03051204080f0406050405150f09 86
    0x280301d0000d0345840c6041009044079189c40c0c03010080c01311401e52500492115101c01c10401420b00030315a071010041070030003190b040780010070010714144000c504028013a071000360900181030412404c071180c0e6800b50010403000141d0b034403170b42001e01400e0010420803015503242c080980c007045120b100d5940034889c3d4001201210546c0c0e0080c020040995000401191a4500b506c9c0217402415640900d01604082c003002030042100040c1240c4142c0d4400a03008240e440c11021001802e40080d4140e03009540395540019512140f044500b842e0043c8000f02e06405c180c880a0305160a80e00a0100c68100b0051083c0240c0002145501c110390240180788507500d80ca03007100c0d240500301203254580607403440d15040c01800a038850800b002403840300b903040411001541d40d401c074114000c01084003400046410514084041c2d80a4081c040c90340c90300071507515001290f803060b0080310120b20003044c18003403414401210010200b001304e001b4500000300f44017001c81c0c090039034564031503 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 268598929 1250 268597679 268597687
    0x118120e060415180e0907050a15030506010e1207031103060106090b13092a030b010f0c080705060907090c090e01030209060a09020c100f05060117040501060305060a09020102011407050f 82
    0xd0b208421007042c034080d06450008061725250102d01c418401d0300c0d080d40398400c00300c000c991480d0100e1803004a940303090003041103108004058016002c000d00050501c6142c07481d0259544500390080881c4042d8030140c04503600b5454805403241600c140c4600075400b00300140040f80d0085841c4040e646280720a03503d540e105900c0c03074003010700342d00080421802c0001c036009880307002003070341010890b0030389540b40710300714100c00c40031a407200d501c403400941100100341d0514007407020311510381e02801d070483c42c20000e81c032807900d010310a032801c0e543c59103d03078410441d800151180411254541c549441660b18180c40c0350031503001070202901c46c071103160105941c0c4c0e540180c1d200040c0701c0200207640b0f0310300744441070742c440b19180b1044942030305010010391210100e201e8644910340c16182c10840a1803040d0b4035982c200004c0c0100e81c65941d0f0f00000c00840e0041002905c0341000590200d0441140c3c8002420764245000b480d40400340360040c0f00318260007078181c40b1f440c00020304580d21 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 268600179 1250 268598929 268598969
    0xc011101021312060e1b190e07020c031b06030a1806060e060307090902060a03050702030f03281a12010f020f03060a0807030f060506010905030118120e0604 69
    0x24850031500180710603240b10001404400782c0d498024040c080d072810415000c114101076201d808001940c8850115040c84e85000c2c0741080c82228903820420178403020584034581000107a4042d12240702592014401d8661460300704000c2c0f0440d40059126848151703110f020031064000600306000300780e103800268003030491311400100c046170440024000c4590b2502458896601580c802d03002e40100034000c1a456068012030481e1035000d403045150501b844400c900800003d0712400441c0000c11105400da21503001a42c0135a02042c004101c01250b800e9802d6000d91120301103140c642080c212156140c0c0d002c41071100c4900945410a468038150f8000d401402d8070003030907001c2c03071012400c0d0041807644005144a10002e0b945c1d541c0c7e0a03124400c00750354541d64071000f89410301d00d01c00200000e1564100d583c20020604200c0903040c3c44d0000a03083d01e222540d40340c450783c1c082c4001e20520010b0000c4407203204c014101050080c4a00021944911840c01848849902641c50910b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 268601429 1250 268600179 268600181
    0x23010b0a0206160e0603100e07020a0f06050c070f0c060305162708160504050702070302241b0a030332040c030501020406020d02070801020f090405090a0b2d0105030c011101 76
    0x3c44e09200602c8990b136031622024020101165016050102e00c0302800184081d0000400701111a00035609400c0500d2585e60380d00545002050a406210280b15850000d4040c400000c00c0500c074005001140e401c1500007421101c0041c051412540c8816921130f45982103d140c0d010302c0c882000311102002c10446c03008011415a00203030740303449071207062808808200440407d480c011101030102d501c0d0b440d0100c0c0c0e00c40f000c1c04065030007e1032280f80380b841d04a00d42044031040040c0d5815041c440c040113001490074104036245429080000b80808240d0315100e160b504401b074000e03442c000c150003518054001000ba5000070204e07500030100e0244101c2854420045078000001d640d21519580001e490b04640b43c0b075040584646d5401040707044060090300c8000003494155401c050900f410400a00000b91131403940740a864030b07042c0450b10b0314854502c50040c0e04066020000c5051548103006641e03007540d0003025400d401031109a43c00304250049220901c0c0c81102c3c86c58001c000380c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 268602679 1250 268601429 268601447
    0x12403060c170a0606020708060601050307080702210705010c080f0a02070302161d0115080a090305071a070e091302040b011209210203030603120c0c0423010b0a020616 74
    0x30380750402d0504000c0c1c5000c0903082002030f200c50f5401d0712103180e030381d49101b1369a42c025281036011400600019a14502c900700d203540c080c42e584121680444402601e01e08955103804400b024a40000e030402441002d00900020309401e10300035200c1d2601c40c03900e100854028001c980c0054002510100307251082103400c0c6002000d4942d400307155030b916400504a1851410003003401c00b00400092080f4034000f040d000240142c481c00d00d5513842946c0c20300200700c01901201801003d0105a0220755008016090f10010700b5002065040080c0081d0180031002102441844040204000e0350b080040b01e100441c0d0680340420b1b43c800000c0180c0e982000c0300407002031180f034000002c0900c0702a0b4010000014038255000d000380d02d51b2022604c0303110444503260540e1000c0345002403205604002c0c10454895800da07038510b5850400141070b100080400180c00c812101c009489109001020780140000c3c00580c0c0740896426000e921840001d03c610403d00881061411040c0100110 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 268603929 1250 268602679 268602707
    0x31d07150504031a010608060d0c0527090607090f1206020906190206150a1401200f010207050c060403030c17210708070f0e13061a0a02012403060c 65
    0x725074050644d0b024680022024451040000c5020000c03501c0c85c2440706007040c2058120005500c40e40c10034041c404800001d018800c0300600d020318000745009030500141c0034451000c05040d079401c10020042c81d004aa41180c0140c0429140400c05c42a80f45a004241c2c0c0d400307440943c46000080001d54a4001c0d003002000028080e141c07030f00c050b40d002c40c141e0301c41d0b101c2c1c50020003801550824401400f400380079683c05201c440714201c0003076000b06c07801100034844403090441c400c0c007080103500307044942c0e140c81110b80d000f10303484041200c1805070402d85c0005441182c103003451074074018080050190043e24001443c0e901c103035592410001c85528405007180d1a9001d000b4109038050548125840c10004142e02e002c1a461403003400d242c42644150b503075120801c14070008200075035000c440395481d038559038040000e541001181600e595641c044946445910341c0001a0a4070312016140400742c0307410302050f060311080008441540d4000500041c2403131600c1042e5a001c1042d465 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 268605179 1250 268603929 268603943
    0x3031508030a09061202030c0d020c0f10060806010828080c010c0c03081023010201020405100e011806021e0f070f050a050603010b0a08090a0f050706031d0715050403 73
    0x8410402070308401420308469041d45d13288468100d28916404a010903500b25540c80740070052128041025005000003078844800e031108542d040c00c555240c5280c954030701b10740355158801008400c4060000a00400c0540b0261000001106916400f403d00f00101d00040c10030201c04e00c1801401c0042e200880140c000030000c0d5206c264002d070000a08403400c0700015001ca002891002c83c800c8400d0888003070724020359480b8100e8250f04845550303810321034115075003031000140b2a0390b00450340a2101700c6480300c40300001088001040304d5050b07080500402c0c011503041100325800120442404d07184104200d5402d103c0b14414103141001400070014400e0303542c08640341c4c0760940b401c42151021215410b00315602c03024800580800d00c128070410720103010890516025804480d8802c2c4054107595810b0003542d5040c0d08440c18034001e64035640884020701c4095014840c42d004041344d03070401740c82001c1c140c285c80c2d69114036010386143c101040300e03070181c594081c0c401e68010f5644142c2c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 268606429 1250 268605179 268605187
    0x6180905071e1112160f110f0a0f05060706020712120b0d02031203100f030803041a09030304032d050d05060d02010503160504120506041a130303150803 67
    0xc01805078003070700c45003a00540000c000e0308141c1e00070011585043e40c50320240607034076404c600301c0b03400b900406081c0494042812a00700050000404412100d04c100b1001401c0f01241091181c01948081034501a07160000d003401040c4001120604a501c11526103a07104200d02e4044064066242c00600301210700600c501260b82040303170f010300c080084008108028420082240301045900c000c2e4040d0002340400c40c0c6119414001d5030f005212038144410940da915103001d840009a200b43ca443c60040244410001000d25140f10f08284444081a0341411101c0d40d40f81d201c0070f44014240701d88062891841c2d400030301210848081c08001c40d040e2500940040c1407680f1040c5010461840c010002d11030b403030450248184035406a481034155070b141c04107043d06c4030244105005111003030100142c8042280b18a4500c2841000038003000d0600c4d103410002c4034400c40784078030040213a404101e0299100190900344940510700800e807000c7d44030380103080f41d5094010804c41c4c00005 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 268607679 1250 268606429 268606441
    0x10b0313060f140a1b031104031b06120c050a0e03011b02030403151a01051605100605090702060601050a0c06060302120304030516060f0806040b120c0a0602031306180905 75
    0x9402060f18000103a5a290076075901001c3c5003c50b0b031400041c032402c17100d110024544d20b200780e024641180c0080c1550b464a91640c4415818502c100c0804032001440314013403041560212911690183d9803005015840a195002d800e83c0103040d40002001140390342c007021568250010401014548a40d05100968000094981e8061300050312103040454107072800a0881c8a5995981180c02d03031418079031403050044446030b0028500c680e1401318490850089101885506000b02000500007a010301e400b042c0018200f006205034150f4100004001c0680d8002c003c803034140031589071600c0b03000350502e88400189603640001c0d40117000d04600303ca51040020081c81a42d014104983c1c0510748075006a0f070310503050140c03c000a25020783c1c0240a0300401c11645c1110008002040030420840401c5074501801d0080c051984050208581402e10200e07000103448588041c0d4948800b90480004441d850f100f0305082128041c92101cae000c41e0741d58042c014060038502406141014 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 268608929 1250 268607679 268607681
    0x1260405060a0b1f0e12010e0115050102060615130308031302090906220c0e16030e03040605070f0303020c0307050703021c030c030f030b030a030810140603010b0313060f 75
    0x200e442c80292803070810150140e1600e00200851006145070445103800c0f01c0c3c6007101d12101d22403000343c000310072450400c1002030a014501100d031112000040360306004071854070420080c3e0005065402007402e000d0143c035215019144442c030000f04542c3d945c40d005640c80a10080c0d40050000000401405a61400c901704500124000c03541c0301c070261985a030064448400b03460300800c81c3c841244039444400d007080b424551502428041c07a402da83c03000124410034007140c800b507185540b484c04045581e05445050011201ea4001303604250404d40b0140013486841009410f42c1d19203550380040602c280c04503502e0101c0745040c1ca1302d51400746002c079558100d5000403031003400e130144208006400380101414258060b6070341000c0b203080da202554038969034201001096229415803e290701c0402503180c025210707036900721003890010100c1c400b00c2c0b10313504010880280c1c0c400302401980c540068906503038072012490360300d8469180c10b048d00054550003c1c5030034104001550964a6 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 268610179 1250 268608929 268608931
    0x260f160512070c0504110c0303151c051507030c0e0409140106030b01030c05030604120804170f0a121b050d021303060c0813021f0507020402030c13080a03050304020126040506 77
    0x55500f1b21032809090800c2606014002d6078a0065209000050898868600038020600094103012118841d40718400c1d142032040000e841d00da1111640341c5985c880344680941c861000c0c60f0401c0000715003c2c0050201c04042581d43c4107986691300c820034042c3c103030b0b10000d004000d80001c0081039600e01d04410701081c248000e44400100710f90005903401c0c042a070740d1286901c8224011500002d10f015259402d0290044e500c41107403080305400b00e2038500c004e181e209954101280c0751846014002c00c07007030889904041c05400c0c40f4218500d5038030001c2034030702c0c0c940318145281c81701e1071000180024001d01500444810b008071000050084581c004454001d443da07821076070384c3d20500d0901d4445c003c500025000009541c801c045207410300310603003a5050502c1e09a14003182e0350001400c0e80c0007920002c82c44540001d5640440009500710380007410f00401420100392292000303480d5000052000e410710203003a43d107100300152000140058114005889914103181c1071199907064 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 268611429 1250 268610179 268610189
    0x9040f050f040311011404021507020a18060909380a06060f08060d0206030c0906030903180a0612050a0204090c020c0f0a0e0402060703020a0f260f160512070c 70
    0x3214a44c0e443c070014041c0514444030003112069109030315039a00f0f00680030344164089400e0380080c000140140e480c030342180000d10b015184024001100e440350000c440c215804549d1440c5007082030000915168481d919801c02581c4140030204882ea80005581c00d108079100c0031100c4204000a40000794000300c151801035032402801800d0b858290f984600c26144c090707000c1c008500842c01031401200950340003004400003820149610085896078009032030f4002c0c141c03c00301d20034409040f409400f0700c00e031360700b21461132069160030405070184440d00c0c400c01c1c44545410000e01c07942c219404031030040020031010061840451402500c40800846541c41000c001400700c64520740002514103503410034415030740c02c0d290b980c00c03c52607601800d030480941c080c4082007004224844441010103001d0b4034241d040389140808036082106080040e94903541c20300002c1c800382c01c03480036505100856150070022145500301030307192122420902d80711060002d40c00c410040d1854481003100c07 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 268612679 1250 268611429 268611437
    0x3130815011d1302030106080a0605090d0c08030703050402030703082a06010b1206040b0904120e0105031510020c0303030a0b19080a02011d0303190f09061409040f050f0403 76
    0xa41c07290714240c1000c9801c80042d034020100c1c03003c2602440550911003806200030000150f45030b440d070100382080814882034440540d507200700241e81000380300301005003000e4680a200200f007552200e40c03a00000d01a10704041e0b90700d0014085480802c01100550b4000c3c500c503486805031080d441d08034083c03a5510281e0700c9081d40808841c06c000941d681681d140c005d101e4200000740c640c60b0002580102456441034440d0701d14042034581002c90303402180900a10911070389600005011030b0b685061071030400108204021042c19843c1c030003400084111070044000c52a2a01207140c04001c5040300e03494080042400500395566000c0c80c101042943c0c906a003404001902803411458815450507400102c0e5080c0198400d5500070440c059071200719280f8020344003c03a18603049031224101100d0282d841000b011b803c00780803110b1800d54a882d0141f141008401800c07070420121040035a00e01089404941c0d4603038104d8038000d003401c44100014500200034203456507068400350041 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 268613929 1250 268612679 268612681
    0xc080c13091409010b0f01080a0e010209150417120301120201021e100e06040f2307080c01120203060a0b03070e0306040515070207080c0d0201030b1909060b0a080a0e03130815 77
    0x246c14209103030790300180140c5810b401d5507a002c9900010304ac080c19221001d560800040f0103650b2145001603d42c1020401a9103907410011403000103408041d0200b190791021070f941c0e8589005070201c0f819a22076282c5035040004d00e20050b854000081643d01c00b2801401c1d0b0044070110010f20721700345c0c01841d1402d00c1089070441109444503819103016042ea24910484008503036410203103412840c1d540c0c5005400d42a5200745410300a250b044034003e13411088c84580d03a583c0c041500c2484542c5170008514609000f00000d008008601c00d00009010200000d16030900a1404502e01400a010b8035200c0c90030f85032107500c92441900d2240c680c0950400320700f07814800550107040d1943d84004240050190f41004800c0740f01050403410507480307000da5000741e2920740200d00d0050694680560481c14862240d0582d6455007200911940600100e40c8403540002741c0c0d0340128400800040c3c42c584041c0315070540c883d4020391081e9034509000000c20820011702c40c00310b500420341820017 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 268615179 1250 268613929 268613951
    0x3140c031809070e010c0602031e011211060a0e0904020102031e07050d051303030309110a03060b10021204052e0504080d030b150c070305071202130c080c1309140901 73
    0x841c50780b5804c24006031041161400160007a0300464100a0840d803000202d4406c03001c40d414400d09800c10000c044c07001400c0c108000c0382642c22964407030704895807400c0c06810600101030328104045140701e000c2110101d0151f9001784201c030010b620141440f44650141d030214943c0d640510b80c212060b2154896200c0118458001d13610b0710f2000ba052034400038510384084018040d1403901380c610040c038400c1c10351965200c0b203001000350f10444000c2080d0600404010040115801035400e6400c080b4006070b110401c00c0860b41a01d1044808030350100b42c4403011004560017101e00d18000c0e422030421401aa04a40504111010002150140ca6213200100d0030f444805115a0308111342d5803003400e60032450405042603540480031209180c0d940d84440741b5288190340003e0088010f40c1b203103819428008104848103031040010b000300d19905038018802c09004184140e0700390301180c50700a105200007550000c2c400c14009100183c1c40c484092a0480103031412043c640c6400b412600b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 268616429 1250 268615179 268615187
    0x306160e030102070f020d082209050709062c0301020703020a0c0914010b07030512160207060305010e010902070305191701050904020d0209060406120f050105010e0c0703140c03180907 81
    0xb104c00d510038a20002804680d0901030f60143c0c001c4d00f19420b08040c0300c1e901d00b00003017820240190200c4148030100501c0c04040c90b00b15036024103d0b10030400744400500c81c0036000507042000b00c101112504094400061005c401c2c041541c9095241d4000581a0145580002c2201044d40245140d0760401e036101e140d0000c07100ba00c403080343d190900c00010002401c1d010f02401030031380281080ca1900000c003680c9a44180100c5044480d02c2460705001440c560400841d406400703181020032503035042c0321003e240541c0503c610440c468000504200b01889141070340c800510074030710005006003400018080065032050b0042000300880006498a0219040c80c099500503003801e02e140307460f400344140342000030030701070b080341e141c0100140d036060100c041c02080b4014000056050258a030a030300b9101c0603031000b0a045c2e40102032000030b03e0580c080707034203080c1d060a080b201c0b1b1031800b4030001c0902038060720030958000415000040f004001005094030b004a80e0301402d6500c454040d5 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 268617679 1250 268616429 268616437
    0xc0a1713060c030909110d2d09030813171b0d0f051c0e1005040611040614070606030c09091704140915100c060e070b07200306160e030102 61
    0x1a0000d68010020017a505c442d0340500c2000003003401c1c2ca850041945a10015100c606d5006184041c1d002502050041a224070402e5542990130070301a40303206480c001c152000c007030401000c46070309401c614100020086d0707000520300d5032100561a681244803041845207031035000c0c102801001c220a00c424440d45000640d00b00c542c031411304000c1080110b0b10401c5540c40014074180c3d0380c41812264107410007103900c500c0c440d18004103681c41c00b0b04e0000140c400c0b40e000604407d1003848180f08042d0006180e40300c0314584414961504401e08003640601100d0748094010340c0813610104454003150408180a40203d41c00c8005011891a2100030f110724420101007001401c620f0f00e082ca4402505900076800183c01c0078040381001c0096081e8416502903c04506615004410042c1134000d90002ca442000030f8000903151601c500c55910411200a1081c850981400e540c01c6130380002c0c19200c900078007105e02a02d02618408060700b401c842c00000b04280621403007062034140216 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 268618929 1250 268617679 268617683
    0x90b060301120305030a0b0a1e1d01050607031b0311160605030106030b01020a060c03050403090e090a080f120c030106140306060403081606090c1701020901080402060c0a1713060c 79
    0x44400b101d00c64030304580710381002d0000c0b42610b840e40c9450300e642d42c459914101811008002480c00328802204141c50149a8000716400b0f4400c011203420b0210305000d00c3c110f81c81583c00c0703940c0380703520314080320740c6c54000342c5c8103c1150003c0751032010325a0004128260317410b1300086640b440e0080f4180c3c500d5415a10a080000f0020401485040c0c071a4210303509036507040c0103c4d40c80080c00d40d40c950a41c1c200342e60140010369070320704100030f00d644109c80c0130003400040c1c01ca03400c41c2841c82074280c503044941d002403c180c10024542204600c01001c1303a9040030502200030701420310140803c3ea907402031160900203100d4101085000000300100d80c007400b40100310b01d01d0b242c40d5540f503c03410b81160010ba080c00c030b001071080c008220207000c0c4515280c850440015280e00703004903281d034666588502c000c0d07070b071043c8002d05407030341c22481d050341050301140c500c0d80b40c1c0d078920f45052418401620040c00f0907001d080034200c145468000c0d00c41603d2018800940300e0b02e904089036405540e07180 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 268620179 1250 268618929 268618949
    0x1030513060e100e06060f06122703030f040b06060c0601050d0507170601260d030e01110705011506030c1b0c0536100b030604020403020904030801090b060301 70
    0x214000524181e20038a020100c1c0000e40f40c024400300320507011522240c0f0070074120381250b0b0401409140c03280c506940f075041121002d061014000142130502402810000402400b13034001e40c0c0440074195400c1c880503190110fa03640c2c07408000340c62400d0020303107040b5079a01d070010200d101c0307140a100391603200c24828018100e980c030f001c081043d920410b02c010740c1c6078055428041020901c02054503900c1c0340d404000d01d001d5241200b0494000c1150910410000c41c2d0324944181c2803021400c8040345c00c881c5008100308141c07541150050400400704010400c0c000344100402006400030710707030b040002c108412000d41d2008290141c4610700780c1b0354000b981c0b0301681c20303201e0344c00d40c0c00c016150300070079000155170b4841d00807403503d01c000304002c1c00c0c0000e0141c04541143c00f0784404000c500e920050403400703042c40c0304000110b000314042d244240300302000041182d00c0340e07411382c0c008607001840c2d0251400c03c0d0402900c0b0350400c0c05030031500da0521f00240c1d0a07003002822607040761000c3d10 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 268621429 1250 268620179 268620211
    0x6050a0605102001090b09070e0c0d020912010606090306050a051006081005090f01081b09010b0a0c0605010e100603090812060f030604051b0102010902030705090c16080711010305 79
    0x40c00f16901e014082c40c0707030411400c906015256840034030501810610400c0780940c5424600b84582c60300c0b815a20a00140000008010560800c501070390700d40c554564016846e100c40d600010341507003507040c4070686586810b20006e40c0f694050201001c07240640c500300321644944110405544045540c100c510444050400c4a603101e003e88650110926410510060319040060000c4e001a100d0304050680600144400c000c240301c50b0603042d1041003000920f08240c0c001c120004014861403100d582c0c0800d807120746602401d04941501d61009040001d90f07119501c50401034420341c0c10301c621489031003012440a001c1c0c85500031245e00502010f040c00042d0070641304c0188004c01064000800780e000403400c5d2005c201380b500032841000a0301c41405041c0301d1030b403604920250981103a05000c0000050303100454403609891045e104501e990b0b0310f640380f405480c424900c15582c040d8821014030180002e02001e446203506c141c40340807003034800d40b00442c19141d09403a203402d00c8134801 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 268622679 1250 268621429 268621459
    0x5010906081c0e0d0c060504030201030b0906030a1104061706010915060215130b07020a03030f140a09030203091905030c01030c0e091008241303020a0b100302150706050a0605 77
    0xf40d0302082000f801025084035600716662403400300115804000441e0022406108540e018090b5084149040c1c0c0c08400d907260800019503141040e180160132040400b4400c0469243c070b401410240c0031030342423011410100d01c00c0503525802486500000c2c0c0c40d01c0402d0f141c00540350341c5c1da02100c40a5000b00182d040d1385510704566040900700d91100e50400500000180b00300d514240700322140c3c1c010b444d64002c0c0342405015140c40b242d90b24500b91802801214092445060300d4103d030302034a000031055090320b400d03845e511440b58419400704164007147c450100d164445001d07a070040c0d099032040d0345010011750079954221642000714503080b04c0750300e450134030501042c0e016031090b0140124a0f82d41e0829803e11808501c1640c283d0b00504c4940b580c0d9400d43c003103940101c40e03141384100752400c0c1c1d00c0081d2106001100203090900b600c0100b00c101550103252800b86070000c2c0b59240a00e940101c0b4441c0b6400304000711200c45c06d020002d2140f04440c8107007411240047c00390f0260100c04c0c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 268623929 1250 268622679 268622687
    0x715020304080d1101090b04030e01320d0207050f0d170c0904090201020703060c090806101202130603051f05060a230d060504050f060a180b040515090105010906081c 73
    0x2c044c20204641d44c2e5040680403072079a500e41405a0b009440e000495890385000411100c0074024141036181c2d90076a0b01e02c49640d980304407032107840700046182c40d0200422031101134458100c0c00751161085020100407460045425400301240b9140d20307418120600d25084000c0b011907840031b4501c82408034200c03606060300645801d901c14816198a15140d03901d6400319040022844002a5540d0051102401c00c001803070b04442d20780030b4101d119103070001130a01a04010710003801000b450040300103000182d0801700207036a1001c15600c800c0b80d0a281c0d00140344074601c00e409928107100c08105603081c48524141585c0700402c40d203000d106031035400c00c040d014080905411101d050410340100301c0c144192401075116070302901c48503100d46122490400c0180429080e00c0c54022011b05003490540c9095016600c20104096031359681481424100c0c210340000f00700b941941042407040c0107500c0607041c0d4036091401c204207502c80030841e03a42c440d6000c8100c0b0108004442c50105401 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 268625179 1250 268623929 268623947
    0x3020105030619090606140c0709020f131d01090e0c06030705040e0a09290a05070516060b1005040506040b16140318040b090f04080c0f0715020304080d 67
    0x40e10400c4490511000040c039a1001e500030780109170381704406c5c800302e07a00ca003800400041400c07045042080700b02c0c96944810180c41042e5135140e0000d110081d00f0340541c00e03a0100d1121080d001200c0e683c450304060b107420f0103944e1601e04280c07000045415281c501c2031382d80545a50009115401060042c801c00c0e900207440c250074002d007400001a82c0310301c54072040c17140c4680b50000c0b5400007549040d481e4510114041050909910203414450b0480c40f02e4030ba202d208100040340030f840f1520240c405119403000c0f60502d03d00700030f60905220094000d5075001006503001105400b00d56011119400b4078060903901c082d080100700811f26890001d88000040f41000c21186101696034104100c580710404060f07070004240d503414541140700b001554901560103000c2052002c0c00504c140724020314420242c0c220f40301107024066003600f60b40113240c80c00100e43e646900d580c802c5a9891661046114010602c251030320f8443c404016a42100c180c80e00820b000c4c141488260307034060b1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 268626429 1250 268625179 268625191
    0xf060b03040b043201050711120a1e0c0210095f03030a1e030b0402040b0d18031707020c06040303030606021e03030a0c090e04060605091806010302010503 68
    0x1904500340c0c2103075201c242e0824079031612104560380007244101045d0075039100038502010301200d0b8400961800000c181c0740b03400e4445080003130762200071442c00e40d004841c0762030b00300906695a102082a0707412800c0d502c8901e000b200d440c651555281000c60318001e250180f42548480c0c00c50300c40b800c1c0040121000e00090000801d0075040016845800c80c03641032400031449020808800c0d02c0320420700307418800041c02d40240d442c103010010054441c0d4103013907040340f1484141059085483c86640f1413150500001c1003555a2680c800c152420741d0041d00c5d1280c8841d24000c10a806c44012000044000e5415141d15000d02d10310300e059401008010034100c194002c1c0b03000b0203a142e80f61001013010358807a8400154950810702d0091804074070300700c480203840e204948420054000016207034082c4800001082d1034942ea0011201011642d01c00c0056041c0182230204100044c0c2041054070000d0b2070841139551042800c4415040c0700c52204099005000180090b5200d40001c50f8004 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 268627679 1250 268626429 268626443
    0x105031b18070201230103030512092d070b030411060313080f0d05090f071a0f0c0703120810030201030906090213060314240603150412030f060b03040b04 68
    0x180200206a06078412520100141d554808800c40d5482800c244802038100c0690001c0303a40c119600138006201c0d0a180c000488030800025061490420000140c41c601d010881e20310902d03007007601c4140e1154410704a20703000d0701d10003054004c40c82c419640b040d90130281a4899264035070522085038030282000c0084048880944041a003e10040400c90b1290254554a141d050982012200058401c4c0c0303079a000171103480380800c0001510801e80e40382070781504064035441130301200c0d1301c1182d502d03240700000825046440e5601050034803c89004014030f00750002d0800d0221a88503044036000140c4414210034000340d40300e54010044541700d10b40000e440702081d00084e4000e14002c0052801c180c80304407e01c100003407444440d188404020062002c0c1140c80b0580c0c4190300c490020458005c524400204030f55000c01c8142c034070120b80b24502945003014240321164825611205020a04080488501c4209841944225525550b1b4142140c0715a0758402e40590013600580b004 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 268628929 1250 268627679 268627699
    0x90b09064f0b01080c0a0302030c01120b0d030210060506070c09020c1002040902090f1221070609080409180b0103020103090201030e0601060f03051806130609081207020c090105031b 80
    0x400360452820359224042e080ca04025890041000d25040460580d98001d1100f0a010401070b03e0000380242403c0007401c2184c42c094590705010010030a000a2560203100e25010000303040d00480c254841d195140310500105440e4014880d075480ac8180040c49031148000801090416038003406031080c1d10402d80d0000200d420204050b03070010380000f0095540040c0291552520720585c640b0078100f910f911120510781d50319180c4464071420550a900c0c80001c4280014150380100d0703a00550140041100a08500300801150414015260910f240501ca00c84004130b407421b8100c0b095000080e80c2c45a821070340114080c20b40584d04905041d01c418120f0300110041c45028042c1806a860402c4600f030040003d09a880180ca082e40c0d03148441291a0714010101e0900c1e80300e08400000005030001e80303048001005060710241141401140180300080c4483c00700340140426800c0355480603c4074204082c070b800a10400e0390581c00854030800c106c01c0c00901c0342815500910700b40070 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 268630179 1250 268628929 268629061
    0xf030908060709081c091a09060a020606030d050913020c2406040c1404030303110c06042603070e1201020c10140c0307080a0f090501090b0906 63
    0x341c50300070764400303020560050013480b0389481000040c0d070f14811051050010150303528068541c1400d8080c422082821007a0349035100600400c03120060000781101e95503400121009458002c00e44405100b4021954804c042e58032803010340d1021400103107041104402c0c98075240003544550445c0d00c060184401031a60260094031803c001d0070322081c0002d0324a008020042214a50030602007442900441c016a4002d200c1c00c0c0c5007581d6041c200092442c1c520f00c0b0019690058043c00d802030311488080204001170b04134508140b401141d499191110b0740321401340d0a0100310740000008143c5030b00c80b130480c64800200b102441508000500c0c0c15a5160700c14200303002c8041110502d07445070703025400000c0402c12503520140004c1c0040c25814105070080c81d505014040800554440040308400b4649a010080c2954004001c1042000d01d01d8810a1903404407016095800b40f000010701e100c2c00482c0c04070003d504032400b081080d82c1030003018030503011100c1c03460040e0302151003100 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 268631429 1250 268630179 268630183
    0x120703090b040f0311030403030509060a05041a180904032c06072a0518100506120703141003030c080c01050708090f1207030c050c0603070309020108100f030f030908 73
    0x4040c6024001183c005409400e0261072000750032520324140d4800c00c0f042001c03903800419901c141034100c42c01a56664403160448190045801803062003003071090111050f8507d1005004d07103600b095140c401d0f81d041404203e1440f00881d4050b000c41e42e0721019907210034800c3c5080e80c07450f0700040c0e80c1403083c2d50344000ca21341da00314403001c0f298404604840007504140a24030070100510402910740c80c1d0824000c241c4041008202d84c944602c080081904203003420509000b078840904450380700c07040d881080794190815103408000c43d2805103c903082041c0e1440c05441350928840e644cc0c50352860707404880b06041d02400303640b0070506210403400740c1020701507540560700554031f8003441d04145940e80c0c100190f854816000703a000c203d101040c0b00707144064601164050030300c60072210082c20100e0170621030214450b03115400008003d6440c1d010b501c180e500724000e0f61100320664949001220280320340c001c11f0300d40c407071004041002444841401d15014428542544019600c05c0311038 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 268632679 1250 268631429 268631431
    0x1050d090507081e010e030406090608190c09030b060a0b032212020a0c06090f05040b0d060603030810091104030f05030705060c04030204052203030c0201090b150301061a120703090b 80
    0x1104d030141d4013904070000c0a0901543e50210b039003201941c07a05250550260411050b403003000d050000500000e480c03183c2c42d00380c0c8440d101c2001010300c4840070b201e900038049420703400200d0303c104403d0301207046814201081002d4175030030b10980341b844c0c07036500202180800701501d0445080040c040d24000880c5071440071080042c6400401e0b0f49001031038240c2002c0141c0e08072008101c06140d0030000c42645039682070032140c2c1074500042d5012202c0200e4914000361601410090422030b00208166025031131521580b6044096007016483c0e80140094660000f01202601d4083c402480803401c03100c0c3c920032191151049074500010f568856003410003c60306410385142c0410304100f503080600034183d12000155401c040000c2e26005800146404000502015603032120040b119000b54401c030300c0e440d040030203560280381510752b01e81004d140d484145e000b542000c90001e1084504228200c4100c0300148190600310707004843c4c40203280040120040540351514400816882c40d016 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 268633929 1250 268632679 268632703
    0x9020c071710020c060601030c080f0426370804122109031b021f020708120c0f0c030703030305040c050603010305160e0112030309061103010f0602011a01050d09050708 74
    0x703003145c0e1500340005021154881404401c3c080c5000c2045140c00030003242a80c01a0b200850140c1d4045401d0102e40f4424811030811081c1d0001407c10400c0e1200c0c412004c0c10210240e10401c4520340f44107220204810045110114511381c0110b400500030040c0c11050344094900452503810010032221000000f50b02c8902d502e580b1100c0c501031580c0001ca4400ea00780021414800c41016030200f00000044501c4c120021469038194010794400e1240d80c00802500b402c6810000c1260f000011035400120140c41501c541e0351940c190300e5001c1082c9080c0703080140500f54880ca551010740250000400c02c441c0c2c0103c8842c00304c1c0c9a81c4510140d40614003840c014203402d88a15400c00300c6d5107081e004501c1180c3c02c100104260100300b001007118079454a4042104407a07854520040c000322080c03000c0311800800085031031030000c64408100c800d19802031121851540c101d80c06440d90090307660000e00c041040307103000c0c001504084041c9100307400312020650350f41110380c01e10410201c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 268635179 1250 268633929 268633933
    0xd09060c030e04152c0c09010e030109060f1406030703030207050d061103040303050103060b030f0c041107050d08072624090a020301050a051f0c050a080309030304030909020c071710020c 82
    0xe008200c000f019204554019170000366490401c4110b0014500503081490f0400003220041b22040c0c81c290032807126645d00240500020710380c09200c1c405040c00b0a06401019000d0001441034600010540304480e0590080c10616040c50288032101d01c05c000191707881c170f0700c5038098841c0402c0e02005610807406542c0c0040d10354114a00042601e081103640b41c0300b6848034107401c41c0c20b00085400351049204413000104105102260805d40c0641900a0114000c00c42c201c040281c024075124030401700b55560410501004203070b41e08580030042c00030000d0302c2c04400500396114190fa5038116044aa85258144600b480020400d10045941555030754000c0010001030500f865500054a07017111000c00031140f6a0790707210a95140840001040b220b1000300003803040c2070010507202a0081010380c0c4c2e070f25103000c890791b072584140d40843c0000d03a140c6000901c142075100380c03502030011102030094940b070a50158582034020350b01445502032001c3c144107054451000f40105251000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 268636429 1250 268635179 268635209
    0x626150109080a170d06050301020409060608070216050f0d062918060402030406111204030801060c0803073603020901060c081207030603120806030d09060c030e0415 73
    0x10005000500e2940545159400740006100180d281146404130900300e884a90702c03141c00084180c0038107113aa11050b05035100050110f000700d0107800c04025500075448010040e118080203c1e80c07040660082041804540000c0c40303580f87c803000c03214402d80f004040c11006a00c3e80c60320710442c1d010040900d0440e07080a0324902c400010400810704d210111103502d80541c05409001400348001d1403244281e60000010b0200b048583c841080d00c50b5070184141c541c1c030714102243c3c160005071420746c0844c1c036030000050880e201e021113a0381180e10800301c5003140c5508205864801c80e15109459070010a10b441100c3d06903100304101b1213031a220808510391450041c880c04242c107030000e5040091404413140800c03800c8048a410a010032502c0720b0540e1100804c400401e07468100074034040b00040030b040c1c8164004005030050307100b1030564440340410002038410507000d101d66000700d00302940d16400307c1e000d800c5c40b44051718068070126007602e131040c404405d10140c0c0c00000069416107 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 268637679 1250 268636429 268636471
    0x4060915080f070608060303070506040302060f06040501050604060e011205150108011a0a050d0204150917060615070c24120b06090f031504050d1103130626 69
    0x4041001001c000010748100c0504064040e29807070700c0c0c003070302d814030220780041201c2d41c804004a44142d50000190340141c103042c81c2c000c0d21410241c40c1550a52844000f2540030318003841202e04880c0020070491410b0705c0c111080e603140c1d4001460b58180682200b042124a00c140a080c2c42129404010000741e50100f002414105c0e0682091038000180960124911404011100c010b100e030b040a5444010021402d8042d11031500b192540012810400216540002104042e2440c00e00121004400d12544a550f8901282c00c1075000307514080c900c0c40310701c51000038407419008141c00d07004a42c80c1c85003c41d0800040f174007aa8888020086262025440455100c401000110521550700300c2c00008a40d400b41d410034034410522054001015076081044030713045109102207903410b00c3c0a00704141c9030040c09002d6404a031a0b40d00107607210b00d010003224540c3c10b0403001d4804160a00d4021111081c03c1e101c41c0320b0703021013009140a009220f01d6410f00c200c01d40d17440206500181 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 268638929 1250 268637679 268637711
    0x3030c050702120f1b09010303080c04090e0d0311090108071b050106080a060b011d040c1b03030b030c101202070f0f05070312080112110303041a0d0b0603160c020103020702040609 79
    0x814083e07940449181c103280e0755030351546e000340e04407900b518008103c3d840d500c2940d0321b240f10380c0c3d108d080c1c1240f40080480380b40d0404240d103041c460280d14104070f02403825203400f449101d9198010f0009420740300088140c0d000300010140509210001d142d00c031810341d100c0b402c69045801c070001c241d004898600c01c0001c3c50282c07010b403c0081c40c2c600010460405018130b071140c0e142c4014850b544800c2920741451080404c400390f144e600c03600000003c034500300030f0010001421554020f00540c0c542041a0400c018052803a41d165910407040c41a8203007007400941062404503181e160024100c00030611000044001c80e00800140101d14a54a00840ba0004980c1f07079205115104004226188800541c030800c15040000c4848200c8820002811889107401c40c0042021103a0403500d00042800900010540300344100460603e4204101807070100b255944c4d01203080c00d1036000b80340c1c410124a1880c900c18140581426615130005090304c2e480d4011030b003c10b6840118500350703511 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 268640179 1250 268638929 268638943
    0x50c040e011107110a080d0804060c03180b06040609020910050c03070c06080f09150403031d060702030a03050f010302060a05220b0a1b0818030a0c030506090d0905010c03030c050702120f 82
    0x30a86c010031500c084403001505446000340060221540c0d0520300702c8040c0680c1220078580040094610300034400e2401141c5901d00b565924000d500d04a00410310b041503100b207a28082009040c00d10001240d00200c51a03804200c01d504140024000580095030215000340035003900d84170400103142440408811240c010007404c9603a1062510401840130050741541144c1c25160100d001000c08001800c082c0c15031684144900c2280704101c0151350100103841c401a00b583c05020070740340d2180c0785050000c00c2c000079500c81d41c108a60320303005001d032004010b010403403038010390b0009034002956101e0381a41d0080c00000c60006014040750b620000c203000c43c00504084403120a4035481316205405400c41c6417800d03542a00643d0204c1d902008454640380d40200b040101c244c0b41c0c9401501d407941503900034181c0c0f20700310702c002840b4010032506043e0380e03044c0d4400001e210649c07000c6002d480309024100510408020200151721804900041604420010400160b001e00b88d03030300e4059 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 268641429 1250 268640179 268640189
    0x220501051206011406071410020d0b01020f0c21030307091518090f020f0f09152d25261b030c030409150e04050c040e011107110a 57
    0x800061110b0340c1c0713580407003882035015505076031500c45034904000c0218249602090310300c1200280c41c9807a0460300201850f0714003680071b0002d41008401a6038405241e0f89554643d0000d5609240d01d051051040041c3c03541d40b01000c00321107800401c035003182d100713641030800075501c1d4109002c0b0052405081d81201000c1c0761000300c1740042400786104440c00d01030511017030b441d20182c8080030a640c0603541c50300001000c07940e4540700c1e0754160b5203d80c041d003101c0d1700611401007040642600d0806862006038540400083c50329010658000d5051502c2d94201c071107418492400c0708a190010710542154040d01508151414203007000b80e140c0f40381004075891615443c1c8441884180f0585104000e40c0b9448180652010f20460443c09200d4400620340710200340004d074080b650300070404458203900c007481004c0e10b8101d00e0314980c1c82120040c10300d0b413006a01d40c2d164205a1312290044080c00000102e02103181303250301d0340f0b85c40480159194203441c4460462890100d01d0903000700 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 268642679 1250 268641429 268641433
    0x3110319030f1e1b051c09090f020f0d050702011404050303071707140c070902031608060d020913140f0304080c06070515040c0504050408040603050601030504021e2205010512 77
    0x100c00c070052502100d440d004e405400000007440402400b0001074000c0b400c2c2e0461400b40200c81032000b41003d5461060480c014200300400140e80600d10840b2a942c0d61100c005103803200101d4a40003074440540303030904541d07965144848103190105c03402d004500c0750001d140c2c1d07820207d000030300030f055090b1000124000b13982804003058115281481501d802144c40d5240e00904c4081800e003203856105504e003600000c03c2244404022501015040382602d5003101038556805000c481c0c80300307282c000d4000712041c001c81c4070300e0300300580300702414800d41c503010702d6084040041d820300072030011b071202540c400315040c00710071414084003a0b1990182c80030307400c00078991520307947e501d40d014038002002c0003a00442e00348030704030704070310050803002d0010b0015080628000010307600500c6402c0c006442c12000c80c81c80d40c824010540030b150003c2040151710b07090224030380354808558441d0b5020440781343e64803200780c001e280384015248a184c0020300707616000c1880004040c4c03001c00c030010f07 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 268643929 1250 268642679 268642727
    0x3050702010b100c08130306090302060108070e0f060f041e0605030a0b1501140703020c04050a0e06150f0a03050f0606090405280b0a050103110d0c03110319030f 71
    0x154603098000b10056001d484c291810764044d05180a43e80314001042000c0000b4031404414000540c10601707078140b09074211045680e03a1688103480707000e14012031140e42c5021020404141c140c801c0250400300c018402c1c085100c0c3d400c00502159003900210301d000380360210032a01d803903492041000400040c0d0260030605803580d603074880c02a00a1010b4186c2d50446036803491350344191171060311035025404582d82e504803030401a41d100fa0f20341b146480b4600b8180000c4081a280c0240000101f04600411441d107402002410551842d00e620b90491b4071250f0710b51b2281d5469400400550040001e031000c5400c1c0031820341003e100902e0a40161400024000003541c00160000c40400403841401c0f00da4403005c080074501d07001c2802421404241d000d1201c1c0360025805207040740d1082660f07403a0340070303040301f8400c401920210244c0703001c030114020004201d04298108002074014140c0b8480410320001d440320760004c040c20340000b041c1515209103560400f503042c0c00102c2d408210354903 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 268645179 1250 268643929 268643951
    0xc0602030f120a0b03100f0f0902030309010c022206090b0105340f051e010b0a0506030a060f0303110d02070e011202030f030309010b03070b0f1b030c0607050a0305070201 75
    0x103441241019074452040400041c011a00d50348031980e4240010107440d2441c1594a60001611f0101c100640c060300e0070301d078085007414610941c40c045a0113800b07581040104001510394110300b680c10b907017002e610100ca503032b0322043c00c5c120f28411000580c00110f490400961504440c24032140d581440001c0115580111b010542d10304420141c0c00c01c00e000080a40036854178144c4090000c0400010f209400104003010a48031046000b00c00b5020082c0d4050300c40909854958002e9504101405818842800d1240c01958040001d02011900703540c0c0701004210109070342e0003500052034901c0d448038244802e004642c500c03c840e10050203c1d03401c00200c400840c00604c900304160045010080c1151818080d10404600c0801583d4481c0351a900b420701800d2440b601600c01e01603075201103180070110702a152104100340e07105003843e0403521402c5a000541d0010280c0d03202c01e02882e541c0d080c01300110340c49400907a48494842424080107800e542d00030b0142c4040d6418006440e00c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 268646429 1250 268645179 268645207
    0xd020c0402090d1b2102010e090105090712020720090f1b0a110106091b03050f270d03090201110102090108150604030b090a211e090815040c060203 65
    0x1400f950081c0c80c1c01416445100e055528011aa0142456000034107601d0307040348007502c0160f0303418000e032541030081c1071075010454116000d0050982c001079a20221b0400c2d481020700d07012001410748010302c1c1a2440c0c6074443c10340c00158055011490400700041182400c1100503080b120404420b0750368108894550076403004030b181c2182c2004007081d4000c241e486101c50021020000c002004130603150458140a05141085044070582640001e28058803920502e132181d404c0c1c00c032465564486020b00c81c40f40701e0700750019101e0403070807003022006601440400e60701002c81d180094246520b10000d8484900005a100c07164418441504140d07007042c912540031660882c80d02c69410494005407003800713640c2000d4a40b44880c1d003080740d95900040c2013510280100440304500c2c049000700602c0307050b246060000a441c00c008584101040c0412012030012800c104c1070298590b2406464000301c050050b1000f2144014042408007004408002e82403900c091441c084080109503 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 268647679 1250 268646429 268646449
    0x10203160b0a23070e010e031e0309130b0f0a1211120d0509120d0915210f0f150b030411030708030a0f0903020f1315080d020c040209 59
    0x3815000c0000000b4078030340d0042e84180340c42c41d0340349081ca00c101002030001e81240c0c4200c640c1008181c04081201c540e6028110500030702d40d00400030420210480000c80389039140c08500032080c401402401c42c1070356621010002500c401c440011040c0455081104600c0300e030145e00d000e0070407150203101140101954560840c1c20460701c205800b0030383d01003000f81100c0be15219a9010300614002101d610000908504400310b0300d0440505401c142e003902d520004004002145100e12308000c03040603000c0c0e0b104048000c1c10910313620015030030240c000c010700d800e5110b13409940d4909108480030300e1151001e00309144c07004000c00d001e130b00c8110034069117900603552403080c080001404c01024842121075084042c054590396a40d80c0949a941d8010000c2d95000c40c2c401075690041e20f00c10307064081201d80082c90b46501c40c910701e05002c462410280c842e03800f46d4496202d003203a242c0c5610100001e11600c001403007040d102d408000d0030b0152454809124a0041000128036982c4013040 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 268648929 1250 268647679 268647683
    0x1060b0a0828020c07062006060909010b041a191401110a021201060303140705030301030b040203010921090b09030304060e1906030b1017040318030c090e070501020316 74
    0x741d00007030841c04880d0000311011100110303031400024905413400c408a031407001c450305600e4400030b8007401d82c50300b44514504003034528141d000c07200060b510300e009000399400403808000000c1d044070090200b000d94030b83c0c182100755030807000406e003800d04040d0f0141a00000c400c0703122280b02c0c1070080d5900042d0042180e50f041059100c40c101e0454000d2103003149040d401000100c00d040807000941c06001184000e8020071224a0340d08110a0f20030200d442c590b0b444009140340da82581e403002400c800c05001030740c042d9038138240340b40011146100741054181d629810240c0041103800104905810782200e180700300309004d59141034500105a03420b0b2105810310f082481105da01051303d4551403a0603010316080424001100c1d50903900c0803201038400d031000d1424402811051b103182548a0701e5103030101e11440010007003480707009a003000c02d00800704041802c0d0350341c49044411003250002c0400c50360301e82c0c214402402c00c00001c40100005e00185090242c3d500000440c00100390740 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 268650179 1250 268648929 268648951
    0x60405040b15060d0203010807170a0f080a050d0c0e030606010e010e1201090b0c0903071d040615180209130b0102030301120309050409080d0f15031509080307050304030201060b0a08 80
    0x2d80380d490750f2400151500036114000441d1a5179480880c240d4460780b61040e40c2ca0b0380048100860090400300d0096049500142160b00c88009981c5204c01c1e03500c01c40c441401c0050520981c001070b2500e007c0d0740000941552106860500c000c2014140100584001c2c1401815602080301e80d0b0400080545a0011034591440c98603c0304918050a0307a8440103000c1c0c0307000ca04201207041030f10701419800f0300036400c441d440fa40307030516400181484c41501240c811807000040004007103030441d04541c1c00703000e904144181e51b0211120000d01d240d00840b0701580202d220750b030323a040680d00c984601048050900c1001c00d40310003c0c5d1244018060b5203c1038800f10340c0d510605014440300030040001500422203d0f0450411910d103420400045581c1400c1110464041020b030090428080100c03020800d43c518641d01c2480c5907500c4000803280d0741c1c036114880085945440a50f00c10605511361590b01d03d070601e0024212900d54100503800705e014464900e04981c001e01c0f09920225440d4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 268651429 1250 268650179 268650211
    0x1c060e01020f07200d0b0f0a090203061302090907051521010e04050114010e07050c0a02060f0c060c03070f0806030a1b080705010203190503040c0314060609060405040b 74
    0x845000e0300c2801d0044550080005a56040024500f4180a4841c0e0030308203d108840740b03002c1180001e9002c070b000c2c100848a0b0b0204c4c5410346107541c5070780c00c040c64150000d5400d80d940d001ca42880d0088440301d4010724107441800550130316081c071039840100e2002418001d400c01e00010301e01015007882029022020640c1460030a0080002d8022034a420a10100f580c0d170b00e0b2560b1014104a400300d0380c550070413100000d01060081c480741601d003412108003981c1e4030641d0454944c5c010540354005449106282d201585514000300740480d4a0803841d070340c80340036409592400c3c2d0003904e00c6501450402c2041003080e40081510003006880c900200c0710f80360000000e1034442070600c0a004401909000c41d031003515030744124129080304003500c003082c1d0b4074030041e40c5902031141d019480d4292030343c1340e00a051040008603032040c4244491141e007612030700c500900c90640b0003003011a80c01142408240c0c80c0c01e4010720f611280c104d40502c40d03032419a90fa5007061502404601694103c0e031 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 268652679 1250 268651429 268651451
    0x708070e180a11100302030610120207080309030309070f140103090206070203061e06011b060c11061e1501050d05180a060501050f030c0303030f0c0f160b01051c06 72
    0xc1d40180501c540101250000102424901c3d1032011996030300d44141408182100c610b8064000d0320f1254030010701c0500e0180704030200b51900700070024050f0f0915400c201d450002042c400c01385000d05000f100945e1a854040e00703440c03400000d5000000740c07e80c5680c1c100b05031020f0b130b0030000d982c0100380307000f09410843c0e1010803502c0c0207121b0000c6d494020701082114810941c0701210903400041e80755000c41e221900117640f04031400c3d040300480041080c001000c03520a40007030100c080580340060f03250190000e1036040c204182c0e100024030400b1036500c0a40c80149036200c0c0c21030b0a103030345044c801c010700002034068072903499180c2000f9100c000044800024030f01c030025241c80c3c0400c0d20700c0c40c24203142c807400400090250a02c076074090440345125040024102c0765492001e002989103403150300d0b07507c0065500400d08080e00b1410016540e006180e0b4015002e04120b408405160010780d1034543c001080c141c011a00410030520a1f121100180d075081070a80d03041640021006040c0c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 268653929 1250 268652679 268652701
    0x3020703050f150a38011403090a02060c150c04150906362d141e031203011d040222151d010e0c030105010e0d060905010c030b030708070e 61
    0x240017001c0043d4411070500d500503000c00440c80f0040c0036078035141c20f004a88000182400192141801540200d007010010b081400c010041844d440d0100e030400c20360090100196a0103c8001c500035001280800a0107100071104c00904094180034031000e05000000744020703544149034040044e0132070010101c003216014100d07032442c0704414110842c0c80b0400c5907081503000001c0740214403503050702010004052000000e80307000403444080030902c5c03020440306081c1881c009054021040d01034a255604020303400c1840d81d03034801e41e0f48030340c540700c3d03460140c000c594409001e0302481410000142e541072051080d03407031818485004118019036001c024a50705050741d040c020b01c501c0200380302420b5001d007131003c550080080701076030b21456010030380c0c0015244a4120441031006004640c0510f02c25840b0b0030000c1e14058030600540c80d660250f4921001c20750301a55070b5070300f5450465050060254000c4250002c181042c60894010f03171300d00d032510a109103481c9000c04140d144c428 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 268655179 1250 268653929 268653971
    0xc1e0d1407150b10110307080903070803030403080411040c08010e10090501121202160504020d0b0306070c0c140a0b160f0b0f01090612020f061603020703050f150a 72
    0x102c05004000d800b0407039801807071000e40b664400e43c003280c403843e5001d12980d190308040c1c490002550504103103036a00191500320003030680c0c0c035005400000c5030f400820405948558000e617101009420103007030406642c1e06024080740141c0c00c04803541203c1d500415050304480b40004400340681d5608408a131849640d0000c07850b4034201030000802403c64a10000700900442d00800c1d00c4c1412241a03948103004010240c1c040e4000208101900c1d2a40c05420f004180e034074080760142003580001e04181088803480b010034201a41c020030310000d401c600002d0010b0b01096120f050041f00000e80600192180440001002800c2c00003281c0c03050f4a0860280d00102d00a12440149441010300600303c2da000d13185042c04c400040c44c0203c0b40a1241210f401d060405105200e43e024803c00b5002d821109400c01d50800154000e0222030154a02c003a01035809030145600310b00e400b609008283c14925400d6101c0c0c01031859400710750b14000e070042801c00300080e5449110708201000c1304 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 268656429 1250 268655179 268655183
    0xf0c030201231602030a08011413050a020717090319050c1f1103090f0607050a0c1202040b19050d03090302030607030f050912161e080c1e0d1407 64
    0x6250406800080b1860b40050241c02000e003200088100410100d959000315441c40c000100881c00411924036200182d00400d8806458003601030181e841e0324040d43c900307582510311035900082503814400d2a5010070020317500007203038620f4010b0440019540e040007a20920f40b1b05010801c00d030420004010226460201500c5004088001040c05d00e50407202d82428000c20030720303940c41c24065004803c42d08c8416000302000f120014070418400950030100017201e4610070710b0442d4000c02c4850304d0b000024072400320307070500110307503403050100341c0e0800c4500d5402003503000e0100103804503654014080c0d4409459480d00d20545090440d4a0021688080d400d030217000c0a00c0441c5516402124142c0040041031040351661050b80740c1e50014074181050000040c0440502c200c10303d030004000c24068000b6895060760056000d0904031031701c100b15814500000c038900c4c0c0403014042c0d11010355690b040c002c10a0604400700e0f0700c0740e030f40025103401c000e0845140b0484103050420341700a25 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 268657679 1250 268656429 268656461
    0x36040b040608010c0c0c06031104030f1b1401120b0d02060903240a050c0a02100b06040902041523030703110c010906150909080d02030618041b0b030105010f0c030201 73
    0x803138080f0000d40110144042070b10a003501c81004513480c0e0090144040c0204c640b00e000d4501851629038208001d940401101d40b0108201c07440b051907190080180680f9103400c4185000105600241800001150b2048001d050056109141c0e48074500e4803092034064609036520928030740064200800c3c04081e000c42c2103031200d09001403400c4660144200c114030740c00c01c49601c41e0f1041d4040e502a011243c00141d02000111000c0303c50b0742c002402070f890240100341481d0316074644000340c0c0c20580000c03c1c40d0144c400fa0b0105294442e024034003500040300b010079040c804a8003100d4621005169a06264540c481a940480040221200400c0c19402040b8080e05850210701402e0100d80c080040300070450040799129031841004129035209031820f00d005603e00207a400707500300604459100c511025010b50321003054001d10310039485400340b0640200c01c030451030364181c0759420001550b0f80520050100d640c110841c3d1046107400c3c01e24070001200c9140803409415845041c0820b2 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 268658929 1250 268657679 268657691
    0xa1e05060a0b030d050408030315013014060319020102150a05040312020a020705012307080406120c0509090402210709050f0405070b031f0b36040b04060801 69
    0x501c01d511407610310000324295009220064400c503014092170140f1100b607002007020480d03444a46c84031a11242043c100305085420090601400302c114200c03107401c81e81c1d2f0701d040c071082c44910f1080801441c454513040b00e41d401e003603003c00d0b650b003041c0341200308900d1070202c00d0056a00811100c1000211a031b8840d0072403510001d85400b804068501300c001c500c00150000c1c45280030f000340d03005643c055008101d010b140000449401c0b00312044050606481404410010010001050400d0043c20301c550384500d082401003000690103240e40f501854080d00e0f20300c0130b42c0001100d491601c111540c501035159030000910300d0030888003a101d029600e0384188034030080401c031101180e0030f0003404c20130340d958020000c004141c126070042c01600854010710120ba040d2001e1900284601701e407070130300c4212900704041410a6002a144042d000c220f20b50311041942500408461181101c1001c100f0030b645036405100e8690203621464448646219648507617014b5402042600c00a002c1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 268660179 1250 268658929 268658941
    0x1020403030906120531020d030509120303060a2607060e0f010e030c04050417040f03140d0e010509010203280e0910030807030509030d0207170106080a1e0506 70
    0x849042c910460001c901d03070b00128410400548100c510403106146600b0507088645d41500511881908198203c4510704c46040944c4405082c440f07071502c65159240e4a0b40d4010400c92014445885a0001c0e8806c00800c101a154000c030603045a801a0080c401c0701d0181d400c113448000000c0e900c240500c59106c002030f525510801020080c002aa146454007050310011595900d60350100303a01a0700202070f0020300c1c1090707400141c0c0217001d000e5429001c00b414150503c44d5210b80c0c4895544041101c09005010901c9800c100c07682c0801c000b400d90306428180035090160780001c1d00e05000002c2040e00699000340308880c509054031030840c250305800c03400465083d008040c6140015040c00540c049401d200d145203002d041569155014a0b240d541c0d01e0b4040da100001c2101040000c0c008030b14652020400c0c0580344003160094074003e42001c0b488401d0000400c4901d0503a810b248082040920111714405200d0300031010028042204d80a070703e0314484650020003d01c00d100420034 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 268661429 1250 268660179 268660187
    0xa1b14060906010e0a151a2502010201060501050a08070c03050d0606030509010507020705011d060409020c0a11190e100e0c03180705090604051e070c0b160905120f0102040303 77
    0x3c142c40300d280354812951035050301001107540f403c00078070341030310210801c3c0020180031100b1034155415420852400710f12810344200304a07008603500c1044100040403045603028020752014000c03e2030300500b0205440002824048090020024000c15514090038544141c0440381c156160b10000e2200c00c0d0b94500c001d0007803600700e0300402554a80307004500b0380c40c03010580e0301c12500140d403901850194402d2100030000552119540558100030001e40c40840d4005040340a11810242c21000c0d82411b0a80101c0101c030800362207a458410101040c1c070f201d428240076100845012040c5548201408009161a41082d070301c050100003001301c040c035090000c0d4414030283c00c0400090395442890795030b90a0380d002d05684890300e140029030500306a803081c1d51201d0b41c2c500d5030504034071107007580389018001d44040c000144240c108801307104e1086a0f95402680c1c3d03c9041c0c0141105c000010100851401303814424035603808404102d0b80b0800801b0f403c40c260b18021036aaa41c6c1e460050 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 268662679 1250 268661429 268661431
    0x70903030905180414030403060f0605180f01060e12010203090a120f020303010b0a1e0207061b080d020705070f0e07090b16020127030602030108070b0a1b14060906 72
    0x40004003031040c08100b5050000c8221022240c048040361640c0701c554400d030030362004061010a9100510000002c20343c83d0040340102c01c81c0000000765503040c4070074451a6124203505504c8c0310340c50000d2001d404844000340e1b04650552800403160156030002501482c0021b02c8140258000710030310070004800f2a00c4c00c0902d1280c00d22980d804460700d4251900310f2030100c0030340503800500041100f14200d0004000300105450300c10400900d09000075100c00e4032880c2e038401a88102da00307109039a080404502140c2e0035a1200c10039404503138408007140300304207156004503000309110003040f8040101c0400703007610b41c0c3c141d620140c850036642d80c2000221401c10001d5070700c52000515150140c111518491414007005003012145c0040d100c0080c03200c0403011019114034140c002d046050200e801840c42000301591343d515207400e942c6801c246400081c004582004805d504036040205104821910b06141c1e404214505040c40f00500c4a52004220f000301010450082008502c403 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 268663929 1250 268662679 268662683
    0x20c040f1a1005070204050709030213060501030f02090901150c0b010801020c1603031d0105040b0d09050709050709180204050d0b160206090c0603090717150606030601050910110105070903 83
    0x554a038036080c02000b10400074401c010010403c10000180541041e4112541c07002e4181004061a03a0780e40c0800c00c0a0318400200790090303038440d4140510340c0c2c2740c040c0103242000c80c603080d17007003001c440c00041301401e0610525130070782d45803007100390039900a00c44400b0039078100305505070943c1e403080b9160203584442d550201900400010496915a122900c016683c06545d041d0441304800f242c0c0741804001c0300d1f998103110040c0000120200d00700c000300285640140c01103504003440c07902602d40595508921441410030b410030800d190701003480d8003100e107004c0b004008450021f1181f8000e202d5604069001030100020005002c044118140605148000790001440310042241c0302e0300300b43c2d1082e00030703044822071403402e260181c0070b0341e0010100400d40d401280e0300d081c1da910400651200d007000da0441038046040740310b42c48403180c1c4108240ca502d40f951130464002081403041d08540c0e07100301d0308032200c2e0000b188141115a4040601e00080000d4209801c0240c0340400c00d20003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 268665179 1250 268663929 268663961
    0xa050601030b1e01140f040222080109081909080318010e0409030905103e01140403050711041103010807171e0f0d0c0b13030c0b07020c040f 62
    0x2081c10000d4002060780e0000000d9803d9042e03034281602500c00d98811461203038442c0090000c40c0c141d80c1e4610044c403992403000c4c829000644414418540c0c4c0880340d0002501e80d24041804010070401001c489040788003510301a0800f0702e0501c15558a2000d403c40d000b60b00c030120b16802c0d001d828004402140e8800d80711b0300c1c4d00303085882c00c00c01556000300004002400420f010061800d02c06441003200c8014202410989244890200743c0c02c0301441d0750a41510340c40211030400945901070000d842c1074402407003403411048040c07403c5080070f0030080800400003240c500f4084940f02580c5900700c020010710040702c03003a1110b00f45070400e002c0d0781030364041e82e440000c51305042c990103600e8140c40006000300041000905001d60030b0724100503014003a018642121030402e12588100ca801c5444030200d5040704d09004140c1000100340405904800303619002107a0401803115205902c110600f50503614001c0c22418000401543c507002400c010032103840d90a1034002030082204242 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 268666429 1250 268665179 268665181
    0x7180b07081c0e0703110409050f0102030708061e0f0a0e0f01060207060203070f0204050612071503051e0a0f02091306090507050a14070c0e040f050c03061603020d0b030a050601030b 80
    0x10101c225183c041c0c100d405030b03101040800001e104543c0006961400504c000b805103066250103080034414151204a07075800820041c05940040e00a034010200b50350700200042160300c0b40c50400401d04070140304401d00f1070302011594944a0100141280840c908000e05010200050881007030280d43c1c00b5010340175011514130705c0003040e500181d4001d81c1c03c00340343d090ba4003400014a8068400d90300403214500c890b002150421a0070000e08244800c040c1113440c003503004040f602c01800c035040c200003011010342c1e041800404141c21004001c0001000010f81103000028815600025044500f15440f080c1c0d0241c44d038400d0302121810740080c4000c6da00c280007141d60740b00d0300000d0b0001c100b14020340039100046501401c7c0b410300c120300510b50241c60f450218203210040360308454079003080040d5420400c1c05c0c0803801d04140150003d0250307082c0080b01d4a10786603603101c0c40d810154041031000380b20085401012000b030000c2c081c0c40103612241041170321032109000c00d49000350402c0c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 268667679 1250 268666429 268666477
    0x306050a2c0f060c0f0d060e101d0c09040f0f05180111030c07030c0f060513060c0c050c1e0603010609061404080706030507051e031501021507180b0708 67
    0x1160a0f4800c2c4d5180515a01e082c2d0000302404180d00009040440385070756200c0071464a4041035010300442d80c5000400e03a0b50f1800551842c01b000701d2004d00d0150040b0070070b1060b0202c0d540c0c10384039004021a030100d44000e06001c21001000d90b180d009208500b00000d10012000301d244084400c080107000344402d420a01e01010b95110640301000240802c02130324010a11801c1d110296603c500102d02c503490203501c41c0403c0d02c00544003285e0401ca040ba9200400509101311621194035042070301d94450b00e5180c8940b074944501559001e010b00d031890324400b440c104d140404600008203041d0b141d50b1510001031010711035004807004642610240103045040d8400c0d9801c0744c80503002050002e0404030200d002c0e02016041000784007052120200e4003041c00003005140b04402c000c0c03912490312125129014000da601603043d5008110700c0d889022104c011075901900d076003011500d1610f968080c0300c2a03d4181d11007250a8404643c02d000c210150380280040c00c520158120700300280c1c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 268668929 1250 268667679 268667683
    0x30912070f02010c050f0f0610060f0e0f040209220b09040c050607030e100c0c0515090f031c020f1612140313030501050f010603060803040306050a2c0f 67
    0x100d140a00300d1160030300408015031040c080f0416540c4140c042d50503213504003020b03500e4a0f40a205890003500404100000030191a00c3c060003016a0300e08441350320b2021002601c00814004103d00400d8240b60840507500c4603011991000e002504022640c80e4414054190341e88100000c0c0c4034a0404208605a00e400500307203005603009003c000301d00f03240808010280e84100380413400d20490380032144540c2d03140c0c45811960207260301c6141504806190003118034500e80c000c0e6104e0030004941d840c9004030701096981041054403c5101c103120350380024034001800040d0400900c40c000c2c0f178528654082066582a070176041101c0201c0f581e1141c0030901c400501402440554040341c1e10042460181c0012610074244144ca240001070140040c81e10481e800503145a03443e001402400303080f0b880c18a005222514081104608024a0710784a208520024000355164808654079181075404210131403040c01d201c05400e060300c010f4440281000200007000d020308230007010001d0340 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 268670179 1250 268668929 268668937
    0x301030c0e091b010c0b16170705090f0d0c060521062d09070c030e040902180403020c310c0504090c0512040507170a0506010614091302030912 63
    0x11070300500f121240580ca052240c41410343c81e181000f1420341464045202c03502c000c2c1c028801c505414103843c5540001034020f00440b50007803944200c681c1004016944007090758450707142115540e1000300c4010008115099407200a840c04c8c8880382e001031b01540250082c40740d1200504145004035603100350031403051040b6000c07a0001034000c50509000500364002c0000d10010181040000c6028007091600e102183c40380045801c902c50003042c51f40120701e003106150221402d0140403180e50100d10410186030300680d41c10a00004501007500a0000d040e00d184090180c0c0040f00c840000c19000c1940d2584034801c403816a103e05402007803601130030300302c0038150f00d400c0e140030300c0d280d90b6000400245409604018040c080009005094481c8900039401000107100003818442850035295100b03c0e01403c90344040b070140c000441c04284d250440c1d1083c100341e002c441603840052464032501c00b0650f070041c07504010307015125032540031f0742c021680078080f01d80c1075034803c1c00030702c4902c5 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 268671429 1250 268670179 268670191
    0x801090c09060324021608090f030105010b09060c071206060e01050603100b03060102101a011b0f030f0306090e010510050a050d06050a0b0915190608180c03120301030c0e 75
    0x40050b0030144e20829444041c1c01c00108000d00500d4070b50200203d0359031020351401221016800948440285001c456458009104400030003855240c0101405144074000420303008290200d403084807600140100e10040110844410f448105440c01d800180310303500071800400c4080c4000314403414100d050700c7c0b0905641da0600c0302c0c0c80c1000d06491154000804c030604511682c80c3c50203c0304442d0058811000d90009240c040c000d881c400504006401c40780d103060a4010300b940400300e503500016042a81d0141000c0c0000740d4846021000340c03d1582040e5501402c010000901050540c083ea12070b900c070305503040000b9180c10821030002150300c1741c41d42c8071000d030b054503020a01070790150703810418246000440c1c1c1c4041002c11401802201c40c000465100e00324150141800e030440401141001e000030f5801d8181200a006030101070501400324034001042c816641d0700308200c8a615900504481e01c06401941040c065442408100d4206c14242ca0008d96440300030b00041c040d41e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 268672679 1250 268671429 268671443
    0x6140102060703270b04060b04090819090b0a02031e031e063006010503150a05040f0c2310020303130c030215040302030c01020c03070501050c03070c0801090c090603 73
    0x600c42038000c8000d80510794482041c4e403104007030381e055500d24072500c140c0e840c81404885280d01e410b040c65000c0303400345501180503038100310b000c4000881c0c082c115841428440c160001d0720b0501b60741111600456040410700e000c0c00035000040c2500000030301903c5ca984292141101c0c0500c0d10303802980030507101c4130144469007980295040360f01c00c070142d0200000e01401100b444100c02e840282c07541009140781c003412110301c08561402881164090a01031f0700a01c801419035070345051000d8000e004003881543c0e94046010840c041e0312940c4840d821030030300d407881901d074411052500c020811038001100f00e02540c00c1346090041040000940c141c025506642d28424090750140030701404403126041d00c035021005a41e00700010000e43c03011840d041c3c541d411881494500441d07042007030b040d0340c458411000d580c0d0700042c1c260152070081c40d0980e250390924521501e0340c0900c0c80000c0c040c81c10100082000e4005510404402e402113061205a5540b01c291034200c80701e0f800702402e10 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 268673929 1250 268672679 268672681
    0x4030b0c0316031103010b0d020c03040b0c060a020a1d061608030a061a0304060c02120d050106031a0a061202211b121b121620030304061107020904050a060614010206 73
    0x2044d014003c4d1640740101e50000d49483c9001c181c05e2f09503403184d000840700120220300b0012001003046000c0d03014034072180451602076140c002801120401c840044800e010f4003142c559611001c3c2524070500c1d074900d42c440000e440d0b00d46926a81c0048a607201254034140000803032801c00c2c0108a815030340f4000c021700c3c6480b01d0315401c000c0e00e220100744055200c5c0d2131000f5031406500c0020319000486010006403541031800017400c1d106903070f5059915240707540b04150b61747e440d03000d141d0848040d8104036081c40d06507418138010b0301410b400003980841e010550b110860705010910710905807511030071080605840354601c0f50040342c3c0807150b040d074840001480c503e01001c032a0061302e0095807a5042c01c0d007006180504c080100c8119000c1c10201c5613600c903490300300c00c44000d034900c064032210f010580d9000caa0341da404020005441e5a807160b1655841c054100c0441341c1c0d054000d89000d0b11841c00c0e0400a035191008030b0211030305403130310100148582c0b0a05d031103041c10005034054089 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 268675179 1250 268673929 268673939
    0x504060b060a2001060b07080408010b040905031b01060f0906050f0d0b070309080415030e010c0f1407060b03060702032101150c060e0f0f0c0607080304080f04030b0c031603110301 79
    0x1c01105500f9074001c41d0b40e5410046510040300d0044c3c84140e2080e4460b07945e80f818801150700f0745101900090243e820212900c00040012050320703103d100d2219103903259265142e0300c03401340940354480a041d2510300c0f4040384200d20f54000e14140c40c1e090311024140c49907401800442040c200d0b026281c032605101090402d44260426060203014901b0a03083c43e440d001d06500804007801da00780801c0c1d8500310618803038021300504000030401e04280419500c03112001d4640c0141600751340c2d51000000d0507504100e45a44a0b0305015005401c55555241802006c0d541c0d40c4055200c1700c61880c00b190301c0c600005400310742c9040c1c448600d0b44105842590384151900d088200c0104c0d841c40c1c4036145220b0b0a44200302810042c043c10000701040e00a061100d8108903d40d03a00d81e001d940704009980c04a4850000c42e41c10a5000031925695031000512019900940d0070050000d46400c0c14071498800b40000745009d84041a180c108284640100350b00703c40e2246e5810230510300038001040 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 268676429 1250 268675179 268675217
    0xa0201021204051c030522061b0305040b090a0b160312110d0f021b010b1005040e06100203190201050f090109020a0303030203070e2106010e0c180a0909060504060b060a 74
    0x1202034402d042c247d040005842c10ba004007244861140301c001d0701c1103030030130a2030350140c08107071030895010031680d20b41004c0e01e000b00385101c0c50080d0041e6040c00140b040c465140e0900040040032114110f6884150440c51750503495107143c0f0070b0340013074510106500d900c000e520400c4061105c0c04031251400300740740b00103400780107000802d160301c2e0742c24000303400210004401c00308000d150340000622107403074a007003000154041d2a24000c0080a01c01407004400350000d45401003011114a80590f010b404100e05e180b080100f40c850b040c003100e4040304c0181d015080a07001d4001291081d81d01e95400101c682210300c04030020754070242502040002c04d002c0d90080da0081054580111055040d00c08038400051202d00b50004000d030f40c1641b030516000b4003040f405040a51000c00e09414040c41742d00541c018041700700010003440c51000d81c142c0e940d0302d405005000b540824002043d450810320300900f0211016100c0f1801c15641018600d4004100c44035074801c9e07101e082d00e008560030701013 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 268677679 1250 268676429 268676479
    0xd050a05090d090905150d0b0405010e0a05070e1320090105060702131a0d0804030b07050304050706050a031d06090f010b060d0e0309040203090604030201060f05180901060f080a020102120405 84
    0x51b44146401c011613a55803205455549194015600600c1c2418a854040d0840301e4013080201103030000c0d07100300001100410340b1822500140b8100d4039544480880017189103582c1d0300208922101920211803c03030038202c006660004803601c1d0704c10780c0c1c0c4005000030f6114040009620000d0028010008400740c0e1282c100ea00e01d4442c04414040c40002103102e044c2140d005407a544800324040007007009200713482d6030180c40ba01d005429410302c1c3c0c0d41d0640e591020f000d0395041c0b000110305031404034400e40c0280b501000c02c111050444001c994129100d0600b44ca41e500e613406144e2140d450403005006603040345a000d00303000e1500d429850b1450017481000b032998624041004050015903e900196003d842c0304009803443c2d01341072a0281c01c495042d803208802400841040100b56620400c0310b03e404822058602d00f5079882c0340c510700400442d004003803104403541005c40c41040029107400c98a00c01e03000c44001d1102e5140601143c011441659032045091110351402140b40001c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 268678929 1250 268677679 268677691
    0x19020c0708010f06090f14060105030405010908070614071107090c0903060219090806011805061f09082e0e15070e040609020918090a05030d050a05090d090905 70
    0x40c840c800c0c0c0340c241c010700303543c24004a0121a0344a5a00b40640001840354202100d1510303000c0010004016500003042e42c000d00043c180300c0c000c000941031100039000403095990040800d03555440741d207020401089010001001d003040d140c001011107000f0f1207641c0d44209082c000301403a51419000c00c0207820307102c00550030072a403104000002043d49c00a0045540340c481c07d006204540480103000c0781ca90345c0301d483d40380d200300f0040140c00b04402008840095100c004504d655903580840c00b0100501000103240900314001610030360300010100c00d4030f801e903041e80c0098103403156840f6244c40c100456113107800c5207180c01240036a15030060141a08a0003600c1290b0450042911041c10441d00071000c5080c20300580ca041c030b0b152245a01614404a085061424000c082000151402009100d0754074035000f15915460421120900907405030881e41e60b0407035185490040c100945a007041181041c01085800b100480e0a00c540312084e03840e001d069203050001e1001e402c1c06010 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 268680179 1250 268678929 268678933
    0x40503070308040501081b04030b041106072301020a090e090a050d0504050a0e09030a03110f0c0109060e0a0f121407050d09052403060310020a0801140919020c 70
    0x545480610290000354015650030b921545004c0c00507010450003003603940f20b5800b42c0780301d200500d40b810a03142079940001e0414882d5a4610307101c042852503200e00b5901000110b4080d00300492402c01c1c4075071201001c450018458040c102601b80d0143d29140c401250481c841072040700c41c503101c0d09a206803590100e0f008150350351070302820941000200c00000d800042e0030721050a20100f1440200f0020030003041c2403600c074081c65240c2c060320340003000300b42d103494604028018000c00d0320500005840425a0f0741c04c100d41844c000c020380d4008031141410140e645404e80c501080b5004540d0704109a42c01a5440d55039000c9129a00740b00e1001380641032244c0d904410040024000480c03280c0003c0c0100d410409018009020701d512042c401c1c20f8482c090352030003510720040c04480c00f52101040c3c4a0700c0341e01c0024104400820200c076000c0c408600026241da01981c80c5c0d04982240b1f8940782b0002c2d0507014000115011502c150b420f005012002c03500c200594002d1444400b1311003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 268681429 1250 268680179 268680187
    0x20f0603010e04050f060106090506130902040807030c051008010e0a0e06070e090f06030d050706140a0902091303020c0609030a0506090105070207060203070f0f15051f060305040c0317 81
    0x40010400d4000703800903115039500c50200b20800804009111505803400014110382d8500b800041c105d601501070f40e4025100814401001340c4490380c6003010b00120f01c025074032261610a0716603254101e200c1590320402c078074000141c0d820108000a140719285d910350300075a082400c102c80900d0301400099041c1d64405003907030040c4051040034050352107580c4030189900004200580100060401222214203038103010b042d42d000114000d0001140c203000d900c1c1c41701c82c20312130004d0500ca184211074031848000c01c0008241c581c042c002c414400c0b545004039407100c18059084070030080004015038400c0032504064a031610141083c010001c2c03c443e412500e03030340e8086c1060b40990b491030350b40c1c2d12241030014883c1c05121001c05080b81d0710046090a0840d2900740c0380050651010f03001c5046200703c48184440911001340140b0000014050750802c5070034003180300c609011000c480e0304040408214603100f401064011508615a001a1811178540c000001c1343c800c0222044c040400c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 268682679 1250 268681429 268681459
    0x6060705010204121a0f16090e13170a0905060d091202010e10140a05071e020c01080604050705030423010e16060905010807110a02061b010c09050a0e0402 68
    0x10009002421382801c0010000d1214500781d0b4812082c00c00c24012510341d03a00700141c5040c8110031507402040d446405040c00c4112409035103800c515040900c100000f074082000c1e201c07202c20206080752140500005107140340710005064044c0d0035404c1c000586521307081100345004405403021425500c40040c81c0c1a456603407007202081100d500e40541d45038141000d8115052104100c1e503415003100307000d0b110314071000039038800c4024110f80904e03a039900824038562240010010f4101e410185032410703650110080d6542e850103440700d0000700b00000141c4241010f01030140241e0242d1640c1e41180c55540d2680207402d2401403044030b80899041110880c50240691180914044041d15560700f07028060400c1410903002032091160000c010030103642d0000c0a1a400f5007140f40201200185551a0703080070348850020358082720106840340110030450f180315840000f50000c0100c2d5040c0c00094401d15001e214803070340441c02d00c0c810001c0c8040c5040d0710303034086e10080003d034800003c1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 268683929 1250 268682679 268682681
    0x20414040308071701150c060204050306010303090305010e120a120e07060309020f030604081204050a020a0603051510021e011508070305060f04022b02040f0b03010f090b0402090606070501 83
    0x32030342600094800c0e010b209446812640f60001c0c0070441c9008186907040100e001984c2c10034941140821984502101c144000b6505035400b0301401801ea80302c40d43d490500400950060005a403a9480c0070500e040000c40001d43d0007440703c00307503495420101090000c0d110300c4482181c640385140c40318125020310109200000c0a040d55442c0003a07541450700500019810303686c42c1e540070341e000740700348008581c944d415074450708402d00c05120385030348a20f006800c1580641c0001d4000c40a040041507040c0c154000c0e03071180300c01c07926040055078001c08000318200303100e40540258000354402074414200600c08100f081c0d440c800030032041c0c43e110b401e201c901000d6020181c03941006000780100a01031050039005511500702481d682401d800040406916040b8504911404801074014500821051031010340051080007042c9540324810f01400e00c12100f00c3c0300354a842404446400d0520400040c107400c0140500b05540d55403d00030f4002d000390410f98401c00a0084800044003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 268685179 1250 268683929 268683931
    0xd05090102030109060605030c040b1605030309010b0909010c17070e0303030903090301060503070e0c0d0902030607110d0212120c04050a09020406080606030105220f0e0a15110313020414 82
    0x240010707501e40c9405054411281c15070442400c11504000b4028540c5400081d00d0954034a0010103a6484070088612800104540000d0942c040401044441c400642c400240d42405417150f03250f99071744910040c200c810940306000899090711656000f40c0001d17004e640d0140060901e4092181c4600010345160412500c0783c1c0b05510006510907581402e0041400405058008141141c107020201d040c1210040a21810b401d010440d4880c0d4842e80d008000e0741600902038480300d0a00d07e100070503103005d00c5444406c501c40d208484002603c00196800a0441d80d410542030000c0e540101c1e0341e00c0d9001c2e2460220100600c408900c0f959960f48003c001e18a800700180e07511f103004030107001a980180414411082400108070a8030760032043c1310b0813685680403841880040806e88020500c0d08914011645410440200041d0001e0007884c120f0141c07420920400790041880c0586d140c3c40b081c0d401c07000050002c030f00d64400410460f070007140300810114201c041140d0400450708 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 268686429 1250 268685179 268685191
    0x302090307031b1a04090209010e040c030f0c1e031d0d050c1207150f0603080c070e090109031e021921030606091412030c070812030105090115050d05 66
    0x71008140d0500b40030000f8150010304100b5000c1c9000745000d100383d21030b8001d6124203840247c00103422407541c0c2c4201d50509840100070000c01c000c0d0b00005005004200007828440d40d280b0703100304800d049000e840640180c581e1241c3c81080803a00000c114003070016500403001035000c3c42003000c4042c50a0040b01a070001e40d6482e140c95440350100545010802e51558100000401500002c1a041f4170051900c030540e0300003040d44074202003554020800ca6002900a03000491503861114020078a58201e03442000305603030644034001843e088540260004001c22900c2c06007000780090340d62150720f01205401540c4615105015100304075162510403502c1d81c10308840c1c030001e5011110748004a425500d000c100300c50410f0009420300116000c0c1c0b0890001400001e05103603501200b0514200e001000d41c0e440d08400c81d00103690703a036140240805809210101600c6103c1c00c42502c0c101e940003000700c80d0592030008800e80b000c080340c0f480401c01c0410040d50100d90898040c181c0244 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 268687679 1250 268686429 268686443
    0x5010b03031b07090b060703141b010c0909060b070f050703060e0a031403130b06150d090203060c07050c040203070309060515030607050c03040504050a0608070806040c0b28030209030703 82
    0x4100c2c010064100401604030b1040c0501c0d101444005840e070310300340d4800b26410706020380180002d08a00780356004800040e0448080c0c0711029044c0d600c10740005900507550303182c4900c10350701c403510303081a19000d0048450142050200c1c0d00401c00c01c0c545401607a009506603051603441e0345940c0150f0342c4101105600307504c4502d540040690040100f01c60380301c1c1010181c00c40c142607103035145501c21490301404c164412004103006581b2240191000c00700429a07503941c2c694910107002404298034203a100b800f90200080b1103002032012542e1269016000d03000c44606501003200a40018140208143d07441030100d0016280f44250360045150416180350b170044842003601c2d00e20000d201c84c0c208101400003440612001054805459017250041003a41e64404080001c04140c1d0020125110701c0f170000030b9034600800c0135400360b40a450010412511140741c2e400ea88138440f04002024600c1c64803803032040d9940c0a030000044103190140c980300b16000000d2070501950002d0f03600c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 268688929 1250 268687679 268687717
    0x120a05010503120301081005041e051f0b011b0c0302090406050906010501390f0819020c060d020d06030605090c010206090c010827070e071b0c05060705010b0303 71
    0x42d140801c8107401c80c0d00640101c03450356051040f01910341d80c50710340140c42c0700e4a48001c07808101e411030702d01a4032141d0310302034138031000581013090b80d0b1282e4909040c1c0c1e000441c0009044080325008011074030078180c4030312440c00c031003400d0390091000884090300d9101403e6008030042c1d44400f030003400b0740d010b2000444c0c9030a0000a01e8241081a404030381401000c0347c0c61000300344c01c4031038550b046054401480800751040b0449031007001c0c808008064003030b0040418104100403000c0c040b0900c400500d4600c5d10341441080e80d5076a42d14054585c08141403041d1940c0500540040005903230000010a001e0b1b520394405050b1401694038804903045010b82c0c48070780d40d040007803d91010f0120000e11040716290000781045070040c00040303a403039141d00d010f4041b601a4000f540030070030071002c5412442da628504980b400d000d944603400101040781355580e000d001102081d034031350010759180e0341910301420001a81e101e00b100300c0d925503c0e000d2801c81981e050000d051461604600e681348 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 268690179 1250 268688929 268688939
    0xe090a020d1e080c061501080105040b1302070b0405060c1c0203070509040606020304090c0306120803131a0121150510051302030406051303020c15040e040c0303111b04090305120a0501 81
    0x100320300106a10740e400c045e501120011f81e0f100d08442e044035402c3c1c800180060b00440440e00f2422500c0c404c261450000800804020482412611a90045050314030a0711050081c5003103128009801c800c0102c1c29000a590925aa0003190000400d05101c0e14010500b000706c2d080d500701d80d011a001d40c1012404121700e84075400760f01c000031710f14a02001100d090900c20918100f00301d0028051540100001d501d07d00100340905401e03400c4907500c40c0100c045400002040024011038000c1192903680000443d403600904421541c0a20030224a150300c50b15079004120041c80d1103090803170010005034640362094403803001d40018401680d2854079042030400c1d114064401c150300e1841d98034079170119034042030110031040c0032204400016500d480c0b82c4d40b907003d20b03004440303400300c0c48040c0020001140059000c483c0710b9160f0304d000510f1042259154010b1828658003001210512001c5280c140d000070326961083c10a02c0c2030198a0340c6c3ca000e80b04045813411882d0b03981c0c03001488 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 268691429 1250 268690179 268690183
    0x130603060c020a0503160219080a1203090b060108070927050106140a03050a060302041a01020105090d170a020c0d09061403130209061203160c0e090a020d1e080c 71
    0x80000340c5000a1204550f6603032215640e11440f10703020840b00035189248111340d81c901541603a200410109450244c88000003610307800c1c401011039110a10bc2c0341014403a009001e000c001070f4003d44100c7e60360341c8503030044da8900c000416000c200440184003050701161103104044481c504e14034900141082c08640c01113030360680090040c0146024000c0c0140c15620031645004900d1801040d41e2322920601c0001d041d90f900029840f500b031803800c0280380000c40c00e07045c542070240c1c002e2010740c9882c110a5110f1694880000c00283c5000c40084c90810480d02c8030b0700000031410051801444151a40c140004080383c40e001900080301041309540c06645c5000200e02008107610314240750000d0000480b1462009000e1100c12000624076a91420961810031034201542d95905240f00b0911401e42c4141003140c0e51182003801107620086140070621905485000b800c0070701c6560204250000791500494111210a003464400d140c0001412620341c450b90300180c80f8041c0b41c101034 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 268692679 1250 268691429 268691441
    0x6050109050f2202090301110d15031e030507050a03091d0106080f0402040e01050106030f0f0b0306220611030115170c0a09080307080c0c0607050606100e13060306 72
    0x1841016100034000e19a96880c40061100c08040709807007496600d030301508081e0040c000000d1b803551905800d00e9440001344000c0943d603031042d508202840508064006003001400050107040c0c0d0a150b8540c0240f0070089100454001d06003076007012030695409180c54407201d421400600c855034200030581288041c06c80707015500c0c010359000c1d0304010009104101c020203450b0499030304c90100c0c2c1951207590003402c180803100000e00c02581c40d00300c041c0140c8a2a0841d40d0820f00c2c007907031482055035904c210720712910010041d040e541c51314030390508000c09804d0060b8840b0b101000f2000000c805100d00300700322884180044e00d940c54400c184000b03904110a403001d20480c401000b481a881e00c4526030701c4000b907041151680018034045034210035a070001c0c280e0b44400100ca1091121030300250960b0201d0604440001d1510070920040380a0385c00010035592040c000301d180c07841c02d00c00c41840101d852400a4508450000281010402c42c0e115410903a861005206004950180e8 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 268693929 1250 268692679 268692689
    0x711030604080706050622062301080105040f180b0123010c0f0305040f0902030406150f0605180a0311030c1002250509100807061809020d09060e0106050109 69
    0x942034615242d2119000c502c00e10390010000c0d965000041d0721079903640036a104145681e4090060710103c0c44000b0014060741c01001004110031486001086022188000741c20042c1c0d140c8055910740001c0c00040c00c01158140d080ca521007004c0780490507041c0708003041c0b600408020540d545403200d5418030003c4d42c0c1c3c45a10f5000c43c07082d0188142d07040004480361716400020b040d4081c825080403202c81c001c0d90046e0100302000007000840b8801500914011400b601c0200a0b200c5404004004690548512140940840810080107000f070010b04841c1c000c0050005052840d0310000d01d600c402c540080b2060544041281e056050130401040c03500c0043e2034142d0525603050010b07540b55402003080c00c80310708480800c6440c0302441c095000400f405010704c101414010408041034900340a8101b5030b214007100040c5540c030840403561103e079421051107a06007080c1200c000b030350021400317400207030b2103900d408005109442a2000945074200009986052000051207400b0952007 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 268695179 1250 268693929 268693933
    0xe0304180216020d0203010b0405010f0302120303090d1125061d0603061020031e040b0403020103020a1803060f06062102070f0b070f080c03040309061211040308071103 74
    0xb201c0038440441041c0104150100c400d1a6141032520009001d054060016900241020300000e04000d0108560b8150384c402c0702d11003511070148a61590300e000459860600790702003403003014528001c0351316607041d04480003502c2008100700b01a01645100340301081101d000102d0410166601100c039031051000310341c0d10351620b0040c00016000e4080030704040d20500c80189038402190084021652800580034400c0540980444003a140d401101d010200d41c048410003401811895084806481100401c1400c0504580044000b508110740e480244241c0d10350075414405c0f80400100214403c010110b001c0019aa85c231069030a55800340d410f00c014101e140c041e1300c80c07402c4070300c03081610940c0c0180c96038120b042190482810f6030000e03020003540c10501c84040e61058804010010545602200e900c80110031402480100c0b805000240804000c0c0700c814071400c11950f1400c180180400c0320500942c140409500503030040f0f03088007000901e9000c0041c07006c446101d544080780 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 268696429 1250 268695179 268695187
    0x80f01080a030c060506040e122802070b0306040e03181507030e0d081c0209190501020604140705130f0b03010203040f0f0f170a0e10121107060e03041802 68
    0x60b0192a4030a80341c401401c0e00e032110001046603d86070301c82040d0302100b80444071207070003040300030215031b011014580c4c80204c0091006000510b50035000280507880d0300900d001031070495040300390780010f4289a17000307840c1c51681b090350008002030240d401c0070700e0f04190615050410004524003950683c01040e005000f5140840d80107444680030680540398001071883ea850124814801c003c4103807110400c0c0400c1c01604207044c5d01500b00c04000b80c809030003681c020319040ca2910181d10035207005a2001d400500040e1040042c03544480c072403000c44038650380703a2000864940910000d0b03c0c03181d80d210001e68652459000b002c9000030254021131039810161118203c04001040180101d400d030300c801c8040110055402e8400303600801c80b0348120113403034101c0c200707a8006019072000501c4201ca0207000d02e00304004000c1c0459989544d00c02c2c1c0340c10904000903003030001e2000c111080c140440d9000c030f4424010031040580010156a80c2c2c1d08003da9009001c0418078201c2e08a0b1042c4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 268697679 1250 268696429 268696433
    0x606010e030f121b0303010e010e01050301110403121709030a0314010e1602030c01110d0b03370f0807030906091406090f19090c110601090905071203080f01080a 71
    0x41105003100d00103c09030341c3d0b1a0180601c8075500460041841054030000000140d80700c89400402d050356041011210180da80b40d00301800c3c2c81c0c9070700000c620b0385020401040080e008800308250300700310b400c001e010003565040c3c41c0100745044030304101381d420001e840213080e94188180007507a48500a14411541071508a00b401c3c18010100f0084e50541c4085091550003041598154004403000307000c8619840340d44078040c1c02004c0c6140e02d450901c08900b0305441c000c541360030402c00f0290f0355005281c0340340260304a0b4424101180c848240c4001c42d1000c0b03102140703c1c0701060300175200305569552034070f8010808182da0b0712810800c40311500603c5600d004510811711030380300b12401a1515960300000d030390021421620303a484015070078821030411300741301c085044880036401040280b84512040d00c403c005007c2c14000d9070040c8005028001c280c0e0b104940d280c0c0900211190184c40301d1100344602c2c2042c0003600400c240c034080000040328070b11050b024080e108040c00e03981c0d4480d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 268698929 1250 268697679 268697683
    0x10305071a0c15090a140c0114030601020c06090f040203130b01050108040305040303050a112a0618040f24051504030203030d050a0f1e050a020301080a14030f0c0606010e030f 77
    0xb03d54090b10810380500402c0900c58100101a6525001194149440034052007aa501d10203414042c0c042902c03900c102a4050300003040c0ca11882060300680400840181040920380c05151101d6100a2040070b203001d58444e0b04c0514411a113042035400d9400c05030401c0089024140d10050401903901c04100000764003a090f542181c2e07140c10907548699440d41c09481071240c0513084031203841419142900c50b0125008580c1c064000b0350807007100401e00051240d14270810094074407050f2041c101c4901401e2681c40883c148180d0000022120701021300b407200c0e54a9505115141c3c50603007800d2201e45000007007041079025015020b442d041c503550200380c903800350000407602140d49200003603000d0100e80112815400e00001004440001e030012030654114080b41c40301c1e5890000081c51009d0a032084a040c1c0b41d0000040103200c0065641110388182c032142c1c04041d0000340501710912088101501c048064031000e00b08a00c3c10700f0005041031200c040452180e807002200b0000d400340 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 268700179 1250 268698929 268698943
    0x31401020306030706110705100c0c0902132903010b040f120f0303200406020a1a22111816030b0105090d02010c080f030906070212250b010305071a0c 66
    0x5d64149002c482c94440242e505044103584626000b203d2402d02010f003940c040c160030a2144510288400b0a0b1100c0c0044200e0040d5200044c00030b02c16007041c040b10014291403048814049070312040361403566114402c130f400a91100d20f0f1848042010320140e0f440350154800391040142d0b199440e030041d2a40482d60000700d80c041d00f03240e5200f5882c150319541010307108040d03003005c5885036a00d0342c94a00a41c0e40d44020b170181c407402400c20503480b0f9110042d416601501c888000c030000351000e249222030302090418111007050030001090520745550840041c1407050511500003403400d40190440644180700c0d041c10940b03892450030160f0780020a0342c0c40200103498070a0850310f9440141d071254080701002c0c040c004046084101000c10200452240c0c00c41416507a0380d454110050303070340302944140021113601c00e00040d14458112800c0010002d41c000444070301d0328058072440b5246000b138205481c69000080c090219010a074041d07803070401d1000c072462900103508441034035401 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 268701429 1250 268700179 268700189
    0x1107020a1712160507080f0114100302190e07030615030b01090b0307031d03070203010c05070c06210207050d08150603060f030a140c010806040203070e01180f06090314010203060307 80
    0x3404120f8a045903000000f100a1641c410201c5030813584603003080703a40f6041545550350035820801500204041404420f0040c006002401d003554195420442d10711103072040e0490702c540d074020001da40000c002d504c40c09081103840010781c860600070650342d0300b20034821141c10325091950515050740d10055210480341400030f078544940f16044101c018145e00380000c004d41599401e038110070080400140f5403103100702d008000505c40358000341d41c06d00a00401806c100c0444108000190103403070034003083c42e00d440d5203034002455011507400700c0c3c1152000351000e52211405070012a04010702a400200c181500d0307100c400d20310006605807200400081c0038400c0556100b034280c50070041d0001603584500d98030380d80044c1e480410360394041c0901d1700d03000800c50f4010499901307003442140d008140990b914070742d4482c0200155012402a00400c00340741d50345100140b11540f180f400005440c1a503200d06da590329500b80301e422074250307080241490744100709001d819607000079682c040712 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 268702679 1250 268701429 268701463
    0x30a0b010e040c0305100e010506030c2a0f0705030c060f070204060b030f04030e040b061801020a06110d0b1005070210030204180605191a07060204091107020a17 71
    0x100100403505a400c11501a80150403c0c40451451350590441c07445082c054000c60b840d19514492410854401e116180d041202000882c40c811041001000d0940068401e02c082602d81e845281180002d0271440032150441c40d800e82004509001c00300c0108000c40081020700c44007400114144035440c1c0c3d403900c169000404d20119104c50b00300030000c003645004035440c3d00e414a104110b007413044038100c0016225020726540c5103440d114010310014090040c6003458000035482c11504e02d000c507118198407800084a000590300d00540a42e81c51510507251a800d140c00f4103001d5030808201240304d8003840110f000700c10b138408c00750b605085c2c0480e10540e04118003001030f0000d104a0b00f050710240b8141c48014600301c240d4101c00c04580082c0e81138940401020441800180c8501500c50001c001800441640c001c5d80050302001d4004d04005150907030b282038000450723151584030150300402040c0d990039440c0c000c8a5400410ba6600040041aa480b900a46074600c3d2010070008d0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 268703929 1250 268702679 268702691
    0x10f020303181c090302010f02010606080a02451203030403050307050f0d0902010e010c0b07030507120501080c0a050114030705030408040b0a080f09010204030c050906042304060c03050c030a 84
    0x8001d04104490140b03d0680814960300071900f03000380045001e000503400724000c0c41f0312616041c81407040c50101e511039a00c203409501c0f64080708020390702c8071582c000b90743c4c0040c1d8030000643c1d031000e40186041c5407642c1c0340101200302051751412040e501c190f41c8030360040300401c0d110380c4000c400c49500a60600e04256280d98079001500e0390301070b18141c0c0c0c9a80c10302180b2080814450307800400303554002d0f220340381e107002130000450320704c1c0c0341d800e0092400b880c0350041140c05000340c00580d0800100e0034040040c3d20341d40490f00c01c4401c00d07440464654440d41d00307401700d07043c8441404050b01080ca0f00c1084987d0740d01007031070940b00c0a0300c203074104400000040d042c0f000310320544003d8450800400d90311555180010f01c03100d8286c07180c41035407a04001045a890051003101d048035840071400d250145454200242490010310050b0403c0e100c58018602d03400c0f0303800c3c50101c0464801005018202402c005048900403810b40741414681400e025800424005607640315014000200b5a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 268705035 1106 268703929 268703971
    0x32d060512030a030f11130e16090311030c062109010e0c010503190608031b070608060d03140406050c0c0a030b01030f05011523010f020303 62
    0xd0b8030400841e46920b00a420080703e07004a03050003e01744441e052104843d60001c1d82810071007106007020b105041d00603078015000034003503060513919601c013000681048440d0001800c11008a00b8110b5566000c2100c00214800070b00410b4840440070485803a440d60308980c228030f0304642e03001424464051050341e80030007da00041410425420054505610241584500c0103e10f5152148684980940740087c140d20005641d5104c2c1900d40700c1e5042c008000013003c80e002140308102583c3e00041e91900f1082c202c441d408608424501500e0780b6400803110745000c1e00108000800f80d810a0150401003408002e95410203084000c001840c0e20a02000f800590315200500c0442c001c40d06110303006120740000500344040e880b8400e582512584040a0000407604915800007001264100c1d401d083c202140c3c1a898800080e4490000808100c10041c80e4400540 = true := by decide +kernel

theorem cover : BRFrame.Cov 268525179 268705035 := by
  have h0 := BRFrame.cov_init 268525179
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268525179 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 268525179 ≤ n) (h2 : n < 268705035) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
