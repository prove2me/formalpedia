-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3744
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:33:29.502137+00:00
-- url     : https://prove2.me/submissions/dba9be97-a174-460c-8e97-b72c2d4d368b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 673201438 ≤ n < 673381294 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 673202688 1250 673201438 673201457
    0x1e0909060604050916061218060c08150904151404030903051c0f030b01050903070306050a0b04150b030405010b0907030e150108030901050705010605040c27120b040c030c06 76
    0x3868580034550788a1056002400c0c00c5080c03c405c461700702410300c1113106000408410f03414801494000c0d21348100a100380840030b0b29145440303001040005c3c4106c00041208002c40e551803102514007031a100000c001c200d6030340300c80e00e0301c6507003082100385141e0596550382e03000c2c2c0c107550f8440020320540c02030300c1c4c120a003840c40c10081d0a200c901074910307a00c80040692425555007241c14000d00352901c0c6000550b01030340c0401660b5910450800c0e61b45842080c0d000000c001c20f5800c030510500e84100d06220804071401800292103070100c1c4071314112460700080c0a008a02c00246501c64010000070850386c5208021070301c404402c0e503501c80000d44400044100000402061401d00c2d00010311010300d615054005849000c0c0d01d042c5410440c0001c1c140007840404d4104d03c0c040c00c40204104440705d4040c07405400c0501c00b01403e10740203c1c822000c04162048064001103428042042c0840c401594810340101002070003111203502c03206000c00450320403a02d040c00b5280036151314014 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 673203938 1250 673202688 673202701
    0xc0a17090a1d0c031b0304050109022112030907060c11040207060e0c120316080c07150f050c06012606040606050414010f03030f02030706110306100216051e090906 72
    0x840b200034421000c0900030020302004c40d2001c8414880035080034116903c03620b5502d4811701500c40e150b000303540131008095441c02071a0804c007003450314040d0f40881c0d80c0c0030504440520240070032900017440e90080340b800c002c400d0050b2440550039104000440030000f2040028017241c210070b005460040c9d0b00c410451100000300420b011042c0304a84a02114540c540f28550743e00c1500b42e155a000b6010300c1c1082000031020999101000e42015114074a484403424442c24060150580006c1c107a072207641c2200d40114101da62010007940070b4520307a03080c20125501d1034000c03c510031405900580c1048805014400c5902407846500c0109900e49000c04010560b01c68004203500050f1100042017092003240c485c00840c1c1c2c0c50708141c02d2104600400b80e045004260024200a0807c400036414180300c0c00154440d044c100c80303903084002d000000301d039280c4141000710f03075500e444071080c0140e03e00308079010130314004d900c0d000c040b20441c1004240388250548039008140c2c080018800c9 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 673205188 1250 673203938 673203989
    0x270603030201150909021f09081c0e0603040515070509030d08010303093002030c06131a03090c010e0a0503010c2c090a0905010207140d0f0201020c0a17090a 69
    0x40020207010700c4441010b40000d004002a644c459089134096034200d00d0303603030180c0d00ca08c0080c8840c07015266402c03904010703100c2d02d078810b10541e0f0014030785003516449860b120003603d01540e0170000404074112002c2846262040280c07083e01030040501004003da42d040201c91913038000c80e40c03405075a5140d484c02620080283d040440007080b03021407100781e422200740204000c3d040441001c0d0030000781c00402d040100300300e50309400a90014000e2881a0309119140c200c64050103080c0c880d4034403201a000038017090310320030003680082d2078001132513116103080305410100501c2c002209030f603180082d017101d00780342030f800c04603c1100a42180080715810340e0410000c80c0c07404101c2e074807003c0c0081e0112100400305030703007180d4070f0102c201031020950554482c4d6038840701c40c0915450300c0c40131a80c0e075250340180b2000500182c403000350741803042c003c0d1180611183d0040c085030010395220441c0034107116074422000c2c801d110040c26a504c284044004001d200c02d040e680c815070160200 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 673206438 1250 673205188 673205231
    0x60a050a0f0206090a0b0c0d0504050a030f050a080103060902031f0f0f0204080304030b0a090803040b01031e0b01060c03030e0712150905060411060702040608032a07270603030201 79
    0xb5904100b00304241484007150214040d46c1c00301282c21540d0710b24421603401d00803d512091030500d00010802000000038040724494000e0b00e401007850a0518101d40500c9084260400248a0742c01000002c03019001000c44903c02800d460400300503081d080e80c90000124850f6019440e000700213a00e1440f88242c1c021802501020340c507043c00c04900d0303640c0e84140c1c440101840e00840010b0f180c54065404942003662260000c0e07540d080905105589103402e0100342d44011800400320003680d5805102032030550300c00c2d50003c03180e03e401006da521030600e0b90290103158451822040d01d0006002020241c1200c14652808030340e07034109200d803801305d8408110061701d400d0700100800c00000d8035a0307100d5881203050900c0031240d000300300c1600414170020b40040c2880b070041240d0401001a24114400001a15000d40c081000c0c2c0c2c203880c00a080308810b5000a1030600c8a40c80c0309a2000d04001c03062410091245203980d00030446a0307070342c000c2e00144d548510581c1540c40b49060003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 673207688 1250 673206438 673206467
    0x8190c05031207050c030a0320031311040b0a0329091c1101050727030f02040207020117010b09010f0e010806040c02010b03011e060e16050a0905060a050a 68
    0x40120215038030a5660301c244401103001c08605030018400300c2c410030494400c50000802e50740c4501150340040c000d403001d00b43c50a00b0807001c1038090b121451460603244100c4080340314190041c0ca03512101300701406001c4164100f6100c0d54404101e448003030152004504c034050015800404950f0340454507102101e0098501140c4240100076200090740404401f4030b5103003c101d40380151054503114a890150f5500d5401c12040010300c640140401450081400341620341c03815500c1c1030030f240c4544c0e0000400301c074900e620a40141c04c06070301030103202c1c1c4181006c00e1041030082081c03074080d200360320500c0e0090300010b0113103403964000c0301c0541000413410045002c5084030006001803100030031950165688500c0c1e862014400d410802c1140c10180c02001240e4418110300512000300c0e6402d020a4104440010300211070703074582d80b2840c040343e208200540000c10842c0c90764084e101500030401c004002203078035a1140000d1104e80ca00d070301c40643e21004500081d1410328907480c0c4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 673208938 1250 673207688 673207697
    0xa0c0201020c0304210c1706100501021009020d0b13110108070915030906180302070b030903030c03040c0807120209103c0602150f060f040b0d0f0819 66
    0x407030311018400025030701030342c0c925001d0800b41e13202c21001c104c0c0c00c0741758100a400041050741c00141d0f409141c0090702d9542201003680c0003a0b990308a003a6810010340328090050340304082c0c1180e52112a40a500d9440c40100481130b0303070809403207003e00301c4016103a240c41030000703241000030000344a686111500d000e08002c030042c5004440030b00450301601c20721009540c50703044001c00c0d900c25840b1a03082070b4000380030007580140c2c0c4002c8588039100d2a085000d4400d03100b0200d56007a130402524402c0002000652940c6d59030000710390180c0000e00304a4041c0d1015201064a1009000d410058010010320042c184101c0c010440c040b01c01400e600c5000220f01024004142481c1900001c100500d0905070480d80b8405148040e4a001c0005820410515004100c0b2a400329400a842c03503403440c4040705850340c07480e81100500c1564120390200c0342e1a00340c1c0d11410700360031800002000030100702500403141c03a400140170110400f02c91040b000200340e4114540d100c0e55a1152441e841d0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 673210188 1250 673208938 673208947
    0x7050102160b0a0806012c0a0602060c0901142803240605031023030f0f0a03030b13022208011a09060a1806030b0606071505070203090d05060a0c020102 67
    0x40b040040c401d44030a4400c000c41140041c031540d0160074001c100d405143c0103003240c4541140e0064010f800d46100502c03e40e12100d000075810304c0020428003c2d04427910003481c002c980320042d070f580b40440101b1500c20f48240581107940200c03010140b400740354200420050044080e000b42100ca104200c0c1c1e02c4080000940d90341e41c8035150110b0241e40550901d6a03890b100c078200029030b11641d920010058403044d110103150706206012155480041d411182000303600050b580c1c8809140c40c400d18941d0101900c800428441c1c1c0000c0f5010f0030203000c0100703000c44c0d8078030002641e00c01001c01014201c1c005c0700304280c0d94050000e1000f00500030080141d030f030b0045e0012100c03d0508110030b119a1511000c1410755030360003120b00040c445503d42500011540300301341e019011300c0c841a43e1505d0306000003515030601000701d0b0459a40710700741c42609a4481920300c0103010141c054000c510061091011980b52105604030041c011801007000f440d050b8110019500e226054100710f900501 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 673211438 1250 673210188 673210199
    0x2030a03110733020c0106090515030d05090103090b010605131e090e03120103121e090e0421170c070201090314010b09040b22120509030c10020705010216 68
    0x20312503040305000355001c1e00e00080d00c1500307110b0f808000360381d03001610004581c001904154410380442d105c000d024043c942e2482003158410007045480340e015008a543d6418441c032500040c083c001050500003100c98050701c4500071403c00b600508080744002071844010501603070610010a80d01c0e1003082c00c0e8015807016501d40c1e00a1040e20403003a1166110300c441d04040c000c0d04d51003c0340d590310300120b603500d0400c80d807207100c0a80e0f2400801c203040c102042005c1e01d002201c48141b51621070100ea9817134000107504000000740152850203000c40c4002255200072250551461103039600081b035010900c0a07809404042c02c0c40380300c503504010420050743c208003410200c1e82c100448000004182d900355004d841c9400d80301380c0c4401c25601300300400020019003070203101c01040d56040c0720070704100b20440600103040541044540c481c20010b0910600c000e00661a02800f51603003001200701243e04410345032030040141c0c01416085c4500e59040114160945a0b548a0100c083c03030507 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 673212688 1250 673211438 673211453
    0x114090403051e0702030a081e09030a121101050c0d2403121103040b0418020304020f0402031308040e150d030f030b0d1a010906080a03082d010602030a031107 70
    0x610340515040d4041401d2420f000d81d500c1564240c54024003540c0300640180303800403160b4440b4142d081051880c40c0c070b11108020356400d94101d04800b400a1404004503280d540c8040150708141040050b2401c0c2000010030030300505008071001041c00e41c0380c08400ca07840d0242d400c0c28501840c5179540341d143d071100c02042041c400489401030341011245083c110207c403940f20b41c4012410341d20000500040b0950f500303000b08102c0d100c8507074048a020303403920318005910050320f0103035029901286240b912b2500307070700079600642c0104c42041c00102507078030b0f0511500203500104911404100300701440f240103020003c40c110491b03030440c00d8649560f000c1c200390110b0501d142010354032020080395895480c20702003e00d4000841688880d210641d41003001004d0103240c220b14100b42c40003079100f5000039900f20483e41500c40410702d95441c0e40c032559080c100c1c04000d40508080c10302c0c9201c0701100c4402800781003940e010f5980e40012510180680f082d1444101040301c08111403008200c41 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 673213938 1250 673212688 673212697
    0x170c2a03240a140903030601090905010e06040b06090315060319050a030c03090e16020f030301121b0e0f01080106050d150c021219080a090f020105031807030605011409040305 77
    0xa000d80d503401e0b80b5440120001402815588500c0440301c000f032101c0c111001001d9849070740260382d4058140c1d240c4c0025400d6400030302c04c0e1001130413282c0109a252030150070044141c1409014203003400c0c00080000e260404607044124108403040601c40305007801c3c4000e2185101d1011f0700f103030150050391000d50360114241e01608001440300100200740c0315810000007810369038241002c6080c0854140c01c81440411400003500c1800301014200788040b0503a8100c84e91664010b44c4da07620780d01e4200c00200e001c1c14520a807241c0640109aa075018a115805140030003410300305c2e0b6040c200341da401c491203a004588108100d18410303000032884440c000c90084440c2d008540340705518001d03490451081059003240201040b11aa000051940048840807541d50391110f501c0351028042101c0b144140a4103084442e5006400365019000960308000c1011050325190610b840c424284080c075081121f05a440b040100034580209241001010b000c9402d00f00508150b0ba019006124 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 673215188 1250 673213938 673213993
    0x5010f03140307051c030e15010e100b0306011101141305100605090a0b0f031c0311090d060207242a2c03011b0327170c2a03 55
    0x302c42102c0d04241d1094209a8147c40041d0071114260f180502078000c817a001d0242d050303540c41e084001000240442038400482f003401030034070f20790f0311101d00440304184140c06010b559074a84c1000d01200c00c084160300d105200c40300040601903598601a42486040c0051541d040c0c1003180c1070085959072804250401904c440002e0f03008062008150764000b140310160b1b00d401001c40c484101c2503007529190310b400b00c56400708542c0501d410005024050000503e406c070302c10b0f80545001460581c0180300721401020720620511480f590042007020351542511159101d44421814200c1c0c600d030304070301c1480082a640c0c008003080c00100600c02d600e100003a00c030803040f0301c100110006400316124004c09402808650700c50710110301f0007030055804000203860055034240f4000c0907003502008607030004400c0e90b8001c494540340a42405042c1c6860749440400c040d501d1218208011340320304031a01800c07241700395450703000e140794459002a80c0c0070381c220341c02c410080812140890304005 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 673216438 1250 673215188 673215223
    0xf080303090705030d050a032d0f0f06080307060c0306080703050705090c1215010e0d23030a0206010905070e060d05150a05061b0f01091b0503011a10021005010f0314030705 76
    0x205241c0c25604454911030038810000541c89c480302e8050710741180340341d203d015070244404030400b690070007180c0c4284a46e110640040c40709800098040d0400c1c2a60f0010789401f04c1c04640b20340a0306c1c106000c07035108403926072150004201d17074206000240c2d80704100c016901e082280d40d0700750b15000c9000624110301e1403842d0844a84980c00341c00c000c00100da01416206200103149000ea800c0c00401941c001c62003081030368a480d90200000701e4610840503800340c0b940d64a0840010042c210140002080c000a5080ca16003521100040e10790304452450200d400c2c00d08000c42d40c9030102404000b4080c0070980b009102644031581140c485c80720100005456000c61503116050101031135a44109509140c800d005000d1000745c10300e400800c03604d14042087d44d40b0101030072901c1072419000340084440c1c4249292500b000d41c851691882d0040d90030210f842d80b50001120400d030060032410180000c113006100c03d0103245070400500d035000714a0f00450341c440980e200040004a03c801 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 673217688 1250 673216438 673216451
    0x2010309020310060b04080c0d17030924220309140406050402070506010510030203042105090a08071802090915061902060708131101080601090f080303090705030d050a03 75
    0x54508204244107020843e0302086900d4076800c1882e40c0b0381c85889000c65a20a10b100000c441c5403568514511580c488201c00542c403144204500075000100104140c0c0100e40000e1070420b5841c075449402d603991405d00c00e503803420a10060f01c0354800c1184d075a8070349240c0100400241c00400341e0040c0c64500d40b2041d91407070720400040151420760803240e0054000304100007001400264241a12022545821900f112600481c2207000480300607103c01751007042e0403110501c4a1500e482141c580c50303e10f00e8210f0142c04125020842d13030002c1c1d11680003030310400c007594030b2062103214031003924000e41c50480c032000042c4410201030b00400604030241c100d11803550324041100c0940d03d140c032030660304400060700039403500350032506540410701080016035082d40780082201c00319800307004030440e00806801118141401400d4a060010800b000700349410440d81000040584c0d030f00442c0d032407034203030203032810102d1540c0510f010381d00c180700210b5015084825184002030625000514 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 673218938 1250 673217688 673217693
    0x21f14190e01020c0c10020d0504050418060c1d011814120d05030403090501051207080a15030f14030c0304090906140103050a0303050f10120c0510080711030f0702010309 75
    0x1401071105140e59580300041900044030003280c0f08078030304e1044411610003100c8100507070311403103802020400140100001e102d07515041d0b111700d540310b0300316466200e03810a940d5181d0449020200c050003003038444807220160580014810170260302071070725500180e00e080f0640441d8050740511140c204035072075140055158040000d8049071a5070498012159071000901554011795060f4005049450f010a09501a808449000c1c0b0054800084d6540c2c1407001c03036880e03801902144c04a510b4003c07080c03106030826544406180a420751900b005042c2c0380100c087c1c0044520030b840f43e0014401e589103400c01200b030700d0449540c0040031505509500d804802025140c58a600c100f0b4848004000c3c00f200045140240b03110340ca08000070745a12190b001007080c01c892103400c2a03000d020510802910444c1030f12054810030b5800c01403519480002d0b008211100143c2c0002c0c0c80000700042c1540c0412504081403c800107140f03010008001c0f05c185106040e40a81810348404a403001c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 673220188 1250 673218938 673218941
    0x15031509350d1103010308030f01140604030809130e010e10090b070f0207080a0c090f0e0712030c0b070201050f0c1e0f0c1501080123070c0f050607021f1419 69
    0x3c2d62902c002e507640c0c0b582c587c0b800d4036040d00290b07a105000d0440000100e00e0340e0b00a08502c100600082680d402c1071f02e550b40c1c0c8059540070080325500810a2988226030005034010500ea40003190000f15001c80c98400713113403410007a940010515404c0000d402c2c0410900103030b05803c64981d00e441003403010b05440c03d03440c100c03031640500601d104250303c8009001c0d56001c11010340d888080140103500d88079010509a41c148158080540c008800c1005110b00c0d640d6818015442802c000c501a0b845440e0240c2d02c0f8004c032860000760b51500300300001c4075185042d060b48011207410403414221420342c802e42c0315109a40c8013419910003d2001c1c1105403ea0a0b03c04a038440d000b15050884000690818800207208400b159801d1601d1100494649c0803140d91403603408207a0341056442c3e100450300c000364180c0a0b81d580b560382d00c0c1d40d03010810510006d0301c0382ca0280c005040782660a003480052002c0e2003807a0016606d090803160500c6120782c0c0980e044407115030700490000d01d5604950 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 673221438 1250 673220188 673220201
    0x603130b04080a201f0608101506110a08030a020c01021611060a0503060d0f05070f03031b0308040b06010516050703060f05060303070615031509350d 66
    0x42001403940d04200400c41c55000900102c0d14a640380c040c0310783c0d000180c040d15912501400341c6900b049503404605400440941c0480f01c540a0204031160340c0d4140c02d0a0558480a140300303e5101c0601203081303030303189048130010845803424412800d09001c11503110030115400810030440000070441c2c040145d0103031412a00d041000f10740c0c54042d0f00d040c000c80c1184503011900c030080f141c0c006c8040d1500d401a18551507036520707180c0c55941c41c0010010000300e194030403144460840c4403940031990800c1134802424107403e01d0340d001401c6040c05403034038a850040f50703048003000d20417000103580515510740060744540588102e468440041c0c64502035066040f034881e03005d00a2078103204c4005502412203000700010466100c050020000b524070490700c45426501c100240f40001d000d0340d1004a036a0403880300700c800543c496440c040c0ca80700c1503100034006c40c2c41c0c60740700d030078040401d8000d61104500c0854416496075801001e0159a4031500590f10440108204030107410540050 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 673222688 1250 673221438 673221443
    0x90f1806030c180c0201021603080603150c0a1103090d020423090a030e03010203040c051c08030c0403030f0306080607050c0c0d0303020a27150302091011010e01090b06060313 77
    0x11a40c1d42d0300c0e08101412003003540340c010f101c181014030440c5043c0c0184216180c0f010103070031214004510703480c103a840307180c040d00c065050f02c52900b4440f0180005000240100c03076124051799208111000200500c175440d5900d202c3e80c10402205845917190b0003808070140c0c1c10384011542070481c00501c4103c0c1c07540300840c1032541c050303010040c004101040500606220b91600070410000310245800c0303010449000707002000d424018000d6140c00d803000c2c5441b0085904a0112003215912030030240c00c1910300c41040c0c40081818020150400d41070000e06a0321f140c10440715280c01c202c650340d440050300710410710100254481c1040f50610034007440720806450790014146a15008001b54001d8041c02e0010b40e2120303400345000031440c03c01000303040200b018030455003841c580380110701001c40c51500f07140d0300308510b0456407946d207040e40003800b440e1581ca480c9041c801005003551003039540c0a036241d1402c00c0c4c4000003030303180303854a4026070181d6401c0d89a903a400215014071702a072901 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 673223938 1250 673222688 673222703
    0x50d1803060e1608010b190f0506090303070503210a0c02060a1508010501081506090405060718260f011401140a0b031906060305060607020d0c0b040306020c0d090f180603 75
    0x70900544c1500008800042514000c011200404950718081c010f0b0191003090079034058200510300c1c0c100f002e0065458000d090b68074200b8603175182032441e03000784c00444009502092144840c0c481a010f00e034094042c00007030200340c060440c0292500340c002d00c42c445143c1e0343d15070605800c0045100c0000762840c1c3c0000c0105503198406039540700c80c404045c0074980b80d00da0004146081004055004550000091000b0348540a090320340c0944400c7c0040344003110940003c0c054008214585c0c40c8418661605a0a0300984600d06260203080046a942e06219004010000800c4001e045609910617606407101d05000907000c20526030000c2c0c4100c0c0040207005001102e001c00c4201140f0301d5030200030665403160140c082d10411541c2c0e43c1e02c29028481c80001d03050804081008a04c185180c80001d5212000c0700360a07006034105a407143d60104201a180038108076400502100b4240a4a018170300a90100000c0d41c0c2d0280001c4090384c40b0041e11000e4044c0c00c102c000d075600084 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 673225188 1250 673223938 673223983
    0x9052a2d06190c140d12271212020403030f020f0f0d140c06010f1509050d0b0402040f0509030703111204060c050c03030a030b010201050f070504120218090a050d1803060e 75
    0xc00c041680c6645025030341c94140c0308122160000305044007455003404102549801d901c546035000c8c1c1c181810002c0c401011506042d4203d244024005940310791100240e8000e0040002d00e405811240c040d260b1740000315a0300749440028400a04e1162072500c102911070009003801c4501500d605840544030345800412401c89070503007041621292049569002296030040b903100300d1611413540c10203280940f060104041d014250f500c1800070301f01044c00c40d41482c803002180c504503104400b071741011038150105030b40041508500307407e08005100c08501464581d100b88107920405091160b41040001040b106100301200094014241c176102c992050300a00a0304802c5d400358011351a010028128034080e00500c0d00036012503440a003010b04104a140c108412484242d9200f0b0030304809d04581014969030134429039140d400341c00e45402614066140c4281100301d04103025062007104814580070a003042101d412620114941b40d1009a05003040104079102241000904 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 673226438 1250 673225188 673225213
    0x4030501050910060e0a050a1503030207090b0307140d15050f0103021002010e0618070b03131a010815060a0315060e0a09052a2d06190c14 61
    0x41c0454800e8010005694401d140c002e021001c9582c0360080350300d441d6640001c10708110791540700c2c41d8000394890002030030a80450100720451920350044005900c0002e007440f40010b079000d00140124264000e02204d800d041d0350b03a8210700b14249583c02034685885c4082032116846021540302c25400e070406c078605041a06058070002400203034000e4010600a1100601c148501056504404080e113101d03120040a58202820307200f41c40078520400c0b10103d10309203580003c44c061680140303200b0308000586010b0b04003603681c00c80c1ca010b002040f4010000ea10010603901510355411000c00d485544440005945d05d036a900301034028005c001400b00411056408203042c0c1c0d002a4034103803240d554842840560b460030200810030380000344c0008480055010051003200401a410042d13100e031400b0031508000700300384503038007500b100300c40ca115801f00741e1800c80380354150f90880c03411800503d138454001100040e0002c020160302454144440c202260380c1200740403094543d2000201c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 673227688 1250 673226438 673226441
    0xc020111270f1005040e1302032e020f070507140904110a090e0102210c0a2607020327060306091305030309030d05010b12010b1602040609051f0b041809060204030501 73
    0x46c01500d2050001c60042808600426003031000036600034014000442c2c0311050314600c214030080d01d05081416844070003203034558000f07481000c80c501446620781e6110704000d403600b846644404000c443c0d51400e00e106d6224034204552164100c0a660405c10821010031075003843e590101602e1490064030120401d410340051040c1a90109540c1540e003200660030b42c03102c0262585280d4801c10022034100c2c9018012410403003100c0a000e40c00b0088001175800300c40e0301143d42c000180c10010704c02111100390320340002c49000340310b141041d4214141c040395080c440034180d03c2c8511034840004442c2068101c21411007076122040c1c81e220700b4450002c0e980c0e0303000380b041c4004450a1200203e03041c8089000d6410040c005171310171409910f400800c44d640d0b4014440c555190380010944805611103001e16001884d803854001001d140c121020281562410754002e24100481c1d03042207000011380996003900c0c1844110401704a4074140300b4010020088002c0c03c45001080000502034103 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 673228938 1250 673227688 673227697
    0x5091003050118150e0303011505070506100e010e070e0d02120106030303150504020319150e071e0f0c0201030f090c030b091507091203210c020111270f1005 69
    0x10130a01e80c2d00d1219180c1c810075a55403000d28400359005000400c95030741c00803498580120907040c1245025420b884160500c40300712806101895540000c0000118100d15a4014000c030031042c1607904101d130303000300702c0300032110414450100c805c06501503640e101b0b00e460806007030034003c0103074a95030314000d80540061203083c0d0144d154180c0c0000c00b410710340200c3e4482c410f840b140e050641c80e0000300a00400c24821104590041c951011425003640b695141c016001c9844413448904036510790a810540101d003282044a110f1200401c6500700c0062820258242030120728100c221000c6002011200b00250992101680c00418000d20110050050185006035002c400d0301003a0740d5862502901d0b482c000403a45030042003021540c21003050480d02c03918160162a06c41c3c3c00080106030307607041c1c0c0100580d58904031164035409101e83c002501504541394200300300c83c0c1c2c0c0c452a0b940114051001071043c0c05031340c0b20396507030710360300400c82d600082c0b402d989410102c1006103260013 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 673230188 1250 673228938 673228943
    0x9060a080327010c020a1a070b01080115060c02031f0213121103032d040b0c0105061206091f0204090e03040f050a030f0f020d020907020a0209010504021305091003050118 75
    0x82c4590b0a0b8140d4401d0315400d094980142400200900c0e00c4c00b20b101000d48042001d0f8928070a100b003200003205010464001c02074440081200c11200540c0c05003913209a0044090188180e0200700513207001c40c6040c1c040c1003004210034084010600310002c2d2007540c1d07004c0d407269048000403c603900020404d204490103050042114980d141c2416500e00c00c0f80168034000494144c181c1c4014010841e5a028048805880d8245680d46d1801ca2040e04030340c001503d165102c41c1000500d042c09002d82c0b02c0e80d111100100308504041c0742203500c0d05001f5041040720650460b24041c400c2450701158021306013907800b0011100400324054894109000700348c2d01e01c080c0f8200060030315202202c44150303038100d2042c2103031100aa584443d0307030403c110200e070022840541c490240c0d5401420398070610003900507008201c0d161040140d90070050300124071513481800300c0010300800c42050004d5601c1940c1315016515000c1440000110583c801030156007040a4a07080040c0100a00d84062 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 673231438 1250 673230188 673230247
    0x72708010f0c020a02151c0b090a0c080703090c12050a03020f010204080312190501031101090603151502030d0606120614090705030c0706150608220209060a0803 71
    0x511907030408003602d1444084000507032104030280003518044440b241d8480b07800d242c50b4500400c88041807080b60081e20300480b40b030b07aa40528801400c1009459501c62030300302041020f0044800050404030000e01000304055503060b040e810441440b6410001d01205002c889480c041ba01d84940d80b1301c1b8106044005009050007210b034404140207a400f994041c0c005542800c1c0e00d607a4040110314000d11001001c0078118025030800740d2817082a000e503004400c40d4030080c220400140c0401c0303507907210030201443c00040e0401220034224800030748690410120390600d800200702c0c81c40c020030b854a00901c0c0780240005805800c0110360041c2512140c080c4000c0d0b0b650904d4400465160440d1504036001c080058030041c818401942d01004a041c00780c101423054170780c2000c458004800302c0e9119400c02c4103001c0c1035005124240c0c0704201c480c4d0501c000071240d000402c035440c5e00c1c00003405002c0007800b1030f1090350750079401c10240100408036911541780c0c0c1c1e94940640000d400076100c20 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 673232688 1250 673231438 673231451
    0x6040516060c0b07030c031b02010605030c03070f12020f060d0501080c090c0d0b06041a030a0b09010b0f03070509060a021c0207140108090102121e0109051003030807270801 76
    0x2180104034005109401500a80090766441c9051700a49030ba0b1941c5803c06d5598032884031f121880f540079046c0403000c0c0e8000034001e4100014903207400b04581c6d82ca4440da0100008118104030202c040b000e941482690301284038087c404542e038a0540244c6540c81107000c19905210145030340554100c440a40844d000384940d8000d2003240c0c002032700c2d80708440d04100000450201580c0210002d800d01820b0740d494107a4444c0103204841c4003c01c0041c0500c0004140180e10740d003030143c2130411000711540111545801013022072481000c005e10500c0e0400320004030024041c07001c0d0342100f400680421380d14181000025142c51105000d0008045500309440d41e151001032034005031402c5194402031049403030010b50348044002c0080d0604c1d9001c1054a00709240c103001c060083c041c2480040c4c0d1800d035032101c101c03d007105800140030079280100300000c4c10f00d00c0c040381c02180e40504085105883c0c00790202c0c0d801d450a1a816460032154801440c4d00447c40003007011180c0d00402007004 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 673233938 1250 673232688 673232699
    0x60703170a090b0c0304230d0908190b1f090b040c020a120c0c0b0c06090609030a02031603030f11030612031e0c100c1d04090b18010e06040516 63
    0x3203501d80040a00750040c1c12000034482010b1000442d0000d000e0009135036224440180120f000140880c42202c1b23801810801c0e00301038100242d140a860a40041c1a00040313520f10b0800000c0e041c940500b0340c00080d004500b8822a60080120000030104c00b400c085407501100c1c00600903100f000c5020b00d203000144401c1902c00310b002c3e4103843d40318a416042c2c808003041110301c2000520b00381c0321302511200c00038a013104140180031511985010f440c861601d20b07130b150b0030414000d201c025283c208000c690503950f03000c01190030780410fa240150405d0901d050450040c0640100b4040075480d042d4000c4c4007600010113948108003c503200303003c0e154200b0241e502c0b8001c504421038004074111142c0003a8441a000c0c00d00c810100049940c400c103614100002e45188002000c0800c61a800c50b02c02107440c4011120020000c0c0c400313001d030400c1a03036413600ca080b009000c010a82e290049009507070b5000c3d044803034001200000ca6001c1d017054180980c452612200b440daa4030260f6100145 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 673235188 1250 673233938 673233941
    0x3070b0a0b0a0b0a05041701050406062408070e1305040203011805061b13140108062e0201060b070605060909070605030118020d05011205070b0f1e09060703170a 71
    0x152841c050282840c0516021940c94182c01a10300d003024040c0501001c21001c401790400c809603500c000010485080509040b0304583d101e4200102c081e1076500c1001d40d290329004110b018403180d01d081801ca640708103044600c01c18040c180c81d485403041c3e070a4001c1c180150009405103000300d00800c5610b1900710b500805800655004000c1d40005c0d0002e44500c1781c0010802034230417a80d444910f0145600c60710a29100715421001302400b14040186003940c0c001d0f105a4040360035100c52054040160300041106400d164822103c2d43c401a5002d04034400c0d0080c4c0024941b91000d107884210a1a00b00041d00040741c081c0d000b620000b002074030507071001405400303d82607a2156440c40e401c110107a0307a07511104034660301e055001c000c031a900320f8851145600030125141070840003942c0349041c40c2088150380c0f0041c030501080c051407012407843d608844103a03100d425041c011101856440c4051f0107401c0c1210303400702000c10100e0605411042182c1001a2000c1c4403015581e40c2d00c4400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 673236438 1250 673235188 673235201
    0x4051005060a053003070501180206040e18060903180307050a0e130203070306060503061302090c0903010e060a09030908060709122f040e0c030d23040803070b0a 71
    0x141d0141e8942c0b010081400d0001c205114003080703450408054a801500e0b038080c1d40310a2030345145600c0020908107010083c031802d200c0000e0400b00d41d040e40c00f55000254a0700890007070440701817468000c034240003c914068500055810b00f542c0e49460030001594070f030b401515043c1041d10100800540b24500030480806984006141070000d609001410703844500040500d038082d6810078404015950800c942c60096201d1070020070940c0c01e007411f0508100c0058182e00c8200c1c452800000142d40740380305264030a6a4201150301c1e002460002400341c8001e608030102d9000700428001c0751501508081c485501980f14040c1c480d40d100307962503440c10225202e800080070b41c2024000b0401c08883e01000702d00071145464041d101c08281200c1c522000590094040b1403211513445051600030409540243c070050403600711110082074688216035054000c1082c1c10004101030b00d0b06140004481a41e03a0060f81c440f602c035250555a580580000c0d13504000d8240082d400840030302468 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 673237688 1250 673236438 673236451
    0x3220f06090f031211120a0f030e1f1409010c0f0f0203180f03030a03060911070510020c070f1401140405010c0f02011b0609110604081222060804051005 67
    0x20b960720b4956110803041c6149031081004004501d41c030a030300464204240c44401c24500016a500d6440d940050a604804558002494140b8121310840c21b408180c0b190380080714021440c443c45151340c4500144881449a9610b0428106129179904154420040103c030b984500b00212110102031320302c5080001c0c0400160f0080050f83c800644103c000411544090b000109540d00c40740000c1c01c43d003080ca0048000b03a525071007080100d00900890107948006081035103000135649590361100080307104841d0541c0c00003140e060450003040040020320b054600c00403580e480f1208900460034650156000401e01540d586d00005101d0441d41187d60584608401b0b59165850030121000d00c0020783c1804a4400d00c1030003010b14056980103144946030004515049140c0188818480d8444600404052000b400f40843c00582000c0d0303110041101511841001d000600030079001c003000b10720b0512140b00241071038004140a024a109905071020055904d008104840d0100d424 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 673238938 1250 673237688 673237709
    0x120f09061805060a091b08101b0e0f0d05011409151311011e21051b030a020403080d022d09240703020705100c0f1403220f0609 56
    0x465020904c0d9400394410a01c641001c00d4021040341c3c6400044a440c1d01c01c1405420210348040403c805100342104d0a0364054070280315010034800800c2001c00c5190b2902554003803051201e1503a90180200300194480000c0c05040400c402030000850305a41c0c002d014443c1c02100040d509654050b60b10860580ea5a50050fa600303890b010007000c1103c2040341480100810071800c1c0c00540c2c0401c011140a4440c204a8081c06c1405650400c801c00c0003540e15240c4010301000c1e060660b2100714280300c01c0f0f240c5407a07444001c40c040080c411640001c112003000606888281030980140072006e182001506440d240c020150f00907003548081d20090002c2003007003500724074044400c026940300c204c0552591041c486110803640d405a14103030b0260340000010889071a0101000c2c25030090342c50041c80401c05540e400302c040612031801000b888451201030010902041520103030781000e0f2008105030703003007a100140d4541a0140c0a00c1105103040401c0321070051003404212404c0070741 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 673240188 1250 673238938 673238941
    0x122e06030f120512090d0e0111030306041509090302010606090e100b160204091a01150206010b0702011b0b060f120a120e090a050108010b04090201050a0e01120f0906180506 76
    0x2a5201c0082c2460b640d0400c1c4803041c40101440c00403040250b01c11006500144601200a1800303885030520000541c1007281034242189640307000b01c156500507606403400b0a1801c5004000003200e46240c003d5010589004540024181c0c150003400c1154429141c500c3e40d5510782c0b00384d0b1001801115282000c01142c48100701045680c40108810355800300e034a41141020707800035092b125201802d454007140c44c8900b5029090540c0c3c91030052406446107101981030800194513110705100d00d1200c84004a0620156401240e0303071910030b8051307006922000214603014a001c10107840b09406840c80300103802c00e03810200400c0c136045186900400c140f054a688903c58419490040b00030080c180900d162643c0311507030302500804094501003110760600c1205400c40b1000c400c01e600c02c60074900c2150242c1d030060111151000281f0f85644290690300040e86c5401c000000728031014a4092404440c1101c2d0b0300c01040c20b4400d00301072001c024504020440074004001c0680303a40c02400 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 673241438 1250 673240188 673240193
    0xb030a02040e0105180f07140708031608070207030803040c090c02061602030307050919030218070807020601050607150b06030a0f06050625030207150503011706071409122e06030f 79
    0x4544941c0150f981c0b03000004548c07500310a2441d5040044121070162012007130210944488111440074200c91900e18440d00d00061700035035030815448003510610000001c14244121203c440e00940b03440070090000c07003024013000b90780b01d100b1141c661b402034002000110306440441140e0290708507540b11810300d81742c3c4080164072034500b0084480e605100c0c0000005071221884050ac07010b1078400800c00f45007030800640345c54001001501190822001440a544c0d07003000d644a040e0401403c04054442c0e043e10300041c070304ea180480c0e1290003c0300b0030038107100b103401410401d0700811050100a40d51000d01145006d02c2d6055504882d19250740c04181100500002000e8001c0c41200d03011a55492842c12104000fa51080054400401404a0310b0188d15803800380d5081c200802c034620301508010641000d0720f40402d00740d00002160307042035a80e031081181011244059846200384e031440c1e001c040c81c59400c0391502840135141088800e549200d80f40403290407210100c007645459 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 673242688 1250 673241438 673241461
    0x1502070b0a0e130e060618070f0503150301090507080721030e03070b130905010605180405090a15050f090a030f080c041e091815150b030a02040e010518 67
    0x180b00700d500003101e680d040040c18103070f01032900200100130142ca0729051038030900c810200d2140c54a05a595540180f101341d0f0351100d074026030020903160480d02d076140c944030038007076000d00d0a540f940741d800c24243c90180700001c03c1c01e008440d5980f0484007415030343e20381c00c010401c2070b0145140f0520600020004640640c58880780d8507401800c3c0e600040d202c1440403499000100c0300000001701320400c0c04940301c0351117070501528035403c00c0b600388220180d07030000c81c0b00e010311064055030302d40d000308802c2d04003000b2403a4441d070300035140e01224104d00040001020120380c1101c8041107007010800445002c40ca40c0c81860b0541d56004c18401d131204107995941016054510f990000c000015001c00450302c0700202c1d0480c01c102014a615204d1078009603188503440413082c0100d043c010002404801034040325110b4100013089220500c4090520045c00d640a1a1050000801c00500782103e034020010794600705400c0b90640d80300c000f48081440003803d0310704034682d0300b40441d14102d042c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 673243938 1250 673242688 673242707
    0x10b04061d07182403021812010f0c03091208040503070615051011010e120403200303160605010b120109021b03040f060801090506090c0307050c01090b011502070b0a 73
    0x241c1000b505940d580e07255002d241c60103a000025181c0b4910351840d040013042c1c00e00d0756184140c40e05506003030280311440d00d5968400c0150744159000103081c05041000c0d041441f8604403c00108013525170740e000039000d000408411600840c0142c5002205400b4441c2c0c41d008982000045003400c9640e95500000c01540d050542c4c0000401300016541d43c4980c100038501c0d0003991120344584240d140c540c00c1d682c0140ba1000641c10505002040e451110103440803203802a01c4d9070400c0341e903203d0543d40c12105400c3c0e2600b5000010b1001c0c044403516403014003a5201301000c1001d40ea98400310700160207440031840402111200412110045030060440685040c0b00245407408091030185140d006611604841814030010031003642c1100c1d8850051801d0038051007546410000245401c0008080721078040010011444441c41041620580c001000c002c1007054900d003810f1244503400d00c107820300b90b480c49104e00c0c000c0303201151101c203c0b0002400103003090fa03401c0055841160 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 673245188 1250 673243938 673243951
    0xc12040b0901090f0c0320031f0e01050a05160e030604063935040317040516060203090d060c0c08072a0803030a0c0309060c0908010b04061d 62
    0x12906000004a001c040c078a100d00c5104041d0b081c001c501e14500350544440f0402d0642481c0001e60002450383c0f400706040c1000c0c0509003080c1e0342c42810342440c000030200780040001d0bc0d0711300b0040242c034a0b06640302c24019800e2244407100d01008078811140300c2c4a641001e0380580200d004a40002d80c99001101c80b0048880c401d4000c6806071962003540e2481038152401c0548150700655964008280c1d4004804000301040c03000f04040700d1083c0d000003802124110718003a40001c082c14450386800740c445000d003485501505007418284e0341e902c035000200f1082201c0354800201c6070700000071940303401c1c4054016192500b00d51130300c20003408005030b60b00510864401c4080050b182d407008050552141c8211003010065000400161010750007030000c1031012003040c810114000166644a4960781000c03503000f4180310100c0c06080500c10040a5500740520b100c0c103ea0040c00c00c0054030600d0008100002c8002c00f00000e85106202c4c001d51845820084814000700d690f480f40d0056 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 673246438 1250 673245188 673245191
    0x14070f1509060906050709090606020c09090114040302010903030605091e070e150315030c0604090203090c06070f0302060609101703250b0f0103030e04020306180a090201080c12040b0901 82
    0x401500d45800f41c5001c0702003211001da03210f00300146e10382c1100c03201025020720a4108000d900340030029698800354071480d8480d40c1d60200040b003145003500f100381103484100500344507041034a8064041e15800008134042800c0140c045268180940d242d0321459590074503809800441c0ca501001e590068050000c0080c080c081440c1501d84904004544454035982a07032417a01c0021000c46c0700d00c1d0b0070701030302c29082840c0c1100d050752000143d90580783e1071000142c1e25103035088414540300404000c00e40008002c104c081c1880301309118500031314060b400759507050341e40004000c0d0107501251003005e40d1761407140c00d0240c44400101545007803801c404503450304421000314240480d800603e0100c111525441c90f08200d0040040b030f8004420915100c2e031541150303405064040c0b0250040d000d1680800000c48556403c0d42c00072694145c5003445070075050290344540904164002603000c03c400e11b001c1070901044d9002c40713103100346050104015031074560720040d00342c8018001c4401503 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 673247688 1250 673246438 673246451
    0x1081b0f0118090c0c060f020903120307182705060a140414010f060207060f020d21050f06030d1b06020a050705010213140f010807110a0b090105040314070f15 70
    0x4250b01c10301c244404541c070f8a284a40c5d45246c003400f916440311f00c3e0b680e61801032014410300d450001f03520b5606000044a562a40d9035004122420704502c14007803c40015488002001c2d6a20302d000300030410401d2030b0030642d0115030119425034000352103407904040e10340c038200091804400f07070039001c500c001c1000c2240c1d0340103420358600ea1400e8004680d04c05c52950200806034041001e107000b1f1155007441e10324001c1100019403507035038400c5004148200b038075913034172840001801e500c40f40c02011400c2019080000c4000308141c1c0480314a806441101e080c0c00c020750003540c3e0180141120702d804003203104584d990201035040040303150309201c818070104000650a0000d840d0700d501800710301003420f28004000340d0000110020f1401010028880e0f840c5980c0120b00580c484420309041e4180d1100b008a1072403d01c0248001d40a046110188090600c040d0070142c000e0303000c2c0d9a5012214402d4800c100306102e0400020043d5003400300745400141c031088001080c45101c6c0000440 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 673248938 1250 673247688 673247699
    0x1502030a0507030c020709150b1c0b0a1202040209042307020d0c0f060e0307050a05010515010e1309050f0f0c15031e06030a06020a08042a0905040206040510050301081b0f0118 77
    0x43d07040b5481814054410b900400b00c141d02e00d1145c0d08208100b1529019800d00d0300b82c250a00a512110180c00b5980000d008550364b10342da04050b8580000809a06801c4c00d243c40e201c014080c03c3d64240c0c01030044d0360700c00511503c00d082c3c1429035508200c90a04c01c45069482c500140000c0d60510300703601007409240c021540512803044183c1c09100041a9841c00108200c0203040b0000b010307051243c0c4000144031501c0b14443c1c0c0f8124049180b00080b18615410454a003540301c3c4a0254507119140f081c240d05500412941d03920502594450103070809100f032080c003404200c50b4640c040c1002904200781200400c1302a030810000390a0318600303074907922050f00340d0380214541d0700491020784c00d001c10081001d00d010307000610041c114115043c01d08405518005512034405840d848001040070355035445c04540041c03100816000707d0307560554018000e44c209109251840c09500088003e1a403003100f050b1020354010003450b203400d4003000548440218840101000e805240045071 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 673250188 1250 673248938 673248959
    0x312150303031014011d010806011205154e2a0a1401031e0c021e0a020f0603040501020d0c0203030610051204021c1502030a0507030c02070915 63
    0x14104a0401000c460b0503d00c81c80420741084c000030b810010711803013240300002d0310000103440040034600a1740b60388038200122080765005c5002c00d41e180c9807005004021a003212201c1d0340c200d0955811750740140950003101880d80303454414210303001c80201c8040b10400401c00300804250310301094020019480d400c0c0c84e01c0000600b60710b071120200600e0b00319604045810241020855455a0307180c1411880491a0f443d00010344c1815200c84000030340800240c1d00511840004500300401c3d03031a610000e540c2c4825450b031401d10704451600b0906172101040c29900389401030411508428404184005035200070025101c41d5802e0201c0c1840c141030b80034140300030205500542d00c3c1c0c2030120802040b12014140c460034040c0820640f15004060305480748d01c03507012100243c07055071001280061219840c802042c4046081021203130038182e0b0f01031800381c06082003c01a55a030000107804803410400400c01680c0190810010b11850f0740201100600c4e0740e02461030599103690042 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 673251438 1250 673250188 673250191
    0x120212030c0a0309050d0c090f020d181a040b06010e06070b04050c1207030c050f01030905100f051b1602010e042307021617030f1b0709020408031215030303 69
    0x740d1a412550030320060590024803200540800c480802c4070081a64805c400342950340700c1d01c0400754441e07a07100003100716541640e1400380041002e00c01500c2095480005030044502243c00d20f4035114100100070003810128442c0b0307400b41d40c114a07626200c2c010f44900d00c0c02c036625580704804000c5000042e1910305018055845000140616000070b402c1003100035500b0b9422100f80d104403000c10101c0d90102455045440640348403841c1150300f001240942848000030b00144103061034017110402e00d611480c604080740808104980f41e00034850704909941010f107072085170a0218000c1000c2d40d0041d211524414100340c65444d9606001c103092700d6440641501d03407446203801042100b80c1e014241d034020707014400307813191040140798141054001c0c000d50707680d20008280024035990030400c03658645000c41405440d9400c00f401d8038101401c240503041c0d540100c20000407800c5580c0282e81c280d4a01d0809181445854034001141180050520b0084041d0b290a031203291014001107 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 673252688 1250 673251438 673251457
    0x30c030a08092127060414060904060305160816031113051302090a0e0706140d1812030507050912071206020316080f0f150307061809090c12021203 65
    0x103034607021051010381200c1a40703858000e00c040c03020303240800baa45d04d0302190244c6003002c41100e81205540007142550080c0010150000c0c40c00501000b0f2040000c1c81c61810071000000b070602d0394031105001e03290414410380340d01c0c030420030400f0f0000801c148048074048401a241501e0840070707070080003c4d18020707104007903c61582041c1c2d02c04d40c180703c403103940d00c5501a07c0a018503840089500c0c2d841e0081d1060340100b180e41c000c400200072002013151600c0e141d00c078051210070f0031400084d0905540c44411200741c0041c20300e40030301c035000f070045031700c41c4515860309818a281c084c10307c0740c50f80003085001001d018192021500600301c10000b5517850082a006031030b460301c030700b6400c04511b8804071038084c0700a0300c040201c9034026105c0c1d294000100d0003010115141c480e045503580490550300d03507060141c1200400c400d940003c4400150070526075001711142c7d903035145011510391140c050000c59191000340f02a02e44c40481034501072002e050100e503e05003000d520304680110000b07 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 673253938 1250 673252688 673252753
    0x10c050714010e041e020a0c05070608010609060201090c141302040b0702011701140f130e0a05011d071401050c0303040f05070f050d0b09121201030b09030c030a0809 73
    0x707a9400c0d6448810441d0090007501c042100641041100500f103141c021121086600000d85100d42c6128036110120154000104c80030180c035444060b020340303424003480c40060400d5000081071441400385102541e0040300550075a410a0031482c0d07500c0c1000d070203503040069040048007501c0907200400040c520720212684602c0031b0f200040013480c0e00c0e10302250b000d01043c018406400e0008200d00c0341e20080703480180c6c0c044040081140020f0b110038452004e031901885611030400400e0505040e07220b08001c100131540c82d0108032a00c001e00c0c070710b05c2c400e6100500512070381100c0c1c140207040700b0050618038213000c00303601d9072071850303200f12011501c03682c045090b141000303020440c1a000d8000322520140721410b1901081c004100c0f42d40c0038040a2206003c5006040280100c4804035408095213a507002c02c00c40300c010382d01e801c0c0310440e005c04200e00020705030303600801910140143d402c080d42c030303107454618100d55581c0b02520760503a0303000b940045011000f0503102c2d5000080203210 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 673255188 1250 673253938 673253969
    0xc2703071a090418051002090d060f0f0e0d090501050708070501021b0c010c02060a0302070c05130c08131112010e330705030105120a05010c09030c0b0f03070e010c0507 74
    0x144810303500e4284c445225013800f8001d8000080c2d0102d080344d0b221800035001620340703200b20005044002281c4001d0049880e011803400d80041c29000464000d040210a0013012054080f40fa0b407003201c020000001107440d0301c240103661289009122641c0105106410461281c4546007240e000d400e103491101905941c0c000c0c00d910030b001c0c00090100901b402c034000b51498010610314850041d103030003010f50000c4c40004001d0852000b41c0038000183c0752907101c0030910024070003011f40c242c1010200d44141c000070801c440032625106100d0740595580000c02034402840b080700207410b84d02003955210185071003981c10410880d13410000900101205401c00c005c100b024066813580c170200e10180c00704100c8110b8200080300c0c111403094404da50600c9280800317504003000d20400611550814201108880d170081038981524007416121001640d0340c507140041d8400d45034004641d82d1f00740001820f150140462109021060410b044003c1841d0740d05410000c2136001401e00c0004240e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 673256438 1250 673255188 673255207
    0x3060f22060f0f0602060c070317040501050613020702030c0603060d06052505310330020601080604110f09072111340804050301050c2703071a 63
    0x8071044010401080340001c20f9041001c000c0d215000144a85800c000c00035014081600c18412005034041110031102181401d24185001e02000d940321803040c880075480700f034490107900c02c441020758000c0042404041e0038040c804030b80c1009007007a074848143c8036000e01095550043d144100c44240c0210310315008654000804849503503181d08100c0f09002c0002c9540e8650110745510000000f940c0c800c500c400811911003116810007041c0d0612103200c010840c081580d800c4012011100c0d0451301d100b000012a9907080074400c80c6c0a03036110502103008a00c1c6090203841c1030300d02521381d12031541d6a0f008260507201c15184940003a042c2007040c0144001807908590103040c1c100e062000b50010358401e06140680004645144d00e69003403c5c40004483c91500240c80380380c140582d03070080d10b040804442d0018400c0500035400d1200007a080181c18003100c1046074942d40c40d00710111650380c00c5c40441c042c502c1e40764061084507404110418458000f645113034a401d24541c0e1342c103107030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 673257688 1250 673256438 673256459
    0x1060503010513050a141e011b1704060504051c021e0f0705090c0c06282306040b0616050c09040f12021f0203092103060f2206 56
    0x1d22182600f140070038408002100810403000658111081c810f040420b515818141090540114403243c01d040036075051000640104013101c212403d54403503401482026114043c0a140705030f42080300200003070028885a2006800c03d000c1d00468040e25051608415024040210000580d000c17844148112100c45592914034005901038001c00800c2c040040e5544103c2c050b480c46003401c00700040850405005542494110104648460600100e000701d28090110208a4028484420440703060706005c0c410f080070841c5980302d060065880074146e1101e002c0e03d125481a02c5011b0a45e00d0b95030800500710900038542850000d424910700507180c070703138144d01050044040c10204030105400c203482c104001d4000803500c00f0341c0c4c02410f08900384071000d442864a540541c40c612170220307643e0b025500c542a400c00710b503503019180c020f5003048000c00498006008040002450318100500391221001c3c002d40920400c1010002c1f044400d04240d2440b00074a541c0d250420120720740 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 673258938 1250 673257688 673257691
    0x2102031c24051c0c170a020a030f0203070603110306040c0c0f06050901060603050c030f07180308040e010608041203020c030f04090b0a061106060d140303091005100501053405010605030105 83
    0x9880350100e03816110365034113101801501c102a0f1021046502c41e980769820b109091010340c4c0241041c520903240e00d00b00b018401d41c0241680603124040b00030864034024807030103505c040b07000b07001419607844004004c00792a0074900e010411201e40e0000c00040c44008284074130601c00c02000c500ca1904c0c0180c00e08482c256031100d4101800d200078800d5064240c411a41c201d40f14404a00b1b040e519842c00340d8941002e0031081046003100400041400b203820041c00641704665031903c071503680d400040328282004e42c0c0141027140820008040c01d402070b80200f207004214810b8904000c101882408560800e034027000d8816181e03410300705e072403402e100010090031035428113406038440210881e5a910000301243d0092403403000141c1804a010079030600c40103464216a41d0b4600280f2841c0c94080c030302861080103050401281040e058000420181c51040e900c1d54280342c010311580205030b01041c022200041a5400102ca8003407144800c0980b1b8000c40022902a14003002c1c5400c5400 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 673260188 1250 673258938 673258969
    0x80d140f1b04030c090b06070807030203030406050f15041505040e1b0108040b130606091b020115150e0607140a0c0e0105060d0b01021203010807032102031c2405 71
    0x74108002c0c00007134003441c400c000352003100ca0f0008180c0080300119155204403000900301c3c801c01706446040550010065101e2407103000300380000d0329401841d03c07405105a40320b4426011200b1014804d00306540008007103c1c0c40c0f00d01251950366040400c00320340d400c410010003908900c01c01c80d000c88000510f850096020b2810300014a456160451060301c082c04084189000c02140e0081c810b95400031382c0901103049080100e42c980513409900040350543c0980503500b00100d044003480c0c0c04140d4012200d114114044c0002e103008101e034501d0089540681c440b106102800c0031400f45030603000c4880c500701c0200400e006904044080482c158090586903000380d005001c5600c0300380c1075a43c600c2001d03501041d00c00303007a00140c1c00e00c0655140c0b203400c8203010000041c171300c100081802c1140c4c0903500c41c6c0741d5050244845214141210701180243e801001035952980048180e0030420044241c005407018160701c00c01c00b090054035685400310601d0354140800c0c03a010602c40480761 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 673261438 1250 673260188 673260241
    0x90c020f010501150f0f05120a02071202120f0c160f1d06030307060b04090b0f151912020a0e10140d0c06080a06050303040b0712020303070c080d140f 66
    0x940700c13a0040100b8031090105041109222201c20300b14010740c2a0380d41c4c40c0c4840392954441c90700140620081d0000d00090740d11126980002e07480741c0c00450117440e617101101c3c645245c125044d0301c4824550000001d00783c94402c0ca000d840c1100c0158101c0ea020b80340c5250302c2c9882c0741c54036460384d2030542c0e00c189603190324101c901403020582d0000103c070b110692080340420621100d500050062a050802912030300f400720401854944c182502481010f600c80300d059007543d401c051101000c580000349a40e04690b01003440f01c6903810440f0002c0a2004005c0300742280c41d0009130503c84016a03409924402849081c4240072050100c00381500c0280e5a4000d480050349416019500900ca038800380115040411606a10754010b0005410090201c0359600d5941440001c02e50140c4400c0c0c13902c6803200c003100c001c2e51010046074000e1515688640c849042900c815551760b000d0502511090f13981c115002d00300ca42d82c2c14071481500310980a40041c076040081601040d80881c1c8000c460 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 673262688 1250 673261438 673261469
    0x80c090105150d0f1d010e0d0201060b0313051911010e0621271006050906090f09030d05090c010f0f0f1103090a03051006140f19090c020f010501 64
    0x607004203007030303070400b608602c400b2542da580588444010080c1c005107105c0303071030301d440c030f103200f0540540041188020701d40032200c0d05008803600b24201c2e00240580c40c1c0155042000c540c030f480003500d42c1e0305464010001e40b18640c0060005c40c2040714110000c403000700240b0481c6150b03682000c0a45000c081c15515949041c081c00301801c124000482c0c0901405d44140106249085c07404003088280d513000c80749000c3c020300c1c1c201183e0f603403c1c030628850380a0401c54081010309000207a54013858020300001d00035180c2041c24082500000e01202d0f15120510103100403881c940a610f01615850010788010b040503c001030070040d500c1d07083c00500103890110384201e50301840002e504551890000003158040500500b07502c102c4419560000150002100f4401d0100d1807040c40e031005827041203001c1c0d4442000214800c00c592240c0d010000e0f0380c1345001828000c503a5601c00190000000061f904c65108201325100d4403450341c0141c2c800c1c140807000010921500f809040707010140c0149 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 673263938 1250 673262688 673262719
    0x1050403020d0b090f030d020c070503010219050f21040218091b010c0210200d0e0103090213060602010e251a0706061203450305030301080c090105 65
    0x1c40c4107140000f805191808005520359800340b200c45911912401034903582c0303040e51102c202079000640c95910303a0141c140f0002c0c0351b02d414070032548101203041034513400c040d03100d0741542d0741e400606004d40d86490030081510410043d05107801142161607280301b541c01c0500511800508010300900725060f40700074011107a200007000120007100d103501c1c03040316481400480f040300c0048002500f1001243e61020080e4214441000d24580c43d503807840146d1205030314954982007000a036000c904400203158155220f904809442070016000c4642103d054032080101e80866001e400141d6550ba110031100c0018030129001140c03a807418481801c003072520484484070b611580004041064140c0d02420300714080c0c07581140c01810800140d03a862107507003068805540c0440001e900c810321504805050f8014200c44802c1c49040340079140140402c00c1d0600034510612803c0030000b20000000b8800c000940c0a0000c000141800386008000e00c04080300c1038011070321031240c803541c1c601c1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 673265188 1250 673263938 673263949
    0x60c28060f1a0f060702150c0c06130612020c0312040b0a06030b18010e07080f062d040602040b0a02070906080f0307030c02040b04091101020d0e10052104030c05010b0105040302 78
    0x80b00360448140c507000e038280001824910a09600035040028072a8640d810603136034000c3d022050040d400d88016541d100f00300200ba110303401c1c42c044d0441c00304030140b05040c410039001e45002c071010001441d000105211031310315040030045d1102828070702e041004000259280725007080002134140491411965044411540100104000c07001c0618a1760031003425081040034400b11400d4030511525102541c0c1c94502218140e20309202d40804a000b07005e80d108503407002510310104c1d0904000e001c0103014440030140007076450320740901000ca040b9910000905080c503650f002840042c0c6041f8409060701d03082d601030490781d0008000300c17220140c040304494001c2d916203029000380c0c0340c620000e13009040c14861140c0041c5003440071010004948601d5610010036000c0720b1303510196000899213041c403c4000382c2c00200580034090b1844c000c1000c0d000050304248003420100d04410590030013641100d0607000590040c18120911000b8031818040310301c00c0c64440d2800d800e5802050 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 673266438 1250 673265188 673265231
    0x1505061c020a030c03050601031e030e21030c010b120a0b06100c080a0503041401052e0305030a0504050a1a0f03040501021e0a020c01030b0906060c28060f 68
    0x1800303a4081504565501e19400041c0d50310041210246480c0c2c18143d644030403d02044179040e4114441552412002d50700201d480d071300d55a54020800c03044280100c842c21402130410044014110499000003131014010594a40000082c98400c5030104030444060011b43c14981d004010700d2404609d1355200c079540210140e03802d1080b10501c0000700c07601042c20201800728040810009141e9500a005500560090742101162601d081a803030803a101611051201070014000034004940424560b00300311042008070803070b0f541c036110702d811544802d8480d0300081c8000340610991030f000301344c03202901801c1001d80405c8402c2d12182350712320070b00c3c41c0010385080100000d000c0200940480f400c0c4102421140d10440d01981100c0003604001c042e040035016902c8034034083c1d4820321540c03e46040042040e00c19844180602c0341c5640040044413841c014054402e654a81900c1405000700440440540031099801c1000c200c078846140300d500c440c02d04045401c1c48a60007e1203 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 673267688 1250 673266438 673266469
    0x30606050c07170f0d0504030c05061611030f01050f01030512040608060d0206041d070e031203040b071709060a050c0307021b280305061305060c0306040621150506 72
    0x43d151102039000084ca032041e003100c50b65091290400480c07580c5d9101028004483c800e2588040030343d1150100300c0a40520786000ca00d55440d04003020120340c8010703012101d25000b80c2a204490f10140c03d160a5030800c48050310100031701c400400170040c080007661824045e0f64000d0f41040e040c21402030080c00301804152103820101d1041c429591084201c1c0c000f420500d01766200030480e0000d04200d0581100c451020803e001c044001c103080c08240c1040550510060f00e15580d55980c844640c090050074002c1003006440c1044040300e20491403c0c0600d401c000105100d01d007603c03e000554400400006903a2800c2c02480951130700018000d10f11400001c61902c1c011821010800300f0b840c440103081102c0110f2009442c07011100c014406a038016415110283d03110381c03103503110040b0000010300c10b9208800085030104404080c54020b04001c01c0440c84540d2608211076030415400728000180712007c0b20302c200003480c4d0b0309550301180d08000380007515101000034041c0d007020800 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 673268938 1250 673267688 673267709
    0x90d11030c0301110d1a06182b03031a10080a0b010f1704030c150b010e0303030606120406090b07120510051f020712030c051009080904020a03090210080601030606050c07 75
    0x28071b051451020981504030310044c019039254201c01d659003105100c021501ca001c1c0d42005551900d14828485452182c00340d0515107241d600325a800300c00810105004441c2d801c503140342c0c41007598810061341214201e664624440c2d00f016202e0301c08845000d10174606001009034000d42043e0406481c3c5020414a8840b80da941c4c0c6505040d211150340c8040100302d44c1c29252146001c480c140d0000310301807000c0c0c2c4c030040c031409102e0500d9580e100540f40701c0e50140090000c9806021603800da5a48144a2a80071410340759560341d12004610075038903400801c03000c0d916a2228942445260342c04502c20000416152034040441e100860701c900401000f944202e0040d05e103402003000034018800404016042449820000c0000c00e80b1142103d240c050502c81d09500e0724907000d1080c001d40c000898038900103100c010040258800280380c400d16071128120b01c0940d07210710070074803040d4113a00c3712507203441c0c00f10006084a003640c00600520106121041102c5000a80403042d10045481b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 673270188 1250 673268938 673268951
    0x30203060d060e2415120a080d020301032d12020c1809010c2c151812010908090f04060509040c06030606080103050d14090d11030c0301110d 62
    0x1140d00303480d03880800b501c00c2c1c1c2004070700040e003040010030ba0200800800e41c01007281d40016600c03502402a900c05045111202000c0301e1440d228410700f002000303240858008840c581d9034259650440c00403c6d0004c2d502200401c00e0004804604d0004041113501c001d440c4c140c4625841c0204095002a05410000b0300041000e8000c00c40e20200c000003c04500c80f04060800120314103c040300c0741c0010b0350a01400980803402140301c000307010300004564201400c220b94150920b000c0e50820fa6020070341a8027503107000c3c0507600800c02550703d82c4101d43c8090b180c0c0c0610441c4c0110060b0b420682e8035148100c40451142006d032507160b0b408a0740040100031702800500540495040103511403181410b10042242100074031003102d080c0d841c01d01c046651607505440306402480040c18370b41001e181f10801d10300c680b044045070400c1c440d0060078040c528020510652034001c0072150290401e107091424a400c00003005242c1d4110002d00c5507101042415140d8010365540002c45521441c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 673271438 1250 673270188 673270201
    0x1b01020d081503010603080915070f14030f0d0c2d0818010606080f090105060901090509013201090c17040c1809030f020d05180402040f08010506210607030203 70
    0x1030003a0310102c0001e00a119032074490412080580c001e00d15944900c038150b0001c614641014140d8030403a822602c1198450300c82d403100301490f16892076080c41808100400701c070022000020340b00040c62800e00040035081c2c058081c01344620301c03210f07001145019030f10034800361400303400100301d91852901c82c00303d4a66600c007004030a02281c2150320f550900c0000300f9800d6021059900c28600b040200201391a540c004034220b94058940c9070308558190014001c4d0b4481e500000d82007070206000240d02e180d9140c0ca21010700e01449180c401c01c0080000310307056900c0c80c110501500b0100300c20041c070b00c010600500803507400070031084130421010008050084120307107a40184240c1e6400d4244408080200b0018842c9010031030200d6111000d001035030f880041c032000c41300d0a50321407910304480144145034207025030005e50b03481a000c1101040c240255400e00005292070310020411303040000400c20440c002d06119004101030400d00468200009801c98108003a0705005a50b0707155038 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 673272688 1250 673271438 673271461
    0x7030903030b0d05032502030a0201201516050301050303041202030a0b0a20030609071124090706020a0c0b0a0e0d0507050a1e031209030506040605091b01020d08 71
    0x4000c0d2a030043c0e022054605000d4040b0041c0051348208040c080f440042488040c00d00d5503407a0041c1d0164002041c0000550207210001c08446400e0301808000b00000304c941d190001030603001841d020300d90305000d0f40305030304c02e4420100009420030070305560400d4080303990380c0100d120381d0024840003c030b65029034806008020216800418082003071400039405005002c1041602030400001c5800c0d483d448481400d9a010b0351005110400c107490308081107400700f0a40298003600c0c01500c0c2c5030200a4400b070720341d0007078101c251400d518a25018034003e003006400c0d030020040d90408201400014445980720327041d07034451008551114050f10080728040c00700e000715600700014400c1781c1c0900c04000307540d000715981180c001ea8000d40341c00781d84040103641c1820214100321584207100046040701c0701d410009852a01401d100d680b602d0710307860101c0503542540c00d15680c100f840300c0d10400b0b01400e51540307158041d001c0301802c603000007507684a0b43c40068040041e070b0004030707a1000a1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 673273938 1250 673272688 673272701
    0x206060109050922121d060702030c192c010801090803010e0c13060309020f01030b0f0402030a110316021c0f18050a0801021240020409060507020f070e0703090303 72
    0x841840818070a05d20b4029000403001001204071081002c0c050200c2d10700395040b186d0f12135020b0060212510094188406000302e00401c140000e00c190780840c43c1c0c14502c1c00701c402c194000240340804851240c000c0325851060f000030f005641814140300114041d1021a81100c00e40031054500382c0d01c103501b09959009550356844546611200002c0c1d9603070642103071002034003c60b22140c080001000650445110040c1941c0280c88401040c040f0315041d03029544c42903004c0d402007a0102c03c21021445580101c0704000c0c080c0c3c2c0b403811000a250304014403040c000e40c5ca0525107544a0305000540000500314152041003905440045201003500c0c1100080801030498860544c5030021300d80030350444982000c185100400107014032820024045004060482040c0b84400010f45801c8500160000d402e001420350f81c42801070300c8500c0303001000740c010000090141450140241440c020b84034651841d4070051040c45292039030304040d0380012403805c00017558001d07031a05401501c407 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 673275188 1250 673273938 673273943
    0x180a080d14270f06220506010f15030c050d050405010e06090304080f0a02100309050a0c030f1103010b011e0c1b05030706090e010b0f04051903030206060109050922 72
    0x89410034003203014040401e5a00c2c002d90000c0703210190344407440c2e09560b450159444100360340304a012409841c070050305203500031590140100008081e444162030b10800380c1c00340e244908031220400c04044854003d080710091880e060141d0094035100038086e0240010304800d16a40c0d00104042007003d502c42501d848003441950050700c0c044803150748a0f009440380101c40c2c0600c10728004085c40200b200c241d416802000c1a50003078850000314024510710b00111040e10030083d90102241956000d4401140b08501000d01e582c000d02c0c000904100c400c6446001360f0600c414400c05a8000503000008054044412038060918900310b0b060001500c000e003584180c0e81e4070003007204440d4202d00544006508650545035140380844610a4a00c01c080e01251900c0c010310105100d90014401c4130f4504803000d0416403600c0014500d030300c039000c40e0a1000b070761450070400c05070103100d456485482402c00425052500020841c00c000c014603d54407070a980c16000901c0182501301c00c036054 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 673276438 1250 673275188 673275221
    0xc040521010c020607030f0b031207060e030304050f010b06030c0d0c05041706060a060513090b010201060914070807030b032d030723060c040b070203070315090b180a080d 75
    0x408202c406501c40b90159a0100040e041c50302c041881302c40382c085d010b603d00340035000380742000c2510500c2e600354120f08412164241c40d000405c502a1040001d1070003036006d0b802611104840005407421191a01e480b1402484140204078044044c1d40585800060011010403c000c050404880b0b43c40b0b160452080000215505401d50302c000a0741c0344030741d10070b8450300d840544915007a00c8902035016900c681c5842d507501403002c40401c2e08901e0b5605410700001ca40320b0f499103c80d8091722501215908079036101d004100150f6400407002d80c1210507401d0030032400d504a400f02e5101c4a03115240081c00307100303054041034a43c0300f0301115280d91444064a8580c0d40b646404203101c0d281450f40c01044131914242e03a0b0042010601c61b01480f540384480e46098907001880609811a040903039040c0903280c00000440c3c00e0894035800c0b450000800610100989450400c404000c0d000c1c01c07980003800207110100c00c1c00281c22220365000300195441c0d008240c3c00300080c1c10303000754419051 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 673277688 1250 673276438 673276451
    0x70914130f1115040305010b04050f1f0f060c030f030902030d0f02030f04120201080a1a010e011e021f02040302130b060d0f051e040f0b3114060c04052101 68
    0xf02a00c0a0001d5a1152000388089120304081100382c40342924680c0d04c03d03124101040c1c02101c14000c6144460b00c4120341d500c00c80c3e4540b03604180c1c1c4025440b20303000c02c1074160004200f640c0005105445909410100080d004603000b180d41c0c1c5085801ca0300c14040d04901c1d401c99107000300140c1d00f4401c04d40c43d03820760301c81d1100b035403201c40480c102c02213020079004070200d007003441a4001d052629644c0c1d015194041ca40380c0045440301078a40c11241405200c2003480f034458801c0c590a03194a20540007098548804550300f04440c18091990045610510003480181d54000f21150b50041c0d403000400c218003c0c400007030491143e01c0125101034540481100800b009400c81e40c86811200291580018011100201050120340080c030203240803070f1450008942d852003a0700031200781d2245419950504808844914014040c00001c42040c03420041040d130314001c8610145d42c3c1c0261102d4204040031503001e002d43e0050310301c184002c40d071f004844040040001d1184001500a01c200b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 673278938 1250 673277688 673277719
    0x110f0a200d0c05121216021c05010c0e030d0503182b020c010e06090d05010f0c02010e0601061814130216020a05030105010f03060504110a0305070914130f11 69
    0xc01c1e0300c0b84129409100c21405070215a640442c0c00a203070201c00390600c1c1b410a40740541a0840ca18003422071f400381510055801c2184104074201605214800004c0e031010842009001d84da54855824844d500c0201c01d00c00041e0703c14252600500c40c08002c85040311144051810301d40a146040c3d819080e190b940078034846402a1082803902030340940781007422000c011141c400c0c0c60382e101504076030100012001400d10f8007241c0800d42c05600001095034200e0380100c2a917000302c00031030040c1c0d12801c00c0e0b0f250f210709004440c01000c2301e0030003a1055065200750310b44000c40f8800c0c070003118070646800e49107854840c100d100364030b901002155581240804400404480b00d000c3c0c3c015215080d001c0307124141442402c0c1a1203c00e0003690041e41355559034000f40800610403183c0c2c102c030411074420b9807030343c03070078075014520440c040c042c0541420b145104444551402c802101c3c0210280002008020723490311244e03030000700310888884107013000c0080301c424519594025030f100d18075951 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 673280188 1250 673278938 673278953
    0xa02011d031906050f010f050907140c03070302100e0601051018150f0918110c01020f091005030402090103120c0b27060609011205121207110f0a200d 66
    0x4a0b2441803004014540781c0854105510b8802d005d21000341d410342c60b0a00903858441c211aa01581c0f03450400800e81d80e0032070880031508503c210250f01d40c00404c941b010140c06226401403162000810040f400003103580594405040c41414020031b107030710740c00700400d1280e440c035500d1141c804481007034266100191918030b0282c0031001b00080c3e01d01e80341d600c40351044c0c944400b103074a4480000194032031121080000c1180f03508082d48250104003811103001c0c20f00141c44861440340c8955107410100080c0300718421143e644904000c42002000010f9445102e143d05480c0c101180740010007103044180e801440c149005403540400e581000ba001c3d2031804075089804131002d00c0b0702c0c80e80c15150080e54592042d145c1c00c0e8049092001484075144060f103802e1010f01400459041d41b18801854105504c1480d1014510380c0e00c008204106070000c280345000c0030b0b280c3c014507100480d1401640c5449001000070325412207005200e0480d81a0300500d80b424200400c4a00d500348145006030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 673281438 1250 673280188 673280233
    0xe0f12040608180a0b0c1b03030f181506060d0207050606030c03010c0905090c0f07060c1e0203030a0b0f12060a06060801150c0302150c03091501080a02011d03 70
    0x41c0000c25560008030541540c10f42102c418685800a021007182030751164000e11000704030700c40c0d074002440200409182c508102c0185242800595031782d003884c4503131038001e00c0300a18000301048202003000b401c240019940442c00301d07226082c40140c5440c4000f919902c2a6205094001d0005c9101c005104001c44c9090044108804036060b003001f80c0c0a00d82038a038840e100c40d01060f00c4c41070811160801080c130070b80c40800c022405203003041c200304c40821a04041d0701031f22030595034001c80d1712194009000000d651180512a00320716a5100004d583e071100034590030382d46403036001c445403d440e400341d0741070034280080c1684608200041c06a5440001f1a4102c0c000c50800400040c01c50249041c24144d500fa0700c49801050f000840a030b441e0740c075140d011001c520800d02e40001d08000301010500444041150940d01d0030480c0801d0b15004404440c86212440040100929900011010035155080c01e01000906001018407181458480940c1c0c247c011405140c6c0000d000041e10b0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 673282688 1250 673281438 673281449
    0x10b040504060b0f0126090a02040903110d090b07060213030803241806061c02040f1401080c04170f030a0827060a09140a031d061c0e0f1204 62
    0x400600040c00112011b0516800f102400549446403090038000b20350701a0f4021002d108981025005501003421540340000540014401382c3d61503812007020720440e6003040403403809010080c105040080c0c144141040141000c2c0d002502100360515852078400031600008035030b449107010412910305d29110102060300300c0070480030154529101d102d00b260310072100c0600e602e669843c42800000e9100d1408d40e1400654030080281c8248507000810141c1000070200c2c0e051403814900e0a04003401c4400c060511a142040100000010090301e00315001d4451720003602c0481c81c000d03424481008010301c840d010000d69184081d80008a40b070180c0d0400101042c11808004454552012000041100e42280004c00c80c0e20004d60080d01c90076005221244955000092040c40d11424150440111fa440c555034210200c80c003c030608004402d44003e03281685614030051120802ea03503030044183d850000001030f06081000e60f0711b12403140c044030b0000180e0f45210b8038a41062084 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 673283938 1250 673282688 673282699
    0xc05010f1803140f030a0f0801090c020c0603060402040806011e0803030f0705030c0c011a03060c12040204110c03040b12060619030903032003040b010e090703060b03010b040504060b 80
    0x40c2020280328190180180c15108504100d05086036108201905000115000d5106520044000784003d0006220b48a4242c032050301c030110554019028000503440204500d00d40300703141c8200d903000b0520303c642050484030b50340d60ba40c43d000041c1c028082c03030b0054402c51048900124061403101440c3c0c290403005101402401e0391603403080e80d00c0c0700c00c9a0b1031241030070810108090a01580c05140c10054aa50702400c00030003034107803403c541d15540200b0141040348a420014281070151031f81015044040c1403034510103101c4820707a401c010b00001d000b1581d914210301100300010580f04100c41401c160b0b503541c1e5030703280381100c2c44d0440030800c54001c5181e0f001c180e0300d18022089171906110018411060380516000b54000c02d20b568040e07040c580c0f60010100c0c4074069413400e0342055070000640f5201c0c10981460221080140c1100072403a11100c10b000d40e001c7c00003006c40031a980844089400d8a500000c03d014080b00014507400500b000180810044107070813054040c1c40640e40e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 673285188 1250 673283938 673283957
    0x51c06050909070f12030302040504020d020318010c0e120f07060c03030e011803230307030f0612170a1103030a0911100509120c10020105010305160503070e061201090c0501 76
    0xc59103c0001d480f03642c1c144020714604105080c4000320814076203003c1c1c1001401c040d0341c0c1c40800d0a90380241c620140c1680e0000030000c8100d40e1255070403a07020044020403008001036805844410300744200e42c801c10308800400400a81000001c1c0c00d5440201500c120380d0766080c010b01070884000b400c6000c0b0b41014403840b2070640c14421100319420b1000a10500e6546450940301e0b40d0400c4104024081c8049603030120f000c40c4070065002e460b85035000a100781c1c3c503c04441c21030b0300c140c1111151000080201011401c00a1b110080050800010b40d59000021050300c030003c07101100149400080b0400a1424540c1d1240005d03901518400208060403000c102a64a160140d04c000ca0380501c00160a81000c0c01516030400405013154804880b1800280c02900e800e264500142c0d15040144100072080c00100c010701c890f9030079080400d04107400240c80d00c04500811504030180000180b85d82e5440031070500060081000304201c26090070b040719018081c2c0100d40c080b500ea040d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 673286438 1250 673285188 673285201
    0x705041a19080c0d082a210a1d091f09091a090325020109080d080403030c020309090103150e0a0503030609040c03020d030305010915081b04140a09030e09190b01051c060509 76
    0x40d44024040d215004c03423441d0403002903080e10705030b0008141440d0380e0070320320350314000341c031480d03401b500548074100790615418802c5840e1700414045d400405e24107041c0106180040d40d02d248408407201882e006103a1580d400c05458594091125860000460a50f03000c112080c184400c03081d272030003aa64200140c7e11031040aa490050030a9800040e0680d400a80840e100303034414050b4000d2481070300d19000b90040065043c075801e0b001179614100c00d90210464112078490b460040b900c1a000e030a9002c0e2903268280c5038003000f031400d070007081c641c030020301004410304417240959401880c105800c407103400c001340140b03403d0044040d070614004c01c110b000c482d210700c40c0381120b0703941004280051440110700015003021004641243d200e40308c1c10002c407020f03002a407044540040001d9602482d060041c8092003209900340696101414408191101d40b69440b9100355000c01058120121004807841e00c02c11000e206a1801c40c1090b0920602c00d801a50449608503842c90441d01c44a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 673287688 1250 673286438 673286473
    0x7030b03300a0806011202040812091009031205160c06080907050f032e0629180409260901090e06060304140705041a19080c0d082a 58
    0x9000b4070041200c1e60000342c215031080380c0982c10702c841900f0240c03d1680d140840c03441c00c0705002600760f40c844041034256040c1881074003105182e40e50725000c0743c8240b4580340d052480c1c0040c0c0c2c1020800c18005050464840c0045184030060350180c5000811f680e034420007441900260742c94281030203001800100c070301d071001c0c12014000004010b00002e1303034003800c405074171040704140121090443c4521401821980b05a5009141308450400444c482003019641c0b40c6040c0300b0050007100500004980c01210f201d6500007040071303100002d082d0718604003860100d1916409440c04000d010824600080c900058144001c01b0389030219030640b2100c0001007944215811070700180c083c40040d001c90701d10140c10301d821031080e058400c95030300c6001242c241e03030240310454486140c003018080a810a0388204584400004007014001e040c56036950710341c240d0100440c89003401404090912007034031f0032208000c1c60440d84204852460034192054803200c0150041d034003545603444801950b0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 673288938 1250 673287688 673287697
    0x4050f0702070b09040f05040302060403110106060c1502071212150b031302011806050316050a0c0305030a0609091b06170103020918030c16080a0302060103020907030b0330 76
    0x894019050b03903810407070040c07142c1c1c200b0340141d0392080d11004000781010151003068061070184e8060034042c945400c0c058141000400503031a540e25080c800c102a40e4880043c6100a6101c030168440c00c00346c0c1c81001c040d00956601906508048818610560700140c0781c3e0301c000d2800030b0070f024041151b0f50425400c5242d210303006800c02d00700f0016000b071040c0361b612080c0601c141000e9954505850198910740056000702c4003092001040c817204100f082c8614840c032000e403030000d140400d4803c00400303014006800400340400840403464180c490b800c0003003e004441e604004087c4c460130090600241e0861202404070001c034003066292007442da21908036040119112941d10b55802d20050301401041910002e4225510140450f8184012704901410030000c00007030f90408107114401c0400d5008400c1540310041410004e0f0700441c2039811030360100c590200c1030b91650400d0b00544014039039654940281400303213031194100b00b15a125019409900e4500309481e034994a524810f = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 673290188 1250 673288938 673288951
    0x3120c030207090207060207051e01050117030910020f010906060f060806090c16080f18010e0d140703081215010e22290315010308091302090a0308030604050f 70
    0x38000902503d0700a800030300350b45104220042c1b40401c65141c5d54100000e100b00e215695100102d80d0003100b04c01d004190250141190500018182d5801c80d03503288038240100c0c0c003e42d208280101e04a009122411000c86454000c0c80402003a1030010000c15403801707405072001943d200420001d102d00f4505104a00140c000c442d00d49480c0381c8c00328990001c000800b1459044040134000400c0c0c1c502900c0a262481c400075242d078403d0005801c400480b001840c104050180a40901d07070b20b01d111741d4070540d0002c90840d0503d1f49000c0c80c0d4201440390304040e141200000312a01c0c03640c0d80780d96152107050910054039507022490b00441d04030f20346c20b13041540f00c5807100d4841d10f1110100e0200207851036207500010140c0001003c620b0300c19002070040100d1040701c00319507280c2000d014440000070b403a0200c0c2c0b101e60642c2d955440d0380c002c03620103a000f40491014090301600b50360440d030342444010545141c40750380b403030800c080d039208032a40c5000d14105004034002282d500b66081c055030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 673291438 1250 673290188 673290193
    0x30c090605060720030114041e0314070606050d03050a0206010816060e1c0602031017030301030605040c090501080105060a12020a06120f060e54030c010603120c0302 73
    0x48180d1103c034448504100e60a205141c01113005400390380900c55040c011054000c4403e0314074190400110003c1103885a4968a0045041d180001d0b884a00b4020040f00e45021580720034090800d00c00a04c1581c00ca203400c85c2240c14618241900240034040c0404a5800c44040780c1e299000681c85d40e009181c2240c6480110a0501000b0b00170001c010484601401c0c8401c108526450090b500511a1068038195400424040003104203850301e0003810321481ca100245400010107030790307848144400341a840e96800030078100700d14600300305c0041c60301c2e41044c0010b50715017440034000c00041e00c1040c40703004194000039944013155100d1291607002020301c40380d02e24204060741d841203880052102c0d01d41c0c60f101d2960080c564881c6102070590040e107d10700340342c00001554032480140e1444545283c4408000900103884c4401486014461a0420b00030040b08070010828010000f00c41754080444c1c2945031100560100c01200c0c02524a2a003125821900303130395541c40b5500140058 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 673292688 1250 673291438 673291447
    0x50a051f030323091c0b06010c0b06090411060c032d0a08250302030a11070512090112140411090106050f090f0d1211010b0a09050907090c0504030c09060506 69
    0xc0441044a140f41c20380000c40c40c3c10142d1000a0302038181280c0000c901500c401c03042d041c0000d400f58903030f00903000e090005a00701d0359114046180c7d40109054808c01e000400507040000181010900c0003001e485240c6800042c4c5503d078070f90308402d4000c002045004410183c0040d10a05501060072983c40740d8540342c13041d00c04a84198000b03002c4042144c40d4111486100304c40c0f0540b03288021280e600689a0400000c1001a00c1041d010803031803050520903140420004503100c13150160a000c501d65800c00305005a074404448480002c2c1c051404141181000c05400c00714807440c0f141c002d402c12071420714104080c1d45000c0c012200018030921141a0a8604000400ca1030100425000214403208002144102c04080440d00c0311035407250040440d4002c403580400ba4201002070000002540c0820006c00251060f101000d44036404211992000c1c82050090310003c038040c0481c610546010b09254482c4c4000c8404580e080340000342e03c00c00d48560425124018041e51a0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 673293938 1250 673292688 673292717
    0x8030601080601030e07090617010b010f320301090e010e0c040b0d0501020315010809071508060d0b070917030301080715140a02100c0c050d1110050a051f0303 70
    0x10398004107118141036030795412642c5c001e010040d1030000c02c02e0000c003090481c18000e000c201c0031044444180c09a0514800300382c00da070004106100100b041c43c159000701c42d002128041d00100c590300c807550b07840d0000ca548014080b5001035058411a89041c01000c4180c0348031400ca5009030f8019038150030a2900344650b00d02504071035076840c801803040c4060600c0f44ca81c0c908991041c7c40d0000c031142003d00d9950700e541c00101c140e600c90840300103010003e24000e10314203040b00c099a407004000030500010400c2c6e4504602c050166003002c413030540e0740303000381014252900034043d204070304010345809145445d00000b16416200d0304000f81c10f48a281020032050901140024400e1010607d81c560070704d07a004020b0000441c0326801000300e400305041003003c44400922100070002e02501d0280820380010300b54400907210301d817032250b050003042883d043c003420541c0207298070705050501c400341e5800d0700b00314041d540c100c000d0700f14140044480441c000580c4001004a00fa04100600 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 673295188 1250 673293938 673293947
    0x606110a030e120102040801020d0501080f06090d0806010908031308120702150711030a0c0e0c0f0a08070e130f05150d151508030309150712090507030203160e0601020a08030601 78
    0x2403c0b49650016003010340361060542039070001c02c0126900765070b80c2c00401010008010b142e0006082201074402400d003080f42c142c98064403100e01d024010908007281450348203252100080038480107890b215560389412918529082c498a01030344504400499602c0400c4100d8032456401005010a9048141d51116039008864180c0d4068158448203001d52414020100040d20880c070ba55065401d080d00104892000750403241c5444060121001025560044a8020405007030861030b0b950381c000f040304c007642c0f82d070003158010f8882c0d003003080042030581040034200ca045400703000d02d81d12040444403205a00e010305034814080c060210109602411001c4000814140841c1d44070025910041a12007070744225065400042003003404241032080701c0701e0001d03040c12116542406000242054124003c4141e43c41e5a0008801000001c00c1010000c55000d001d07036610041c0c80803190402d507114842d401400415000081d42913201040d0300300001c1d4081d0242c2d0668903106c00455 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 673296438 1250 673295188 673295209
    0xe120715060308040e0108010c0201021606090213020c030d060b0a02060115030e010603150b0901050f12011e05060a08060712050c070f060b0415050a0317120a0606110a030e 76
    0xa14281d55044040003090800b0010400340c81900704180140d494030b0304c3d840c21a4091040041103903c140b10701d02ea01984649140302980d04400d002c60840780d5800050209040e50b00c845041e00d2000078070b40d10803100480a0181591002010417442d40e907405407141c0c0d840b8070340300900140c01010060155200c020b080c6485100503190000d46000d13076204007421102250419140c07003d0207010b155046005000b103040b01007044c1c1d00f620440d403526010529020201444900c20b016120440721004025402219a10b46040d00015000c4c10324602c0d20041506641d0140103042141d0003050010380020010301a94069070340c518851213000409000340784c05070080050326410400fa0000c1389116543d088040c2c007990002802e1980182003000719201d40510b00c100c1001200204290303079920000074106c81e0403603c080c07a480c0c88084500c03050300c00d6103126000980301c00140310030140b560340520700b1f0302e0790360701e07104c1160100c085c2450380c0312171000f001000500c2d0318040c4074050401d80e8004 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 673297688 1250 673296438 673296473
    0x103060501020c060d0e21040f051210110c16030b060a06020c010c0804031505070e0d0b18031e0706060f0b180301060902042408090d030b19180e1207 66
    0x11280303030b401f440c0e44020f0202c4601e40c03800c010b24042024040b02d4494108840149000c94142d2107400700382e04900d8aa221720b205100c80c03141c3d141d500d036603074848200446c0c40102c2c4110980d0100d0426400c6031600da101400242c98071100071000500d103003450300c1075909848581d00140b580e807981c00011110819001d42c01c645090017804004002440000d003030100803c50400450340746011507005060017050300c2a40d115585000c6440c011852280b0f141e5044811641401041d0704035043d004e05d0743c85022003844000da60790300c1000d0005824005040c295100b04005e0000a954200c041e02202c018000c4000d201e0f0200440405100400d03181100a00301900200e99183c0e1058610700320b8000398007038070940780000e9250390390010265007040134059038140704500f0709083c2030041d6110702070b082000506030f4070603c0c3c005a6842c142405210014110068089900d80302c41800030545d11a40259080c241240625034240c0400c115410a212103c554140342d002e403241004c40e86c80c000c2d43c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 673298938 1250 673297688 673297693
    0x3060b0a030605070806010f0201060506090f04110c071401030b0f09040501090c3f03210c0e01020610063c03091707020108043801050103060501020c060d0e 69
    0x4000b5080f4020030307109408a89070250b191911394000f41c050180340580d0b40859151210521080c0c0d10720003590080241a1039a04180034a100898010801030501052040d80450f6007591640c002408900381c44030081d00e05101280b54005405540145442030b40c0300d1407400c011005401d00901c0640d0050007000007140802141c2c03184407110042d50007621540d94140b00764170880d14009000d0501c40406103260125124040c003c08540701445002820898140c030803801284031901c034125a540c0c2041c0c01c118000c08500003500040764900200d0140c015840080c0b04949219005800c8543c10b0320f0302c454020f00162410780c01e0858a58034422a4034891040044518614040c10202103130b0301c000516002e00c1c10450b00b0054004000c01e500b134010024200142d0b4050281604640d000d42c01d42c10351030b81d00c5586900740400c5d0a0408904290140c0c00c0c06910301540d156048400a0300c0801c182030702c4100498840c101860507a8102804202c950076400b0541d0000c805200d4003420f = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 673300188 1250 673298938 673298959
    0xd05090a0213051e100504110d0204060c020f3001061a0d0509030a120b06090301141503030a1d0d080a0512010906150c05101107050c180103060b 64
    0x180715800e4914880700c82030365440c10032113480c0c1c0b003207034542200d1043c908002e070601d041036403007a03451154001c1c0340c0641e4403000e1119000c2d034450b06035000301800040645d00d5540b80e0200400c002c002d12403d902c44d50341c0b1036100c615414040d01160581444291300d6038000242d4400400300861801c0060040d90382b40d034009805280070491502400020040c01e9441840011600a0743d10141480f10700383c0007003290101e0300d504034000200c41483d0b1100440c0e481440000107150340a840304580e01075092030701440d42c00003a00f240d10302c900d420060141070454600145541d0b40190078008003c10103c24404c0c20704850200d0440c05c1850041101180641c0c95035092995000001d030301011400c08150303420405160883e4502415070008200b202d07610b0401d0500603901034411800c01c0c40041145c0c02d0a01c2414400c403881c46141c0a02070004900211480f180c2e03600085081e00c0c0da00440b44e072604036107003070041518170901c910b0b0400800e900b07583b42d038002885010040f6900210159 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 673301438 1250 673300188 673300193
    0x6040504031206080c03151611011508061b03010b090108091e030d0b0f010e10020705060c0a03080a09020d3008042907030b06160503040302150309030d05090a 70
    0x5803c1c007030701c0044040c0064a00d200140b5140450031040403540700501010001a1443d80032404032000440c6441c11341e4200d11800301d4010300007960f44990006000b6800300340c2d03510000e900c0d40204403500201c0c0041c0c044103a6101c49000a02840c1d500308030030800702955601c0f0f0b07945560400711120903980100802040310725a090103090480d100c0d00080f03000d104024141c070414669200c2a610b55200c10b0700440002d2490080c0350343c7d40d200d8201c0e43e400c11b1001d4402c00003407028120240c10195502038001000b80d032410084000c5000403100c100080000341c05026283d40564007806c0d402c0c590305595510202403480d04070030146410100b07d03403815241441d40d840f4108d405511a1b107018102414400071542c030321000c4240c1c540c4103158202ca19442d070714529034008024136000446416000004885101e406014001a1628050801401400710040c400c90b88202d8001410b000503141405c018041121600500c0e007043c082e400340c11005410059000000000f6681c201c1001d5 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 673302688 1250 673301438 673301441
    0x1707170a02090a2411031222020d08090a0f050a05011b0b0708040b06120a03081b0705070816081b010c0605040c0e010614071e1415150603060405040312 67
    0x11004c04118501480782c40c510a90400748805c01544184091854100300c080002103c4d000900303c1111082900403070640d409000320894411a03000380901a40d010504242c4003c1d00321180d500c1c840c0714020030015031814072504141c11141c01800321032409141900555001c00e406015003c0907000320362000026904904681c810011501c0d211140d00b407608202c5101d080082045000f58004c0140704d03050080020344c0b59005038185000b4020340d40d21180d044001124030b20420f40270300041582c0c01044000702c0c150044c1c4a6282c2103a1001c45890a1850b0900c81c610a44186030020103c41c0c400300c0321802c800d084000c0c10b040ca00d4031305405030740f29011558126401da8030700380b11490070b02aa4291450040c01004140fa24200132041d0520404440c4607041c00200388020040f00124012180c0d9074450505c1e40040d501c1d0078042a802c02c4988640182c8250b940625807400000c00101c00c07403002059034400640011f00b96a109010b010041c6009082070f001d20102c4900c2c18407200c280d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 673303938 1250 673302688 673302719
    0x1014090903040e10030501060605030f040b060406231305070c0b04170f0a143112050703050601120c1503110409020409050606030f040209040f060c1707170a02090a 72
    0x4130225664a1a40c00c3c110700b120055044881082810800c1c48010302051200d80c0d00319030410b0300e040645d01e81d100000c0042059034014921052a0380901e208243c08103400540c034070081c0c0d6000d0484c00000340a000300c580c102c42c10b00209001040c000301040c0400c2c0c1565200d8030030b204411031802070500039180c0741c100c003404c65025900020040b401d16401030005461715556100b550a1448940c004901c0ca02e0b450354079110b84070240f90894145420191810041c030794000445e0b40030340c0c54240203403210518001903c95100700000094504248000390001da500801d40d01c44190500c0502006415001e05003002c06445010850740d000b03c0c40d0042005201e150001a80ca5140900751402d03104018a0540309400900401c00940b40349076031242d1083e811604d80d801c2e070743e40340351034201c40d039000e40054a46403508150b0080150401404c100c05e0f60300c40e4419540d5a0781d41070440c0d1050403026070104805914020032200f000c00e401401740040c0080602c3c0010351136106482e2034000b03 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 673305188 1250 673303938 673303951
    0x309150c03070314010602060c130e0a0b031b010203190c0210021b030604080915070b0a05150d02130c0207180510060216031b030218010e1014090903040e 68
    0xc00014406500d0b018030500712414902800c0b03c0d107a40c98020b01030b44841000b85140d00030600011035420030302018070036101800d0100030307848141c1001c40405004101d1000388034042d1080201d403070306441034400342c1003040c40140d00035031810340824114080d004030034510a080c000e101840f100183d55910714054039000c10f03070050040301500100c1c1083d1000d489200c5000350003400512000ca003008044811132102540c0c83c800203a01c030580a1200e1065120107443e106504040c001070a00540045000b10a040d000f01c1a500445081180200850f04000d503c17201d07603400c0c0865030001c0e410120303410b0194016a030ba603c1d82c80700001050344240e80d51a2105654404000b01d45611400c503030302a240520042020188984c1616104c9a0074007026100c401054150480c000745c0d00c808002941d40506508417140c280c00c68aa1607031402c4c003a0550091150b40014241c00580c6460402c0321491000304200100403c00e01c80d10b00b03005001c160160200b003101003118080840082d01a40 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 673306438 1250 673305188 673305211
    0x1803080603061605120405030c0d050c0607141204081b01090c1d01030308090a140604030f180b07060e070e012108040605180307060f03050a0e0303040305030915 71
    0x5003140c205414040010b09105643d4100103040c6040b40e0f008040c3c0f100d101c148091050980c5450500910303500813004158200e11500307015009032988107001e00449410b40c811030b0803070740700d80d0f4095821001c41154084203400070310503000c1000d00141c915030800c0c01286083c4c40c004803103013502220080105019403581d10364601da002c0140c5881414000d0050070440c0700f00800e0051118940c06042c03002408104c4484042aa16071041c4015128280d0003190703c2e880c2941c500300c0c55202e1008440a40101d20f0140c5841069030145c0c007810b000c11010a0280c045a04091210100e0f030418041551099990140300491420801c41c450161a044610382481d41c9025450034002c40000703030454801800030704480c00102d42c0002d403829608035080140d02c40d015064200d2a000e42e0098203645072096000005080e604081015440812668280010754034004544103413882200101c2c42948200f00140120b0321031070103580c120441000f41c0c0c45580c02c04260450080382507074241c0004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 673307688 1250 673306438 673306441
    0x1030e0102390a030804050f0304030f050f0601050a12050a0b040b041509020d020409140106060e040f02131401051905030a1404020a0e0a14162d12180308 68
    0x54025032001d80c40c001c240c0c2c410b000003400741201d9a200c801002000b024403022101143c2086401c0c8010039000a4450840f51500c0d0740c0e0074a210329550505e015601401010103480c0181070105809058405c06081c05031101d150000002031090780c41c8017a141d03802100c034400c0020342e440c4180c5004501968551000f402c3c00d0a1001180030740c4000000407614200384600141c54880300c4041c010b804440000d100145414141ca02100701c6681c0b41ea254a040b4002c0b5089422a0110fa2a20020359003007141614523458107049200301d5030700d03103a403544101d8100940d041003c00e400c030045040c5030050501c510304501502031980d00c40c0140c0071a40c04810071107010711350300c5061a5020300f202030081a08154001c11405036041c000c00c21881c001d64001280c0040c2900305202103200700c69100381d40c1c50484d8030321024103c1c01095a000a120040d030030003540701000c08806c40070501003102c1110420000550300310071000d42d042e0380e0310780340d405a140580c00c111490181601135140d04089 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 673308938 1250 673307688 673307737
    0x1081b0408150709032d0b04140c03030a020703080f090a0305071a180405151009142e0c080705160902130302040209031023070f081501030e0102 64
    0x1140d10040420040050328401000400c06140c1240c0e2030035070707900b5003104030b40f40c5111480210f031300380201030500610103051004001e40d81c40501181f241c5127060328502005201019143d204124000c80182d03c00720040c000704400c14000c0c0740b01002d000c805890301c0380300404a20b0b42c15490f84240e6280d0800482008280c0b040064015020b0b078111600d07140410320351003840c2c201c820083d414050744d42c40000404000504140011142d4018406807034816400310040c08800140609c000030a40a2500900c07814031200c000d140f00f1800c885884050281503c1007051522480741d00204840aa25140071914010040c51118001d0018000c50040c00c4805180402c02d1740c00b0541729441040a000595030b0404803500b5241e0480d03000d603a61602000003840d226100c0040f4030a00d18040c000d00d1b481c00c160b81000c0c450038803100349403066a50340783e05665003402010702c8004544c1c0c040004040c1e900e68407099100c254141000500e90404a19050032038000c083c42c3c443c0d441040c0c485070007 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 673310188 1250 673308938 673308973
    0xa0c030807030e060702010c080304020d06020f07140102030709051c171216020c04020f120106020114070521130c080105061207080a1707081827010501081b0408 71
    0xf10350401d481e00c500d0100c480e40020002c00d2002005464264088041000c40d41c3c1d4140341c2c801550007c0040d900c0340e4606629180640c0440400c59402692440c00c0c20304d03100c10300130b072032080e50191602101c1d00e280c1000c0c0480f4a05022209145000d605101c034001f0b695002064000c1c0c690783d07116500d420703900c00d0f42540c0c0c80010300f031840c458104150240d0300681c000b035039140e60740041d80c0160b200e901240c0c403021180540745181b84130301c0600002086041d415446010043c880c00741502842d241c0030004d4409108038042140d1000d0110103240c1c0d911b01318014160404101ca00b0001e043d0344030707150581403003c1c0e80c009030004c1e5114000e001d801e1170240011541008080081e2050a103010030f215940c07400c3c01001480012504005101407100c1011f0f02c5585400500d256500c120500c103008031086001e00041c0f1a02024082e2940349210060300350100c40c01c9445840749900b00001034400c000010054000005007031020107d0b02d880034060401401d4010041c580190712200307203032 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 673311438 1250 673310188 673310207
    0x40e0703140105010509030d03180f06020a03061d04020123070c0e070201020f04150c0b040c030611030f041403040503010908040302040e010c050d0903020c0405010e09010623040e0a0c03080703 85
    0x13030400c6406e0141d0b510954000c250319402040300c0c1000111030b1b4140401d140524843c0c0c9021b00441c0a205801060116980082c650701d1145e031303001c200e49a2178170740142410201250300320540d5400740014005500680c64103180c054021142000e9150180300701c1c2c401e42c8091012180741124040402003007170141c04c035507000546030009505107138210207041054007440c440c142c0701030380035540da0036018052541400241e8000d5031030f0790580b40c01e0810444102107031004894081c602001200040051825a8044e192900318441a034896455685020f10140040c2c0d615010030400010150350074070500c26090f105140007030b100e502e503004100c01ca13940d00c10035a1159060200505020b907001040741c14418500c0800190b411030360404070300e00811a0766058109213042e00220705400c14030707103851040000310b000b844400d0f02d07503030310b826a02d050004c0c5e03401c4160f0202e04003545240c1078005109601c0c42c0700480b809500b007074031491001d04a59005032000d0100251042c2810f5200c134100e07 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 673312688 1250 673311438 673311449
    0xf01050705090f01030b0a08032a160303080411030d02010b180f0121050328030c050901111606050a12140c07141006060e0d15020906040e07031401 65
    0x11402e21101c0d0000c142080401d544103410140c0d242c210300540d55410111002500303160b4126a1241081c41b041c0441c4101a00b0025105111212940c80f000d80006c80c5403080842c1c84101d080035107503076800d4400e1039024000312414609204981c0950302c0400c0004a0300c0c11a50021503050480c01c280030140b401701000e6404c0410b031004220010404c10801e0341101c200520620140c030520400c60718103445103600804034000051025224150318401211101c000e44852225100311401030703003110084000200807420500c01c02704d096000704000e9540c144544244d034201d105110011032181540d070860400f00e403010800102c010380c0198140b00d24518541d00304501c4604002080300e41d500100485000c1c070001504001700b15a40c95040c000852a4088404281c0b003840305201800107030041c80005007105504a00c54603100d140e400d145500030480b142240054102440a507002654464104078200000070325841389001040c0300721040eaa00203000c1034080401c0d0034542040e03000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 673313938 1250 673312688 673312697
    0x10052e050a0b040302180705070f0318230108090c0a08010501030c050303160602030c0d1d0d1713020f06040f141807201009050c03070b0403030503060118080f010507 73
    0x1c2c00161508401d44802e8030000c0e041030090b03501c1240848d601d01c201d2070014001e080c250307407250030541c00042d01030860f0030100c01a00c4154844410515070307000103510f2521244014203182c0e25500800ca210341042241080d22220680200420221095940204a12b030f40d154010024403500486120107044c0490207545810b9140749480854600e404016200560000105802c83d41107801c072100030360a00b5040c8a030079500c0703043c0549e5038150000d01905029021402d00d4244c440c4c41809900b070044d114407040398491010300000e0b20000c103000c036080700e51604a4461a510500980b0003000050b10006070641010850020800d040310460b018a42e4010081e482460440341c003170b40102d0900d80320581d140014024a00c0e111182e80f4180c09003e40308500707500170b00c03a4200105481c08ad00c1100d50b040e28820616594031071340d205101400724103000034800203204200644e00003005141101030025011103064803520039502c405074562203000c0c40c1e2103145e02070054039400301c000c1c1070 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 673315188 1250 673313938 673313947
    0x10e0a02190e062107030f050919170c07090e0319121512030206060a05090c1305030d0e03060f040308011e0b120f1810052e050a0b 58
    0x1c825a141048a14076010301c9200c00e0307044515103425080d103400286103518200025a00c05401c0d005407015100000080e0510800754800b40c15409024007540e107030030082c1034000d8420850301440d00c0c010000c64a2200600c011004029401c0c060182c200110b0041c000c0585407004010803034581000b0a12590401d001c0b12000400c54010780304100c0031410700401078003856006000800003072038131081c60140a240455141480c40c01c502c1c0c018425000c4078207079191881000440e490500c60550b10016090020700044000301c00740414400390798800400a440c1c000190402c103c08007148001100102400a98502040f0361900000019500c501c1400c007610014000c00c0305000b101c01c01034079040030202468200003d03000511540c0685a283c0074a5450900d00b80f07829903652907201441f2011a103d00c0c10307100c542e42840d00c06402000140d1142ca4400e01070301d80100000d0800c03220b1000c8001424410b00c138441c46540c8a580d600002e0b04000401042c1d0326140c0200144010901 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 673316438 1250 673315188 673315207
    0x3030f1b0b0109050403030f0903210e0a02010e0d060c0e01080f06210a08040e06040b0901140906010c05030a020d030e03070222021e030108100908160318030b010e0a02 74
    0x500c120705442c0b030f105011440c1d548506060303000d480b2885042450515003c081c0c130a0503880340c50407003001c411104042901c400c00b0004029503044801d1003106803c406010780056015500321002c03001c010300400801c29550719204211012226241c0c081303003c41c1c556016543e03000683c6584126145a44c0d00c4a0400a002c00c4a5228400b4001e8000019041013070340550200b0000c48500c0d0701c0901c195a0742e0300d44500028822041e109a80146d00301002d401c030901e413030145507059480030b502900400c036404040002c1d821024011605000c0b940d4050004200140014204030440e07800818502401090007800c0710000f000b20065030b00248440d40040ea40c131000058071314400d00071400000000c4130410000d1041200b61103184c1c10110032404440d009a024604a070040400d41c0d0340a854401410259299410300402c070600c2000441d8500b1001ca12000c1c4681c002c0c07038100229010444181c2901070150400c1d030300301c56068010131820450080282e030104409400798101310461 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 673317688 1250 673316438 673316453
    0x1140301060c0b0421050417150a0b040f051821160c0504020c0d080a1104030b04031215170a05030f031902040f03121d151303030f1b 59
    0x141c000410005400700444c050111845ca00f8042c064514803001d4101c444e101c002c4c16070392240c03242910074a003490004030344005c0414049400a101e15003031156076120400d0000800a0080950384a40e075003408128404161160b42c1c440d0888103020b442d01c03184060614605849000507011840c0068009400540c0f00390503600000c0d040301d101400c0290902e048155080c2a8110341e070068400b1903903c02e401400128004000300c5521101000c2c0c031360300c0003c1d084d114002c0d0320100b034000c100400c00004110140c015480707801f0303107016220600c11030000015510301c0b403600f030301ca0307540713440705021078441024940302c0d2468840040c011688581d076100c0e00c1e8040c410151030503460200000e4548840794200041c41200500110340d01d988980b4403034070741c0e030843c002900c4102101c6104202b5600503600141050301400310201301c03201010411401c03006036400304803440c2d000e004c51050340401940240c06144203444e095100c403e420401080d480461420380001080310940a0116840 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 673318938 1250 673317688 673317707
    0x90c0319180b0640090501050906011505031b0c01140117012307030c091a070c06031e0b040906020315010e03060708070c08070b04030e0307080d0207050409031704110114030106 78
    0x31000340d100c03021382c0c0030490401030503403480c094180c3d402d00b81041061400800d0a0781603c0b0b8003482600c01e103002031012580d9010407034611041a010001140541545001409030602448000300d2204120954540140d4003a800b011000c001c80048200b046002e00950500b043d080520003d80c40400c1640388440101419000506650b404110091031059200e20082c110a80074000d9048080010380ca8580c4806000e0f1440b0a0b4413074080344041c40f074044e81c6180c105000c407080d039442c030445014000788024808154071695a04000300025664000f65110f10207001d1101e04640c6900000340031940100c41d294801d4201c18104200c40350041242d681081c1c4914100c0e0070640d6a14002c1150302c2a506d0150030ba8030408104410147d2007030455040040035002d6844581e07131600c10aa40b41c900710079003809a08016800c1c0140d0074a907000e164154028500055041c51409810072802025182907039105001018840d095811010380204074180108462942d0324000001740803000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 673320188 1250 673318938 673319029
    0x5030309030738072105030402150412051515060d0e030702060706020a0f080112080c120f070b130b0406240807060e090c0319180b06 59
    0x100010281d2001c41c049070710014561040080c00e0748003d0ba18030100d40f0340c015840c00c6510b0020484204086901d64004128490603521040d0941d110f83e803c200d41e98040135007500e4960800d20000030303c000b00c0842504044c1c0034402400842054140808c444100204002401d0b03a071150301d00810b495540c00c88122500240e400601124841d51581c2184503400010354411808664403051107542d03801810503510381d0302d0f80098600095401e40d030b074580074840c4000d820901200503004c13805a000904008960100350391000403021741d0601590040011440d0a400116011017042401092a60040c1c0414000c505450ba541d40380750810030000c0009014507162071824503410034001000044103804980d08d1a003d886030305069944905200e075000085020b840f41d0030764140460914003d01051a00c145569500358001486900403034000d6001b90b603525401e440c40300e0300140e500311507219800000690408904005912819030800d54a48200d1002e41d000d2030001040e0802655 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 673321438 1250 673320188 673320209
    0x1170f0c0a030f050c0a060504090b010c02030c121f05011502160b0a02010f09080d0f09080d0b0307032909030a022509050c0403120c0c120f1401060807050303090307 73
    0x5031585045410017481d500b104d50411828000411400c5c0c01c000a80180c88a112080090140f4980110303030080821b580030390590041c2110b1555410421408025213400d681112390034a5001e09604911180b01d0b2405919030b9542c005100b440032551403041008081d10050035807035000700d0204170b0700c0c1c000c1c03003401301d2034a001a99100e914002e400407850156603003420405c010b80d03410101100d600c54100f801c035541c54088594a0782e0640d22036140e0841d00000d2a0f401c00300c414039600007c00d20448a140d02d40b140400010005600c18078042c4121040e490001200c00214800710308140040c0c03540c070580e00103104900b42c1d69070000d21034890300d13445140da4013a5000a080116086005d40202000d642004204042040240020012240305002200c44640c0d00d0108031020403113440020030804450800300062403081080d00e81240c0941c030010842c50b81346d502c84c840c03038581080d5000d483c0d4603441c003004843d00c180141d02c01404140c000c5c518103024a40029182d0880f80224000704 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 673322688 1250 673321438 673321463
    0xe0a1e111e030c010212030a050402031e03070b0106050f0711120111030405070f05061204061413021305090c01120f0606020a11030d0903080a110601170f0c0a03 71
    0x404081052000194080c250440c540000c00346084090070400207907002c1d114504502c121544006070841c5504510340c81281143c4542d032980c07006d0400030300b060340d041c41881038640c000701c4040040e40d4441c80d02c8005541d1000c1d9440e00e0140740b84140d002c00d040c010140a600081d1051b1802c07980443d5103c0807002461081da40090640e268071032600c1f103d98a807092407091350102200550080e80500f04849400307641d0165803500343c64500a154000c0414440c0151112081000701c0d003142c815500421080310182445448001c00c840400030941000b03650000d6051601c961000044183c0c0180860718100e01c901d40d071031007416a2581000504003051800700350321340c403103004455004014004280e07181c1c4001c0d600d8203004000e88140305280c0c1c03181100d04d40059501d140c0c9403a41c4490b810300d841c40c0c58038000c5412000c600c1080c4031004009440f03200052111074080d007040c2400012282c500f0b0841403a04c000c4c1c100a0b1402d5004081220250751000e0044084980c0f050820210 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 673323938 1250 673322688 673322693
    0xd0c03080402090a110408030a120c0507080f04090908090907020c030601261005011e0303171e0405010f0f02070c120317070f030e01180611040b03011203030e0a1e 72
    0x10b0880c040700d240188404180807d076404044000e24100c4413030364550200a0224920204541c0c5445200011400c100910800100c104018200c8a01d0328104c0d00d0400e41d0302d01c4280b00350307580503000301c1c1e0b0501d000070040da036490312290352a0041420b20080540c1c880700c80100351f0302c40c41030064600c07001500f0010030503051030117980300c0c141d00302c4016168104a1102044045e00703085c0903600030a611002c442000e0b080ca4180d843c1148d03090703503c4c0003540d0700c0d10000340c4880402620a0f01107e103402081d80c01060111500342c02217204600025070307484e03040090000c480e06840c0b11401070f401001144085070f41c040e22407003a504814072001c200c0d00b480c40c0a80304e03c4c00c501c002c0592102848104040c09401004070940c511042e01c0c1030020030030b00041d0508942829094101c0311100f11106400315200340d004007243c440c0c3d500620710300340d15600381d540c2c04d4000340e1112032101400f84c020020554180110889400b481000309440c0c001c643d00c0c401c0084180607111124042021050f06 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 673325188 1250 673323938 673323941
    0x606010822150504020102070e0f0f151e0a140a090c030b030a0c080c0909060a0911060d06092f031f0b09031507022a0907110d0c03080402090a 63
    0x240d40350302c0a41c4200103002c000e0101c024040c100c0b0182c0c00750145031740000380d0001c2c25203810b100e41d0250003030007200d0752000103070a44000040c2c1200820704441d020f1a0301a11b44580708171031889807107591032040641e042040303001036058116140707040755000340c0741e220344a000c0d5490a440081d82d0108815000840481c0100740e5041010380c1403044125810500081c0366100003540e00315429510482c002900380010580c060342d01c60402e500003000100094a40d40c81441440e1203040869020710540000881580010140c204415640d46040060207154401c0c00e8606400e5061148031a042c070381d420415540b80740d0f100640050010020b0224450303101c560443c403016180140b805901c64201c2d0440d031700400e017410300a20481da5610304001e5a01d0b4401e1051416900405488014180201c81100c0640300440b600002c8046a0364542c0c5c0c4c4000d8078411062a602c0a5040e8941c840f201d01d0203e00081000a02c4030340344a20000c40d80c01449140d2054055031903883d00d8495810820 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 673326438 1250 673325188 673325251
    0xf20100507180918020a0e040c09050f061c02060301080d020c0a0b03060d1502071208090c1c030315080a1b030209130503090d11030d08060f0d0503040b04080a0b0906060108 76
    0x354003d641b07003004103010034a18002c0c1d005074020030101d036400f500e51104400f02c401c107444640508200e000010701c030b45480094072046075821228105403603d17a0340803c84541003a009520650003000368144207640c1000700b0610384400300e405202242c644851201d00384030241005008001c00e4000344c003031008441b04201400c1128504545d500a41d042101c18049510070200c0001c641002203201000c0c00144481d283c9401000c0350740600303000f484100074141ca00b000320241526004480300c40c7c0c903a01e60110007000746001821880c0b41c280ba2500000d141d80012600b02140d1850034000b58480f03910840d4402429640d40d003c08040d4104503166001d0401415030041010100c0000c000e041c80716140c0b194401c1c2c044505840c40b018081e1010300040700c0035600003512a510a0b80c902d030108010070307110302a2f81036920306500e80e14864159449500546040c0d40811030765800c00c2039825280c1c2d0701c1440308002d44480c9c100031000a107082d5025040f000501401c5142d00c1c0d078800380e5000d0b203 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 673327688 1250 673326438 673326443
    0x403080712020a0f050601051003140106030b0409020a090504030f020307030203030f1305030307030b0a080a0b0a090606080a080309240403120b03070e0a060807050108070f20100507180918 83
    0x44c2100c42c980f442c0c3d038010074042c61340204424526040c44c240207000b03403525030507441c80b4100a0b03800c1580131001480c140c2e61543e84543c48510714005a03e50702e60300d074054818a00c010485240030f042c0644011241d292420071503104005040c04a50f000c401d0b0781c4c02c112062208113440d216081504440c030f01300b1074060305900000040c4605c0e20b0b019070000c40012000d0700c040b80081e68900c149174031110041400740c01c2601240004500d80580e501100c00980710703d5000802c10307128914146400c01d040c2c421a1604000410b00c9014401003021050111704490004e0102590182902e14960040d1004040c0020710200722000002c503085101226005821100c420351359081202c00510141c0f520300c152481c10001084680f00812035505442040e19514041c0c0c4400d90202c41c601400210001000801c4040240f04030a4982c000741e00c0140700014040d80014a070280308403440688250207108201625052808002910000704c5112400001d034510400826150540c81d01000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 673328938 1250 673327688 673327703
    0x30f070c0f0b0a0212010b09010f14070506190b041b12060915062a14101d010b0909060c0d11210109020a090e06120d020304050f060403080712020a 65
    0x1042511400f40e80036007920a08500c0c8080940d0380e07400900802c0c898a041da030300192010282094003409114995001003505401074640000703501d034503040030070a5401c0b5464610342c1314141c00082642c050072a2910b4119010000c2c00c03040c0842a0203000c002a0303200c10b014001e091000c0204ca15440303039006260458060095104000700074510464500960001c6050307201e0303101040341c00c40120340081002854000300384409841d007240104d094030007403078588610501d900042c240760042c0e111141d503850281018201c031010040c02c0d200380d90032040c051811802000071007180023a5580e080501245216600c100c8440504c0242070444c281c51400180001c1000210005150160030094150750442299884e120034009a22034010340c2c0c00020352490040c4042d44800580035041070000700440401d840ca510070f181081101080003015800102e420052070a10300794a4040b100122980391502e8111303922603255010303c40c4054240801d40640c5543d0600800160231180e811450 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 673330188 1250 673328938 673328941
    0x1d070611122811010e1c0c0c050613090e0109061407020d031814061b041a0d020c061315020906031909140a051c050a08100504020c061605030f070c0f0b 67
    0x840d50320011401640000042003001100d003038031624031f04601c03a5004c0100e0000502d02010020710b90400654109000b130802c0d000200c01080c2e215102c1c42c00c034500f0002c50303901c0503800c3c0941211a004840300000c0306910070840002d9000c01e02540001d800d0400040c800007150484804d4035842c1c000402000c814041d82d003404d107001400070310902d04650711000c0446c0051540c045801140b0840100c2202c0301c01100c08100400701400031003041800050400300035000d5546015019104591814400c140344014000c10300f24400c0c85460805066161600401c0410614440200840031040112001015000007034100120003904191107042014000c010b4648030185290308580c184039a410320b01202d6038400d000e496003815a2140c0c3e0030540740c140103596500c00200740c886092903102c400b003015540e5101401c1040108070040190389030800c0c080b2800c645410050301808828030030060440707255001181e0100551920414000c000e140070b220541c21400014041c00b030300fa0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 673331438 1250 673330188 673330211
    0x2040b03160c0f030503040521030406111e1e07420519020c0703050f070b0318010906050f09060619091d07061112281101 54
    0x24040c502900e09450045070a00030100d050712450900030004125004034841040400c1c069070146510601540a8034520b0314000e801c1c1135040440c0c1d44642e02d0360f0010050100b4404107128035102104840c00583c03600c0740c001d035507402001c403100550030018030010351405041c01c815040181d82d00400342454a406992030305420070b80000c484c3e0199031100d240c00c0380020f00419056445800000710840c04400104030002c0540001017030003a42c1741103404008000c01044c4010001101400064070740141145401414888005070700ca41c281c0c0012014080058500304030303a0450351103404a06100e04820541e8090f000e141e0002e05800d107031004126120310000c12191203010980240c0b21241d40c0c1404022041c0d0041c0305085c00d00b05840740911268845030301c0614241c0c0d50008a40c111101400e000b85004000d8001d1030008050f068020348030720040004030400c0e8002090a42881068061100c04c0002510440c0e0034580d40920070b01e00038001c142c0440d82004982c024000003d045 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 673332688 1250 673331438 673331459
    0xc0907091e0504090f1502040f0501050c0c100906110303010b0a0f09180f0e060f06091003081c0b101704060f0e0c120a0c12032001050702011a0108070f0908010204 72
    0xf006403008405c444011508203100c7c402c0382e0a60b02c54481010089007820011151a0003014094055110743c401d80d407101d41d101a044200c0001e40d0f9241107000e414041c00804524880701b0f0035a442d40203000502c00056000107071840e80d9135601c1c2c4020701645200003142c403031616902c482c107001c10011000790071641e16006661100a01c9030240301c9030900a00352130307a5550850744800d94540000200d092441c00500b010340090103405011286a103030b8407060700310351101071023030b8200c42d6180c0300e030741141c0700e0340503060070f2690460702c540c0c04808090010304060501421004905017401c00031f000c200c019400700c642004000010821144020256a0768500c2240c1c400e01c1440d413203101d050106000611001c986522001c000e40141c50110000c00c205021304088051000c00d1210900101c031001c17144a103070710300350008101d6007481d540282c2100c1d40189140b00044402c13502c840d00b40d82007001d05801504510700111034403d44034048940c0365294010b41102d500005000801e404071 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 673333938 1250 673332688 673332713
    0x90a0c0f081207020102030a120b06040605130501030504050604151d0307021302031e04061b0804031d1f031d01090606051804030c0809130e0c0907091e050409 70
    0x405084541540208107403001c0b0380551600240164401c10a03445400d11540052000c000d003130070042146d00c044000203095800503000313140000d4000c1220000d042000b007084c0700421082c00c0400042c01c203619035503111040100060302c4100030308035202801c900c55101040864141007034400150307083e83d845480384c1c04108107074464505410700500c41c10300c034802c41c0d0003900000b001e00703184400381441d0803401100800613180d0366601c00020703c032413000d64140502400255140492450549130143c001c402c00340361050700880c500300343c100c541c44406a0b10500003402d40313410300715658024102e0180410082e400e60b07000e11681040381010054200c0c104042c030540f0f081c8880c03900c480c14031a907200403401040d074682d01c24010030082801a0f420300107450003081e5031454962600080b54038150f0208900b00e0465864490b0b000d820f5040c40314500c0c000044070307161618185210001d0604c0440e0003085c0b40003c0300a04030105405091407400206005001800b50b80300318245107960325034 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 673335188 1250 673333938 673333949
    0xa0b0708130e07260a1a060a031b031a0618130c020f01090f03030b0a24030c2c01020a051b0a1e030f082106130204080a0803090a0c0f 59
    0x410031100a001c1d98803450001c460100700f1000030a5070382400c4070380a006c40f40d50404c0d031107a40c602c041a030703600d07038100600c95a41c00d5100481c140c22620105441d1604030301600081500e4009421000380c805883c0c41122030048030343c20385403c112642e81035075034050b90342642e000120840c480180c1407584c02c5440009450380a8034843e5607000082820380e40616030007041d003010a070405c2c0000f4021750228141c0600a0200e4040c07584031001207280c607618600c4585c4100c810070b031209199a040c000d11051444614100c80d09064840d400c0740c034032440c3c00f03a14104c4140300e8044003042c0d02c2040350a052542040031202806c2d48045401d04906a10190074003c3c0c03ca0f00010905520800803503001460f884c0018000c5840c540300c1040078800741c0011035081100700314145490030344000c945040824a50b14618505020007000500114114100d01090051004100d602008141000419006240c40e0b5030ba584508245040032450580108000314206001c5005503030b000001c82a84c4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 673336438 1250 673335188 673335197
    0x8100b0913020a0f1803050312180a0c2c04150b100302120f0603151003200a141c0204020c0a29041203020702180703091b050a0b0708130e07 62
    0x5842c80e41d017181d254940c00058140c1e40100245052029800f003615481203111ba02d480011814490b1b450800c1f90700310081d142400040310078062103000444075208200d01030f8a0a100920a1005142d00c07000200043c021003a01c0c001a40741a919070080d9504030300040c00d20a00c40c01c4160060000d4124401c140904212040011428401c41034a680101d10090040040c80f8888e04444000100280720300c024041008001000894002c400403040c06075000d8003c8019030481404200d0040c6d43c040e04d0700fa20f036445194520348500d088100b1402c540718019091208500114001c3d00c503c0000050501c0b0303503083d40041c081c40d480340c1c2450581c512034540c28484482d50042599000b0b540c0070300310400300042005250300aa00070b200c01c030b10140070301050703081242094410318000c98102010070303191400c1c201004111035010707400c055078080000c0000e0070700000c24041440c5014030004000c00203103040030712810106842881005103151114191200d01c0c120424105407841e00204 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 673337688 1250 673336438 673336457
    0x9021309050103031b050c030703030302040e070e0f0d021909020901021b061602012102041e0803040e071e0509120604030c020f060408011503020f0108100b0913020a0f 74
    0x803890280d01d0403a0341685da046440c000e618020941005100c0044455215081c0700194585080c000d00c001036000e601d0060b2510300d0020440c4034001b0040c0200100400030380001c04556511014240ba440c0546a0504c030554510214900d039000c06180c144560301441c0005450079580c00400300c082003a429518107803030a9444007a484007030440168080d90a004900ca40e014202c0c5100c08a8014501010604122054120300418011210020a80011b02401420386010359040349142145c03280c00031510702442940c8074043e0303000b0079400084400c0030071205407050301d4801d8080c14180c80756648600300000a003080d408180c01501802d21140600c09e000340c08141507109540584600308400442c0c0e00b00004801e90546c1721354405030501c004510300d00c092288280c2c40c210f82d0785040e030b040d0035401002910711190348c200381089095002c10902e08030341d01d1254101d8401c40319141e25281d00d0b40c0000c103410b1150101e0204a4800701b628020540d1003400965140340f01e88554865 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 673338938 1250 673337688 673337699
    0x70c080715090306020d0902120d1404050a03120903080f071b0b0d05061f08040506160f08040203070506030c0306012c0118030f0516090b0108130f0804090213 70
    0x103a81e80c041000c000c1000500100040b0392941c009040d101103100000500400076400903240d01c1c11521190b02e60744c0541c5036204083d4200103100e0740e04210000c25801c2c00e01e00000a20b030310105020044c01059200e4013024018081d0550001559100c2e00580c0c641458204901d4544c02c082815501c20460707404001e02034401c11200713000c0e0b0f500d0894251034000040c014001400c1d01518031504a104030002d60034501100b14108504411a40c0d002d40c0c5081c04c0c20031518014002d0075035105012030302e450010003034010b00d1203200350f42141410240c642d260300010b4104807550788003940100c000001c111200306c3e00700007940b0921098891500c003481442c4040c0660b141c10598080c0d00211804588480d0b00076181e90903200307600500600030545a503141030070a03058080c01c46003640300c060307040c50390442200000c002d00b0403204204550307c404000204140c2001d0614000113181e0030110090004040707100c0030752070304403030029a11541d40407407100035800420b0406500c00f2110000c0f40703 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 673340188 1250 673338938 673338959
    0x7020d0b0115031a062b0510060e040203060321040b07030909180c0909020f130b0907020d1709161401030b041e1104031205180319030518030102070c0807 68
    0x880e02c4c050039040c100540180d0144644902840058050180c168400d80380c0200c1e004092017651500d500003400340c0b51081c040e0540142441e039038807481c018020000340fa00e0010341000304c8100790114188100001148000c103110b15000501001d4001403914249a0000c0111089030a030080400210340c002c1c61095034800d60210040c40d0001d010700810a2140c81d8104058070750000342010301d548c51050008000304200c95118000c82c0e10390113010b0261800380c4110354002c00600150124180041c0d0080c400015014450001d051003808940c0c0c08101300040300310000c100d50031005240d210507030b0045040d01321f011035000a00740640c408031402c1c41d02544440a1482c02d004070000c52828000d405000c6404040c0e060310302c00d02c4000301140b80c060040b1020b041070303210166034001c0240400c980b0b040c40c00216000e980100000301410342e50100590400b501450281d4035808102200024421075040c541e500d58004a245001d004038200c80e82c1c22510740c02d04440409503903141140 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 673341438 1250 673340188 673340231
    0x8010806060312090103021b07050306060a032d060212160507050c0907020a02130b0a0f051807110115080f06010501050f0a05040b040611060906010503100207020d0b011503 76
    0x142c0503008080c03018000c2800300e018041003441418007509100071501160340592558103101180e910484080100f41018003899420040079500c8202c564196201d0f00c900300350801d0f4060814000301c00b01550101040114100760354003410a55450000d801c10000c02402030354011540c654450070035184034012801c403407030700c1d5000780605040d555040401410980092a010550107400e51100050340e90100700d800000560b03200241c0e900c0f2010601c4030050b5280c1040e148100184000c1c01f06554103850380c00c180030702d4425004140e5921008484041c00704000790480d42c00c044001e0120f582c2460f4000541c0c0f55001102c2908182c4030000c0d989100038812a80841c00401200150900311001065403e94034107000c0e03d03280c0d940f000001c0a50003580450005009160b0141001206021594009030100300030f0506505040010781c48003d41003079080001d500007011002c544a6010500c0d0907500900d00c0401583d481002c1c2c03106810310010100024905200340341441c10502c240d0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 673342688 1250 673341438 673341451
    0x2040615021005160c080d150e0105060403150207030e0307090903080c07031b0c0b0f090117090d0e0a03060509030c0f070b0703030906140709140114090423040506010608010806 78
    0x12101864500e8041d506510f0303484007a1b901010030401c0c07418114007801244298180786503900710081ca4080362084040b8103070010b80c42410100810000300d11017000c1041c0038189a440160303102d200c0e1600b503c1198403141455050b00413404002440c1d2400e5001c80141030180d140d4281540d80c001061500d4441e100c40100460040440135000c085088000031080d481105000ea0030354403000c422030150445e041140c4c0340f542c00180b6251659100010f42e011880200f520000c604150315229145c0c02841220303002c1000325452000075664900c041001541c200310f0412807424100040380d140d034451100750105202c1c01c0304c0c03c814118000760b000f0407a10945200c07810f1150942d02140a0040030303009481041d12000d8125620301d48400c03084c0514429280d0310941071900403445011640a00d03854140103601e05000c10000101044a07114402141d0004c1d42c2c08144000d030307280000701203213585440410420081080000a0703d641680c200340c0362300c14542c1c1d0f5501c0c0760b0b0342e5400c00c4401 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 673343938 1250 673342688 673342711
    0x91b090612030809030705070311011101090b01290d0c08090303010f051e030d080a0f021204120c0b040f021519110f0a05060103061407020703080d020702040615021005 74
    0x4507000700f4482c1c407405030045104010741c0e1400906c0d0311584c1c41d0064a4005a8400282202030301c541d6070003c0c1c480d07800c0d45440d80244804240c0340c446c080410b0052091050404c20b030402d00042030ba0b01034002003085070305030b030f956150000050714000501708080c80300c0110f10341101240b4a6074001003582d040f0f171800080703151440d01340800c4c819418141e1a007801207040f041980069036a00b4491401501030a80c1e0341c0156140c00700340c280954401820303180b0410b20401c5803017011440a84510b078826040190f019000207400412584589031100280580a1031800e000070005400b01040040d40210352044002450340b245803000e2180300a442050100045a00700303a50007552070040050488081c3d41c04500502602428120001d4086503190030160040c800c018143c4031b000040300314071310a64050310380340070060b6a4618501018201e2480412a44000e8800360101c6070815401390081c0602561043e02c40300d6a199191010090301030500e00314014030365482401d1282007004e91 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 673345188 1250 673343938 673343969
    0x30306040507140f0f07060216050d030c020c06090324090106050916080a0e100c110a0201050714070b0f070506070f051903020706150302120f062404091b0906 70
    0x101103510b64407654914030280c1d802c2c1b201101044a61020303206642c0206200907504ca20344c9081818510140810814540b400d061800c14550010ba500300b00301c01030b034558ad561520440001e26001485541803183c24861a03204180e501c410f04c03080c01074400000900c41c2c10341f100104030301c5800c00c4641c054100292100320303032003511070080c072904074401c0300000460004035482c40f4184410a40003540e429101ca440d4481a94030030b4580e0710300f1168801a08541e00198002081d501c80c032035002d080c600c80c0c1040c01003440418000c0900908131190a5982c500c20615103841541102005685500640000640450040f4501c44d0001c0b000d560780d52500e0080300364810060131550300001016800e000f17500005000e48610201c1100250410050900d103104118040b40301543c6906186c2060649102d000e100041964001500f59022503411010400c0400446d201045141d441810300880d00184680700000b062001e07040d0f6012141c1584031203200060f61751500c140d6406851248 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 673346438 1250 673345188 673345207
    0x307060e06181504081204060c111c050a021c0e15090d03031d01060f0f050d150504060929010504150b031e0114030d0804110f03100c0203030604050714 67
    0x1030b501c503440b6204401150501100206c0f10480e0002164122500c40d6580c022040b416000b1a1003291480c6003801030241d1030405d260740e07010041800008041c0400801d60310f6410f4001d1002d94000401c0c110800d00d0031100000052164800c01102c0e0302900c001e03030312829a80c1254003215140503016000b0406102e4a03076007140103115441c07440651960880300c040001c0002e000b1000201800482d8805e801e09252075000c40c103e86610203232044a04144210000700e046140b4403c3c4040e02c1c0300040c50340c0d51818000064a21650010210300d01c0c4018441c19a482e5082d845816002029412050780c030352007817008582d800541d14008404444c400c001021010005603401200d2005540e916151070b202034120380020703004260000c402c95840d004030300702001803607082e407501d107440700c60342c02c0507284c01d910481600035080c0210f00c201c01c01e08568804000d17a240381c0c000b040d0202700023415188000d4403504140d48807840381d404c103008550a1449142d000403074600303409500b0b03e009040c4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 673347688 1250 673346438 673346473
    0x2040602060f25022803080c03040f02150d0c09050a0320190806241207081f0b0d0203030a050a0e030106060504052806030207050a050307060e0618 65
    0x4010814100203d800040703408410b002410310711800307400400404004c10056120441085030135154000c2a0001601199211038a00c0c3c0010f9540304e010b940e0780320340c20002000c942c00c480181d0414000740b4ae82440001c10340c01020044041c80081010034000081240ca00000b0322889500542c219424408030380022016801103803081303000144110f8000c08294469203034900d0752503905031084100400740060060355806904070401c0c0000001c02503508480b0046c07155500d001d00c180c00320100e0740004c04c00030000076000705403c0310090040320100130f44401d0108251a20903050001c0e07a00e0b2401c01c07034584082503500038051401c006001c842203489030060090760003005140c051240190724213200301c0015280320340c0c6240c0d9540c00e1405201064082441c005064004102882d80424088131400143d07402e528000d0780c1c48506040151808034118809840c074000090382400b088041d074071004801c5843c0069500c04e81d60940c94507490400d020410000d0342001e0240203c03a0082c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 673348938 1250 673347688 673347691
    0x105010308091c0605010807051e0102120d18061d0105090c06070203160b21060d0305032d091524010924020106090603020604050d032304050f0402040602060f 70
    0x810f21001492041c0d280d82080c1c860a0b0b010b8001900301c10f805014034200b545e40c40e8403014200c5e4400d1440c00007840002d40d42c031406180741d40301c20300c0880c90039507080c2a034005140d500a020300e071803500e2003a41059402403216080c400050440498103104048040c000c02c1d01c1400031101402e620301848062026aa0100303c0899241c00b58045205030030086100400c00340000501d482d031512105a04203c41118420305d1140b003415201c10410ba50750340c0c02c0000c00c1d180d807615220b502c139140d85842501c041c4240d001d4146000711088010400b00040492501c81c110a02c1150070f0036100b5040c2c1100e580d016552142d003e244082c0402d4a58072039030300c803282c40c4010700d04221711a5944d80000340404c054410a50b0b40c501d0380f1070b41d00125509000e13030000b601321f1100070800c1c945180d0002d44507105d1442070b00d004881d403410640c1498006da2035008080502441400c0100c410300100d0041c0d0f00600815110712440d6007020303902d0401344282c0303080d1205900113041340c3c9c89001400030b00703110 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 673350188 1250 673348938 673348969
    0x1031502090a0e0603060601030b0906011d04110d0f0506010c110321070c0b0c0a150e0d0504180908040603051503011b0e2e02100513020909010501030809 68
    0x2020030820440e911500c0b00c4030000c00c01c3c003a41082909101c0201420800060170050400d41085042c14441d80e45036101600000d023428054040c14490b00e20f0340110700384401095100d494030b06003402d80718034513005042c081c2d4206c1e8100b1019600068450841e8821340d40d90740011915004040020240c124000c03402c0001411158640c0202921101c0700d162203200d500c0a2102181081c10002c21600400182444c04545410032424480b900d03034548091101a00f580902ca064144000c0c043d440350101281c20015110700c003141071805090342d4064030840c080700041c6035089007110300a03c0340007540c640c00700e50240f40c10301e00401180032b024007030710181c0c1c001e410882c08111680c091040b050030518101c0b071040e01e00900c1c100542041007809401d8040d51045881800450040c100c050ba04004200001e80d020b81b50326040340360090014a40c041c4620304024042c203038901042000c2036078404c480101c259500c03204a182a55000e02c00201140070500c40030030945002040b0051000c0e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 673351438 1250 673350188 673350191
    0xc0a05040b030a0902030c010f05220302030a0506190204030f020f0f0a0f060e01031109040915020a020105160201090f030e12030f03040b06010203250201030212190f14010315 77
    0x80d01c40110080c90340c019200340c0c42159540d81180c0840c1018818040c3d90403090a2001c90031100031030103452071140340d0440c04403200820f103100c171a841310a00900a150060102c0e03540c404030340f9000d80c1c1c569054441c03008804012001a400342168021101520b52046114030f48500765402d115045540390303540780e4032604500301c81880e9121120714400404640d03102d18020b80c645000a4503d10745081518101818404400b0b1140c600d101200d100c08420b0b01c0000d402480b82c01c0c404010b0038101c0c0f03000708043c00001c0080b1311030b80c1500868020071840006481100540000b64200c1781d1003207008240344044803540000c64094540e103480601e02030112080448001c1c07081d8210761082e500190748040200c240401e0060822000d40d02003402c2c00110700d09500142c003030311200e598400c5400381c0303105d0b18500d42c11a4429010348e14004000714042450341407504c4007044100000305194246407604c9815001411540603540680043d8120010980d0035a103034945d075102036515841c28103 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 673352688 1250 673351438 673351447
    0x102121807230f1c1b2c06040c0e060304170703020120090306070f021617100519050702120307031b1e03090203010e1212010b040501270801060602030c060108060f0c0a05 75
    0x3c0710391002030754140340940c00d1000303544101d82c1c43e0506d40c4c010b4681da026915200759400703c140c0140c0a5013070904100c41c1c403600c95840e442c1c59503102d070701c3c490a10114040451000201901500081d0902600303503006942540c02d49148103481c0240c03094642d26038064004140c4040c003c003200c0c020500b81d0300c15950084241300d860303580e581059109020069049038a410074210a11041e40d24041019061103207003003002e00250000d41103840d403554240c0d200c0200359001c0c004c0140501a10300100450340324a002c4401600800100740c0300c07400c1440d8084103030303c4144134850800107004940c2e0f6041c080901010100e000304600c103422600f42d966880d4000400390300308251102c2600341c195182c1d03120b001020701080184181d2100225501c01e20043c8150b82c0c010000041a031039880568400c40d000c2092603c00901c80d901c440032a510300800400c2003513003c001411454030103800c03a941c1d641d80301407540e502c40d001c445801e40f01911201089509214070001e0a0114803032400e03a040 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 673353938 1250 673352688 673352699
    0x4060207050c060a050d0b0a0609170a0b0f070e030a0506011a1324030207050c060f0d0501091a01021908031e01080a0c080102121807230f1c1b 63
    0x10fa07071000810501080001c19440d960b1056800717006032001082c0c03114881c0600e0102d000e420f80300c41e4082e00d009404018040da0740c000d8100400b0741c1d2641c20080116060074000604100f40d007003501c42030b00090701905402c129060001384541c40c01d501400511480e0300c1e044944580c0700000c0c40d00280401c00308101c803010100c083c91400136084101100420408140320704445220a640c0c4078141401803009a01082010803042c840c180240c0d0440e0342e818510100d05900c0c41081d10308010a460180003049a075519031000b071100d00f00c8550300604a0700d580040e641c658800045601002461252030002403640004d15040300a1680c952a51010200c0440e21150260441030a9030300803100e26045c020881d0408005180800c000c43ca0b2041c92400e0f008400c9004140820483c2d00083c005442c9004005c0f550040c40592483e00380418036000ba82c81008420980d00c2c4990b65080d82c2d01c1c0389242c50503480c0c02c400080c01076070740007004507902d22001031a203110490810300b503620000764 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 673355188 1250 673353938 673353949
    0x302030433230c03130203150f0108070303020601290c1f0905070b0a0311071a1b19200a0606092a03020712020f010f0b0607060b400b0904060207050c 66
    0xc9100031220201c189c41c003412034100c3c04005a1110190740d101c8181040461740206a0078196642c1028928940c12440c0744081c036440b0050340e0100a110000c0d82e4140481c0110b114100400240c0c800102c9804d040c0c20360050b200300042c05010b5801482c0c0402c0040c00358401400060094140414041c102d1220b641e82504040c00a0318a030a0800c54840d50520565a0b1a440040c00d003140040340032403840540180145589104c0d000118100940071500170302c154104100700c81d03d111906020296801c0e1105046e00044400f6030800901041821050250501c5000b000d2502c0c0f60480c4007002c64040220365040202c1410b07400c004600c0841e801250395400d09001f6002013000c4441d010726242143c507031340340d4402c60b0740c5801d10440113070382c95038201c1d01c050f0780002c0080f80000403500000c01402140c4150058400b459152120018440c140440000703030303410886040364070b401258000e490703404c0200c03640001140c001400040c0311f580680f07181c50080c82165a501442c40c0407c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 673356438 1250 673355188 673355203
    0x2071104110409060b0a0503040201110c1906140a050a08040c0b03040b0105010f17010611151303021e1908070606080c0a0906080a02010302030433230c03130203 71
    0x50400040a010702c0c0300344d0240384000d1030b0040e0120320b000d02c0324170014041e0102901c0281003002c0d03621000d40c0b8040030031228a5031800184202025020305071804010000c511910000c5550602c21403108400362058880c01c0443d13441d210700d0500c600b00c0481d81400b0003441203651500e014800304144880a01540c031961140c2c9540c0c02079410301c00050204024040310303100b0042191082ea4003201003c12a030f04581e210304003200d01b8085008040c1c2071022045031044e9000c401e10030405901c0400f02039111150185d002d4581052001d5959501c0400a03030f03002401e903200c0141112060162091114294020038849040c20304d81c2c2d640d6001c1da10643d11107083c0e03611038112140fa40c581f40f0054001080702200400c4101e140148007625580e65060107410305038080000390600c03044d200da881c020554410180500d100707180420150b02c1c541c45000303643c1d6103401038542c072050a0104624465554a501ca5866641c1800425455000901c0085801000740140300162010060075 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 673357688 1250 673356438 673356461
    0x6030c1b030f0d0213050d02101d1306033c0602040e0703062301120506010219030908070f060507020d02010203160b0f0c1c050601020114010801050f060301020414010302071104 78
    0x240c4c1da9481c8410b09400e5561a4200612031f0003154250340c0160b5848d50340075020000341c100300d040503104400120b4240d02071003600f500302007800c003a2680100640c4c410b0081e01c3c861803019403007080000143c507130000031442455803610005207820710b51400d004140341d4548035100141c036045d2900d001c8500e4184c103851540c04240c0340d002c2408200c0c0c904511300614506841600100c0c81c00320f000900f9481c04c0c13a160064240d07542d02084081c0d10902c500a000329095070325801ca03003140d1800616043d4075200b800c0c420b01418401051040c3d01a0f80c0c0340c12a200c549d15141451542c2d0200318a84000c0e03081207040d03120070888591610038204031580201d0060742c070300e04589002a440481c043d070080c85074020701000c010103104422004a0b5181c05106410700042559498005074018050741c4a42d14140003e5400014140707030540041d031054090020b103142e00c1d102d880c145400d0340168020030142c1443e5040f03001c107a502c268060055240a01c032450f0486a5800214003120429400e0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 673358938 1250 673357688 673357691
    0x3031e03060a06031b0503041b03080d180c18090b0a020a02010b190b070c05031507110616030207030e0603040f1a060a05130905060c0409060506030c1b030f0d 70
    0x3004540e280a1159000603c2c050030244a1010381c00d207900020390a124109080c44004000319060100c111200b51900004100d00e82d001038480c20f088c940750700f01101d4400c0040c00c020b01105094000d08029146551095425440318101380c1480b0205003096035400c40540d5072458400443d504c985100d0140c001700f40016500c000281c4003c4c02d441e003020b070490144205c2e844c6498280d561034000022a6070983d03045440364528940748443d190b4030b42c48243e03d4811121600046036604c01c0541c05021140c940c402d44c01c03003086500e0b413101c0d000c40d0405050454a044109017038025001003000c10b02c00e00e42585071961002c002803042d00156802e0340c062a204050318104a05000d801d43c5a0101901a0500b4500303400043c00903092801141c0c040c00410007a441ca4502542016050340e502c0b1040d5141e03440c100d000c00c88160403500c6030340f00603410701d9400030395400c19034100c80c042c02c0f00c120b180b441e0a0f07880b6108010040d07064001c40c124402080046880e004800152010741c0c074082e030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 673360188 1250 673358938 673358941
    0x9060d060611070f0f0510110d050301090b040e06010b0c030d06150201050702030c0c0d060b04021c0b06040509221221050105011b17120405011109030d0e03031e03 72
    0x48103840c1015030b40021020030841c003021712808071004c22000480e90704444100c404880383d64104e5158501914001c00c0f403103102c40745419190080041e40c141c81300100f04011402d4070404100035242c030f00d800102260070000c0180801c048a40041c081c218840c41120711f4062000d100004441241d44209408501890652110740c0d0a0254540004003840114104450344100c035840300107183c941131080815410120410006170400300d07020400030310131510746500444c0c80d1400c40c1e40076902c2c01694540402d81c00c45150910950f001da4001411120540e07554603900880400c4a031000300c08281e50149410000d03401d20301841050000c0d640380410b510404901140005140e042c8225007828400107000a0741d010100602c01142002d03804610712460401c40e18496100c500760050400014140703e4619820060901552052000300310302d03c094080302200d4010950041c0d41034110b240c2c00c1500600c56101c0640c050801010740e86045044489060091408844030312040d40210 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 673361438 1250 673360188 673360217
    0x309081509010e0a020307060c170c06090f1b010e06070819030c030c140d0e100b09010806040305070219180902100e130c1107060201023004030509060d0606 69
    0x203001c104502010081c070005405a0010b0b840e050103014420030403000158031720a0142b00e545c1c0d040c0d4503841858080d80e40c1e05115040d03440d440d046525044e030344925840700000040001d50b02c100c0508420440d01100d49500045a040585541840e800340051041001180320000200030750703106d106201c03110850b03081011701a1070a05880c0ca06061a00191800303c40c2c106900d801030f00c0c84800f11964940b041d03103c850040c1004400e01c0c1c1d5600c100c80003450704d0746041c0d0001c14401401c881d10104c0b0703aa40d000d000d981e0001100c0c001e000950074007044005082005a080c0c08500b4900c0058a80307841b000444050401040c2c109079007902d810f001c000f942003034804d4860070070251070042c114500c0180843d020000070107803010b20f655541607500c0403d12070603608104408100c2030f10041a0f0382c0800a010b03401c042c90310600d0b071104e0310f80b0101c0009144050441c0c00343d2425000885c0c0c2d100e441c21b940c02d40108141d00e4000350200a841c4199800348104005030400e178440e040b440380d012 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 673362688 1250 673361438 673361441
    0x911040e010f0303080c0307030e0708060711011b20060408120606070b06090a140c04080f070303020c0d08040504021b01051305030714190b0105040507050a1b030908150901 76
    0x42e0700031410101a40c00c1400482ea126003550782c001c0801943d643d5039100d40004030000c21030310f03801207498051084041394044000c1079507802009a640d4003050703044a00c00113030886100300100c1c5240f072280745400d4541402110203042402c6501181e41000503440300140c02d000084074100c50315040040d0f0071001c40b2a1000950b0844016108030b03081040942d29011696005842c20340300300f1940000490b504456003026114081150b920f041c9401d143c1d44002d1240c005000302030075400744c480f45c550041d000050700c4c801c03641c1550090840500050500c42c4403401004180c1c3c40300400c10003c1081e403901d000074030045803d104846010459420f0780c03421183c0260804000c840e5020035400030a6000040d070340c00780c3d009001c4900c20704a03020064506450440782407129a0f20810200504c22403021181c1220004c6e0f038248059607a24000302c40c141328201204010900003075000040360b602c9018440014824102814041c1d00d40707803114981400e4020001541c0440020000c405401707 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 673363938 1250 673362688 673362691
    0xa0803031006180806040b0901180b040c09110d05150607050d090b271810060809070e0a18020616021c170a1701030303270507140402040911040e 64
    0xb03d1020100c1420b0119003911800c01800240050106101080f0324040030b40c4030002590a074004200031103070a1500341c41d442c030210740c141c448080010000404085600984000c0c40c0b00076241031400c5030100003180145405421a503000500c4000c00105c0d0315510010f080c986d0084c0c000f8100402d01540060401e0060740045d48507010502100d201468650108401a0398406000b110180084041038142d4504100a00c1459428040c419540b508407400c03c2510001d1341c0e071005580d11f800b110359030b82e5110302c10034080e40c0300c47d000510880d195038050190940107102c901ea49034010740009109810250740b0010f01c4030904480821803a012480c00c07200414032406142c902440d840395008000d60704207500703074400c0004083e10301c1032003030381c400e1402c200f84400445156181d00300200144071107680f16800303411001c881292045005952400994000010320445040c10341d41124825015030703a50300241c09000108001601d805408040d0b4000741d1825221880c002c950500c40c01e0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 673365188 1250 673363938 673363967
    0x120703060b030c0c010212070302041706160c0519031e020c06040e07140705010b0112020309070611120316020c0114070b1513061e061b020a0803031006 67
    0x1800328204005812041520760160886802c16110306209036414060310518070040b064514a40400010a42640c090070030340d5425909402c0140210303000316600d5005441e031070175104c50300c00c2544845124138100d40040d84182c0c265440c1c440025031600b02c02c02c1250084010a1480c201111104402c6180050010540c40100403500080d400b080d824407840c09000e02d81c1045c5000a00d1903800303440b0003a100c25000d1841583c1d60141c0c2800c900910081c1c01003070010307060b0002449400b65500980340207038070840240008a2418006545440610006008500a40214203100f14000300554820801100c8040201c060790070000e047c9031030a40c0d05414044a495511f401041c00d2060315440d941c040f6a45080d40c49103840714000021000d80503920004400f02c244c2098440d400140440b44101c940c01d00701c40c402d01d125480310403a0700500d40040e0440a82d40040d503465000041018006040104001d882d07001850640d441119411389140f8400002c100180d80110390280240 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 673366438 1250 673365188 673365191
    0x60e0c03010606140c010e1b03011107080d0c11010e0f0708060f010b030a11070303090b0105010516021302070206030403180b121303030b030d020d080603010504022101060317120703 80
    0x40c1040e070040c080900e501c184022143c40401d0030780340145e0075400551203241c902c2c120b421804d00c802260400c900241c50300d80c003c1d420002ca00c581800c2960948041e103038844001804d1094184803140240681403c5d00204a204c040c80c000c003580c05c0c0303e404810310b0702074054600a4401030354030389030502e02d501c030f8500c55022804124949403a6031045040d1b40203500c5055498451564a5014120034007002d1602030740007581d0300405415a0005101c18455010b0042c07603a078034801900c180c01040511444900e405040d1b80042c600b00d4001d41c508040c0403030040c200f81e21a000304215400454040b4089035403410314042056144140d6801041040e415501c0c10080903991000b01304050803104042c035600303145008140c081e1b04040105840641107440300c100701c0f10001c2d512018400d409020510a002158103801d060168600c1160003420810f4402c964003120080d5481c07107403c0b0082556152008400545900d0b0030b585020401e110b4107844e00f0b5940d21203c15100c01611644c14175 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 673367688 1250 673366438 673366451
    0x80913150f0503190f1110030225150902060f0409021201120f14030d0f0b12151303180b07060509030705060c3004120f14030a020403050a060e0c0301 66
    0x440c1e51800810101d90003000000e404056207001101c8225501c06158001505500b40f8506581036000d030ac4103403c240b841203074107030b1510541000d501e410940a400b40110b04010043d141311500300c012807600c003030600c1d407524110010581454015401440215170009800d800e840c03c40c5c0380c81805007007071985604900c1c0040c1c1c2c0c3c0488050b9441801403800441038a040040072050051b5800b42c0501e0f031040c84100584c100030001800021003e07407190040c03061711a0159000200c401c14a00b03e001c0203c8075480f040720840f8a0174134650300b2006c001c0000c084031744034004501c120005000ea603500300d440b4005840c0500c00d4820090a00f0f030503034424042140455000210907401a0660010b566251090900ba69510049000303440c9107001b851400d000780311400d01080d2099000d03500b29032500501501c2100d00c9083c4090401c006400c20740442809050714006540050803044014070b4142e50b55141c5061a512090039955256261440d05183c141808014545c0d01c0860080291 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 673368938 1250 673367688 673367713
    0x602010b1c111309210c020d170405060c010e0d080402030606010f050d09031106060d0b0115120501090209041d1009021804050f0106060f0c080913150f0503 69
    0x8140d0040c1012040307a10001c1030ba00c1e103030f4010140749101d0105029040c158100481c00c0189940c548015400301e81c804001617108020040000e54000c06000d0900f9081c0c0310803e61001810524014040412001815039119002400032120050001c07800003061522a41407901d010159820f100c801001c0100580d404680f2590000003400d05906a002d40c2e00b046407140030780c02030302501c0ca20340f41803d8185600700781044a0643d07640c084508542e9080d080c8039100d4244400103228090000051114102800b800751a07107070302c3e20b04010102d2020881d072054030400c0c2c3c0720f0b1703000d1036001615003a1b90810340101e031095140000a4410001d05900e0a07584910318488501035654441540f03003155a80110707690995061448140a401c11303050050b15a82c088200ca0360361740c600800041d01c40e010b48034142d0116040d482e10b4141800f2500c4241c1d02d6070181c2c80e0154030184451228055803464810503900458202000c0e42a60500c0300380d05003803409401481c80f960011070400c41 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 673370188 1250 673368938 673368979
    0x10305101502281520040b090a05041a0d0f02041118040e07140f1201020301170c010801030f050a0c180f0213050f180f0a0b09060f010f091e0602010b 66
    0x34451070020002413042070041655403000362403040e0101001700050005088501540944081c003800c031065400207075901d040100b1a0500d1040c140d44201051125010b464198103822026000346240007900d1719543c0041c04580c0c5000100c1e540d0350010501680b20b0308a0324031403d0001c000d44080201030007036049103640301818424001c8a20b02100401410340b15050f04170680320000d04a4404406514000c5020390024000e006040621407058500c85a00040302d0a1000703040c2c54081d05c50b401c40d2210301c81c1c60050102071701c46100d640218800a500740c080600100350344404501ca0225000050065428000784082d1050042c4000c141e200c030355048070011100c04540d205095903040004c1058541d8480005000d0140c0e05c0410000004101070316104549104007000b09004140801410920035103615400c10094a1101c615500610401c00a0400d0b81001e0f04403560350200d04020300c2e18050f0840e1000c1007544200012a024052144501400c50301d05034194058a4140f1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 673371438 1250 673370188 673370213
    0x30501080f070e0604060f030807060507090b0a0507171206010806220c141303020a05091e06040f090f020310061503090305090a030b090d020d050901030510150228 72
    0x40403c00000082002581d03139500183c000d0402920301c0001d650303070b4101412190041107003070b64614102400114240d102d40d03180011380e081401c0381800c0441d090402c84c0c0320341024000702c03811210918261260008038002d4001c0007524020401c9510301500010500a0068801f600414003030404101070102d510703058128690304040010541166801102c0c2d40140f0a1740d02c081d03080014214900785414041902542d00a0394240c0144d91ba9001340102c41c2c03411180c5020f109409001e240031002241d540541115004001013000c40c51003100c01c0c02c480c00160100c5e401c1c01101c600700d003142814420460601c11902c03040029a1078080c05900304050b802280041551310000b03041090301034800d0700e0345011302a065070b034155100d1610554104083d82c05050307900c101e00b04031864074400200845014100e40e683c508003901a401500500006402e200e50204002c001080181006151202c002c0c040d80c001c1c0070107e042a14294200340102c003c0e00640340030705134032000ca040e5602c80b8 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 673372688 1250 673371438 673371449
    0xf06080c0a0509190207050d0e180a020901140408033112170a0c11030705031b03010902132f03010b03070512090d0905010203032a0408100c030501080f07 68
    0x8408513074810741d10410428991601071640352022a0a000f48000055110003a010b01e4403900c2e0700f10078000810070001d550002201045555600141d10300700c00d50080c016171801814440b84080c07c440d001c1e9503a0308603402c154015803020440700e078070195054190414480b0450078003c1c50014a01d0500495100d0184404906031200d42c101003060308036821215903802800d141e00d650020360000d0411910040035a8500c504d280780e080d207454041000c10803240000c00603c0341e170b9103640a14240039001180c00d54103560b21140880940c40c0c2d01100b8005001220002800800110000b00300905a800700d48030084001621001d032a81401200d0640395154071180d1213030360707a80044905116040700181e81e03642c100144107490400296158081d4150340b01d41115540b900012a070382d000848039040c0102d603e01c01001c6040120721900104410f4105d11490144c850558525048244505d04e426a03034501c01c18403015410710032540904020b0740030b45040c04c42c02100c05c0c0d807190680580c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 673373938 1250 673372688 673372699
    0x30921101119020a0201080105012105090f06010308030f0f07020c040f020c190209180304180212100503071508160e2e020307080715020405090405010f06080c0a05 72
    0x4403691102542903404038001e5400c24502d04009040c0203407142c810502c120f001c941c5110010030190300481301441000c51401142c018201c0302007210010f090043d148111500420a0100480c2c4041c021a0302841c011460203659041c01c042d41c4200382c0c8020300c0c6030800362018050103247d0b50702040c0303400300d0f00c802c40340403a661000c21100d00c028400c44003241d13514454422841480b1890a40a1446034001c40d5919441da5828408009080e082c18031b60a01c0e4000700014004206c0707a402685240e0701c070800050400d1140100315210034010307925041c4400c4441c1040000d85020403a510190076080e2030012076000c0480060b00c40200a0300024404180d04540b01025115600b040000400204000c02803072440401070035042d0141d04201018000f083d91800040c00002100d1209600a4482d482c110303058444e0680104100301c4004615000c000000d12035894401c1d4600fd5030062000184c40120740b0200b10894089501101280c0c10201c40c40c10350361749802e601c42c121074041d500c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 673375188 1250 673373938 673373951
    0x30509031e060705090f0d03030c2a02060d150f0918020f0607060f060605070c08070609060c050f0a140c041103060f0409020d080919030f03030e03190203092110 71
    0x2c0d1000221030100d034101f0780c10340354441031544c10740105200c00500d898445128a5140203440340b0244000784508000710300303109800501b030100c010507009110f40c1c5c0000f441c00401510102c400216840354a02c50521a428007070350550b449034007015400c1d08118902d500c5941e01141c41c1070080c0d1701c2c10b481800302181d200248401600100d40d1000070780b03010450181c480002174115000b40105880100c000680820500c1c000540701003510255102c05524900e00581220640107800c4102c4542c0a400403501d00700701c040084404403881070451545240030303840a1807070220680c8500f440b450418450210344c3c0322034411685c02c0312042d164000100ca14101160180c089800300a4103c04102d00420a120000b0084e02c04040308840f910344030380e0260700c48100031001e400082c012040d060000390000c1d009500040241d004c1c881520b0821440b1090a000030885a03404805600002840342591522a0080350180310f00401401c0310010403200968482054142981c0c240d510807 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 673376438 1250 673375188 673375207
    0x10020703030207060507120608060906010b0c03130e061003020315040b0414040f02090112050615010903080a08010e33240405010e0108090d08040c05030a030509031e060705 76
    0x8040b0f41030355400074020700c020b0a10b017100400c0c1c0c01c0e006130340c9480d00b4074007000422005008601d05015403038100c000d286503400d1070944500c96110204598251004101c04a01e070710300043c17a0f0340141501010100c103450900705120a001104880e0b204142c810400c001801c10b22000c030705040c007002c1c0d6000070751152450201c0c005043c04c20704848403c540004110800501110354098503100792003410072640d03184402c410f41004428014001c0e002040003500c00d070085004080e0120052409a0f0003650fa03880d01c01d2298410016140003030310003801803090301010720440d5003110b5012500d01e03052100c50309084011a0580400c90689a49074040d9401e80c4c1d000141d5a003203441e00c8002c07109480d94081030060754054400d65000c514078001103c2a513003c0c0100d24417401852000d0040548850411120700c0b40050040b101f200b0500350105887c1c4082044100030b40c0709854aa80d905020810145409014801e006580407040d1000001030008602d580c2c2080890411648a030300e0070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 673377688 1250 673376438 673376441
    0x305100b0616030f260a0e07060f030f020405060307020105070e0a081f0e1207030806010206060603130201091511190305120c07051b041a220e0d030b10030c021002070303 75
    0x8100b024039980c0200d6048410400c9403805c18020410b140c02007082d1008003403103503156800c1344210008551414100741220340a82c002c20303085491351b00c00614007501c6200054064109554840050395508104030758160001d0800d0405034003260540e980511384a4000d80d40c0c40074143c7c0024424410f807041fa03130106c2c01e800060304410f890042d0344061190050746000d640185005800180340c000c081030140d40041041b500624028164514590740c5800300648440d40b02000c9041100e84840040c0700010341c030f40c0d500d6078503040c1e44860b040c00d100d01c00c03145003508201965100000d42d0f810700700041c0d000021140e0040024000c4026030752011740d121154018000050054010b145180e030b902c450002074100c00003402c0350708108502c5a500350306082c1801a03036075a00041001102d103c0100204000491505400d00203c3c54000c001400d1341030000c000101008030b500d5402c21b1825240612840f07045d0320451904014201d90000000c0d0380e40c80103064080e01d16070009050302454482d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 673378938 1250 673377688 673377707
    0x20903150114090a0b090a1107050a14070803250512030406020a0801080102180f0a17030307030c0c2607051507231210050a0305100b0616030f 63
    0x2580e51400c05036954040c1440e4108880b200144181680c400260400c80c00c0c0c41111800c40000d4040d81070740d079070b0020302402411200641c0041100c00d20408000500401403401954400c82181c840503500903451894109030b6082038120360030600900c1070141c01102e81c001c1d200002401070500c0316483c2062130078460207240b043c205010000030841802400c1c1c00400120926684c1d0f0040b0b0b0380d03200401c6080b4002c00c5110103107c00d000006d00050318044014840102c4014002c20115541c0d0026609440c54242540e8242e0004003c2003001034052050280d0f094907401d00d01c40352841c0d541c6201c440000721442c0b074418031604024400e020480010344910985c4102102c21000d660713207844940e90003c0b21008001403002040c000150004640325039419601c3c10f40d03d0401c40780102000002400500301d407015000001c002501c0c0e952050042c0040d8000c43c080c0400c5a9500d200c002501d4a0a1100d4014031040111224801100ccc28902615070549007070018050410001c0300c00c81d02 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 673380188 1250 673378938 673378963
    0x708120f031f0503060106020616090b03040b0a0b120a021f300911030f0c031e0a060213090f020403111e030105070f110123070e03030d0605040b0306040213020903 72
    0x203110002c11f030715800056141c0030350b010301942ca010704800c84040700c0b14502801503004040c410b1000c03d001805020038542c00108654010950700f0309000418804408001d074410503500c07494918040d0b0400415038110381d0000f0780040e80c3c1540c5040050400440000031518055100c408100407610714602c615155614a030700b804659600d090450318010a226407922134014401000c0380400e0004115010b410080c024101006011004e51002e4600080041103030140004a90000e80d040c8000c003060584c0345100228182404005170071108010344101c12940304000a0000c181c0810000c84d00f030b1012502a00080030040c1880f010180300652181c1640c00c24041c804580e1304981c210781104001e50b20b003101c4054a0380c1d80ca090320300c00c5c102c0c035806d19401600294150f1004224039441482c0d4117040704e03003958080119196038054459207940c1640d0b50010310940c50940a240c6504104a00a041038242074001a101c56404040030355010350019011110381c40a203d00038100c031 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 673381294 1106 673380188 673380193
    0xc011d01050a090f0902030403111207060e0129030d0201090b1501090806040506100501020a032f060901050103052a01050304020409140708120f031f0503 68
    0x80c0304416600400141c41d401158442c80508800001c1074803d00051f624909810001c2240501c1c00035865075404c01020341c00d0041100c01941c40490300203000041c0544400001401060b185007540c0021802100084030034041008444443c04207800360399059a03d110102c0c01c03100c2546005050315202c00c04502e05401300010300e842c0354818103141c10440c0c3c40c4d044040c0780140484046032a81d0003c41006000a401102d09005003002e00080c00480e02ca50350141024449400c035590000f0070405c40161141c50224140f540f0020b01e0540b105800d000306010301904090100740c420303104904d100012810218a6504000104a0101c646640c010300441e2a50300241c030983c0c2c00354544083c0b4000c14400308040032000c1c00b100052072468581003040d42032404d1103c0e01c03610350000380165410040410112030388042d004540005145d81c5901d43d80d00b11000341c10240c0c052 = true := by decide +kernel

theorem cover : BRFrame.Cov 673201438 673381294 := by
  have h0 := BRFrame.cov_init 673201438
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673201438 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 673201438 ≤ n) (h2 : n < 673381294) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
