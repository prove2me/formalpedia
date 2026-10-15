-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3907
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:01:34.868709+00:00
-- url     : https://prove2.me/submissions/3191f1a7-ca25-4070-af5e-3df26b3d4d81

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 702517985 ≤ n < 702697841 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 702519235 1250 702517985 702517997
    0xe0a0308040b0c10020310170d020a110102010e06130614220311031201090501080f03070816080a03150f05030a02280b0d0b090405060711070504020c0d140901 70
    0x341c00481c1d00c55a004200a1045008401c9201004d0b03070075000840c091101da03490000300b6070070a401c0101c00c50540c0001e00d480c0e40f01c81440a0929000704440d0035464001c03007850030200441c80141e02500c40404c865200380212001c00c00300701020645032201c0ca000d00c0c0104a4003c03d8940241584802c0d208003010300e2400307448070301011610722030b8080d5911915080c0f16000703a48071254a190090a007500c81031403590018003d0943c2481100d00400075032004080081c1101d03103003a181d101d5840c0143c8404000911089141d002c02c81c5031401d503078480c1c1c0844d07031444100e20050017003815001001100c1010800001c0c1550400035030001e840000700600305680c01c1e6400c104007039801c0c1036803500803407004020b18021951543c00000130125481c5065035992500b40c2c0d40c017103071010140300d84900124801d20000c690300041e05039000e041400e240c4e41ca840c0410755186400025800a0751141c0001035030625160b010840414445440d101c1c0c04980900c000e400001740202999503001a203 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 702520485 1250 702519235 702519239
    0xf040c0e07020a0b01121202120a0809010212182b0c05100606050d0e060c040315091e05150405100c090f03030e011206030c0302010c020613080d0e0a030804 69
    0x3034a1080c003504400540100c58891a007642d400d00f0301c0f6026405009074040d0071007804107110500c0428410707011a4800f82c085c6680c20240d2448900840040d02e08200c0400c00042c0c916000b5411a10380882100c1e085545107805007540e0981000e110b40d4070554050041d200004901a5440d8400401200320300f007602e071811174040321000511541540c0d08e00c203064501d4010052445000003400041c1d42d010781d0351110070090015074a000f5a1494a0340c028010071000c03100e0309007607600340c1b50310010841400070448100c1d0003900e035001010f030001d4020310085400d0900c0300200d0401034411402d40f0030700310200c160020025011280070300703075803c00c190000650145900425800380b0b94100058540d032140c0c3e032a50311266076002140450302004140c1c3e825a00103a041c8161260a001442901c2c2140d0301d9028030565840300a041c420311448080c2156141c405890205170b0400c48403680c3c40c0d0301c000b4940e603860700042c000045111640c5c2103111341000c480b0b000984c0d81224000389024 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 702521735 1250 702520485 702520499
    0x307051017010308040503010614031009021302030f16030209031b0102150a05090606100f12061809020a06020a0b01050f060906030c0c060105010f02061311030a0f0b0f040c 76
    0x1044208001084001032000407207148103801d5901850044514940b140e0410301498215039054100000f40c540c0010410a240c2d0005074084c94900c4820011440140713038408a2010305500741c081000c40d00100800c031580413203103c00c9106200c5506d6003000304040e4101070341244582c01585405420190307a00c11144594552002e1a1130184100c8180040f49034950309a008183c555180849c0c961080c0004203d080090035044101103600148080400b080a41b011b0b061030b6580c400e201c1198036030180020180e07c140c00900e0318080c0300040d0402141448001e1010700d000701d00c0b40e07242510201d03280d0710000d602004284c1c00143c03559981d090004100d4001f001070503855102004018004071900c400001d180140d07030402d000c5031100c55051b005030074808142c05c61410408034030641c510081c0d00282441d0050041c0440b030064000c01c0c242041a44265815039815208106a1104003c02d2244603813141d070150508034865100e51000031003224044da0041c0c012084404144503007 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 702522985 1250 702521735 702521749
    0xb070809010c090b09240705030304020901090c0f080c04170c090a230c0c0a080c060114130b0307031205090301061712030910090b0415060605030a0b0f06070501090c14030705 77
    0x3c240e88090321b02d0550328038860360190b42c00100708461940002c0140702c11400c000e40f920b400b505c0c0c2d84030300340120209200300900009511001c07a040040010228401410749011140076040c01c0024404942c03079100742c0b43d41e9820101510b4000e18404d400103041e044144281e81110791b62264003200050840c800e61950f882c0a0000009240b0800030003054540421a402c169403048880645640401d020141040c1c41688141c0059080c079105440d180d076405000c110030700d07485100003407001e540030100e131805640340c0001305001041404110b6603a0001d0181c5502c0f88102d000b4051551105001d07440c07607000340b00303c034200c3e4402049018000640790155a00c00502011141005110541501601d0203444107550340f0140320184020310242d42c0c505000d4440e080070502c10302d458540d00610034403004001007405a641c1284107125610a2580148100001c1c046601c3c0c8841382003080c02800403500440d01d407210b0780d400041388100d02c00c5020142c40000c010b40080b1303103000180030f42 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 702524235 1250 702522985 702523009
    0xc0705010204181409010b09180a0c06110705120c0907180902090a0602030c150c0d1b020f1203010315020f0d1b05072d0b070809010c090b09 62
    0x110354091002090300c2c1c00c2c0c0700c681010b00c1085100800d14224442891031300b5080500100a10f90615005020f5a1161f50050b5004298000c204800012004046092900d620001007814440082c00104141d01440385004183e14105541c26a9035640400410130440312000409402c840144809494514004c43e4002a5401c0c40468841070302c81500641c0851303048610915404074800c51175091000d51203014040d580029440c040c0600c0da91070707071860321900c104000543d10001840d400005010b690300404036070000d000d4201904c98012214844036081e000502c03d80f5040d0500c0e990001d43c0d009425108032400d40346901b90784610600040710621001265002c00140d800903c80d03000500740405503880002d4510100c45110104c407404c21850000c010040c8054404180c01040ba60030480c6d602650b41c02800340c0e40f50602c01c1c4600001c01a0110707040100308803145810104051007121000d0007007110108002041c1d130002124040c00d0903a4170203114607005030034010302001d4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 702525485 1250 702524235 702524243
    0x10b0d0209060d021309020703170a1d1c050a0f1223060a0e1501030b0d0501020a090303110a030f0e4203060d0f0f0f0f14070e0c07 58
    0x8545801d0070042200c9a2168001d030010a60000350710280070003699507540545030081041d840c24001d40ca004000402c19200c7c0b1002100301408140705818552000d40760040810803500c078085202d1519898610320201c0400885000a20b058602d1262048555500890b00c0e006c030512a070079030494104407610700c1c0c2c5250a0396080c41400011418160199195001e01540805d00e4843c040c03140c1505554895580400da402c10310070768000d018902c0da8036820030710700090320440800010f90800000300c0054000c1d4070005001036101d90048041060b28040d845407960003640760320460b61800381c00009000540b601d000d411800d8421003c440e00c0741c0300117251400c03c00c480794580c200c3d5110780c00724141c80440142ca50040540c04201c14040c4e004002d14141076182c040c01007110340000820013050a00c1d0419613400300000e909820180f0781d0018000110310409262810051000030429641c45a07841010382600d20005820310a45004900c804d2050b1a41d412000280c0c2042408603 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 702526735 1250 702525485 702525487
    0x310020c07440723030f03041205011508010c0207060507030906030c021c030501140a0f0b1b0304180f0216030f0210050c0a1e022d0105090124030308010b0d02 70
    0x300198082041e5005800c4ca803410746602d401590502c5100d2070122007442c003c1d0006c0340781d50240e1300b000c8217490443c1d19002d001c0c0c804403810b14007e40105034070105a059410880b00c0400c1c3c2800561001082101d143c0031209260341300d550030b0f90315000703500000300020074907032040c0001482900442c1381120180104c074409c20302c0441c20110b803c402c00140000136992001040455100b441e000c1740384d44181c810019242c20441c8a504101c41c40c010f0380020038000401b00e0141140700000240310340a04103880c2c80359203d04008250641042c0e480c1c0e00d9a0900111880b440e016200700c41500ca44e04041c0c10220160750b0702138924604e6a00c2240550048440201182040c2d0044511a503041c482e89071b503804a2042c041d00364504400b43e2054000c80c00c441d0b5010a40000e0483c414a1496601c820490090324190b42c03e0799890030940f5141d4206030601c604e0003415000002c02521801c41c3c11a00c122110030981c9115044c8800350005082500400c0a079812100510075603403908809 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 702527985 1250 702526735 702526859
    0x52202040c031127060c072102060409050405012019032405100804051b0f040204060203030f01081f0203090c0306190609050709030305090f0310020c07 67
    0x1d0390b81604030002c074410132541a643c54407225035003400d900132010100c503118141300071003040c0ea60701d41d000d0080684000700c0d07082400c540c013044500c480f0311941c0140301e15503ca444401c680f0290100351411507082d800c10318107010700d0344200340802040801d245414105400c95001245058841082030207242e1b4170280c50f80340010f803030082000780183c007600e40e54651604051001004600c101035080080150a0100154012880c030240c9241e452045400c402203100050001c10300c80342c16a445840000c000441c1d1b50080701071841440b180210203196a0380b003160075202c0d03850300406055503c5e01c002626109489501450300401e85d00c0444008c8521000820310b0176005031405450a2600380480c070404c04a40900d401a2a0b903200a002c5410300700805400028240401400e020000c11295015165007449a081e148002d00300d410818151070305400035130108010071001c0c06400d1001c145420710f0308400c48900700c4c985c0302d441c8040040081002070b240d01f241580c1c02d07052007401e03 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 702529235 1250 702527985 702528011
    0xc060c0406052b060b13080d080f04110907030506010f0e0f0607080405030a050f2a091305060a0209100e0f0d1406070f090e09060103060f06081609052202040c03 71
    0x180314080d00701d40c2d2019503584004115a114003030641c7c84860b90f0740c003541d000b1500c02e50140b0030907040721400546c424035443d646841102800090380c20ba4021030040104200d89d40e141c1c01190040c8820388440140c1c07410183d040761249482c4041c980c0100702c000908002d81041c200070414240a41c620a00b0f0585440011703040540501301076a241c0d000181c070680c446000d01c0b140c0c401c210a090084d440c043e8041050a4a020f0154014411785400c40054101d064850303112152030381c0803082e0f904900e014140b880007500140d0401d0f000380609400000344901945081d012102d004010203c000b54000c05c01c2060340244408070340d4258a804504400c44003000340c24001c075643e468800b8955500c000c0107003a00c040c0e6001c403d5803001d905c10b000c00000080b031540d05407a0020b00108a480110301c1c40c030041c1100e03a02c40c0f03105114003103031042c480e09560840401d0710000c2c84144000e480d244003074403110440344034860803840054464001454103034400d0740c101100b8140480c5412450039 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 702530485 1250 702529235 702529241
    0x150207030f061a0105070b0f04020117040b04110411040e06030727111218191a01080d02071815060305060301110c0a0201050c0f060405030c060c0406052b 68
    0x9012200c0d59200d8200c10099043c42e0060700e03c0e03810078a410f034280f80301c1d074480042c00040a0008010041504042020340e44140107612503015040c000050314105880c004500080c211005d807a049860302020300d00307180a01070105060a09890315040c5400d095914480000241c84564180b2404100049805401c0d0422550680d10340044050781c0d040d500c2e0005465600809180301e19041100001041100290f260004186030b51010014104c40c0d00a16000c1e050468208081c41550b10904101d0440d0f2660354695078401d0084081c1d0307072600b00d5980c9556440d41500540c008080500c54040d241104052031000c002001c03d81e031080d000d00180ba1032158101100003929074003041541e0500f40070303000500300c0882c02603140020100c5640d0302c60007400300080c1003101c0000c210190080800500300e100203044182c5006003070515001c1d0f600c1e4030428a400450090f18001109170040d041034a003100c840f6209e076441c01c08040c00403034580310044142080c9540c0c036009106001c00502c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 702531735 1250 702530485 702530513
    0x6060c0a03320d1508010614031005130b0406020f0d06060e0d02010e0f03010603080f090315070906030c270f0b03010f052416020a1e15020703 63
    0x6101c031a20007241c51104030042a4096982e102111441c220880c8110b050b8100c03158060260000681c4405100407641c001800c0d03401940d41c1c2d8280b40c80800c10041220302c24001c400b00320304540b0350b00c00e60340304902580c20454007032050741009031044010880c20040664442d110386e00040c507120054004104640051401507002035450f201403050711b80040c40c0d051002c0c01224590540c3c1400c2d40000c02581c010240ba60045050010030003854600750004000745a012881e503032a48002e81c51100c96030404034103944680b250040580061840100c41800348405540e80800c85040200030386c007801601415504200038161000b81c8800b8400c01d180c03211250035a13004660b407800844440d1042d03590420b905120b030810041120300b841d207841e80101d801c16a4280c226410300740d450684040e4194600059030030010720701900e1200406103d6410384225071103442d181d10343c40119040341c00200300c8be40c3e0f449012400e1180c0c400f4001500440301c424812100c035651240d07180f03a0b8500b10a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 702532985 1250 702531735 702531737
    0x907050d06060e09070203030f220501020706090c0e01080a0605070e04050405062e090e25031b0b090d06110c1c0c0f03030f0f061d0702030f1206060c0a03 68
    0x102c04031030f452030b18030080c54001350030b803000358214100804082d21040b00501180e40b0045c0c103a002041048c078900100e80d086810000031900c4c1c0145080002c05011100800c0342c84a03891000841e04400904009047e03030301c10300c000e00c01c1030700b07641e6824002e100280481d410700119140e50201c941d52405480c0c4140e1050003d040e2030704003055421401030060103129000d4100c8103d08040c408644140300884611070340c00b040e0106101c411500705080a00745030580c84110503c4e92000d10034240403011644200d0000c100d810404100001a040705d00641340000c40c10858035130036107492400c81604900030400004d012050603007001d820340c410044a255a04208070380f00c84030740c20040c508c0f4115a14140210400d8440d9164080c0d1650b9010003028181d4941c0e4242d031030601b6a1082080c20758032402000b1242d10b0b1010012409102041188020391500c00a4680c0e840441950305040e40c2c1142c85041601e85078102e80720210040440c0d030070410074071602e000c0550800041000e20b0003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 702534235 1250 702532985 702532997
    0x4090b070507020910051c2604060207050d0803040818040e0a0203010b1005030c0d060e070905100e01091404110d060609080c0109090203090a0f21140301050907050d0606 75
    0x800d2041c40101c01e0002c01c042a040f00c005e10402c81a110100d5086600c0034010045910103024a0000e03601038825000845041e440d1980780000c07460172000740706640480d001c82d41c0c496907900802181c1c07a042c0100900c00201800030800103407188000e001d10440070030700d030303029400210081070444010364940300c1c580c1e01c05200801941001c0c4911402640b041d14a00b0380342c101c46078090035511000d40036843d40f21001407080d0448103158051000382240645a041c0d07800c110700c0040249007540a910310400e44040500400d80c00342c02640c0450b1410b844100e20140f038100c04100c019403002459401c144c03160f40381034008410701e005140c034000038000001c0c00c42c1840b40041180049400500d2268003068010700540c0e0000f80c0007003243c07203407107001d40d40755290001f45d41404a0301e9001880030603440e8000c01040318504440e00b104ca911001c2101d0003036418011109010344a15403011002d0410051045040801c02c05034864401c1c00d00394604044d0046520444100754041c130300181c4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 702535485 1250 702534235 702534247
    0x92a2e0e0307120b040507030b04050607031d07050112020909040c0f0506041802030a11030f01060206061005040e071403150f0d021c0516090213081504030305040204090b0705 77
    0x1030461524030380000140c0c002c0c0450340c2810f140040b40700c4100c1010f040c01916000190400404000300c00145510401880c1c00f0f00301752804a560f090207032a1000420300340549000490b01801c5e0f011134522104000b48442d078a03000040d2078482c210171000510540800044819448034409140260303c90504608030b6032500d50408201d5209403c607502c900000c0101304589440000503400c00302c4040f41c0188d49840e0008c00c0340c01041d0030704100204400220400c4158050000701c43e0403180580c084e200b441c0c1c0c50104101c82c1854002c1c401012460034001441401d42e4600304030b80c44100780c140601819020700061520741c2040350828941916001a42021706050104011020081e81d07150031100c11a0300041e00e80c640c1030a17188025060b003040d1030620000b0040c2c00040345c000c444070601140c8500a0720080e600c0141601c0ca80340c09120000346040c0005406012213010424202060715180c2c0c3c1140a41405003061764800d40b2807100d0004106c02e240824000c44560300d890b40c0e101 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 702536735 1250 702535485 702535487
    0x80a0305013308041b1242020d0e1005010e0c070b090705060f070303060501020307080d0209041d01060305011802030d050c0c0612190e060c0c030f040e0f092a2e 71
    0x1060010590b9410500c000c18148007d90202c07107500c4a000c084501c40200410341c1e5100003030003000d200804003804c000c1c03128006800441c0100c240c5000340001d11090fa200d009580c1c0320042a5890740c03441d081000701c50f01280c042109250020a041c05495855640300002405a00142610a0382203000582d130010503401d88680340082000f070001e5414031a05d03455000c01806070003007410056400003030340a8103030359075030041040c01c20f8405940013441422a20314020b216900049906601e840342c4440d040e0340454202c91603950050003018020411442215142c00c0510031200a2048800340c83e19560f40c80050000404440b03c10301d094686024221007159403c2680d44140e8905031b04151154404501907620143d60280c1c1507454801003101c42c80c611a0880d010000200880c6c0414807500000c07805020707500201e04c0007800d4030388816481e2280720b0b0034551890021110008004407003000701c0740910042c014905403207940610504040c4c040400d62090200c402050040106 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 702537985 1250 702536735 702536753
    0x7050307170613080d11090f09151009080f03030a05180703060c0c150b010809120d051e07031d030a120f0207080a0305013308041b12 59
    0x1c055449211515600c904002600da0724003401e1000e03030034070307001004050001c0d800807a0000030381e05208001a00382e400070312605400c0812001d00c5014044840c64561800040c2e20b405518110008485140b0800410050400f40402075090014000d00050318400a1060040c107a00c0d1801a42c2d80b40703003203602c0030100c80000f02242e0081101c5221000101000103804056a6008200040503540490300392a000180320740200f1780c1480d0240c0e1002d4a100f600400003000081c0c880c900d8030723201c1d14031154482d191324004001c140403d100c50340e0705141a400c440e03000340004c420401c081c141001040745020049038002c1c0400d4030344101410440000900202d4601c44101542c140032017800004d1414845400c07612440344c4640c0204010a4194100e642e030a03848416159154240c00024010741401d1252403854034004105011418081c0903500d082c040654003400351620324641130350441c00c043c0c0251072011102013880415200c040722803015081080740820035101514000c403823 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 702539235 1250 702537985 702537989
    0x12060507140304031808070816140d0b070905120309010e0108061522170601331e0201150801200c030c060703020a120603080a0c03050d090507050307 66
    0x300315034004141c09007481441501d03001070741490712011901c03008800608803815504030700300742d008010000881e481c0015060726004016010040041e50347c81c100b0062070071640c055034011251145c05c1c07002034560100c013039105220f400e240114649800108240300c440d41c540003502d500001d4264131540c0c0100421813420703800d10746400d16140603404942c040d48145260528500701190100d0b000703100054441103103880014003200c1a59440e5031640e4150441c640803028094007002040300e0780001201d808540d1006028186040464801c44d05c41c00f40c82c0d044c01c00c200d0b1440f01d490056a600c6c40711480f040381035002061010100b800d00c14407032a43d500c100b00384da160942c0ba807100100003107070f004509600340940362100101c5404e2404c510800d50f1460781070160f103080191843e0168050400700038140e03280003d01048960f408216540b900000c3c00c149424040005240e11035007900450510130300d01103082c00c4100c05410180c0f118070008445d641c00050060100d800c0410440e80 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 702540485 1250 702539235 702539237
    0x209060406080c0103090c0e0408041d1005060d140f0108100b0f0909100c0807080a090302150c0405150d0c052b0908190e060f0d0207051612060507 65
    0x2000c2d24208002d81c2d250001002941410f446179646014003d170850550300408030005c24401030703c3d0a142036200d60744540281491881d142e54000e01c90b03070b821503010707100b4100c400d814048242807a0400c5083d8100514072100c0b15180c2c003111001406600305640980c4816901500c154104141141080b410f40400d050080c5400d070002015607524120184500c8155296802a11141201400c1c070078242d04028403103080004221010b54010075a40c42590750750340d840403680b00d0400c1101034610126000d00107910411001009091411851750004540b91413a407070690740d03070003140e09240c020660311440c400109044100040b140101a9042e030389240403840e01a201c90800c60f1041d4a280e4015007100c80d203a488004003440d030013441c42580084030b10361200d0070064124004103c403078040000600c43c1090440c02e0400b4015030b04c030f80c17410b01c0c00d00d820042c1e4440510b0080d00061001d903542e216000034004540000080707800030708071401c2c42c812012500c1c100041a00d8000e09010 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 702541735 1250 702540485 702540491
    0x81006030209070f1b06020405030a0c0302180106021f0b0d05030c0105400c0e060a091b050919030c061803080406030515040608030703030f0209010206010303140d140402090604 78
    0x42c4515170260084000b120345084440d400c49142c104840280601c2e0080d40d0940b20b400c00c98002d01140c010190100ca208444000e090301003004080f5a0340828412140036a11119401a003e20304000b035008200d810310000554281400014030320301001a0207a52035080040e0109240c0005c1c002c40c0e612600b0b600c0340c40003084620820f411020900340b054119280e0b421001c501d104040b5007a00c2d1440d03001020002002d480b40d1407101d1440081c0e40d22403042031880400500c000490098020728600300390884030260402c041550b2030360014a0302c540c0701c07075481d100d06910200c140740600038501a20030001001e042c00c40290085800d6085500d0701085220708100081d9214104c03419500a4640451207450b102c07904c402c0c980310381240950140c18014080349200e8004003800000c0e0180d07900384880e10540b1304000407842070124590050b0000e00c010b0002c24021207040c0040c208502c1d10030f1420940c00b00280031640300c050400c5041702a84140410352034620360080e0054000c883c10 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 702542985 1250 702541735 702541757
    0x6020c06030c1c0612060c0f14032d18060a02070507030204090f050a1401110702090601050705030d060b04050f040219031d030d0e0613030c06021308100603020907 72
    0x2249004940c0129100243c0c001d407040892440d802c002c00901c0300c401c1d0546400312900c0c104010703040c0101648001000c5444240000d4400e604d00c0e5a40d02e00e5054080c5141c0300c0d0020680c02031581c3e0310740c20380300300c05c6056061605030748081e462083c5031140c0c5200382016912407a50410401400ca164011700501800001c07400c0458060b00312a4110380c001542241468000004842c0342e01c0034003107002c3e80c2402028050340201c030320300c200d103054000c0040424051661005000e9602e0180d0030460140004089500074002052803500a9088a08101c3d50021250a880b8580c00030304e508980440c0c02c201c1410100c0b0f50a1041030308580550400314503231f0714007421342a540080001c068031480b1101c5100160303400c0482810041c0203507542d5448200300c0300060302c0b0301b00d1002d0340d038410403001516420f8120341d040105039042d0703180140d00100d07440e550040d4024102802900016403800140341c039041102c10380d503152240011400500c0c40c0100f0036103074001008101440407113010 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 702544235 1250 702542985 702543001
    0x4031106070c060f110318092404020d0902090a1e110a0806190620010b03070608190c0e031209060927040b010f050f06030f15061306020c0603 63
    0x6641c141c072036034030b81000c0281640f00d0031110007080811171405400001a42c0d800c0001c520324084120500395400321140d00c90340304400203080010400c050b07041061680140601c2e10303800628481e800d5017004200d001ba6074000408902d000d0b102078800742e03a614181c2c180c4001030550b0002c80d5400400400521001408041c0140304500d00b1004120346080082c0076655000482c844070240070021010864443c0320240105100c5403200c40061319800a00e91303d8003050140101600d000717005401e12034507201040c2e0310000094104035103401980d002508003103071031083c0742c6811415680d5010b0a00321900381401c00141d445c1c1140302507010441540b55850340001c8480300d80d81a5603145102040105042d21801c85603206000516120240002c0c0000204c0e00d0b4180c9101ca01031003c159030354010441100041521250001003d10000c3d00c0501807410556102120b0040c0c0c4826004840010303465600004000e8000c0010003818024142d0412800010000035154203146043c2048 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 702545485 1250 702544235 702544253
    0x306090611030130032a050304170106090e03090d060e060a0902010305161d04021c0605030f010501120206030603010e0a03020d0f080f06220c1706010f0909022d0403110607 76
    0x60301035601b6011501034100c110a0309803c0c5660440d040d291a6622007000e00c00e0083c00c1602e10101350f0a120010458609a01c00c14246100b2480203500c0c0c000d07070000380140003000038015a8902c0e551005000c1c0c103142400481d10034140f1540010310310078244000340c2154400b50a91400f54029218020a1a04002403d00115454650600030945180050043d1203110228905040140c001030341511054000e0700a40d10704034141c40d00c00211200c00e60884200340b140400c200800c101042c00742c10480c0085410a0010303001141c071001c450002440c14550720b0f011001a03000380300c003001d00390b4810780086082c1a1403802c501e40d4145400071035004140685100d00c1001d000300c0d0300550f522510140041c1c1c01c1d80181c20f0180d550440d00140c020340500e50a60441c4401e01d0008003690b229103681e20841c5451b44074108503508080c1040000c0d00f0a07040100c41e01140c003521614a003004003603100550a601c8119640d030700318540000006002580680107041c203100c10300005180032 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 702546735 1250 702545485 702545507
    0x91e0c091d0313060f260403090b070b0118200a030219090603060603020306030d030b01051606060807080703021005130b0318060619030609061103013003 68
    0x100120305a8603684a00d40403520307110352203505110001c0d09181110081d4106401c5481c1c07038607048105403440b10b00340d8114200f5110f80520401c1c24a904444500102c40550054000d1810380b444a40301d10860b50359500c0104296007c183e81c0c00100070318000c3c0d2114039484401d032501800701c0084c00c4481c850808668200c5002c030350700032400c0440b41d482981510b4030010f5250852100c52110380c006044070415004083c0028200040892068064000c80340640d201800410704503549500850091001111580c10040308101d056a80d41149070b03898403403405071400065140c1f922508030320b86001c40d404401c540e0400030003003000d41c0da21848034034a940c450034030650701e5882c8081041d90065079004004290004000e001400c0c90a581c0420701640d1002182d802c1d0300c43c2000c01c65829401501003660400e0440d081c00010041c1c2c0040a003c0d220b000701080c1e0305800ea14040041e00240c101346050b0213200030316034054201c1c1e1906c0100c01882040000c0100c1c40c0d07100240b064a40c9 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 702547985 1250 702546735 702546749
    0x1a030c0f0d0f080d02160308060102070e010e10080106090204140f030c060c010f0507031b030614060d06080709020a090b04050d021e0306040602031803030f151c06091e0c 75
    0x80200384148000f10b41207031080c5544500841d62000c0d10745a610707a800c1c1d000010340004480c080003c40b40e500001d030540c00e4451608c001400c030303032070070001492410004143c0300d101c806204002070100824010440540b030f10301005038171a1700341203090f489580c1803042d4a218112084c040400d50320702103490940c844040d0b4103241d80d403a144540300e0240c00d400d81460415880c0c00104080a9890760111400041540061240c0c000c000c8044095403854018198211300e5801010104d14100000301a011581c1802092040c6e40f0300e4207034244400c1c0d07403212517a03980002c0e80100580d4866010006005000805801e007814000418000842d0020081c010885800506180d1b9480c02010011a03c01400c0740e055140920b80340b03002e500187d81f040759520b07404c2e9034004000d1000c02a80d109455120350101d81b6a2811501701c0750360080441c0580100a4040030314513007108680c0507904038020840400c003180107151101d0000c16480c603071402e141e400d40003640043d2040b0010011250301d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 702549235 1250 702547985 702548003
    0x21c0606350c040e0405010f060503030a09170a0b04080c070e161d0423010f1d060103110a0804031d010f080c040b0c0105040501060e0c03040f030504091a030c0f0d 72
    0x208150b80300035201c0c41e08000000390844003040100700c0c05400c07024a41466540510201d40d0720000d242c2e8a01400c1e050783c001ca6403c03041404140151001b0346a0300ca002d40c01c03204092a60784841c0480701c4256010341300b043d00014460040300d01048054014107149510308001c1c98050300e01d600301e10b510329608041001000782c40c0343c00c60690001c42d20201d8000c0c000c002040844006840e03090f07249040d00c254540060001840c0300b0660346a0f0100d81d800f4402400079002009020818030000b0101da060542e203c0b03681e401d04c0000c00252a9003940380c1c80d10b0010b402c1905000d0001e4000049044680c2c1c81c1d070f0320b400e01c6642d100404101c200180e003480401a1184460580c40e0f00a0717801101000101081c0038140c608150006400b0300d014900030405646c4901409440350070841d01070200c2e5400300003160000d061501c7c1c4081490082c98294286900c40a0aa00745c608503035011049407814802c0440f140f800384115804100e00301c600811f4030358802c2c08502c06c9041d00f000a0003543d9 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 702550485 1250 702549235 702549241
    0x810110a0c240e010b0307090e07060c0501090b0c0a1101090f0f0320010b09011a030402100509030d111c020706030f090203010c02030307080705030603030906070204021c060635 78
    0x1060154440c46500c1c980140443da0255040d18000e25041d80014400c1c4a9030f4400a0b40e07490710b02c40c030140942ca03140038110035420007000341c440c00f2076100101c640751f50390303402c05022418650b5a0f40c0110b2140b0302c442d50341c0c084060700400f107905c492402180d9900d440c400b40006495031005511843d807210005203202c0880c10140c40c0b00c00300038401410702031121001c860008066110340c286610895568002d40d813034407030440c0810701c1c0101014540c0000c1002c10701516140d40c0c0c0e0b4030607a07610320b0401c0c82c2c15590380120703040c401082d06030030106258000d40c50594100380881d90300e5003020301c180a441d0b002c10200079074400d0207108074018140c3d1201007649140080d04295002038000d0000d00400c0b03010311009540394030440d4104001100f01c030100e0843c40c0300300210ba0103441c000340192b0030180c04100700f0401d5406110304a038030550801c8003107800708036184200c4894100d801c0004076280343c11000b801000303803280c10310350890150b040c01c0d042540503081440c0c00c180010203000340e56 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 702551735 1250 702550485 702550523
    0x318010c03050c07080c100503130204150308070614071106041202011401080303151509012a0b0405010605040e06270f06072303060907090f0810110a0c 67
    0x302c00e003000c43c3c3d110702400c98086581000020a10121041920149020100c01d0f2003100c4600050301c51052111350400144058074098100310010404031055020032b40d40c0e070740d410030507038002c00044550750b4079074150703403807210604403e00d601c400030303090071440062011a6503884220080008200321002214928014400d6000c031520444411480509584840740715589401c200d13103001c214044144017000c942410309203c0c145004041c401030402041c0b00054400c59141e408a01c0790030f1192110342c0b0141002403100c0300710743c000d060350000c5051600300740d401e440e1143c0026001754200000084030540c00560540d210440b040c0080c54941600c91030900c003502d29107180384600c140094116207407000b00d580c0c0d009013096183c1d8a01108030581118a140000c03072582122041840000c116040004030150b210045250412079907490f03a12004c44045190402e00c06540140d4200017214258400c074407031030350000455820041030702c00085c010003207134100030812200000c90fa0b201c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 702552985 1250 702551735 702551737
    0x708040c080307030302070b010501020f061803160f0203010e06060d0f0501381507080c250905241e1008063c01020304051e120318010c0305 62
    0x3401e80642526616010760030018084d4002074001e585000c07010000003a00c1d0300010312440b011740100c3c00340002d81c4d550114030507005984081d44c8914002080440c170008040c016980d00f591250310303400361801d0743e40181401c407000140c8009081d8000c909000203a604c074840d4280d41540508000340030316a40c5002d90240a1032603c01400a04104940019222400c1c2c50991808000c03142c84081d58402c0c2001440c02103c080700752800801c00164010418040c010210020380800300c590a40404810b0b0350054070540c0500802114851305128504103030103580d802c6070908826045880c10f0810030001c0000c0c13144d00302c0c4510103602540c040040c03c61658940790070001c0421a08501404002d0080c0e00c0440c0e450b03100717120324030f103001410f540003140e810840c2c5510340e84440e0000c0e83e0700302c0c00941e204c0c86a4605511050100141b10303030700c0c04500c05800c040f00c0c640400c1000d9074020710516220404174001c0a0700705201c001c0341034031030010102d900202483c1c4201d807221103050507511 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 702554235 1250 702552985 702552989
    0x20c0a1e0302040f022d0f031e040302011a040203010807090c1b08031909120e0f13020415090308031501200a140106031a06060c0d020f0d090b030708040c 68
    0x40350400314103040c003d04c20740c0a80084042c00503080c10101c0c03030303100c43d090302030074511440f01d8904140500407052200c500a582c0c0716060000c4000c1c43c0340c110002e11040d190456044005079100c490491801c113100703101542d03115040c0d03000d40c15941000300d40c6880c0c0d0440c1c05800021a41c641072001740ba0305c90119254045c1c4121000001311009040c2544103500032200c1e05d125600e03a04902c01400d801c1d02c10700c10701030380000300b02e01c1202248108483e0401001c070545e90210030070382201569a5103c1140c518291310f0900140c0d164a41411481d42441404211060004650040010528a01c12a42d0244041c404545080c0e10000180c8001840846180c0c4403800c034545000c11110025030700b4a481e01800402650480c0f0007102401c2c2c545034000104040d042140341a45079010181e05900301e50018a000e09050641d502a03180400094a480041c0e103c6071001414400c2845803035030200e1207141400c00103013409000912440058200707400c000c4514002020312110398035000c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 702555485 1250 702554235 702554239
    0xb0307050a0b130b16050d05031302150910021c0503010303020307080c0a150207020109090b060904020c100c020715080103120509040e0d2c01020a0803131205030106030c020c0a1e0302 81
    0x9141d91081d00040411700d680c01c41103070284280407682d01c42038090016607110b0908450b425416106a5092090303082148862030303600c8009004078400d69907140401d60804419500906160606010000740110354449032002e1200820045c00841c0e404021201280d8100660716602c550b0001d4080c50881d2014000c2c1014807014000546081c050300100301c40342c000d80e90750742003d80312014031046a2106400070740c000d0341082240c0150030940c02401295010b04203031031102800d01c580405a81d0440d42210041e00080c000780034000d540184201c8882c9103241100075903066640e681c08541070341d8a5001848008140b001c11303030740c45402402c134940c4404144c0d10603c200c2d40300504030200320006010101e01d1b0600f50782c541c04014945040c40e01c8164020b0603049616200c0340c100c4d41c0702502d54000e4140c4001c0303600206044c9041041c00542c56071b03c5c190b4031343c507002009044402d2918414119000300981c2c0c10141d03075003085141502e5440106038550580c00500055018280d070000b5 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 702556735 1250 702555485 702555487
    0x603010806061e030a0309090b09010f14010c021c0b0a02190305041e2402070203030a200d261303050f04180e070503073002030109150b0307050a0b130b 67
    0xb000c06911906050844901808c14407960f0b40303d4040141000c005d00a207150502c007600c0400681440b4401d00ea2254410f0410745241031954010541d548080e0103c12640313140481a14100b01d11b00c01c4181d400422103204500745004101e011011a4207003140404058407100850b080c0048001407007203401503040d810f1003c04c000d2800800881040704d01c00f400c20009490352580c821540211203100794000c000d5032800544a030107441c5405a4660584c1084074102804000a41003129107055180d0f03850790702019600c40c4c10100043c2c200a0b50340d60421818082c1b02d1004880080c0d01a00399250400c1c41c0c98684401c82040c4c0d600855014009891600040c0500040258408d0398080c00a500f6030750200e40340c009240e079541c1548902e03040d83c1c00d50700e1184048100031081c14002112004515040d0402d900001c2c251a90580140e482e203030201810f4001d004a40300c0d059005000750040c040036842c03e80004c2480c1c1d51807040c20520000003519501000990105a000d02141b03028a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 702557985 1250 702556735 702556753
    0x70b070b0a151e0501180806011e080f0a02150913050402060906040909140303190203151f03050610050a030b060d060b0a0809030306100318020a230603010806061e03 73
    0x1c3c41c056400fa214450208601d41612600d41503813601c00010f5038840d000609a591038044003040070009040030240d0f02e6000d22010802900502030100c6c1d0040d1030005109443c002c1c0101320340043d200110503106003042040c0345180e151601d041c0c00039400558005400c0d130307560020409500c100c003003c691204000801040d50641c40e44a018103d02994820702d07a0344140111640d284030940307100440040304216071030010125002154029102464a800300d288140807070030f000b01c4842c3c94000544000b031203940c41d55062080383d41c000c504503485e007020108104050700030701c60805081c00701034880c0441c034081c1c1c03941412203460001802c410809a65500300c891142d4101c0c203040c0001580c4134000c41c001c80d13800820b17031340580401442010380c9410060160010040002c001c0e00c408600e410150245c0c2c0d5410301c0e03000030130200c02e54500084401d0038502c3d45002402074244902000e01c0180171050340040c003294064025515400c03180c50300200c01070031895200c0419814403c441c41c1c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 702559235 1250 702557985 702558029
    0xa1226040f060207120b2710020405121c030b010c12020a1203050108070605210709050a091505090c0f220501030b0102100f0b040203040804030203070b070b0a15 71
    0x81c0c88102c40d8036509440d040382d01c1c4e0890861005002402400b040662000328050340c00004019840c2c10072018511624680c5a03041410100080c114007030543c1e0201e810000c80c10700c01a0401c0302810200940080c07980d41031904000034900c1a46001c050740e031203084c0c0712079000d600858030791504409160a11003803941c000396540301c480781c100c0f02c070000d030942d54a69038064000c05050707403000406480c01c541880c0040380c494000c040640c1c8038005d00b04009841032180c0b03000b14001c4520340d0b60f035922075003844284490354015501000001d8a003c5010480000f000ca6600070f0301c40440d44d1004546403428820b044e8014030400c08501f050008071103091050303580c15032480d000c420000800e00c3d542c0307070019007c580031140c030240580c000902c12845036410740d1102602007840c42c0c000802d40ba0000200d4100d0700129421580004005024410361034200103050043c1811140316140041a541d82010600f014281000098850070b07e44817201c100140b4801a208000101d05000c28405e5 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 702560485 1250 702559235 702559259
    0xb12060406110937030b162105010509060d0507092c0c0f0f030307060f020423040e0f190c120812070e010e010503090c0306040c0905060a122604 64
    0x90f40340d9002d224803441001c0c130081c1d86100c101c0c0e400001c02e0031035940d8160200464080e1220000400c00e9000e590400d800100f25025100c4507031050000b4690b0411041c050303910400740100d44150f045441349000107200088036401d80e610300384040b8607201c00c0c0003c064184080480451900e40b008031107060847c00142800b1410790031034000a0b89504501402030303e113181c0b01e0381034042d081008420701003030080d008000b0b0b454803540300526180c1c2d1111594000990b40044042c1c1030301c1040540020300d058003e030840326080c04054842c420000f81000e642c0c0d4610fa004c2c50b0160030003101c6c203040c031044288040091814120b40003890910703103850b85181d40040d2512450f4a2544d0204044600c52441c001d04060180c5030500c81002e0342c0019142e5400080800a0510500c20f80d840151020b00c0843e0040744601c80c2040d0960400e8490015610000c00300f6000c2c0d202c2c100100708180080c0c07110000150017403020801005600242c02c01c0c40c116048a5104500000d0300107100d0500c04 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 702561735 1250 702560485 702560539
    0x100303030923100c031104030303020703121e0e01020405010c0308040309030b0114031c050405130605040c0f020708061e070e091501020d02030f030417071e02040b120604061109 78
    0x3c0100304000340c0e264160102c4410f0728a88a101509000900000b8081d42c01808464083c0c02e060304810040b1207010f056500d0040c000070841c0c1503a9120f440704044d400340c00b1500710f466000b03608050a100000f010342420365409002c0000c42c8001c5021325001703148800c05580c00040b0004150386440c5580400310349070380500d00920a40221250700c54003007080d0300500000d55116440c05142404010200505400d00d122055547c0f03c00a181d41d207034803400040c5070751600d1704036050a20060113070070914154814034850f000001003041d60200b9a88600082d8001c00b19a40c558560800481d82c2804180c9071a80005240d001e0100d0000c0c22410300524120980c210380390842c0001e4103e840740601001c01c40540800e001143c0000d1002c04d1801d8000c48850303059090402e59140e000300c5681325a54410024801c00110041d82464010407101c202c05a41d040d0745004c50402140da911002040a0040b030341c1c0704c00c100001d040c405d00319450604018041d0016245060050b03100d12071034 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 702562985 1250 702561735 702561763
    0x51c030c1a0f06100f2c0603040507050414100b0a0507060c0c3e06070c030606050f0a0302010f08091c0518030d02100507140c030c07050306100303030923 68
    0x41e51109111341e200e65000d01c81508240e64442c0200320010980d0302c06103ca01c088802800d60042410113525040081e620590040c0020702d00146000d0512003211011005016461941d1040013150b1a8400d401c01c1200c15003809169905513280e005c85990081a2000301414140720808c8806c0ba404004600f9aa0199135402d80c04c01390014400f07081070342d0740394041d05008a5114100e14890013030300750041c514058240ca26100305031362100c0213020315410840c0c030b80d99140002c0c400c41c1496001c0b421365100c00c0d10300c090751a00355000a08080700003525202040081d600180d009001446618410b0000060403030a9541c02c01000e002d07504030f10640c02100b80f6210fa018810301e00091030b181781d51840d4000d000c040261840d03901c00307404010030650522019807500e50002d0000c0c0700500714005890701550329400b03101c0002e41040000c1c0d010504c00d911401c18050a030f1518207089040380c3c2d250400080300085446e04181000714082484441050002e0207400b254011812102040503 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 702564235 1250 702562985 702562999
    0xc0c03050a030f020106051e0a090509060114010201050103110904020409080a030c020609070b0324090a0f0e061017012a080f0c03040809031f060807051c030c1a0f06 73
    0xe81c078000c171308a42442c0720b51f6620041c00342c2c3c05401103440150b510740409020303040401c4c00340c80d032400d002568000e6461080e1a8020001049140c819120f00400349109200a0100e545181c4031319100c00751429200d886800214045400c550b02c03688991591544a40410b8030755003101c3c1c0c090010060a42110054007400e00019800040410720b9070a490b490301c101802d40e120403102502c40d0421220039003d10340302a21004140d0f60300d031500383c460720365101e0101d071501550400500740c4200c10b5901e525540440d041c84004807210780750760152541071a0032100461000803140c007502121101000402010710a60111944a1100e06001c801d41d182c40c10961154480450780c50002c99461200c0d94051022070700003001c00300240b001190040c11a2200c107030711045016205413001021a00b195100380c00c20956801b805090028001103a26041100060003142449241903500904200103610800d00708800d02140030074000d2441138502452501d130152031414602a00c5252003040 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 702565485 1250 702564235 702564257
    0x605040f0f0e01091104080a08040504230604110d2408062e03140a0c0b090112110f0c07030302010f0203160f020c10021c02030408120a0c0c03050a03 66
    0x95032200c00300c00c07100c0102c00c007035071680383c071801000034014407103907020142c2e0400c000140343c40200860807000e409100c2c00365845207450300308011515010b080e9220300801e21107800003ca44d001081d0f034400710640380400c0c000000702c441c1040c2d210301d20031541058035018a40506600c1c1e000c101c0352800103902c2901c840307503ca0048643d1442d0844044103809001e000c401c1c0c41052106120a404c40c41c00d80c40d20b20540c80ba5078500c042c421b000c09040a5512400290003800038a41d522001811007a56207403500c001b0781c00090030041107100c120f03c0789844040317510030020900c084035020311000d0029074a03a14100341e266284c8405200c15001582800321144114000341300b241d0090200a45007101c00343c0454082d9186078842072800103600407162018116203403494540450009540030384101e08030845401c3e14001210010811580144010b0000540028400c1e03008101c0881c0c02c1d0701c841403860304844440c43c0c014010001282c150001040080c0010803650241c4252650b42c4406 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 702566735 1250 702565485 702565499
    0x150603010c0905030709020705030f0714070608010501020a14030f0f0d060b030f0112051f0905070f0b0f130801060308030f0f150103022104121b03090501080c0c070605040f 76
    0x30701d26000303d543c160080d0a0400204c0c10325801070910b94402c2090324240b101000c0c1d0100207400485c415110918860300381140c0c0481072101801921050404603119410000002d603030b603d103060024000308444185901c03070303902002600c1e05a40c40034510f50760350000c42c102000c541c0100f011140003906102000c00d6040c3c146003901d21a684894250880b60302c2d003e0000c142d1802e141c1d0a466074010605449003e100e1a0100c0d01086840c50000c1903c00180c0707000f0b80b50100c540d00c0080410900c3c0d6003441450b01c0c0130704850680c91104034050b210f5a01d0f5000c81820180780d48070910b198a020f1000040060901c05148030300b00e00400116195038000d02400e0140c02200e0540e940f10300c0711a200d00b1517001c4d5010300f0034130074002c40c0c103540c01441c4d1181410300d00003074a0545502071200e10444029a00941c4c0ea404c40501c0c44044000400e00d913409040580c903802214148034108000403030b10070b5070b00152081011060101d03442c007a0f407120040c01c10351090095840b01c1d2910307030300401c1c11 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 702567985 1250 702566735 702566747
    0x90d020f06070804120509040906270506070c0309180906060501080601020a020909030702191401050f09090606070615080c150304120309230c0f031b040e150603010c 73
    0xa20116200ca0416540703d640e54001d03131902c500170b5000d020301407021a0035500e0714070412034094030401000a0784001d900540c022240c6220004a2003503100984078002000030400f02d400004a041000c841e06203031500380c1e1900e0190b003248010500200401d201000d0903001601440e005900070410f40362030302c0c01154480001c40d022809640042c070054010b00742410015070140c411f006681c1401c24036070000d901c1e030345003000d0101048039842040c464051008000c400e12030017401c25500d868000510120203014800c00c0c00d10500c0103800040c4251205402c6900b0164442020801d5101b00e082480c19200310b400f0f1210b052181d40d4080040e410300c1542502e02d807408a8400341140d907503989911400b00e48900003c01c06031140c01150002321081c00d040c118508181e041321400d40700222a900c2d0803401240c01380720344030101ea40882a06c01095110240d00761403101e10038480c480780450050b0015140b01c441a201ea41101c4624078001462140940001c4000b845040b80b940011551 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 702569235 1250 702567985 702567991
    0xc010516030c021e10060303030e0c03070e040f020a0306052a0a0507170706150614040302090f04060e030c0d0e060c07150e03060126010603050d03020a050d05090d020f06 75
    0x503034010b281d0b24081d0f07820700891320b903a518183c0031162002003219604090390100d0707000301c0200e500c400700691002400c0c400c6880c44801038004000072464062042030000c00944080d10f45002d6120740800d5403280c4001c000030390341124080c030843c101200c850b0307103440d0200840520172062500318280410004201c400948056450301d04200304d6403149071036040d0110071031880040410103080002c4140c0a1815409450103828131060300d4600f01801520413983c451320180c10402c42440182d45521000d07801490440e840b030311b1079680307260240003496261071040c0309210105100d4800000010511380da0030895035040e0705003000d4420701c002c6000b00c0001030031942001005021031001054140400105e80c0303000f040752000c540200f03040850030b030454038214a0302284181c10001400c3d041047c0b071030003002045041d2450f26455280c2080c1e5039103100301030f00021481c0c0390714400d070280c1d40001c9511908000509002080c9561580c12401090250090310710031048550003141c5944 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 702570485 1250 702569235 702569237
    0xb010f09140601120209030106080d031b0306080d1d090c0301052728050a051012030c1b080f030301050301050f0f0c07021809010c110304030f06051003080c010516030c 74
    0x84c2c0281081e1084041d400440c01140c144d940c03000001500c4004000070022003982c2d4038002040106040c604418441501c1c0a006040c2020802c000080b000140d9035030354405840c000783c0148109035150100e03a142007045a100c0d61700020302c10300307040140007141207500844043d6203020070b5000c001070441c200312480103480306850004038000031405c6034100b102d41804420a28100c800d007200308441040c0c1e260300289a584041244400081030040040c158000c00f0807410760382660024000ea62410004000e00e4583d109114105d0310f05040350301500c607900588114443c1c5008540e07a82e0000d04c9000e203c1e40c28800450b0000c0c034400300d194002d48400c1c084860b1581c80c680200c0d21a840302c3e4040fa0040b80c0251404244442000300a01811381400049902da20001000b0190f2140403440c11054000700020800a007035481180c90035a1302940100c0d5a0303580754040c1007020616480605a1603000413100320304001903000c42d2081080d20040c4d841c6070200c40007101100c0741100c600c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 702571735 1250 702570485 702570497
    0x3040309090c03060e0105060f071b0906050603280f0924060807120221010507020706111b0310020c061014090c07020f0411090108010e070503040f08070b010f09140601 74
    0x11055090230b400418000442110701403601e40c0361b030384004410041005074441c03041400c4003070200e41c00a01078000248411104a8110304241e00004110040c0f241e690020000c1080e90442c00d46854101402c128807044081000b03401c14100054008074200c5200b01100002c840c1c00070700303083c910654080c2e41054005104c04ca040c00503035403401c05c5802c07060707920621210304141074003100d010166010f4041000400c59003400034000c0d241c00f030690011020300c00d0f41c00c500c844e418030003c1e00703000500e04e8401000c08000000042401c080e00c03095406004c500024903c2c1340300c0c0c0001005405003c0101007500003c4d42c1d04400108110b80e250103551140812000c2104850901c0103041d03a1800105000e651007429030008044079944002e00b000c4110200f40c1c1c071701960700049aa80140b4501c1c9a60040c0e1524500060203440010001000444145c11071018007160100341c540032603001d40c10f00d81c50b50f11842c00c001040b200d031040510302400c02c118218071320703120300103140640c20684400d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 702572985 1250 702571735 702571739
    0x6030c03020607170d021c1b140f0309160906031121011401050f0108040b2d0114040c170114040b090f150a03030c02060a05040b03040309090c03060e01 67
    0x42c0a82c440740081d80d03000510255900e81c40032039001451780d110740c1c1c4801030741c45509911404070002c540030210306481c40c000180c80701008424188400c400f451801100e01907850b440d160030b034003909100c0f2142c09030100800c41a1a000102d40300c40d15030805a83c405d442d511040b9005545180c0401440f4101440500c200c0d818101d46512800720070304000038504d206800002d0071203401c0c00c2d0412100004400400c8142080c030640628418203203803080ca2443c1c1a1144000c000028140c0400103000180881480741429052503481d2881c5801d280f0a5945e04c036a80a41e1034504051845545040c00c40d094440c0100c60480c034040071a110554a6881c00c0c04101c41e140301f240c079aa0304a510744410358095940c500311148601a40e82c015007082c00c0c00440b21b800102c55006203805800c04600134408070b81c006505005455044841550703d4550440032629400342d0b0748042000341c00032060000300358000c028441641c50781179080001252030740084084c1c0307605120b9a20f0f140c40202c01 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 702574235 1250 702572985 702572989
    0x61207060f05070f0b04061109031b030a2316180b030c040f020d0e0307030210051e041217060d110f210709090b180a0210020d020c0406030c0302 64
    0x26603a074000060415505200e400d8582d20580c2401e604100d0b800d81c081400c110420815105005c41140000d9000341440240d00203c2d540702030860344c0a0307080c02040100261035600300302c03035041c150740f0114840d0b0100249118800e1950300d280c2c10310301801041912121002c3c2e444511080301d00c0e81404641d020041c640c070400810040607101e425010703d4298040c0c60321103014030340a0a020f114016030761103034141c42a04031807014100b2031250700200405804280d00050480944820000005030b0b512504203004190f0342c010248c0c400c5c20280c0c420001406620b542c4151280d00d9501c844003031901a180d0401c84900445860340c1c05440015501c01059440711100007030000a05602c90142c8030900059113036038240851b08542c1c403016a042c03d150340c1404003100409a8403800c0c08140556504c41080e440014060b4040c0481e21300b8000024a0410070a154590081d00001030b01d904a0f00080d190840c2c810210003512031184c00700f5450919109800c122900300c40f0aa6245040d903007 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 702575485 1250 702574235 702574247
    0x32e0e0a111c0206180102160e010e100302040c0906020c030604031b0203030c010e0102130b03100b160b0c0a0306060801050a030f170c0a030807020a02130506010203070f0501020901030506120706 86
    0x50b6810b41809181c0448005031202402009000701500303c030321041035440002490030350004240312a96518080400010b00c11104040c150b030000e50a581c1e03d0703580e2501050468a06500195000341801280c0400c01d4006414006550543c0d0984005200f0703041815a00c43d13040e10018001198002110954104e454100c002a8802400c1d0b91410000602c0c007070079980348070f20244280e5400141103030a14840c1103210002e0642c409507900758034120020a40c0c10849106e1986079072800a08160f0110152400c041540d81c8a4220401d0782011848814943c010a0340c04001c00e16100340030861030300546895040301c000602c804050f600f1941e4144090408101c1104d02c80103903003080f007421509402a26007141d11070010109074000c0d040041422001070701c50029500306e45603650258172015896090441880c0010920751284170040f440e40c1b00d803030303c081c0000101c40e620b03004220301034004001501c400d07641030150707840749820400002d56200c000541c40e0702409041041601480c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 702576735 1250 702575485 702575509
    0x1403090a230616021c090501080a02270906030c03060a02300601080106091202040c02070503120c0606010906080403080a18060f0f2009032e0e0a11 65
    0x704809102503046041e185040d60941d030446081c0c078260405a10b00b94100441034241002d851059442d02e400c0c400606803005038058030381049030310740004000812680440b00138420080c2101d00c9203501c0706420302c440e24190300d020304c6074000c10042089c6242c0054035280e2002d004020f0805900c895071000001d600900700d2600f540c403402e00205211001141e4203403914031207d4841c2c241c2c5000c80c0010820038058100c101442018401404845000c040d195551941502c00003506404200f081c0c0c90511190703c03540d4144661083c00140e002a90083d0540c510654100c0384113460b0700f001590588003e00980000440000002d00802e2046420380d4021444e440b00046105d00b03100d41001100d02030009880079510b442c03c014041c20b21f846040c0c01e400d8140c0081060012450a0106601d0725000d50b030380e820004514640c0030342d814040d4003101d01c90340c088000035061075004010150703a606e4400c8846480c08000c902911404213040354402e82c860840c5529400b9a8100900e4103200 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 702577985 1250 702576735 702576773
    0x2160e13021207031a01060c080a110607030f060b03040201050a080c120f09150601090504090615030c050a12020112020a0302190e120a12081906151403090a 69
    0xd06035001d40c0303030702c00104455100c40740641492800e40c00c103ca115215802600540104680108811a4030418502c00640c0c00900300d99501055403048410303111003110310314180108818403071040d815521103181094507550501041c0d03640e05d00e86150f400120340103408550200504540c59200f02c543c254002010960301e810841000c0c1e2103802c3d01c0e001c89100038010303c44014850220004c1148046e0000d401803003800e940341c607600081100300c3c540706490060b511024003508000107508512213180340f1040005140d544da007445030f10480940305407800f500d5460350120707081002e250f0310b81030300c3e070107868038041c00401c05c00d010000d6118008030f108040d4240101c444a13540492144d911030402da6500485454000400010925140121851340d101110300400101c403040004085c0d042800c0400056031449410800c00802c82020002c042ca020b1011486002c44500b44500140507950010f2025400600c580c075480700303451800d2160301003000c0c20700141110501c04491030003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 702579235 1250 702577985 702578011
    0x91205031306050f04230c0f040b1c030908070609121401020711040b01031e0c020a050a0b0411010503010b090d05030f12090f0c0913020609061902010c02160e 70
    0x82502c0c2c00040315000e48001501c61100401d20091101d602d02c101251800b01600904102d440c141440e9154032241e40c00e8001c1140b640a00c000d641e4980c00106070f00409000480d410b07448980e1514140300c54441100461003410000c00c003502c000031810243e03601c503144c80b90004d00b04102e4100c011099002240c5a07070070422080d4a105080c0040d100b603611880c03070200300c244150100030985400040c07850415140c095a41d0000c00418100250704000c02000a030b03c005580040b03052200000002d003889c4074000e0410208018114180d12075030003a007184000100c44401115580b0080c410048041c100b40300040452411b0058841004d1099040724075106800c1d40c240b0050704038138051404510000d00700031111005220100e040703030401c0e000d080100c954400003003541101805841c1c0b8440507040c19421910340da000c682c040440140a0380e11440032007a00c26400d00012004070042d402c0c1014840d5071030000603600e103103c01d2121008800703814121400c0f14118028080421240 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 702580485 1250 702579235 702579271
    0x9030f111e010f0b0411090613080a121803020d060f0b090702070f0504090201140307170a0b01180305030a050a0306170c280501080712060603051909120503 69
    0x541100c581802207504004a924000c0a22032022615101d80141c0030310b0a2070611459548074800f12040000115401e54681c2c41c0184030300030300781d901d402081e4944600c0d80070780140414064005014005640c806501c200156a1803032040b0807480020f40001e40c00e51080000b50302d41e040b070310240307141c9100010348402503000150000300a407550009a00503000c240003940b40a482800501402d071806d224004443e40000c040030342700c5005480c0d8140100100315203900c01c03550b11403074108040c1d0303410041c10710210400090603402540c0340441d56481160024078144c0c03d001c03048036000703030181d410b0a00c526801d485d07039440f0703003248020035581e05800b0a00a402401c00403608640c44000c01c085000907051000b050240c126000300039541101003404603d8405201060341c4081c6841512a191010182d5107a485a08040c0603d1308000c004075440f0351580c85148039101280164844008044444003110011400a0110b80e01c1a505402c8503004000450300581c4051901e9147c1c4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 702581735 1250 702580485 702580513
    0x30f02010e0405040b190b090403180801091b09050702060c0901200106060305070c2f181504020f0909040302070f08030a09060e030d031109060d02091309030f11 71
    0x1101120112140360703884003401b03402c2540e03000c0749400b02c3d44c0c071340d0400100f41c507100001c1c1402001840102005940701040d00c400103484103040007030919000074407142130302d80362501060704013460584441301078040006070381d41940038042c000c0401d0f4001c0c2c0960307200d91030340340a141c3c01b440f011414016502d0b071102880c0c1c207002c03100b640021710100004030b00c0e040040c001e060310030181c04007040281c0e0b8040300700865180d104e123100e1018910b10104805403500703d00c040c94600140070682c002c03c10082c0b0000100d580841034420751020140c2268180a03c04102c01c13030290780403946803284207006004250404e000030030f4005000c1c0c01190400c964602d041e4400041640002c149900082420b03000039070403484072000740a9034109003e42001840c046561756141580c4074040503101d00d208007015400c101120180d20000c0d00c000d80d903100d100000c40184d444038907503e010799441100803200e4a40c038415100485d5059580404a031140350b402c6507074881480400301103000c3c03459125500 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 702582985 1250 702581735 702581741
    0x405030304030b06040f0b0901060f090e07261003060f090b07120e0a080d050a0617030406090e0105030d200a061d0a0c060c0503070206030a0510120c030f02010e04 72
    0x314070820003d0b07458500301040c0420758a851030719216003400e20104440e0340c2d035607164050541d0316500e88190080d040c40d00403543c0e41c115a03c01400d4988034001d01c82d9585d44034900c66900d415480300d000840b444100c4121518104550f170030a4181014800d00020303105802400c01d40105c0d10010441280c56281c0200658040d00c910780030402c01001071007000d6450150400100c241c2e400b914030886603481d8a4006c0c400c01321045075213a95040001c81d074102d503502110191401100c1d00100f80c1104d4406a640c0d4014010000842c0101d00001401291142c03403078182d400240140003d860995002c0d9030802c10b02408140c8031950b687d00419940302000095501c500410300030904400c1415a20310042c0001418521500301c241c061020500d1f900c20007048031300d10f207080c180540341e40c20300c5425070150020096002c100003050041c0032040c0d03000240510204000b903100f090751229031007005045030000902480c03a410041000c40d181b000703083e07180d60041c14103040320081d45000400f2 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 702584235 1250 702582985 702582989
    0x706140c040828060513170307110604050312060102031c05181606080903041d0a0b1f03020306041b02010c081f050d0204090b010602011a0a0e07080406020405030304 73
    0x140000100e0100424141044104040d5081c0c0384444100107260403403075600f00c4807180c042d01942d26400840c0e40d15041840c1c2000054000008044040d07581400e007006a000395010000a00b103205c400f000341c8000300300c250245a10100661904085c020f030461036090043c900e40c158002413020181041148808400035044c0c200000303420319040d00724400f0500f240b101740d021a031000350224880904410040305231620f904180002d80c0e117500780070b8550312803604544a0b8039030b0120745a0f140e80041c08058000c2100f200240400194101401140d13580710f00380c4421840c4040818407198002d50081d40c02c034802900c0400c043c20803048011920301d49006c1f1400503075603800f6440c4503c1e03220311340395044a04080d900500b4890009101d00303c031041d000d118400c4066241d11000c5503140e40c40024090791044003c60b056a481e40c0290003828001d49150448054181c1703904285800c600c0002a900252031800c15610389034021101c03094010000c80713229a0821000c58165000c001800c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 702585485 1250 702584235 702584251
    0x91b1e130b0a03060e04021c05070515070b01080313090c020a020a03030f020705010311040306112511060f04060c02190f170f070e09031e0405040c0207051005070614 73
    0x40d507119000740003021101258040d03101030302668240300050340c90044c0c45d41c080d00100701d90841c04408e428101d091040e550302007540305110081303a0141c6d114080152084134000e00400794144e0b601e0f807080362240714562428040041114080c008003140d1303032000c1200c02040c0304441c2081d0140d40414201e0a50f900300b60041411103004c2c441041d4100003090180c44280303014021402c004419040e980030f203000050019454940700400d049140090300e0700036912441003841130801c02c081c0c42c44007248480c140ea40d9844c1407000b10040c01d11074110b4a1042185003803510740fa14200007142c20384620107007264005a055812000803508001020140440b0000168140c1c9050740c1c00c1c1c40c5403582183c000321a044443e440d1091200032640000f101c4d0007540440c1075540c1c1110660440c80f0b032080d505414003424820301e0409021002920a980b4144c404100d503401d034000590303807101c3c41c0c40b40c0c581c0040703511103481710b07a4841c0024000c0d05204402c0804d5240ca44007819100300390450b0080 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 702586735 1250 702585485 702585487
    0x12160312060e131110171e040c0e1023040f1a01080108030a0801150e043305030a060b0d0b04061a0103021201170f01050c0903070f08031e0c0303040b06091b1e130b 72
    0x48044a540ad02c403a400c100400c2c0c6220165240c1300c076241c080a182c1d0b445810b41031008000000075101e58104807022100d540c400c000240740c0d00f46160540130512505400585004004500c0f058000100d4190b00c4583c0c030f40c0c00700d680c60070b001182d4011000c2104010080007100d51981e585a0707024410b900b5041d8803010001b5800344c0d050950303590f80c42d090700300700c50031001080280b910301103034114110307803c03a00110b500310140307000c991180204000140304009403c20401480420790003005802c00140800c2c80b6101400e00440c280c6c01440c81c4d45001c44c500800400014010030380243e401e4502000361042c0700048040c00d82110012070f501041c042000036240060301d01480f010300500504000e01c14094104030600341e40b40108c10900150341d01f440507134028609007605a802c1d1142c1034046035a01c0c9801e1074108c941031030680780c060240201d4408103240750b82507880c8400c040852446141440390028200301440700c40080e680c1500b800304400c446201361300800c0006890442c24403 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 702587985 1250 702586735 702586739
    0x812040c0503014b020a1e0206010e0a022b0b032d010c050a030218091e0609010605090904060204090603050f12160312060e131110171e040c 62
    0x120030390403821001806901c3c030340058003c40405080c0141030004a01380c00585030458403a00756200014041700e800503922002c0c3c0b032060f15500140c0d29040e00c514030b60b0004207459011290b0180e00440040400075403d09021a0745204000c00c0564480384000f404503040001c44d000c0380c180b60303086544581a0380c0000603494150b280c602040040385554008001a00d4048030080c11409030b00000343c00c040e0000342c100e4100c03d44090507a071a0100400350000c1d0306080c440c0404e04405411420404551180045c260b49003954840741202c0160310f40303a14116402c0c00300030040c040101700b11010b5600f80000f2900209078070424016500c5a0000d00c183d0790015805450840b521402061005080000410b2120320b00005040d003a4103040411105440b1460b240141080c6e8008141940300c180c00c0112000d00144201c1c90070b40141d501c0c042090003401445240040309190001040d610300901140d400790340c0003581c0c0101c90300b4880d41030788018060042c144000752800d8940c00d41c03c03001 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 702589235 1250 702587985 702588041
    0x402070c1a090103051303020c190806071205160912031101050a0221040c061b05060a020414030309030604030e03030705061312080601092606040602041a03040812040c050301 77
    0x582600865000041e1040001b181d074029500d012a42c10b060040c5c01800d43c000282c0314611880c80901092010365606203441d00b00240116030b0b01514070320242c100b0300451b0004401c0e00c0a02035105545da900c1441c81d0601c601001c0b020b007510360850070404201401d0541c0d21082c890b550140700c0200015a071a00003510042c01c00c10500021604400414184030028003034500000480d50b4500300895040d080c00b85810920303d07152005072050085000b040400381955008109494800c4101e61072001d210060540e280940100700350164003190114020a005100c040810f440041c00c81e0f10b008910303502d0b203003004801e540404140529403141c8082215904a0f208211010320f440038143c504200024030984843c400c8411030100d145100f942000e0f1001161034a41c00c400884003981414981540254024440c0c1c0152562030560b402c507081010b411071b40150b41041c0c03c1c5040c0603a050340100b008038003034012135030195000c0b4001081e440c01e0094812074018158403085156600d52 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 702590485 1250 702589235 702589241
    0x30405090711060f0a0b0d05340e04060209100306090f0c0503180f2d030405060f0f09090103150c030506100c0c121202100c0c020402070c1a090103 65
    0x1c024018081d0071480e2690a407000078105500400c0d429503001d1540f1001c802c80014070040c5003054008003400d00395014060300207150080050b090006040d0009101520f0302a880c40e20321084803003c1d03222080000019a0101e20b0b00b25004901c01403400d4010000548038100c265180030100761120401c00500125100321610407080301c800380400000321800404c14400148420b11954603906481c04038035040080c26140c0c45482e00b12000000e000300000200900341301c000702c0e81410030401000051010043d01c0c00c8a101078591420b000341003000002a070841c0708090001c60091180a030315940c0e5810090003140201c5440c514064290748800030ba503850900c071801d040c104014040039850300c2ca440c40ea80701c4982341c02d01c0c0141051800d1011006154049030082e06540304d51003c2c041e05404101c4c0b8041503070200d807110ba90082e2840107550a0000940c0491851982d81c40941000d0300284089845020184001c5403682c00c88081e1246042c0030025000010405d45c0d02560584 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 702591735 1250 702590485 702590491
    0x210051e270109030c0822060207030519020f121f06170706080106051308070b03090f0f03070605090c030105040302010e0c09060a050f180f0a05010b0901080f06060f0c03040509 78
    0x1c4000d000c08442d640f0042d21082d8100c030020502c00d00094107031441d20300d1000d04041c41c2d8210751032035036840c0d803101c3c000e6884849000c2543d40d4040c2d004040b082c0d244400d80250441c0e4090001c0d821031560004010000c840b440c03501c51240141c04c0491012041b0b04086c8040405803000018120f04051520b81c450300c0007408082d243e40031040500650707400c558040d044491a1610315501c0b0ba0300c41e80f00c042070429038400203047c4104103001c600300c940600514800e14041c1304850b144444c070300e102650707080541c3c01c40349150020000240450340e5504041d60200c640c0044503003040c60000840e00311401210281d0041c4d669a00e031a402c500240004481400308581e40d98460504c040011145c03e001e22983e4400da1901e810614141c0740d02c05026107032154800480610300d8958bc0b4844032900c202c903003601c030518160012030611005025a4444e00d410707961440c0960307078441d070f4545e44c207405000b1a90018091080c90381060004008205160300c1601854450b85010300340450f0305009 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 702592985 1250 702591735 702591811
    0x60411011d040e160b0721050a1206030b07020d0306060e061911120403020a171924140a02030615090d0b0f040c060e010210051e 57
    0x900e94285034195905005403140c0200d0b40081c003400600240c40c90800d18580410704c0701454040080c3c01c10440d006448038502529410182c1640740106a00c10000c440c0702d0404078605006403c01c5904c110359010303070100e40150010340d041d01c94840d00842c0c84100d41d07600050703210780312020160ba1315001d448011725082c24150071000840000a200f03004900b03186146542014810003005d100311035001ca03400304402607030522002e020010016a11a01003070b0302500b504200000d09100030042c98880206890245c25076100a1001c10460b407040324050328003142c206112000b56002060780072946a45005c00942d4803803031429055221030040c01c0c0056203106004000c402d89501c0600241e5101e800903095890109400042404001c5a40a009680c1c0c0304100b002c050000c8a0560043e4010038007401102c0d0358481c22100000c418507111300582011040028444450b00f08541080840904405094030f0001d001940070080303550702c00140740760ad145000c1442e8140155091110 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 702594235 1250 702592985 702592997
    0x2003070e010302041505090d170403330905070e0106020f010f061a0f0c0102040303030c030f0c1b140d05030601090e0f04080904020c0703110a1205100507051b06041101 74
    0x742c50342c5040002c0803105c00000340000010000450750750002070158165010405181c2000d98601750b42e5150800e00080b582005042c2c0000c40b0a4000030a407580c841119014000ba0b90815840c040a040045022901846803140c042520081007c400703000c4c100311743c000c018985c0341426880c20b603a03191100e201030620b402c0c000d1192984415008c0c6038512080384140d62000403102034007440c458ac81c1504110b5201003000300805504d034025191500340daa4090000ca003204c5800d1086131454409034001c5080010030004000035850344207034550080c408441c0d0820903a504a050a009540c4040000c00000401030b6070340c4c000c0800b902a11100e64900414a05036000074005100508040c0c15410b0214142e803a603070720b0780c0440e0146034020080d03540d0f0b140e803450705181d151000c071405881280c030b50b1400308200490b00070178485541c00a000740154046a00c2600051101078041410004200008500c9404003a0307940110312041c5c000b0016480c00341001714200380411651810010 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 702595485 1250 702594235 702594239
    0x60305060a0504110406140409050f041202010516110106120b090d09120803062b06110f0405060c071d01030606060503040b0403030b033901020705031902042003070e01030204 77
    0x4c0300c02c1d10151091414a4601014005c40d000b4586c001c1f544103e59050615080002c103a01080030795002d140f08200504107004081070903400e0f602c0403038401d001882e0b0745030300811040c8103940e021040200b140000501c41c0e220b80d0001c043c414a958261362002504040c08407920007003100c400029540c0c070b004080389040c4001404054a02540a0103103d404408901c26960300b800d489001490042c1d280410a441c81c580001150400c009462862405442d00ca4840c1e0b0074048926111152444a1900e41440c082107542c0d00214000320312482070030070100e03c0214071035450106001c0c05011b4442980340d0700d4914150b6103a07130480803c0100510620001444946080f50029410304001c0307540264040881c1c64060056005000755160620140007101c0c070040485c40010700b2210440c0001b196001603035035090074401e80390198460400d052021103481e0515002d80c0c402080407030039000d484490b900c0c03200c2c3c48401d441ca9200000901c5002600141032807104034003800c0c2503003414 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 702596735 1250 702595485 702595511
    0x20a031509050415020c1203040311070806061c0501150b0d1505010c060207030311131e0b03041203020c24060906090604020705011103010609080601080319050c16060305060a0504 79
    0x100784d50842c08880ca8010405844454082c4000036901d00300c104030070303103d20306410010a90114031404462a0003002004620700c540840c5203407240318003600c91010500c3c4010825182d0454181c00d5420f95aa50101c3e1505605a2a41d000070541d4207551500d48110344107002c1140c461801113200d55103080010003050340c201815a00d126007010780103840310003d050543c06001c50302505c01c00342c0c074001880c980382806100c0203c26941c0b441a50042c072801c1c868a981c4481c0d49004801e00d083c1e050000030001100f04180d0481f940807032030094249100798072800d241c46090311001290344c43c0d94505011600c2d098070990fa2248013204c0c6500d0780e050800c00724000c603501520980c02950001024401d00c40e094002c80c4000c0c454100550ba07e695602c030041c01c00300d0741d014201d0180280d400000b0b04034000070980c1c6082010841c0d001c10410041c400380c0f21580070f645226441d01a02214222481d650210000280b4030f84d02c0100d414a00803042101014030342c0c000511503841e0044d440300035 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 702597985 1250 702596735 702596753
    0xf040320061b1309050a15081c090b030f070f020a0f120507080708040509180312150301020304060b04051008030906090d020a140907031a0d03090801020a0315090504 73
    0x705031450300711142202c40600740d80140c41504a604003402000c00300141c030142c541d112620600d09004208101c140e07203002c100c1484218030036211942e101c8900c8003c403404055140d242c200550500030344007607076460308642540040782d401c2500c3c00407a0812618680007036009400b921a8406081c44d44840d90701d00c06a03a1100c6c0c0043c0103031481800c40802980a0012200015040680c060b2195040e1030902c455131301034022513015003468004207160382803e8043c0440c440c0403501035401e1120700d201d680c2d10300030002d10590800801200c03220440c0c900b80300860250307000d1031700400c03800969424001924005480c29148411020042181e4107010096503441d1000711400c039a15a07009002031649400b400f0040d51040c41c641c80000c09003144165802d4950042e07400c0d1000d5901e100f010340c2100c08a60340045202500911000c0b1480e0090160044130301c41d080024025840352411070890708a00070110109965100d107020b16007881c00800020050301005001038503283d0359100301 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 702599235 1250 702597985 702597991
    0x40c02030a12061809110d08030c07050309040f0207030f09180b2403010303030506010c0f0305090414070e0a0503160b0a02010b040213060e0d05061b0d050f04032006 73
    0x1089515560b005128070365401c034030018160b107520a032203008100c1080005200c031032130444d405c51125028410340c0c1040b51250003040d03004200f0605550b80d030755014416078000b4400300d41501041120000351303581d40c0b203072140340c0704581c00058079654246800342c81c00050310f001c50300f8850100810445546d40ca9980c00c140c000021012a00c3c05440700880d40c4003001c0e1080c05480401345103d0003680d60038001030747c12203000e542c052215803200e10054420300300000b00508400720740010540403c2c0584003d12000c0c0c0068400601114014490300204000f6a25040051490218052540b03881c080c4440605400c034041c0810350070008040520604c144100d200401c0041100440e1500030b40c402d107800381000d00705656a00713000c680e260440245010b0140400c40900b1040254100b04030802103c81d4008014140c030349504901c0748001e00e800440c5803070100300700085122003019002d00782c003030b10401c88949901d0405140140031156483c41c2d9146118244d140808031a1000602c990 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 702600485 1250 702599235 702599237
    0x90e0d091410140a02030a1209020a0e1f08060a1406060a030506031501081e0c0d0201030b040603320f0c10031b0e100e0f040209030f0601080a060506040c02030a 71
    0x80c0580081e8183c0304421440300005410b4004070341518850340101c010304404001d40c3e10301c8181c82d85001c0d09001c585e41207101075013004070030009104001c03141480d2034100315403c070340c0c0503114410072070031b0003914440d0000e1030380390001000e02405030300c42d000780c14032200619801425842c166000c901d00c3e0240b00c41c0c60081688880114140707031014410002c17242d0303030700e01ea01d005980c4480d1031990ba203074001d0b08142e42d0030a205400f030a446020981c0c10910500400f84100c4a003e60011409000046109a44555a4880000001c030b0f000c01250600c04446c9065122032108a041c0d20940e400d9461400b103174001d11541031341d2117008240c1e241c54a104889200003540c0011044004000710750000c6910342007540420b46603a0804d841c10200b00c0d088900760500c0120100485500701141d0705290022444070740207015103401e4000d050ba0941c0642100c0507028603403000742c0340800c20390285070250446404001488528002c4503401001a642400f6141400000940d070340309504100c8 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 702601735 1250 702600485 702600499
    0x40308090d030905090403020102030103110f091b091009030506010b0705060c162f010329120a0f1a0106080c090d120203040e09060105090403110c0307090e0d0914 72
    0x700c00c040c0180200d8003d014003404900c050310382490080d00030f500a0009441c3e25201d84003c0d405803500541039400b509000d02540115121800c4006110b8141405c82840d03c10902817110540c075a242400d1000445a5600c030802c4d2450510038107109040e0803800f401c0f101081a00e000c10400035606402c1030011005990f548600d1030100d4500210950042500c40340249411056020b01c0210781c000407554180304c4c000d01940015001c03200c00c0c0004400071642ea070001d10510a032026146c00e0801c0103420655105103800c41c0700c1c1450b9036080121041e4254600035410700c603200c400100c007080c0120075145154100500a07058000c010b041000a08002518151603103420211000281e400280d5100385a04207002030344a4009000e40c00344a40303400d0016107010000661a4100d980103030400e485a00c1d542c4080355000c403083c8114203a4441c507071200070107031400c001744001410310f8000003894507040c0d01e4207800c04942c40300300d00411a80c43c80500801e0a44114045107010451b008 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 702602985 1250 702601735 702601759
    0x200d022a06071b09020403080702010f020607120b0d12082403030304020402160605012405030402152a0709061502060106110a0b04060506010305011e0e15031911030304030809 77
    0x80c0f0003001c000c1d004003c0e21800850300004000c0107101178001c0510036210160490503804040343d03600004c56014000800f8880390710950032460b07120000c4400f002d002c0078040346650715060613504a8042141c00644604100800a21203004c01081028150040c201002003000020f50368080504040c0c82141c0c00141c5d40340c500f10700300720031001990200c014040c56a5444010f4061042c044444280300c4992128002040c4150100da106542c010012000500c52410034000303a0020b101340071007029908506c8081120f0310341000d01c8200b892000308003803070418801c43c054510700d80c4000c8807545010020340712a50081a06410340d256407900044480c40035107214a06800d03000084c0030360381600c0920090060b180c0000d44a42ea0a07202031143d640e9501410010404160103541008042c850070301ca0407180c00121508860b4940c0020700050758100024100781e40c1003030000d0440c8420b524141044101c102c2c3d0100303104220003550500c1d145403181c203814402d1101c558894542c0c41a0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 702604235 1250 702602985 702603023
    0x100207050c15211012030c030f0903081c090b09010b031005070f11010f0e0c09011d1f09111c1815060b030f0a0e010902060901200d022a0607 62
    0x1421006012505c00108a003845080c058001b10300c0d1102900080d600404441e6454003591051045a50007003441d850f140394100004810000d070168800c0c610344494540d40441c44003041c060140c0b0034000009000100c40042602d04074406015168080c24901080005500003204c00e00803815070401c0c1e1921410042d01900409202d10440034041c90441c41300c050502c000340d002a844000d030f82c0b45900d6600c460001050900c09442c0002d160a81d030001107980100c052010300b44500303010001d020b203454101900546902c0c14203924030640204071994168008500401d841010441c10404102d5811401500c28080d0101404d00a800d09403142c2134200e90344600d004003600c540b0b01c0c0e164180321161019004064482c6001c00b03050200100c04210f040c0301320701440380e000b01803030f00c0c2c040490010340341d20750b08642407420b00e081000e5100d4004824000062015850ba004d07101c014032240032580030340e010b00c00d600c6030300c1040507a0168940314001207a28054029160004803040304103 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 702605485 1250 702604235 702604261
    0x10e0606090f04031e17100b0405062d0703020d1701050d0206070c080313060516060b03010f0f1d16030308190905150a09020918100207050c1521 64
    0x241e00e1400c0c0c00140990752111b600a43d2000a64480d181c280703096180d029038030354480c2c0c81d80686c0355240c608000400903403508500a00350034007101c03110003104010b0b0b852070160740c1d0800c54454000d00700041c9a000c141d810304c20300079000e9440c24200a8040d0088801e26030a605020b03083c09542e0317080640055584450644400603844481c64202e651609501522500480d00c4400bc440b050780010650b00d0155090780c2010400c00480083c03040d241d100c280241000c400502d4055681d80605440400f0303078011000a030161100204050311b0341031140024802c01e200c0c06000d43c21070502601074080c0e0700c0640080725058074109040e91110b0102925922040321a035504503e4004414100704010410710b0802442c0c0d04442010790341c2d00e80400030342e030a01900940c03291503000003806900d400d4070041402c0f04c05070304071042c110314007404400702d034030407030b400e840b5a448540d2040641c6012410003158000c22010581070000c840801c0720721590621442400e610194001003200e00542c1c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 702606735 1250 702605485 702605507
    0x507030e18071d091f0e010315150b220b090d0803071b12031a09040f05030f070303060e0a0612030c050c06040e0703050603030a1b170f0408010e0606090f0403 70
    0x280203501e079043c85e81e061401d80d01c2c8501c40740300c0c4510502d00000d09584c6056003d040740d4010002021700e1411000c00300c007d007001120224180140003012640c231003a00b002d40710b03082c803041d03c40b540441400318029124010f9401485944d41c200440140364441410049038140e1085080303480f070b10799680c01d880e0180411400f05026404c1280352007440041006000081702e580c60400c4900402d00c50390410802d21402160050500e00200d800919809070300b0080d140030f03405890418003200e8800f42d041c0e00400056002a440d50014000303441d00c004080d4210007206d0f070030441035242900c3c3c082c00c0d041030f28000e028841c0074008a000e11005114440101034001c1c0b016640d2611145240789100d03080d152500043d1602000540303e06001044801d00800d81c4c0311942541c8040a605500068861086880301c031200317100000c5603038510242280c1c036494948291164101002d031421604003501c0070900c1d074072403030030f000c0640c45010380c0c0b81c0c01449107007010700241e480d400c083d50040201c0c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 702607985 1250 702606735 702606739
    0xa06170a030c0c0b12010617070e13090605090c0301290d0c0b0a050c010b04090c1503020c0106120209130305031b0c0f0102040f1410110f0106060507030e18071d 71
    0x2500310b00e030174001030400b81602c0c1a511000b49943c00c0d8203030306a401d0000c880c42030101e045148c1c21041840c240c581c0c1e1244060b0032002155064050380ca480c1034071400d465400c4c440e400071010032098507007070040019251480300c0e0403001002d4002582c0700b0240d0100580c0c02015500143e9062002101800c0c01030b00d000d0301902d81e9482204001070066009800500d800d529100400728a0324207800b84054064000c0c5180080500b40000f810323000c440c440d00e60f0140355081000d00c0001c0000e016190041c2403003408020020302e240140500540c0042200f5120b02504007100c0000f604601030300c0d0409103184444810b9a05a10f4000d032601c100740284034644500d40400d440c4540540040007903031424100920b00c16a2080132244c0f0b08000c182403544a44d110408540540c0300300140744100d4480030807036aa02c1078250040e82100d1041d00524002000094540e0074142c110f2604d110a0380140c8070941180f591060360030244001901c410b0403c1103109040a890710301148283c060707000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 702609235 1250 702607985 702607987
    0x16180506160b09061014010f270b0d151206180f0b010302120102120a051e0103141b0d02010f1404090203160c0515040507030b0703050a06170a030c0c0b 67
    0x1c442d60640e00d039011520317100020141000800c50001c3c84030200507010040e100d0880501180d102592510184402450101111001c000c15003c0c01c1d081d1100522446104965540700b00661809507050448280161100c89400700b000c1014000000e00e61600000b000038a80320030180c85c6000305654002070300c0c6c605603c004609100e546444141202e10845502c1030802102055500b41d004846a8502e030344e98000005029482e290459503004003e00e504003500c03000e2070342100705000c00f0b03001910922a5a40c0f03d101e150070412000c3c00c040082c0414002d60352811000401d90340d140c4000031304100e01c00300103000709030180d90f15041c0c0c4084d4105164a507030715144a4002504120784407484140409112141d0303d009440ca108581c1c0c1210103402c0700e02c4000c1c100b114000b030213001162a8462891f000000c40c186515450045845681c04203607418207140600a991301500316030111240030904040350003000a109030200d905040c114180055802c016500440c90703441030107402c00c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 702610485 1250 702609235 702609241
    0x7120f020a0518030f2a03010e1b010201051003060c0e03100c0305010905060a031b120b070e0f3003071b0b0702180c160302010516180506160b 63
    0x90000c025200142e41c8220080c00c0d0319686040560341d1004032881c0c2a26040f426184070300e40f020301c5010030003003081c00c1c0f01c048081b420b40210b0300b1a07100408c10100c42e0410a4621000155100031401d0b078a0300344003e0001c0c3c141000c1c003001e00b030000d10004007016541d080c0c02d924140920703018010144000d0961700c1c0182c0080503c400740800041101c0001e10340b0b00041404401c511600d4000d1a01508105040342140d84203000e43d0010401c1c41480705c02c030040050141158188a40194494880c00381c490801200151501c00122840391151160300142c207141e45640c0d83c501074403034107070000c190001e0490b400139001104460342246107020001b03d00042c00890680c483c640a21f0302c80350a0002da4503e0014264024404025444040d014608034038508603840319400015560341903181191440036480040001354007203000d40d454104100c10440e100d040c810450348075040500c07407403400407c5551852154094288141c0d400314045505540c01110040c555074000040d204500b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 702611735 1250 702610485 702610487
    0x5091309060903050309120c0a030f0207030605010f0e0705070f0201081f080a050606061e030403030f1b0e0f010909111204030e0a0f0803070210030b06070b010e0a1407120f020a 78
    0xb905c200c840c0c1d0701e9407165000e0410803418a908a40010000001904003210940e6044920a19804400003107120349480400032402d00e200d014000c1c1100c2d5640a985450916480302d020402042c0d8818004240112404201850500310250f682440d044000341d4400c4030081c1d0300301003032102c00d03c400c104550109000c4800038008040602500441d0a03070b0b6a40f40801c015449040c400e4030b1408807003400c0041d2031426501854125100703080200e900c0b01450b54840441d0704114100050520b201081e07203002d9000044e2010700d10042c0c0700c0d0b00603404c030000081c100808610900300e8441e901da4061600f02d00600c10744558402c0000100e01c00e0500c0c0c1002420105e4a0364501d01c1440324500000305085072541d500300301e40810001e1414088690200503400c8256004c00d401d064980c8400c1d1450f5555000500307a0b07a00c211001c500300d50620f0030100f000301000301000682407030560010324100380000596400003180c5003540160359540c40c05c0000d02a0210910312a81c000b20b40c4004007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 702612985 1250 702611735 702611737
    0xd24020c0f0a020301060e1b0d020f07050a17131a0f07080415090f03060e0f1f15030f0834020f0d0c0911041d0106080a05070509130906090305 63
    0x1a000310002e02c0400e481d080c420140c4081914002c3c803a414894100d03c08003040d401808000790127460042c280076144120340d4113030f88103d20440300c940002c1c0d800d004100c00f1140d4846d01181060641d07081c2442000001000f0328a0702840500f1194018000251404582141c2c4901d00800e8602d8031040c03075250018054006004024070740e000c0d00101d0341c001e4401c4000504036181c050303144400c10b18507201d54004007901d1000c2103141c021500360801c0b2035000c01096040d61045d400254010402d40f01910445852080d000703c0180b1155041001c80c410248608265030040d09040c0c0d10800b4a03446aa0071642d4001e9492110411004894400114000c62003144c002e0381c0440700c02500108006026012041c014620300d150802400148490352142d21f00400700403906142c02c0c0c0300c0d0784540701c002d82c15203a031200200000c010711003a94040d0f4801c0c1c000074180350600203820300c088050468010070b07021600401013890f51255001e126000456400d070084010444400c0d203007802409 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 702614235 1250 702612985 702613003
    0xf1902130e16020307170c210a1d13110d05100303030b1804030f02030d09080a02010b1801060804030c0b070207061d030c060309160b0d0b0d24020c0f 66
    0x14451160384850002c81c0040115406990b00551060900402ca010000660026844015a48605d405401c2440d008506a00240184015450300c4001e42840146183d641c00b05402d00900100c030b80204907101c0c101c1c00c507515000014046595185603a03404554040d00203101071103810407040c4494030340540c0c0c201d070540e802641c06000000c0c2541c24400001303036000000406400100008021900c200401c12503443e091060724076240b242005a800d1f40c3e0405829a0b40041c00140f104540350248240c42e0725400550f00302191491191100c002c6490510590043c44102000101010700ca2511910f1441c0e03c940c926891b0304090b40300030358666180c01400003094107125428445031041c0403854031108010b004012000c2c0003c140680c42d00060800c15441c070030005c250f5900c001d4018854050201c40410a40b00e075100c0e000b02061310300041202e405000700303940e608003040508408002c403510000180c141c010748207140300024890030105050a000702d0b0031501d220030001c41c0c2404 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 702615485 1250 702614235 702614251
    0x1e1912050c07090213120f0209070207080d09150804020907050f070c030602130b041202060913052805070905040207021f2606030c0108040f05060103080c01050f0f1902130e 76
    0x2403280c0b038030b141070404501c1d201b000d4084100700f4680300061074001d010703540c420b4180c4141c408096803000040e240c05c00e00b01b00c050114000440902500c4140d41107580988079602c0c010900d81000e4011031100d100140c000d004011000400200c0445844211008503130722072b468143e0741e40c2d40d0501e00029045843c050103605160000016047c512034195400e50f0030b5004160340506103942007103160307441448c5030343c0c001500e0103040401800610945210394640e102400c01e01506800d015105100c9001a107503491410091000d410352081c07078202954030075100140d603225240006907006803001d50700c02110189200b070316400c030307072084131382003a00080e00c3c01c01540c14500c5c14003142c0600454038160142e21003900c2c00c00035031140004a0b00a13008044100c41200952910f03420440242c105440e446000140507a82c50030921880764008100300e002000350500b00581e410f034940242c51114103200c41a030b019040c80090b81141d410003800081d81c1d0f1050f0342c9100b02d822089040b18802 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 702616735 1250 702615485 702615517
    0xc0303050403051b13020c070b0408150906270a020409030e2b03050a0c05073c060f0207090f0c0e0102071a0706110c1e1912050c070902 60
    0x130b95904400c1020050950050103441e00802c820040b00007908006030079041c81c4203081c0002003000603400108083c040030070250907007c40f590004440b07900c018208400341c4e4007210800c058810058030080142086c02d004032880344200e002d4605d040c0ca44480a98064501885c3c2c1d000c0580103210a10035081c207482c41550140f00c00b552401702c2030000b0140100b002c0c010740003000a071103100104084a4a400c01c506d500e2845e45401385800e1035600842c005001052136a000c11680b680000d8a10f03c1501664159100403e008414140103105500c1400641e800c205c032828003e00540c1d001d400048010001a025a030005001d040040354090100b00c1501d00d42c4aa948003144040594050f00c845902d00149100c1107101a400010266152a924040120b0340c1c8484002400e072519103200400100c4a42045604a54007600703a41c100f95024551031808000910344030840d0f682c1000310700d01a0350f840700090b1114405c914200806008000000c1030001d095409030580c220078031200 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 702617985 1250 702616735 702616753
    0x1050403020904062c24090307020f0102100f06030c06051201120f060e0a230d0c0f022101060b0f0d090321090203010e0a020d080a0c0c030305040305 66
    0x1510244254080690009076010005010403025080142c4110001006560300303401c11040c1d2030502c0e0721030441c0d25541c0007607841001010311100c043e803003140001d80d00f07021420001c1c240d0745d8074450102e000740074906e0b0030112001d5a00a101181c44c04d00418400e226030034041c007100b0000d20090201b140d110035881c0011640b188100141e68071018280c00810303040c0d00b011520025022801c1049a68146200f58040010000e004910010703a414000b003650020781e16149540c0c100c006920078080303007499403c0c01c0038140003400a104103d541894100344109040c411054020981e0283d00240c803030840000080303001c034030f00800c00c1582008010840c0c4a004c24003c611030303541403030503000051040341c04540503540924150340c4281002c074520302d14500e40c0b603146c10424078040e4800381d440b001c820a509080c002c0c0281c000030240a40399010345070703000404080321000081c005100c085022034009000e16020b00206810007903265583c0d41e2450001d20a50160100311810b0161400c2 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 702619235 1250 702617985 702617987
    0x10e0f120f0f010908030708101d0106110f0c010c020117010b28020a11030a060c02010e0d0c081b101b030f090b0a110409060305030a27120804210203010b01 69
    0x9000c0036551101e5017501e15200c01c42e08880d402005020583d11002d00350000032100f00f00c82c54082050694468844a50b24008021f005901c0ba14400126a0040c800c140180c1d04c01082416208100342011640c0c6452800101e400704214180d03900303030101c01000403070341c1702000b00605403401c446824420030440c10580c400403825081010000b40c0d01003160200060713040c02f000310100c000602180d03404403440d150001503901003981040940d44d03c40502075010814402e0f0112580c00f4148000e103124195140c020302c0c414402e0b01c0b141078010905104080c1c405024400582e10020001e022240080701621003081c0c4044c4020b011901d0f00c80d10901c1354500707004007024103070040324024486d51044000b102610b8a0b5403001e03a105003c20000c40c2d141c81905c65030010314050f000440c4c036420b40c02000f600b40c508180d1441141500180344a852035020324210b0142c654968803032040404d90720345884070f0300a60300301680400183c9180d4a00380f55889040c49a075008030000d1000c4490800 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 702620485 1250 702619235 702619241
    0x50f0712080405040902060918060a080109080f2206050a17010e060f011206060804050105011a070f0201021914120a1d031c0507060507030c0e010e0f120f0f01 70
    0x300007055004180310802c400e1400b039001050081c0054005032030030f030203c40001c0403600f03100a209580700c040c1d42400a503050042d00d40003d80242c3c0020007101d00036884810103401200c100754142c2000042c513840c0b60450101d1200a034010050b680d00e405e80395030000c0c0c0150400f50206000a8002d88050800c003520080681202c500c00340000003501c0b4042401451071b09500c0c0181480080400d0f01032a812038814000201055901e400883c200741c64450f00351141039100c0050b0140025049030011700813001c5a4a0591000e580c40307042c902480142c0c201410151007180c2c2c16030342c10041c028070000348804400342000400342e80320003041440118450081001501c000b0705125003a455045000c1c1c0256185140141103651861185a40e80791a0402c05148400944080f0b118400c101d80c0b8020160008200d04081c0645180c2640081198040c03401c2c1030704001d02c120207003045032100f40585080c080043d003050248401001c10640c2c2d1150180d06074814070a59006480d00b00040c4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 702621735 1250 702620485 702620519
    0xd050c100207240b060a020a031b0b130c0902030c250c120c05040501090e0d0c0503092b23031206060f1c23090d080a1503050f07 57
    0x4280929800450003c00c040c1d000c9102c454a6000c2d510b45040000f40d031840050036000c90146e004102d02640b502c0c000300706940d031440e41945801001900d0340082d10f078071406540240c40e024036038512552410001c03405046540040b10451000061141000c1981e00408084040c0c1d4050744080030840e000c2110a00400d40c088c01ca0b4206003000c0c4103042c1383c5452464407a001d000310801080c0c4500004e8100c40082c0d20098606076580380207026a030040c494415040103900700182204165100c00d0341ba440b8100b10f482c400c3c0781800e4545100400b01c0100752610201c100344910844903464542d0704400100c10780225000317803110301c18400d8000000c40d072000e0074459040741070752900414040503070403070040f42101c0304040c44107404845c078150207501021109140030664128054007481c000241e0401c0c09440c9481c101040ba89020000d021440c0e600d4a14140c201982e482c805800141b8112924405180d94a80000180400002d000441903041415106007550300c15103070740d005500e0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 702622985 1250 702621735 702621743
    0x303040302060f06060706020c03032703030a1e09050610150e0d02010306031a190e1f240e090607090e040c0e0109090b0c0f07230d050c100207 63
    0x102e0020f507551035074200381600000c000c1c01050038842c0640c1c900047ea005210448107035407021041000c43d8050305441c1e02e074010750982001035a0180f817005c5440303120090040308120f40380d1160381241d41400c50a034070b048034152030803c0095501d107401034907003030196051101d072842d000c40402c0450003c0103080e0500155100e00e2141c0d800c000a1120f03a018011060703050555485000011900d840c5619400e81046000014640381181580c1600c0080c410500c204500e407802c80c0c0ad03821000502900702c0c1e483c0c1641c000c0110031118043d005023102c400120a40c2c1014400030914210003030141c01620045420581e01c0e640e940c241c07a5849c4412070b0340343c0001e10701e107030b00300440d881907018240c2040c0103c45144003540c4406640d0380c0f156085c0c1c07104c04c255981d0310548042c400c4c1002c0082e084444034003c54906452400a420a400390405c007601c85801086180440c40c162550110848403038030644400100c44103024000d6000204448020300034611017092604807442110f10003a80 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 702624235 1250 702622985 702622993
    0x5070c06050f0610140f040f06090608040803060105030a1116020a170a031d09150f01021519020c010509070815061305180f100b0405010308040302090702100504230303040302 77
    0x45540200c800000c045c1c1c022000c4441000b0124811100c0700c0140058a01031340484400c0345003800041030f007a1140c1c003102c01c000c1003c1c180700000e42c1010803250825424a80a5104d89803401440d000708120303805000800c10024500c80307140d80c1c624452800a0017200d1603201fa5030f9500a60603e07002d00413a0240903002010200000b034010380b0400400728a40042603a50300100e80031400f020f809940038031407c100d030102c002c060300e0510b1449003410020701c040d0080b02208080c6456440010301560428040c10542c210101455130580d840d40c1c0e0407600901c4541000b0035401d8580903030313005550132400b64007500d840c603c01010215000e05805444105c5a030510301d40c40300100f1000e44042c0390f481684142c01c501640c200841001d1101c81000342400313074962035401080303403601c00100b8003443c100001003000c5400355066a0440b60162011030007a581e0305ea003203061090700c040a402642c40d11007800148007954600c2050030030b4464412040c105030320507044e943d020442e030040050380 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 702625485 1250 702624235 702624259
    0x1005090c070206070c08010504150608010209090a0e1005040803040606120510150e0f16030c0c14031e0703090608040b06010e030c12030c01061403100b060d05070c06050f06 76
    0x108900100340d15070007145c0c821800f90311540300c00e007903171401c1c3c0d81501e409401c480c602e181503401b03110341390041900030001c40c0b80100711404101c0701c0342e00a082040180d514240d030f9009610911031070302d0898080d1000c2102c3d1030289080c888942042d5002c2d1001c42c070382080401c3c03000000703519412130342d0000300524000f01010020001342000c4220510160b4803c0d0700014042e504440e4a4016040311549107a140740c03c002c001101022144070a00b0542070900d040e001507040482e580c40030717130001c0c0d105800d032000c4040146584111426540010b050302001c0c60586000d001074040e0a2099461801d0142d036194206c1d80d6010a0350040e100f0010300011916941c018098402407002c081d0507039504003105d41c002101d503400f100140c00705810002e8460074800e401c0c440e48002e800e075902c40d03070013200940c00441d42e02c031840f441141c84565110130040840c0d45860640d801c80c3c44240040c0807519241034020142c006540c000c80b6081c0c24034022442100d05081003502c900c901400d0540c10382 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 702626735 1250 702625485 702625489
    0x2031c0209130903030c030f0b01090504150b030702160f030b0f060a170d320a12020a03140a0506060a0318060608070503060c04080c130b0909061005090c0702 70
    0x140c85884156400144078219075040c0050f4054646140c2c0607440002c2d041d4a014005020707128041d80e00307841c1701d2400c42d01500c141c0c0c20421080907550141c80018581e441c01e5001018095641c0208901680200422221a41c0015401c47c044101602d80503042d5444490100d02052030100074411401c1d000080c0000d203030100c0c5d00f54041001800195000d580d226a003101c2210190350991640186141c1041d00d0f40000700040c6694840c0800c103003c0030b6000c4407107461030701001070354295140050b00c6103890344100c603026142d01109204640c0c03604010005001041d80c810240f0840c3d0030f1000080008100b4810103100340f0015082c0c62615400b146c0c118001c18100724102c01d28500585d840c00440c03624400c2d01c02400155005081e01800c0000f0507140c80c500070409140654104405d002001d8041600824030300f0540d940c0480c0c0088244080260841002041d0000400410040030050000b0400d0180a80c682e8a800c02d648407028041001c0080701c1e80034244104200010040c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 702627985 1250 702626735 702626737
    0xd05190c0503070b0106030b0f03240702160e0f06041b08130c030f0b0903131a0423040506030a020d230f01020706050c18130f060b03090d02031c02 65
    0x85101c0c10035680b4100c820b60b15000002c0342a00940b0000c0d54541180c51103042800351503503c3c0074220014201d6440e2458a0207000c1c2c0c00d0301464030032641610115881500811011401c030403210040c1c40550346819a0791009942200c8490202d00308101140e441c0c1004c2c4107140740203541003003441c0c500d00b8a032001e8950503006400c0c899400d129a0406011502001c007183c003a500c1a690b0f01070340000b50426010842021b80111030380e400800a8003070010002d0400701c1144d10f00e9100c403e81c0000808009643d008542c803e0540f103000b0340c0d41c1d440110503803070016034940f03089900708aa910740400381035440c5141080250416078501480010500032481c1e5580982c581088001000e10000b0483c1001ca03034840051080e90080761920801240b401525880189880c4c0d0609000d000800d500380d458001e20040d0051070070324080f400045568110307665203030004809002040e521400c683d41580f00f00c1c0e4450142c002c1000b09000e2a20120031035030070400741c54858540c0888014901e0007 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 702629235 1250 702627985 702628007
    0x2090103060e060913110d050a12050f160309051002010209190f0b0c010e0703050303011a03040206090904141c0e04060e1909050607030504060f09032c120f0d0519 72
    0x1805106c0c1000609583c0c5d4442880794051040c4090081d01603d440c00901c07200b84072150105011003840301c014001d180400340c1d40508200140380d030719045039040c240ca01030880c1c0c000d9070f040040c420080440c59015001010000b4080d5004280b6082080d074141c031284a42c000c021034880f110508014601000d0301900049a01c1000000c0031418a5201464414141c1c021206030f00b011004110340646074a050401698448001e80b661515900003500e03171141c402c6c01c0b840f50fa10400030406010b02450001c00f13540a100c00c0f2207554141d0300305004240480714079000000c0783c0601c0c560385401c1030301522040304c820000550303480d2260444041c200d5601c040c030f0382582d0307926084000030801c10001da41c003c0226440028260419003000c0c81a6904201801200c9042105450010344d1106040001681920702c0003d01071005d2103941518134441e8400d81d00c001d22602146000070702240d40c14500014000700e401c0480c0c0e58109a46500803252a141a4000e407603291584074020382e24004 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 702630485 1250 702629235 702629243
    0x726031f031104020d181407060c08070209070c1b170a0b2d070923011707140c0105150a060c030f03110d051b0906040306020918070302090103060e060913 68
    0x80c101307600b1381481c0040c041ba180103442032400521044000201800410b0150105140c0304240d4030040e151000b052042020080c0074810f1072000407165481903400d20060342d4401c00c01c4568510030044000744c078220703010744c803c034008200d0310039400c54000403840b41c42580900050f4041d6180500d04145410444486400400d40070040421141060515119600d940c0320302c101035040400f480d0960003240225200070211901091450380c005203180880140880d0b094816610404101d82d1003e49460304d010b0f04070701007544c0c0740030001900207034030814101d16040101c03000c2e102000000c841078407406012501030411100400d1041862542c010068103000c151142c0c1c0c01403650b000e500c100f41c80d600907540c2c1c20134000000f40b0a1600e00150400710421402c156034440040d01034441d6107c020021680043c1c0c0302c50320b40b6840300204440c02c143c4043c4a0610f48020064040d5011611003400645411800300b40102c2d0400e549008203001740100c8400c1d0782c5c9411801d404025500152 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 702631735 1250 702630485 702630491
    0x20d121a09040302060103030305101d090c0d03020f120f040314030708070f02181e060409020303041503150308071119060c020117060906060726031f031104020d 71
    0x203606a11a100881d00480c841c1c0d000300a95891410001c049410241201001d40704242d81000000d9003250140d041e40803010000d580384d00d98080e0070749000e01095056030040400e02c810406e15801040145070f03010720000b581d041038403c074074851175407280e02403000001201780000d10129550105940c2000c003050100c034980811500c1d1644150403e150407600480e11810070300850600f16109070314100583da800c0c10a04054442c00c4000300f07045510f2a80b0313803203000024200c1d900c6801090401d50003905480d5516140c20b0700c0c2e080200311b02c0044021a0802d10b5502ca500f00a03060b541c2100c0d000500641000e00642d07a40c0240702004424590001c06291101c02c10b000740b1010400030440c0da10345031810745482c40003600c0d1000300c91008080f2112042000003e880e06150030340d0100c822074a465035070340949000340f880c444c05410502140c2c0396282040b0441e040300b005500944440c18030f00440c6140038507111564a890100503c03120280400307030f4507824036030042c0c41e045060340008 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 702632985 1250 702631735 702631781
    0x9060c08040e04060b010f030b1f02120f130609080307080d0b10020c100e03191704180608061506160819091703030c0703110102030a060e0601020d12 66
    0x10542d4141c0e0165207403a13541007486181d40c5c128a0600d0581c400c0c1c103042c406c6084440025064860820744044a080002d0292003240d00c20701a6000c140c83d4000f10799250501480302c07074255017080c2a90049400f03480741c00300303a00c0d028440c1c400444040b24025440c050040c1d0702c00b00c09400049050600a031501c20120070350355194075042c5802000e41c014809003183c0c004000701918441422402c1c000481c0342e107072440d2804205187d603024052201d0040c44164a00340b5054201c61061181c3c0b0b48001c81c02007044040641e004000261100c011b003d107e4a41c2c051580360401590001c0c004034620039080c102c4e0034410003404444000b803040f480c85111a440d407505581c40480e0041e1071201ca070b81c14000894110005030058071003205140078040d160201036a5a01c0050b001000408000c111002014072442e128038924040d0f900179500ea05107102002e010701351a01401c0207000ba80400103100754400142d4036145c80c0c003595201c00c03000450311900c000f405201c00780c00303400d0844108 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 702634235 1250 702632985 702632999
    0x5092d0934020c064305011509180206161203060e16021b01050405030729070c03140102090a1401140901050d1107060c180602010605210f060a02040f0f050109060c0804 74
    0x4003070614011b100115000c40c44480140303001010b9000800b4481c900701406001c2200d4114482c903c540c1614899074689410110f031072040441c03100140800020b41d0444541a80750300110220303032540c2440b00d03007900e035040c0c0054180b0b03814100b4001648141040200d40340504400c60881c0010304102e80743c60b458a0209007032110310f4100d20101c00d0a4001702502a214514040c191400c0108039424400c1a6840d4440702d200c0344006031080410200d000141c10082d0b048801000008054011750761391081900302c2510a81c108501156100120495111204080b554100c5050759018070740b1650310083d0300103009152813000740350340510000000030718a10440100d040b81e07841e6031040204035044505000100e030019411641003035410440d54070b81329081d19001000c03440360412144400f2080307240511380c40d44c2c03200c18891402030151000c081e50041059074240184040c400340c03208540303802802684a45400540f81007020028180719850203100e4521550005227031998440e0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 702635485 1250 702634235 702634357
    0xf1203040902041404020a0e01080c0415081501082226131401090303030b06130e0a0605041e05091c05092d0934020c06 53
    0x1c15a151640001c050201d40710700e0a500000d844221402e620b0b210880300014059809515002c2c141f000d600040340d81c400c21242694090310442e150780e0f44504c0c0c000c00080800b441680c0403184082d0610351a10554481c8020f40e00c1408840368804030068411151440c0c0224048151400d4841070810039400b204d80e04442e59503440c200c060740e240c08180c104064074000700c3e8801d40ea4880d5218680d080c03641c1100001003141d4041c10001660415000422079a1040180c40e80318400d02d5600804c1c081a041c600d103001d032a103a8810030000c1d0321340d41400211540300000c80b82d2146d035900034007045145e98009980c485551016a50145144d40781c0740040701142c1c1e0b100000c240301041e42081405c1001070b61962117043c9201114040c2d550001076903510039501e91500520600001686a182c21508505120300e030340f800d42041c3c54552400301c40305440809000060203102d803907550b00c4ca0604181c1e4041e9000c88c0c0340c0c603d83d4101d272088800980503000e4003d5581240640840460b52000c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 702636735 1250 702635485 702635489
    0xd02010f0c020d0c030b010609030309060806040e0a0c0e091207021c050f0a0201080708010605091306150305010911040503060a0203040f08031f0501020f33090706030506030a0b060f120304 83
    0x180000340c416081d441c10071b10040d0160010700c1042a0300c5001c20100380c2c0400c8000442c7d40174104111540c403003601190190041000210f2148140201d030010405010f01401c1125240c0b04001c0c1c498868034140d548800c0c0501e00e40b00d4545080c40560050701e0310b245680144401ca145000c00c610b02d95880300d041c10096000700b0200d4102c80000303800d550704202070b035034480c0c1d40e441c1401040d03040c1035000d01a405821400e40c06a0442c0c407141c064200e00e5800203000d02680030400701904608500180641424003038801c0040c10712450041c0520001d0075501602c00060140074296580c1c1510360003504010010b9502c281145440c00105019078000d42c02403101d01c0d021059a1075500c0117548902082e44460304550142e050010000400300c4c4400040307082c010b036282012a5101580c0c080e0619543d0f110400280340305002600d0000191802214540e40f818042c555a020030151500021540a06100710000025405151200c00d0102681d00140b840010301e002c5000546036401c55 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 702637985 1250 702636735 702636743
    0x20a0c11061e07031b0b01060e030f0106080f101103010b0f04090c03020304030806150a05180406170607140f03060d061a03010e0708150606040312020307110f0d02010f0c020d 77
    0x1480f03000f0306900c003803083d0b01d0b112121100308860920b0f0780c5500380b0606c14406da004020421141c215a5601840a40b0141c5000d0000b4840e8a842d40905600c5054000440d01c8034402c1030030381e03505180503001c0d9100044540521a046070b10300070b20250994442c079258104a6010040442c0e50101c510448241c03040700e90340141c40303103000d140242c01508080d14052040c6605088100301554201c11511240c2552611a44401480d0211102c03044001c50715640541800300c0407903240c260540f4110030480136002c0361b100383c42e80b11007594440700b43c1040c0362401e4001c00090480b40b99800c000e54101c6c102a02882c84d2440343d444140464000802c0300c406600402d40d02410b5140034000c401100349914098880c2e6441c1842465503951110202d008000807440010030035500c0c5030965000310740140000c064114078460003134582e8440d040c102c400c2c90b000c3c680160036003410402c80074002c0c40a09100040360240d0015913140704c0e801031020801004902039001a00d51502e244440351107 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 702639235 1250 702637985 702637987
    0x26070306021234050a0e21010c0503010b04051e030d030f06050a0e040b09010603021519050a1b0219030b0f090303070503150a0b0a08090d03020a0c11061e 68
    0x10481d0640030b110f035203200c0300103020a11080d0f5101045404008120519040c007903614110304c4002c0d240e4402c00000c03181c0c0000702240344400120240b4964051003203502c000c22072001001c2050b05c5a000030300521480010900091003241050400c040130004c0030305400000c604100000fa1508401c2403c1e800000c1c1c1340c500703100d513500b041c3c014440509005c403840248035080518851070000c00400c09080071482d48042800b20300c081d44040b010319000ba21044a041c5071802c3c1030b0103640203370a000307000030100e518400c84620601c00e40341c4141035569100d507074004006210112200c0c88500b0790744254048001008038076071901c1000114826a118007944c40c1072000204000002440c45146802c10420172107841d0b0320808880d0b203c4811842040d210402c0c0000c1001411540c0100060b668001070051440383c1208500303100d44407038000c5071074021135000b08800f64025241c0d01801304510a41c2d030740001e514170040c1d5625410180c4564201aa000049444982140600040b6a070 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 702640485 1250 702639235 702639241
    0x150e1b1306260d02190213141e0f01090507140d0c02070911031810050a091101091a09060f1201150503010b040b0c19140d0306260703060212 62
    0xb80e200002c0d10700c0240c0800781c00e81c1d107035100019450300915141c2c0300b0039200350803c00c811580c64006510050989500030052101010011040d00300166040007d61f51010301d10f0328081c1780c03108054072078074034204005100d9103000c401c03c01801c400b60843d000d00008001d05222482c003100500360380d0b49000c402040c0181c0071030340a42800c005802c02d4021714240191056007458030801c03079401050781d4400300d05421214081500708401e101c5049422800c082c2844030039402608440185805440c4001040505600554180d4210310070101c040a44050729109444402c0180c00d0700071010b8101d503d0071030400404469a480040c021018103900c9006012100c1e1061500380d039034485040c194655410841242e81a000718400e001881030000f8059006100502400c4011040303a040000e86d40d1440c40c0c900108003112880f0140340c440c0b0401038000310701c81d0003070308200c0d078a514448a002d886030b4151a4504443c18141149120b842800000900c0c80d10013040c2c14800c03011031401d181 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 702641735 1250 702640485 702640529
    0x30b1f0801090f0b03071205101a040e0303091203060d2109150c020d02040605041517011125050703080901080601030c08060915120109150e1b1306 65
    0x200220f0003640c42c00e25200450a0341c0d1030005442c030a0300c3d02d1220f2525000c1c841e140980c585000000721441c01402c100700100d240511001c2524204800c45041c8000401030000a95900040303440512652000700c614182507600002160070480107000064905c10984031070320036030303000b00204000910240c0d11041a1754408070100180040d0124a0300d00c09059400800d0004850380c042e104041e0000e2030300c1150b441d540103000034680038209000c08200c200031402035041900c14000803007a00400440040010300c9041c000518082009080c26194100e00504003544200c1100065880610300045a41007004c00021446158455655204d20000400740c040281480b81817505041c3c8010059030020780c05507108400762110300f165903414141110102e54103143d25000700d545916404810010b4114a810038000e00700030920b51000c140c0c0f0012100100c00c1c03203005400548214108041900b10860503100041c903040d42c3c0e11150f280001100d0380e550001c45690809240b03600c001c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 702642985 1250 702641735 702641741
    0x206040c1401050a05030720030901030e210c0c03120409060b0301052112130603180c0302090406090813080d1701090903090f03032109030c03030b1f080109 69
    0xa001d4038002070020401d0480040c00600800c41c129040c09004000608440e22450b04044c401c0803e04044503201000c0c05d20903100d910030103a907400641441d03032842d101280081c1c01450440c441404500c401c021071010002034020740f4410741c082c01845030a5101c0d0307a040004036000340ca0140005c1e40d039817a2070280300c03c403040781c0c1c04096104000d0004100503981c05980000080e401690310666002038100a8280400c41d50011490240070401c3d00d044003500ba420026145c250f1410459040c0f041000b81183d07004040c0208491b194034400e10040c2040803102d41c0181c40f500011400d00ba0503030791070845400139080142030040519040001e18007c02421811000034180b98031828098007a0000f0343e00705001e0b01c0c0303510780c03100349080130584038510050007000b000700034004550303d0b03180040c0350b06102c0f01d68001a44c0100a100d41d110302c40e2140c180c50590503100c0d81e040c1e61486e0b40950190141c0e09203141e10140443d454181944005802d172420b00e411798900d0800c0d07040524960071 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 702644235 1250 702642985 702642989
    0x6050306091803030c30240d0206070f080c0307061802090f060d02210f030408070e07030e0d0c14010b0d02150c0d080114010311030601111603030206040c 68
    0x3404842c1c00040001c980403084036004042c1c0e852155481c000d02815070413405d48690740c0602d100410000a003a404442825030107510714840075103180c3c003001000e50b6030602200c05240d101401d031090100529007640100406032054403103008142a54480c403c3d59002000700f0312594100041074001c0212a1240400303829200400c00e80919041d00860103400c1e000300f0280034039005a010440030f82c1d410851003c10795009154003080310000c043d101442104140e4a42d01d0321035000403100b91180030003914182d502400c01021400d140150304400e40e40041c000d0402e059490080c5210020103211424440721a62a40c0700b8a071054a4001000c0034903040000850345440240d04a41d5101d101071440181c0480e840c078410981110290b17800c1c401c0d6030300e540192192088003032003680c003c68994100c803030003030b0b80f01d01d1961014015811f07141c800f100f048074040c00308000f401d0381d80070f0100140311006c0030381200c030078404d00300d144a40401c464000f90f0269000c0010001000580310807000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 702645485 1250 702644235 702644251
    0x2010507030c0c23011e050f1b090f06041725050105031806090f0c0d0b06040c0309021207030c05031204030b0405030c010501030c1518060c06090b010605030609 71
    0x8210444030600500809034020020109080b84c402e4030485016551001c9000c54404003c0000c1c414103c50700c00d18115810489010b20700b072400051001e00d008107528411010442c8510039130440f0001001180e020020540d8496008804d100b4140c4407840a040581403c040001006d42000090b030310f40f40c2e400144541a0f0241040c0004000c1024058002c40d802800c0c0703507440e511042301c10310b03035000b070048030708050311504003006104040041e00a400c0070b008416900200c41020521400308094100600712085400c04901e142c1001c2c0c1c804110440203250000303c040540e4005001000c030918015000da001c0601841803041c1c03210f000006100c111b008011001d001d02820070940958400985943c0c1d044000805103c014422589145a0b05000300129a101d18103600390707110754003d900c0c21030144080124442c1c040c5403d800c0b0b1400050500e0318203444c09008462081c07075440229025500c4480c5040010040b0301240d02a00790b546401d92207240c2042880f80940c40204400307 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 702646735 1250 702645485 702645491
    0x100e070c050c041b0309061119231209251403070302090112140312070f0203070b0f070507050312060f011403010b160f03030b041b02030f0711031009030201050703 72
    0x50413500001c03a00a150032114203011800100505185004003002c21301000300c1040000c01519404401c0703d00200e820090311500086403030001070303145108003042405032480d400c03c0485c01d002c40d55410f8aa02400c0f010407100500740c9001516a14200202000002c4035095800c2c4401c0c3c04000890030031b40c406a005203d09840c4d6000264400411320445800d849000c841c80140000c540c013407075a140400c81102d03984c21005c61004011002154410001902010740c0d402c01440030040b101456000b82c58440e290316000f04003446241d010b40707030700240a02003018400144d000d20190134401e24450418007030345021001e103e040711100b06280c5c10440e164442c096280417801c10382e8159601c40750340c0c030344848002046490b225403000740982010711501201c0101941a0811401903070181c40038040a412544c079000300d800110503043c0903070428010024244000b10150132010700407848a030000706c07584003080c2030100d00c0080300c400c035032541812410300d0380900a254025840745010 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 702647985 1250 702646735 702646751
    0x100b0907020316061107081b0115050306060433050f010314070f021608030702180c1e0702040c120510120312060513020c01110c06040803100e070c050c04 68
    0x90f800d26004500020304031582c03071098191140b0444242c4e401b081c1c0c410309403980d0310313004e5048040c80102860307001850760130903035081c0011151a081c902241c8000d8002d01060301e4900803c00900030440c440601d07600308402060303503040d1038403416001524209018070010b0505080c48512900340c20180c0c145420708203200c20542501c28103540c414041e24140c40c440908400c100e04010503801e103940010301c018004035034814044000c140c05842140d44401d007d0202514414404085a81803d0071006210b140d0328060801f80041c960300103900350501d0001603034001002c27140d902041c2400500348a450702d044440ca803140301c0e0400003041e1800441d40c07070305000c06442510001e00a0403c4010b080039207101d0303007503001140a4a4014a030a01041600031540029006064240d0341c540c2004405003c86051a0890301e012107198060072040c4e81d503490f03c440d20340c800b8040705000c10305901e000410b00b012080b014000d0341039985201c6800040d04046103016603004040388075602c1c256107 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 702649235 1250 702647985 702648007
    0x121e09140f07151704060b030d030b0604150903150915020301051e1206090c1903022b080c010b010e10080708071404032105130306110903100b09070203 67
    0xb2050841d1501c440858007500b480c0c0e000c0351159020400544075088800500040022a401500341003a00740d0440e042c807080d00200310b042d10200c188481d08000100b005014014099050079010481360602c110055501c0d6145010740b804c80d0400c1d9503841d81d4464a204004c120800414011202c0034103600b10f506010000720300d4100c000c0e620400e410803508030034080d1109064016580400b20640e0f2080c60524011611510000840c2c0e20508980360b1070810020002400b0094903000340092035034200c907001c00603900789648140014040c207980740100064000e03000b0840c4201c0d0f40000b0030b00b60305040002d0641001d40b4802d6118500d00d03040d01c04026840f00c400d82c4d1100c091b15040d82d094540c110705442c04802c5807a100d010800c00100803082c85500e0101c0745140d02c01c10418a0640c041d031178101d0325801141441c50089034212000c10100300300c0d820001c5001c0312564010310700301c00ca100181ca810040107916008079200d0305602c50618060355a40c0c1d0202c0c1500244d480d04e110054 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 702650485 1250 702649235 702649243
    0x307030506010c11240712090801110306040f060b180f0901030f060507110a08040e070302030919031205130c0b041401110c150706200a121e09140f 65
    0x1104c14003035100f22440341c0a02c842540c1488501d6a00e10034117030740310058200b80211180ca503c1480200d0345039280003843d58014406c202900e98100c0c4068110744400c410000a41140442d00c0101c0d510b600d004145000044020100e505116034982542c00341c010610200c0c800180d40103119207210401007021925030542c2e078010303d50000d0002543e6880d441c06035200c1c001c0700401d00251140108260030800400004d00640d00440302404c003a954442089040e48000c40d21036615802000000540780d004440020045209041060b16000350a8a0104a0313401b19010340207992000c011600340500d0041c2d039400382c9a0340c0d100a1030036050030005525540303251041410001c0e2081218864a0305220046100000038000441c11542001481c4160802d98003079404070f00c1c00e8101c5240007030101054194140c0351506505010b4002400e51f0355a05070f000401b01daa8954141494642d0889001c4444244110002491511a050094010100704118040f03540414211146800002 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 702651735 1250 702650485 702650513
    0x71e060f081e0a020703020f070f0e09070e0a020306040b190b0c10020705010902030609010603030c060207030513080102040915030f020913080304050105010501170f070503150d06020307030506010c 87
    0x4203100c005600da0900340300ea404140b5803000d500d5841c0340180714a10030b05400412105010303500b1907110226030070405807150003500ca45c241c1408940701c00c00c00c060054100907440710300b800940e4040d5654900b40200c0d200c045a002809990003c2000040d02d4144215400020140c070825800c076440c040002c0358000500139400103010225404a80d0071003088085180030103841c1c19501c0d2081840d05601900707003114124800e001c1c0e80c0000e205001c05204007030840e90559603055480803075407200c038001d40c441075060f000c0210802080900c0b03070742821480014601c680006070368515003140308080700e901221603110000251810008201c44544502d000d0350100c5201e10075803079030450f00903103a020150080078208044108018840d0640c0024129802031b00c40003041805221848007040c0211003441c840c451003000b2030784c1c00344030344003031a80000d55401d0320800c80404000180300d000e07050021118203400004000d4120f62500445411030000e090110420005036182400003006e8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 702652985 1250 702651735 702651737
    0x50714070b27013210060c020f0d11121614030703120c060609050105060d0c0e060705012415030e0c09010b0c07050328020607050102040602071e060f 66
    0x1c1d80200034000080d40180c02d040804000b04580c5110718454001c401c58800c68540e6040c000400d005122a1011000e10034800851000c1c1c0c0641080c405841c0300310342d140240c2c2c00200b4000714400b01c0d119044980035072401840c5203080352464004014040010300b01103112070b04001c0740802c4100c00c40401c01c090302c5808081d05401c3c02a031012928051041c1d01c0a00300786c7c070886429920700e07041800c1c0d080c02802750300240032040d19070903054280e4a00380315050b006003007040000300044140d030104405034024a0440c070f007035035204001280c0e0b40010740280e5603650345001c0106071030112000265100b220404414203189070030781e09600202001031300000e05071250140c0145c400288522284003100800c01c4141d942c6421561015811400c104c6200744548407011486240c0080d09424030204107100083d5201c5c41c000c2c29042e450b40c4001240c0101d810311200740003c500307001400c00343c036a07940107160092401e0825040041c0e4050b40301a1417030402e000340155075100c070b41c60b04c1584032 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 702654235 1250 702652985 702653011
    0xc040503120304050f0d080901060504090f02130e120d06090e060106080c090a062a0809060c01020408060f07173304110c010f020c03070b0601020f01020c01050714070b 74
    0xc50074180d08003003e0806005a5014906c500c43c450b81d0080c0d64107026103200e1000300503d98640041c001164120103010380201c1c0f01e074444070014984903264404101100741d01181004001442c14a48000e1b60a0060094000b1035098545909481000d0061240701018070218051410468407004107000344401c00083d4400100d0103c0c00004607014100050010388071580c0e2031000401041001050305081e8000d90022801c0f014110b03550205150407841a40c0749c2440c2d0820007096901c492841078440d502840009040358062004ea88207140c43d2000c0c06c0d481c80c003101700130101451141011000510101030205180307904104d01c04640040041921a09442000403050803203400e11a50160410610301e01341d003184400b42125244240c020302c0504032040805059000b0303034501d00c169a1080c404600801c00d03403201641c0150060040c0da00c82ea0282d40c02e5426a4001101c101841e0b44540a0060241d401040344507840020704100d81040c1c030b10350302c100308004003801051135001 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 702655485 1250 702654235 702654241
    0x150f1a0a03150303211a0922030c020a090c09060323040b011e03150207170d0606030c0c020d0204020f040f030b07090504050702031b07170105012603040e1e01080f060c0405031203 79
    0x10103c080074103045c001f08014500050380742c02030014240c102b080b40a0241c0f0100002d8450050040300350b140c14a444154440781420030860003050404120945000e089418040c00d40e21440c0c4607000d103006e072640c0a860360402d03884002d10100a80c07111100707a41800b0400200ba21201d411031503200401c07004d40c1c7c650a074200a0b40f601046410245002000a2045143e85c0715078032510031a545038030240305480c05800c042c0c17143d03141c3c80401b03508000b11403d0000185001e40c0140083e400c05036803581099220b0030000d019045c02e810807034400186a050046294001450600824080303070184064070b00750200a41300d0043c10100f003a9500041100381031140184000c1c4040d10600760b0400c003032400c02e107481c0d0180a0030b101d40020840c10f40c1c8104d513083c581c5103024101c0c00c0840029440c01c0d141107043d6604120007810300071507546d0128104030203100207001500a00380c0e01c0c002d24091220b800c0c03090030010060b05040c146041004200001d85012a44190341c801d0000074940300d903 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 702656735 1250 702655485 702655501
    0x9060309060906050a090302070503060c0901080406060b0a0207030605060609011b06270c0503030903060403110102070219051018050d0302010e10150f1a0a03150303211a09 76
    0x95003240080c16a070130502003041140c26030707200101c03003406a422250000d03035843c2815100c00782a11001c14240003000b6040700ba5004d0288290001d2040c070000850903a02c030510022904601c0300d050040c0c00541e010020300601e409110b80105048501a140080940c00a042d820748031080d00c00302c102c141d105005100541c0e0100200c141d00484400c0c3c1103502c0c0d24913145d1502c80356000c4509078a100b20218040c1400026a6012440640200240e07115502c055903a210200c0480495640800c05040140ca07201d042402c84000c1050702a00305041c90200000301b984c5500326401c004140401e10480118688460110b8000769505102003002e810700300d025002d009603003582481018108084844180d11503208619040c80e101c409a407140d0741641d440c00140b0032540b280f140344c203980c03004506000041070500694100040c1c0041f460b043d00c41c8082c1268825004111021011018039810103501d0351189141c0c4801c1021181010b0004402211001058002d21605000a82030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 702657985 1250 702656735 702656741
    0x19170a18050a0312200f090a081f0e01020703020c06130b0304261305270403080f070f140702060c03040f061206080c100201021c091e030906030906 65
    0x141e030054152102c42c90b40d400c02034020400c0c85548581d840c81c0500c1c0e100b940d4001c2501c4000d0800000d5540c2c50224400415403094102c040c1307044e845400020f001442c00c0c01088101d106440740398210781c0703110110320004200c440c401c0030000f560b40100501000030740e001c10111542d4200f203d23500d071146a40500d001e4824040c0d00281e001c0c00c1e00000740302c24080ea1084409100c180c0710300f10740e40c2c006426011181e0703001e41480040f0014031120140041d19161180c0c9402c04400071300710305503902c02551401c0d014810303a000c4e004103032624140608102460200e60f0308c40385a050104031203210940041600c0c00000c8511400c440106080c41103580c0d44080304c2d08800381108803500c039511044c491b150740d40140f14050200303104084207040d00039140540340071a1005409441d00d0b1740036a06100240350030645100455600f000044803a026a5068044550502c200010f40c08528a4030900240340404030a0107002d001c80c02da03002a50088100040d9551850041041001c0c0d107070400c0a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 702659235 1250 702657985 702658031
    0x9130f0b0c0f0a0e040522120e0d030f02012d02250b0702150105100804020d021908160b0901050a020a050a0b060108060d03050d0209010e04060b19170a 67
    0x5800800200c04800c0d6a01413814500c800342250108500d44403c3c8a250000e6500007c0180790314900e6900e00c0822400c1c4022003524105040078240d2a50210015207500300d1280228080f41d01c034880a00713401d50910811540c0030180c16604104041152480c1850300803c100414054000030102c140c0c03100c1380500c00d541002d107000c0384107090803403801c4885280e0445050005205a040100340b103226044c0b440c0c100c42c4003502806000d0781c030b00c10484000c00300030010380c1c201c0d6400d201c0c180140c0700e80b100b00c8038a80122601d031150505001c2d10758100044154015104003c102040c002c09090b02c0c100d0b11045024244143d8850410206a040400140c0003624502800601c034082c80300b103003420380c40b030f030720907600c040304e6541c0c01d010003044400c49003001e0f000501c1442518110807440e4000d158007401414a042c901030030000050658140e80c00c00c418009022030341e0005116040012001d580650800c2c00c49075501c10846802c0c044000e04400d40281c84034846a41d5015910b90341071 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 702660485 1250 702659235 702659257
    0x603020307061e0801150e0612040b100b030c0406180f060e0120102c01060305010506030d0e090408041d0702070519030f0204060815040209130f0b0c 66
    0x1a00c1c56451801a05440890350024445242403286286141c441c01c02c160684078506079042c031082c4a10012115248541c0410b81c201344100151a01e000360210003a12031445100b4444040c074010940702191001c0d42e2020280780f10501c1417010010401b402c2e102621420310341a4101002c0074035941445030700380d20002684440e44400b14205500610565200600b80c0b544c0d080d002041c000b42c080000e150480f4049900200c0d11000c0c1d51840340c101483c501c03200c1030b600100d100b01c90303640000000b00e1520b0048a0b075640c0e1042007002000c0c05055070007807049014100000082c100900b4203545a00c41c81c0c402d841c00301c0010100a039034004d0320080d00714120007400c984801102c04900640584100d80548940b032400611881c1440301c601c0c0118088210700d01042c0f840c0d440c0b483d54028000220fa01546a81000c0743c45003041051005c03c280d80c40f40c98902d0308240c0140040d400c0090840d41e45040855854008980d6840c103ea001642c03200151b9866038a0029240c014041d22032404 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 702661735 1250 702660485 702660493
    0xa05130209210f06130228080714040f0203040803073b0102060108010c140f07050a120306140916030615050c011b200a0501060e1501020111180406030203 68
    0xb8041d51000a18030b0301c04480e20703048803038603201c9146000000b00ca0500007503004d424400c801458003040000c0400c1e801348503401803110343c0c035200039904080e1117802496409441c0c55100d078480c5130134081c08513418241e0f5070852660030941c0711002c45100c020070300d0044c002c100504140d100329929000443c01e46000503c4c0444400c080000c6501140d00d030000c1c010702c1034a001180b030070010720604024080c1a1590310615101001c110ad007a000700864400d04442071001380701190b4280120144d1611440804030a891840340c003408030b4646810500301c0c00c800c085070b01d54a8072880c1704a0b4101e0024180c070040c1040a00d411070246c0704ae0340101a9035406026003e02c0703a500703c0094a0203180400007400004041201c0840e01070811489038002070301c0c010300c54407004241001c3e0520303220420546900581c1610f42c01e007924100c0c2d0000070183c48140130084410724020050031000400d10081c09580c003a85411101405101202c00100c10350020f5518165155031210004513400340c103507 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 702662985 1250 702661735 702661789
    0xf09072109062915070506040b06012d032705010209010212070c1505130b0403030314090a02040e0c3f100f020d02070f110a05130209 59
    0xc03030090040c1000440c2c406042c1220043c07440c40a41c1c110000c02542e089018070483e100040102c50100e01440c00c0840c070007003082102081d814400030384a070b03018003010b90b6181020310004000303030012156030108810300c00d107004500d8a101e015070500011490b010400003000e004046000c000c9080a24a2640e9181c2d03000801c4019005400b5081c030980944102003640c0030025a58802c50400911190345010b00b401580280c212a28850981d85803e6040c452601c107040c0074102d5541101035802000708003081059418010340c400600b004c1d16402c41402c1c0200020340e60215014000e11a80d02e03607a225a408904204e042d841c00310041000080301622000811400c0c01a0008480685440c10405100d0f640c07595640341607400c04004c20204141500d0704000b800d00000c803120058007046480c40c1030003107002910401e03010b0721141c5110300042c541040c401c00e107400c0044c0149410701d020000c03941c0d030300101044000c90703041c0541e0345c41c41100010946980341c040010500c01c1c40c0d00d0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 702664235 1250 702662985 702663047
    0x90b0a0f140931020702030a0204020f0f0301081c050f0306040b150a0c060609090506042a14090702061311030c06071406060f10030e0109050303131b050f0907 70
    0x5500c0041101200d00940d54058420f0b41d010b81c410703424003a4059104103500700060415500504080d004e8411143c14001d40f1600340b0f9160744280d00c411265800b800c040d805410724107030200c40c48407881c00d2051034581c900d00c482580340001800140310701c4c0c1d100c100f10440e0b181e040000881c4068000025a1450b1107030b0054006a00c1c2d0b83c064070f00b07905d815000710341c0c091184a01d892084d0058000c1c54160390b03507070700c2c0800300c103040d04100703028013107a400c1c0001c541c1010081c40143c0919441d9440e81480c040a000207200018480821540300205000002a2800e04e04504540040180c0d80b02e03e459400300c0d2510001402054101c100004d000c0180562111305841c90a4103d003505e0030b40d00c64000700010124140700050f80480036001c108840d80c080e5008204c94912140003140302c03415600c0b424110f410890b44003003180c4081071000b0400c6160001c0c94500702c44031240b50051810700c000b141d030038012008050b0160200c4000f08111500581a400d45a09038030380004004410a003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 702665485 1250 702664235 702664279
    0x2010e0109080709060e060316030b07030f020403240c1b030309151d07060f110a021305090c0d0c0b131505041401020a020f190b19090b0a0f1409 64
    0x114406218800101187e0325240104444100000d1072861031040c03801c45d21070300000b034000f03064070040c5691000483c01d440c048e4009400154000c0c0902c801c10345100803411603100c40f00180007803440c500848080220341103480100c140521451446d00c0c00b10a29042d40100b18198000d40600c0300d00441d0444104150455003901c108000500c60582d240d101c001e588441d40e00030310021030713542410b400756103200b52001c80710b10703481008031070300c0508503000b0610a03803100002a81554a9100f003101c0700340100050342d041c2c8003d840e807032031820301900c43c0c500e145014018058110030002d2450024400070641c07602a101007507e046124000d42c1000d0040e034400d01c01c50f503492880c4888540e6960012443c603102507005007030300801800c090100010642c10340400001c0d04848000071444940640150a442426040c10714a4010707510020b8428800b0354044c6044003010040c1101c8a5030003550180c0c100c405061200d189a03103924207040350b00503d800990061442c1386018646e070030b804 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 702666735 1250 702665485 702665489
    0xa020c0a06061706010815060109090903080a0621020f040905070b030907090c0c060b12011a0f0909101a090a1d0d0c170409050f011a12010302010e010908070906 71
    0x1846402c2c46480e0f480a00780c80d00004d1040c40344540145083c0b05503965920400ca521040500d0070094140c0c8a0310442c0c12500040f5003900010340c102c0c10400da00c5000d208400c041c4c940307600000c28099103645004101c3e041ca0100a00a9001c000030360503075151508041e4580c1d510400303507210f80c0d4684207042070316082116103006034801c00030001113100040c0300781c0007206010341e185005003540740ca505002c0c100c41100103401032040c2488800f500b00a00c80c4000306042d0382086440380e0310302c00c03c120403980d0030040c4c10f1080c4c001c1800e0001101000401d42e610b0030310350501040ca500c3d850030310203107100350200c002c2d041a1007034204004000c2540c407401012482881d8031640c2041c04c001c440e9075099510100021903135032800007000c545000d07003120003038101136100c9240c40c0d101d20840d000d960081da4801c40c002101d03c0184158000d07a40403c000b2840140c40c21b0410160040c0242412418130000e4140103911581d803031164421103045028140d900304544007990b461304202e0003040f00e4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 702667985 1250 702666735 702666749
    0x60c0b0604090f020906030f0106140414010e1305150f04120c05060711010e0f03070210031505040c0201020c1e1e06040b06060c0a0c030309060c0b0a02030a020c0a0606 74
    0x614001881464070b44182d01d49240c10a82c030b80011800c07603081c0014041d015104c80c1c6d1611a1452109010702c0900030000685035040011901c03000c035038180026900c03245000c40c65045e81e000140000003118034001e5000e0300395a8802500e00c1142401c6003050050120115044004010000e50000310910280034920a01c2d0006000d02503482c22a80041050300080950700103401140840d071045540503c0703d050b0100000d800c1182d440181c0c585400c180d0868201c0d080480d846055180141640d0400b00c9182814001e24003039850700006000c05014291045076125000c0c0c24103071003541654101c0071041e04544014902c0301405da04101c0706c1c56aa1070324402d400c40d400140180203500e040c3d80800000908091300d80ea40c80b000b400c84011b001c95000300c418001c1040d0030504204c144070150180d4080e8000c1c50450a008080c101540c200300c052004081d42c4400040700090002d61100207001c0050316516103141c031380064490049078408512448030040c09011050b0300100440342c1c1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 702669235 1250 702667985 702668003
    0x605090a120b0601030c111b0907021c1209022101110406080610030b03030301060801081209010e13060f03060b1305040201021009020607080a0f030c050f1e07020a060c 74
    0x601d521001100150210003024000c29a001c81c100b9402500001500406403e05105044150203041d18060400503a8081404002c5900303101d810301c0031000340c0041d10741c4007401704004040f1403189560480d02103281000910031809450b20b002d98002d00c511640240920a03861300303030395a80e41216100d0801e00301940303811140c003846075410048404950081d103810810b0b035210340400000b03644602c0c414042c185c5401d11181341d560184000e50113880c07281c03501843c2e0350402030824a0f0543c601414182c0c884100318018103a03800c0303840711000c01d100712132a0741101e442c0d44034103015218990083c040d020081740b000c4100304443e00301102000f8144c401c1b400303901d40203980e18240c0b1000d0380c0203805a003115003840410303a9943c110030392050000d00740034a0b241c182e95900403e60b10101c4483d00203901002a100d8055060017107152052030341c540541455144002e600562003609958485585044c2041c0b0303800030b01d03e0035240c03034503001080c807411640d413100098590125020f04441d2002 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 702670485 1250 702669235 702669239
    0x1232060a0f0e25080102040b07030206150a0b0721090501021213152312060337050304080c090f0c07022701060e15030408090906060f040605090a 64
    0x2aa48140c07084905540001d0a83c081c2c4000312001c081e6031840c2c4020041c02100d4040303080c100c240000d00046c01040106592a0790741d00f00241001006400b0300c0c032040c03024452240e80d51ba88a0b400c030640b800001c4940e9074606030b24020b071018200c000121115600c124292001ca500100d0100840d0000c3e002e07200f480341d410180810074481c00081940303010340258140050b143c10f0b01007040d100340501b000c6e01031100c4500e1007035010003145849411204000390342095524080e0405801260540042442040c2500c90b4070102c00c501f003103a02480c0b880303243c02680710040c1b407030420090341103c15682e90f00e4843c201310380c50f100d00d0117850b4028680b20002c1480c464803074032014481c4100d41c14480c20550a0f5013040a40b0300c415608010f003082c2c5103010b881584520b012140240b01c0c80c2c0300e0105043e8950b083c444605440c071240c0300091824403c0001044c54002150f80700c51084400120696030040010450b0181203140c45600c000031601148540e013150080111007411110070592503 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 702671735 1250 702670485 702670511
    0x40f06020c061912090b15040c0804080a0905220e06100302060904021b0d110a0804090c0c080a1107050f0d030c1707230102041232060a 60
    0x3024841d40c5801240c1006001c450000c5881c000003040e681e03103081d150300e541410456060380d424100595882c052001808420010010181c00560301034800f8004034418031405011010000c10240422800240501d9503d00c110b1465018000c01403034407000260300e00881c010b0031204039292009a24040303200c080c8400004030a0b20420304070540350641c0d070445e401e001c0c064109400c2c0030b401035001d0155011485c00c2148007505100c68000030115802031000c003c02841003040f590009421051104000c14017510481d0142c82c015003000c242d00d00080b8045481c19440c840103090358802182c011182031740201c030005041c801e0000c0340c007201d448000b0459824806000c0540c408080f1500d10b0000f400ba104188509000c1d01390b00d80c40c25440c5041c401c05a201c20340480f2008820614048130401c0700d80c00c58658104c070300086003050305101407801464090140504058060081481c150000342c0f5114400c5007944410711148006c81d0140f030f030b1400e007550704102507404d10481050031 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 702672985 1250 702671735 702671743
    0x180f0311120c2206090e010b040c180e06030a0f03020f06011e090f06090e031e0c03070f060908120105180c0301120f0f051e0f06040b07030f060803040f0602 69
    0x20038004080b500301c110000901d12196503842c10441e0f070b060f10ba40b4005403142043c450144072200070f00010840055850811045074044405441449400c540b42600d01085061210030342d80d04080155642d02c903140081c1ca08404208000d05040d44440000109036002c10518403a0714040200c61060740c0f16039200c04a2056410340d8001e01e8204441004501d206800002c02d907408550000748541e00c8604100641d804030a00c819180e1000804050003c22015080407542c201c500c5241000103404030b99489209421004d0660310007a8504d2041c00150b40c444018540d00448040ea9100c0c0d40080f00007882d400d2054921400b9859080c4049192045005201e0002310111519503800c01c1402e41014512030020342d110314170070100b0070006442d2142030075900d00039030040c40d6603040d003490303150b6400c2e0602e00610b2680080210042c20080003540036000366000881405d80c1d500d94100310020301e0719400e103002e42170800301e000600341d6000c4001d00555a401041d0407581c1d84030780081c0d0361 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 702674235 1250 702672985 702673003
    0x70801022206050f03040605130f1202122a28030e030d020d0f0e04020c03040f050a0303091811030403080f061e0d06060f08030409060f08030901180f031112 69
    0x24040017040050300040061340455803141c043d02c100100000c2c01c0d110508500020380b022202c106640c40c0250141d0307010444d00310881c2e607001703015140416090100f80c1c005408004607030001c040384032280340700d40184400d000030401c003003508100700b42000003880c440d021540140d0100302254015a038a05010850000244040d001886140e64030b0030219083c10540801104018080410782c64940d6070340001c0011202e031800450300c1e24104080041110002d0340020f110701e0b44024200b0001c3d03002140360f0112521045440302807044a01c00310050964400700000d00d0000008000c00c258002025602505542c10403034415600c0002b0301c105208806031030050b1050306007405c00c0c1c43c9042031601020318401e801c0071800541d0341c10034003840d0130540c0020000c0c1d00041000d0003140c400d807160000a0007890b116010707040c6030411041c2c0724881d0540c0c041c1005407000d01d00003003070042c40041008110205a0048559aa04000c3c0031000c0400b40d40c1d1041180f654014180840024a001 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 702675485 1250 702674235 702674257
    0x9110901032114070b01031109010503150a110712080f13020d050c03030c0d0e0d0804050f0a0b13240e0d0609020d0f020310050108120c07080102220605 67
    0x554a001c07142d041005002c61500c0c030342000f21900703500c0040750303d400143ca80c640c400d210561301541949012a11000400b1020b0300407501c03507004200c281e80004102c2e185003410b2113140d48a40f10600d07840003904200c204041a400f0005080041010b141408140c604290380c44111645403002d094500107c156514020052201484c60261803d00e4208119900c83c40444882448940c082070441c4c1298011201c5500003d680c001d8041d04138075501c070a0070003191076003101d0b00c641c1c3e5015058061401070f03038000c514885103018540c85200d0710501504010081c20384802a5005414544c80280a4101b012040c0300c00085100c080c6240704160b50043e40356240c08440075000d11450110200c1e041c0d403000d03141c82502c00540c940c2c0c0404a50740b8019021102c0080c0c1d40c0c010f06281c82c80780703004000e05a00d400010030010307102051000300c0c0120010400d41ea5600200300c107140a4040d00b0603503007944001107041400c44514020f0003d01d880c022816a01a580e400981e494004c20b48098 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 702676735 1250 702675485 702675503
    0x6060a14010f0e04151d0f07031e0504080a0219020306040303110d0c05070210020a020906192102030c060c03030402090406060b0318010e012a030b10030911090103 72
    0x40403a600580c814050b06015241c840030071040000050207942000f00503c00005040d2410311440c2c103545010070400e4501c4c0d440c14214240040041288080146103000300351b1366000c2c40c00b00240480b0306184058200d0028021401e05003043c8100c4d07488a80940702500c604800444080c5400e0a0303461100d0300100031f4602d0f951980c800750043c1081c4001071001000811255001ca80b1380e104a644400c0b40e0b95800e0344400542c414088136484100800f0255484000c0c180d00580d035028800d548148141e4412840c2000b100030b03546000380c40c2c0c111400650f40c0d00c021008a4050b40c00c0d200c4503034000c8081700c21011400d000e100c401e104158452030285c104100081c00340c01e1211500b0741062248000040d003e0352500f0591031a08141e0b09105901e04440002d100311209004100c03c02086100801c1ba650241d00e10090030780041207200043c101d0413498101c454020790158985610280840c0034119152100034020043e500088820050242d0801070b5070400b4480c103416261b01488407 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 702677985 1250 702676735 702676769
    0x209060f12072d03110f0307230402120406090305091e090c030709090b01020709110912190201140c010e060a060e06010c021e03030d0902030c03120906071b030f0506060a 75
    0xd000e034145c1008850f0b40105502c220900e0948040084d207004001508411284040d0b26000d00e0711500c000f5402d178820741c0140b2002410036a001140382c0c000360310084c00030f0032001c41e18060b187d9001e60503c0c6036008410000e44031284045041c5401d2189040b03c0b9101a03554009010490340400d60b620b60003c0c1c2850f0040c02074030900d90195a182c07405004a8503101c0d5140141000d40303009401c1e1400d1000301052030b0805050100d019800202c500d8090007441100c0a0910465040c03130001904102400c005000c040400340d0851750070191020090040c1443d0b004c04655605040e20010b002500d41a0001100e444142805006030320503901c50344998555020050100c3c01210040080803401600402c0c0b60360400c0240002901d4440c045800406401054180390110005034045e40000c0d0070ba1503403604420454108071800c5580a842d40c42d1420454100c0d0125054031141e5184031002106000d0100b80c81e900c075a1203803040300c00503600c5405000c01e10f0124840c1c1c0100141d01641 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 702679235 1250 702677985 702677993
    0x1e1803050909091203070f23030c0a11011103041202060601021f0f06080d03060f14060310030503070b0a0605180a02210c040f080a0f0209060f12072d03 67
    0xa0070383c0001e582001c6852001c09400b00710303516481651031034041942c0202490216800c0040b0246c000c003910b500d0a04c55042411a0006100c020180160300c680020400401c0f4001d1500019610090000304458a00480380c40c10700d505c10798003510050704050510040e1440060850b2186034103a010341210600396034420751548008245405054031401e18003030002540c46120000d00480009202d4a01341d00e07000340c201c1e8815049602d100b200310106000c2d801c13450014a00510042d9146540ca03594800c1d54103030b40360303503401c0100707580400070b850b03428404064849400303600484000c00c0082e60b10010031803854401c0402c0200160341c48002141d80209078040c000c1402c0c54030003440014407003448050f043c3d404440b000b11444011800b07108011540c1e0704c007405408001d00504010400b0340702c408010712000e0300288525186400580c1c9500c420907030348000e00016080c9040395203c20603c1c1d4075403941c0d020780248080c00c0981c000e00d130200000300340130318100407100c2c080d02c60850321 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 702680485 1250 702679235 702679249
    0x10815011d040206071b06080a151a09030f033004140118140717030f090102010f0f09050f0712030e04090206070803041110050f03070e041e18030509 66
    0x1c41640e1101050054034041071b003e01840ea01481c0d80300348103400504202c1c0151500d5000b82c44030900d24a41600f94203d150440074030b60a032000941548009140075021328441d100e6406240d030580544280881289800409008008041d07440f911072906a90720700e500e640c5140960302200340b0359078081004600036900a01c04884200004503800100452a604070411074070200c5501d058040440522802400b181c0082c008001038484c88402a40515030b136030140c1687c0c20300076440003650b1174080c0e0013541f00c265100c01c007070014041500e4001c442e2009000c44e000070344850090080c1d01c0c1c203100010807218180e5400d00d0007008800d10a890481e030000c0c2d803030722054109660740410f9000d80d88020260504610034440a81e0303034a02071074244850480c1e0f444e454001c03c020303d0311040854000003034498040c8159444dd499645070079089801040348203203207811a1501075032411000441d01405400021070030203000c0181101410b11420f5120b100c0540011824801700e40e60b0b141c825 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 702681735 1250 702680485 702680491
    0x6021c03150302030111040303320a03020d051005010f030e1213031a06130509030d2d0605030c1e060327010203070e0303030633040e010815011d 64
    0x140038684042e4603580404e0841d09141b4035410356800101d020002c01d980034801c43c0e81084001099032100031480c51402400030704280540e40d840d40030aa180030680300398140d603c1c040f0600030a00203810315100c1c00b107180f034483c080d50b4001a180300016003024001d00513107940e014060014429410310b1032001e100c0f0340010040e002c040098800c00400328074005484031104000e92031800320303414a401081400c0b2000a143c0010340d0801c010400c1084010040d25016080b178840030840c00c5542d60410701300d15560020408036010000c15402c001ea00d603003c401a100190100c8100984180c00c0002c1c5c44504d15540b001c14510303e00c1d80b03485060041c0a1900010302c59140c00d40c00070002007a140320400610002443d0398040200610613a002204c3c8140326401d901951840c102400411071981c0341c6400b81c001032094403010b2088280328001002d54500b2004002d8450780c071206061a403140038400ca1002e0b00c284088007031441d00f0341e183d4078100d810092917030790084d0020a420070518401 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 702682985 1250 702681735 702681761
    0x906131415062a15010305070603051f0b0d090501090b0a0e030c030d1d0303070309020a05120d0c0309170f06060109180c091d0a0c0819090206070c06170106021c03 72
    0x4814601401003481d0b884c50b02852186000d03000d01d600f0102d0080485000800162060015022192041e000c813130950003074440a400d555940d000341642a0058500f10b00010700e290300e481101000e2000301548180151030441c02840385c0114040041d98a0040c4000e02200c0d40042000c241050000e130300811804a0510104000c480000015030640e0000c03140440801e4481c5040d00462030100ca44c00301602045034400c10300290344000d541c3d03907010b0110311824400458400c0040c18003882c00c100007440d440d11115102e03124000c3c0d17291501c1c001514603100c0e100304000702e5545d41c0100c0001055590041d130b8000c61350060b118510241c10220602410702103045000700d001454100750704551a600a540c01590818642a1084400345a40d001c10004000140034000760040102c1005032024040441c082040b0300010701c0c00d00c01c14400400c006508c0b840010744a4102d24030b510036001c03c0304c9002d407982c4d0718003050340c031120461380b141d21620300440c0e250203890280e0b10605011000d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 702684235 1250 702682985 702682993
    0xe030a080406051b06070c02120703020a14010306093b12070b0a090b1306060b19023c19050c0a050406030804050906131415062a 57
    0x940e121034400d58055008000020f400103000c1c003491200e030b08110450890b00c402000945001c040051200120800c001e100d818030103d043d40c622010428803000d5500140030718907241e6075110340c07015903007032540d260701080c284079000031400c2581c0b052000c80ea9803c1000881d10070003441c20303032500701d070841d90210708607001440c00e000c0c200412001c00c51a00030390219a4841c8a130405a00c40322009103800856803c040300b043c000f69200700e41c03d4200008500c0c40710414103c1c03501e440074284540201100150120300740300b000a114403025210740c0c6903000c8d41c00000b40981d04403038500c14400c0304601c1d002070350034142c1e140c02d0118078110400c031400c0603901035038404440d03000d000040d003605444950000740c07210010b20380381d500c04000b854102d5080040f44d2641d034982c042802144109841408c0c0c51000403005c2d15010709003142007481c0201042030480c030b003043d0350540d00c00742c5420030800b6524826000c2030502c0c004480c030310802c441018403c8402040d40500b01c055000e02001c160203 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 702685485 1250 702684235 702684253
    0x16060e0612090304030606080c0d120e1c0605071403040201050306010e120f0c103504052103060d1b12060e25060305060a0e01060c0201111c0e03 64
    0x1140750450380110100c0c2d001d59500c9295041c140c0507511507400040075034000c0807a171021582c600d1a01000203a0103561030003802607512058401c00300d4120f105800100800900716011a400d0404481c0c4e8072922080285484e40c1501300d400d0b1078448030300000c000c0c0800204000d58050750180d944004140b600e0391007d010030b004500c242c0a9012440580d50010b00c00c0b41c81d4960038044102880000d030b1b00c4c0c00044401394002016180c084841c20607840d00241035004080d1012040c80704201403258258090900c0d10380142d4420030081e403207800020102520f18400c00341c0d000c0300d02402005100001902d840c1c3c0300c14581e1140031003a01150b0303200c1e4000145504100d8141c40c4514004d0720006482d00704000303030345d08101c0d24407010b891001ea0540d0880307056142101d03a6090710900e14000403140e5521020941100c11500014003598400000040c15a400144500d2a500c00c0e42d90a001c03180006030f0fa50340c0c0e039100f200a0401600d1600e0300384254862200c901c0300480080480369080c1c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 702686735 1250 702685485 702685507
    0xf0a17160f0506090106171005221505070903080f0a02070801180605090c0d120c050114090c1f0c05010902090709050102120c1e03120115090816060e06 67
    0x180c01c0071080720290040810028007007001e00c5110300030300c0288020800303050030b0f07401d02e41c0750080c408405041d555540c000c00c880c080003080100880e50781540425520005042c8500e07454064a041140b460803c00000c012600c1040d004c02100e90081103141802031880c00064960420b6090b80218440e000001503810707000d0040102a00b03141c1d004a01020090600c4015240c00801c580142c0e80a810242029111030700c000d006103402c076111303403550745c812601150b202041601c050440d600b8190300901c14403003202e403607004110945c00c48688040d544140504c04c1001110740302a500000602080140125440300d6140c3c4207800010f5820010707030000b100310b1004d80302d090000c0c0103142c051100b940c0401c03441241040d0006243c1c100b40c8001003803a0b8501982c01ca100c407110094105c144210420001d443c10807030109501e0f01d140d82c5516a12600c00003940795080055148800014a2600450302590072595188107459190603d103050711180b04150388190004030400c0114684 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 702687985 1250 702686735 702686753
    0xd0e0d0503011403071404020901140c1b03010b010c060c09030f06060302030f1209010c031e0e0f060901020322030206070501090501150e0f0a0e030a020307050f0a1716 74
    0x42401500e4403912541040990f20307107040c0310100c80b4040d60006006101660800c41d0701e041070301c400c80b070141e500c5409000495000b03008100ca0910f42c04081804280c2034400b16646108040c20b04081c44410018801c043c2a5044a019240440c07094030483c3c0108105800030107c2c680c06081080089659560300a8044065542502c50903641c1c6020300441c40c092080b016002002d8006016031b1454401e50fa22030311039688803078148a4100680001c02d0f00400caa01401d007900f402c00041403024031703005020703020800b0185100c2d1010358110f0a061030407a064812050060740258109004800c1116103801c42003c1e20009042c91000040180d0b0345d203004007640b0b0310503000814009403528060382512022840502015290031090141610a80059602144001a01449468124410303005104501c0c050310035002c000351790450300d500000146005c0c1e00c0b9108035507030f104401d142161190780c00180245560019405140c050003100c015254488202da07141440c80120741e10510301c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 702689235 1250 702687985 702688003
    0x3060105120c031c031811040c2c1003050606030117101404050105010b1c0f09020d03020f0606060711220509010e0c0a08120c011104030c03023d05070c030c0e0109061a0d0e 76
    0xad105010b80b40e04140342490619005502407504050180e81040400200540814090001102e0ba9800003c0010008110450080b00d03050300420031b10b1944003407041184070844003510650700300800083d64001000445440100c507408074140b0003068503a000c05400c0282003e08420344550440300569900050781c00264801d400a0400c02807510141d030400702e0041446115072814890400403c600010385544035a044803078598080c02420030038000c400e01030b00951150300c0d00e0304001d6101c405521090b001002201210354444c01c1e2810024085c0d051f0141c00510b41180c9602d00700c106501003d444804802400440c85071700d80c004103c1248c005a10940344801072480c00c006500f081c00d80c82c5400841c00c1c3d0b010250000c10680301544051103880e82c46013980e4a074141a409103e4011b03078044030f6011006aa409950b814411740011030342c0a401c0e4080682c000016110015214400880d0360300c030703d1404401030034601a040d03600004802103441d84c0f03650741c4004540041c031181c16 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 702690485 1250 702689235 702689297
    0x9180b0a081e060106110705041814030405030127020d03120908030f0703090b01031113050a0b030114040506010b03100b1318060503060105120c031c031811040c 71
    0x101000429041483d1480681c8154244080f0300d5660615000c00f0505505968003a14081440144060281e034403d11590028000020b40c2070300d8143d00300003000038011950100c1c02407109110300c00c000c03010140e40058000c41100480f40d84070042c1010040c01c039130b050081c101521314200e01d0f0b002500f0303220204000c4409504c00001c112282c40303420b100b2600280145420000c1109555441400040601010700441b804e0030688400340c0d039040d041d64030320f07403029028001810809111005001103800d00d07071003542440407154241c480f482e5005e1207150400010615a4609041c1042980c0040d141016400d1603400104070350701c241c0700403c9203102d0308081d900e00c945401390100100e910041e10020040c04d140041040c1d5500280c1d1354195031048444012000c040940c01c0d19040b0106040ca41601840c00e062500d100c910f45c400240c0001d548092020800c1844e20503040c01c0104801001e0075a80c506000c050304080c1d110080c06030741420580c45884000701114503801c5103403c1c0d81 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 702691735 1250 702690485 702690523
    0x30c0301030519030512060307211e0f030f050918090f0607171503070e04060b041b0305070e0901080a03020f030901050a050f092e09180b0a08 63
    0x82001420482d003103209a0702d041d64085043c640d074005100d4030694211065141d261070206105a505011580040c06c0130450903e000c0c018041c103002440400700c0030f60742d95a15000c034880110300c141d61100c4c1e0302c0e4031481000803844070b41c3d400e40d84944041e5a09003089005c0c40284d12070b44491504c07100702240d64004e05500c0c07801d01c08081c50004004480303010307a00210f0502c031400e0781007035000744800041c20b110030007961840551509500280c1c00640c4c18450901300045050495101501a90180e48240030044449003400306460b80790002c88083c480085c01c5202d020311a62116800c070a26141140381d0074070280000c1e42850003171b04460bd4642103421488109034040081001e84410b0201a5040c0040c05002800600030070312113038203110340040c03c01c8a0301054000c594140000401d003604142c8040d41c0042000803d80c0f2062200808980360b0510740d000d040301400f2141d0f4142010014140621660301134244030680c80d401c074022401c0803400d480203005541c103002030301d00700e4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 702692985 1250 702691735 702691739
    0x40518010b030a050c0f010e0324010b0909040210121118120a03080c04150201020a0e09090a03031d010609020d0501050a08030a03090c0b030a0905010e120d150308030c0301 76
    0x52800c540107a00c0d4648650b02000506001950100d00c800c10036004039a480c542045100050352400304102880387d243c0280460012400c0310f441044021180822107501c0680c6c036007054010310301c603461045900c001c403400001d005240028007a83c0c0c600c1d540c500000c0002000d10308509036581100700c2404035001107101042400c01301070415a110f411a008804036266440c0e45484150024020381004035040001d881d1403510002c54000300700f1081181002039020030028000e400180301c8500242c0780351104019480c203118024081ca010710b000e00340341011943c066008211510710401c40395001d00178141c1d260020b04c2000e006064990000d40da44030014036150460384142c0210348503031403a5105001d8000d00201740c580803503241c20000f502c200b680c101600c8141ca19888014081c000000308040d00701d00c2e402100001d8824002800803540c07458100e0745030b800c0001d5548607032500b4032880301521350765001800000d21000f04004410f460341c842001580c001c80e52004010f1b000801 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 702694235 1250 702692985 702693031
    0x1c02130303080c13090b010203070c0312020d030c0e041a04090b0613060810050c040e0c0c0105150d0818030307030815010201330b031003030909061a03090304050405 73
    0x1a0b03002c43c01008807480c1241128542c045101c180c051100542d41d0744e481500e50340d00810440d20300c241c00040c8040d00da0781e01d18100110703075507270300d407180042c02000f1604802e40c2c0640207018200700b06403501c1400c503920000788401006444d8401c0c1046840040384211500c0d6441825205405440c400700d40d403610100f0710054942005000f01d03c50700c0e151041047c2d08010038440c3d90140e407078a0108503034032910401c0403940101e801c414000821f00061055a4880c0c80043c9019038004c00203001d6a6034190b041d9000907013140c411604000c007400c0c5e140008454100400421741c50141c980c003d82d0060011a2854000e07034011404a8018020b010a14040c00d9078072071249400d200920500e80741801c080c50484c4030850030701070710300407417850710302024422064000340c01e885003007580f60f107000c041c110109003940c402038000c1000e400c0f01145110107409608282c40c2c480180401c40d00d0400d055210b9036200034285840d5010500012440c1e64503401124081c0700300045000300d15501181c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 702695485 1250 702694235 702694247
    0xc0c03080a1805121504030302070506011d10050f10090b0a02010501030219050d02011103160b0a1811100527011e0801090c090e191803080a021c02130303 68
    0x11a130720500e0380d103120000441c0000b0310301a10b003174000340d0a4515115441c05901070700803e02c00620343c0c0121310001c0381080c1c14506115108850260004041e1164903500c83c1c048000c0c007416030000c1e100c0150206500f082d0340c00c1d650540440c6895400c20380d503407030000900c3d04203c0031000184d441e10010000d602c0c20040a00c441c26000c00020326051410700000c900744425900241403007400c3d41c042900c1201030060390341004540c90740c40c1a05919280c404404541100d00c05206854001c003103103445031001407202c2c503503440003030101010000030802208118951003441003181c1001f10305820000341d4000140d031902047c1d0342031600703d440009402140e04c0001a07201c0005110b080811780e5000e040581102c810040000c1c190701c10440c00c69407890ba54008042d80000107092048000d0782c0c91000120698100c1f0400076042080c18095030359540401c06400941d480c400b0030304900c95075004010102030b06940010140c000d618107010b0b6000904a0700e12620340c0441007003810f410131 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 702696735 1250 702695485 702695489
    0x60b0f0306010b091e06030f0612030f2502031b13111602061e0d14040b040605130f03031d010506030706030207110a080706020c040c0c030c0c03080a18 67
    0x10040c207031640c1801000e50302409860006403040d098403400c0101021201d42103160401c0140c13125a03030f8a0104105030100a00381d1300580a42004810b040d078000d40441034400401c0c040e0070f1246420841c070b403940d8a00480803903010340c1c0719041c03c00c0d0005035420454814085030346d0151042c001e03982c0c1d0401480240b001c0244594506090a5941c000060703011112010b000507607041000e1420b0000c541c081c001c0d4100403010100403543c90a0a09951001d80124404004180081d40c076004d600100d82c0303000c6d180102824041e0022030b0020b10315400603030f4040c0b0b41005102c0909242c1c4c86420b66410200400d03030200f5a517811800070300d0400540092444120002807140703040a0001c00e5441807107100344c50805902207055010080048a01c4a58813030082c811020340e40c4451946480d03580034030804000d440303a8980b1120500707003405001c040c140c264480d44050125614180d07581010044210340300701d6200c00c0031000a00c0003000d003048580558401000d0150000c80e00144001c503 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 702697841 1106 702696735 702696739
    0x16080a090b010909110d020d14030c060408090111060c0d0c03140103030509091b030a0902130f0608070b09091602070305010204180c11060c18030109060b0f 69
    0x650800007025000703480c0802e01d1700c0c14604010f14403601e850300035041079000da030741004100200490028828010166880e250300013030340e90f0405004440455074003070042100c0c0625640541d811041c113a501c0002d0010342440d10030510710780034060428002a031190100002607203c2e411042e4070a1660745aa082d950f100c5c500a06150400b001803030040414600044040c843c000d814554107011844461075600c0d00c01c00740001c0c101003030043c1d8000005042403541c400b0140700c0c0301d22200c00c0e50f4001072041d05210f18182002d00c5075001e0f402ca140f082c40005050795403180440d400c21034000e1654040301146000384c1c1001850340c07024000f03500c00300b0000b42c2006503880c03480e41c09500503400c021403903011806032842389441c0460000c6920600c006100040320000a1042c049000e480310014000c0c81b000a0070f465940d00102c3c0c00944510320090141000a00ca10b1440d2003 = true := by decide +kernel

theorem cover : BRFrame.Cov 702517985 702697841 := by
  have h0 := BRFrame.cov_init 702517985
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 702517985 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 702517985 ≤ n) (h2 : n < 702697841) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
