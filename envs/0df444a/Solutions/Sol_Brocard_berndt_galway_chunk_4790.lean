-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4790
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:44:11.309165+00:00
-- url     : https://prove2.me/submissions/b44a2d20-24c9-4688-a1ce-d14020022b65

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 861330935 ≤ n < 861510791 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 861332185 1250 861330935 861330937
    0x8010c030c050f0903030702060307020c0a170706050c0c03070b09040b0409080403170d0c0309030912210318080322030915031d06090105100e131e030801140402 71
    0x124a00b600c07403504040005515503a507900c00c0008540c140002c20080c00182c2e00c03000a50f010382515801070121002940900c041781c00143c00158048642c3c0100c1c800140340011041c0030b690407071420a480c0c0d00d82804540c5040c0440001c0d99243c05556000f00d84819100d028000080040764107004202151007400102c0b000c10202401c0d14804200500c0400e1155000c80c081200e00382e01c507468600c100b220107085912151040000030744900320f88040c0341e4003400e541d016103225010744900c0d4019580d59080400d4000c0c6030303c1c1c20600700d0210b03104980243d0011444d01182c140884000502d4170300b90185500460308044a80c0161b00420f845600000100080c2d0340c7c59103482c2c0f9500d0400462509000181c180b01e0300b05074940c407411202d040c032100c0f0201c1001182c3d004000c0c500341900c0711070a5a4000b0f105400142400508020a01c18542426000340201d88082020301036400d00661514013880420744410000c4d00c0d03107042603440440300b0b0494090202c080c006196290400c41030f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 861333435 1250 861332185 861332201
    0x151434050a120306031e171c0b09070206060907140f0c1b03060a09021309080a12020a0905010c0f050102030f040c050d02090a0e07091b0e0a0518041a04080408010c03 73
    0x1403103100c504080c5208482c1c0000b81c40403070041c0c00c07001c0c0d071680d640c4080300240d11100568140d111a01030303410102c2203c1c0100d05d00d2000c100d03880c02b41d5240c8024001d690308401458079100304c440b1004107040c40e01031001a004082d1807000079640b107600e1981101180e0002c10390008a12600400440c2103075194691019004000c02602c0e0f5500c0d03a000f810003400b0344500070703684107030380a40c0280f2600c400d100d08200c0d10b200d40711254640510480c003401c400c403120041c00d226130040000c0c910702540503861000381c03802400c06c0c0101c080e140c1098040c100303001c00c00818940c400424403006440c001c0d80584224810000440844e4803407082c48070481b61300000940007440080464030064882e0402066041402d04450101e5a138500207400d03192000403588810702c1a2415008069002400051840040d120b44003454a41070202d0b00340340f4091000e000000d102c0b0081000c0100a04428450003605411003483e030405041c01074480d4003d02c07501d09550329140602d01040d01a00400d40 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 861334685 1250 861333435 861333443
    0xe03070e0907030b15030706030906050f04050601180902060a0c0c1d01141201050c0301140d0b0a09020102031209030415030c090317040e010e01151434050a12030603 73
    0x442c6610b10781e5540c100020180c5505660307900c00e540d00388030392400c02100c001032a21395000300c0c04000d1030904400301ca20180c0a20451612017040001140000840c01c3c112404c6c48810130403020248503080040071543d900030b500c800000344118165900010080105001d0340050318001c0c5e4901c9010b5400080c910030841d8017a10320010000040107050502c405180034101d10140900f5031030050840e02c00700d4410464560200060200704c041c58000a403044e000e0b240c00021041e04c0d16001044078000b41a40c10090321a0001c0703045920a0065030706001c41003e0394100c50500d0fa803959100d40250040d6280c59405c884402d903107510074020004004450b80f110232a49003941c5805002030340016004d070300424100320015000403e0540540209050721021145505200c03000360f207149140d40038401c0004111144d480c0d002600e044a40102d854070164001d230300b007041e03404c414410001c1d00001c18124844035406000000c80d024440500c80e8028442c02c100c004001e900700c480501001c0c1c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 861335935 1250 861334685 861334693
    0x20105130f021e0303070c091b020a0602092b151a0d03140409020711010203070215031e09010212101a0c0124140a120b0a0b100e03070e09 61
    0xa005810003052299a10f0075100905100e804400c0119185a201c007804490000e01140100101c4d081c80c81815850000e5442c0b0035000665900c00a40c0c0781030182d800b03400700b070b40060092080d6844403d4001c90f4610380c5590441030320f840103201600354000c6401d0340d20b6070314400840d9010005108030303900b6080710121001c0003403a88041c442e0701c00c01e8220440600200100c0c0d900303030711040c8002c0c10003032481100150740c0d86c10600e4400c42d18040c04000d01c0c1598007c1c042e0500603550030323203e0303500300114901c0d840c2c5981c2c98808040c000c9441003100384041c402030082c41446101900144203e04007080947c425031100012802c03220748600c6042e1003002641c5c2014180355100c0001e15400004400104134070b14000403144c4007480030b510160385c1e290291410880e1803d00000c410100b0421156601214a001d40f5030b5402c01042800800201002d00003400c9449140d02c4024415405071a0030010303544000003400d8981448000c9109206940d00010905220401103115801c8440031b0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 861337185 1250 861335935 861335963
    0x1e0513120f120617070b1e1e07030329010212130807060f1103090609101101090b33011b17180301020a090312270602010513 55
    0x40701e803054031600c0802003042005460ba61001c4038000c2402500c021034070100c0203802098503e242550a40c440c0c0d550003c241310000c0000c000c441d102d40300010002c0b800341c0c1c5150041030506117101030701821600900100d0b8010034140e240d4021a42c110041d0b481c002c1c0703d050b1a5924406003008004140140d108040e4043e483d440000948600d41c842d200b0001a40d450301045402e003192074110600080440c035442007140d13403100d09842540700000187d85031080340004528984180d0003d00e00a804420f04000c44621441501c160840441c008000701040f620b81030845603002d580007004008480e0b0034101111101104440d403d80d201c21804540c48000015101209944444410350a0304400c85000c102c605014031032004100f50819034404691803000300e0341245a801c14000d0f8814058030b0030890300001c1110689400c090a00038481c41400100c4040c04c14115a01400f070403c2c02c207501116560710340d1710a4034100d800a01c00359507400d511103074031141d85a025017220540069 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 861338435 1250 861337185 861337187
    0x50405280b0d0b0d11150c0703030c08070b07030b03010c11060a050c2b05180a230706030b0306010504090c140612070c02030c191a0408011e051312 65
    0x2d0403840e4010101283c0c0c505100c0000d41d00c40c6084400f0f03034040c01502181c100502e450010310380411101302085080c00c0505200a42c1c547d03081c00010184403114484e2401e100100090720b40c41d0768085d21b0f2503004d2800341001005880360502860003503007480b03400427010f1300411103c0b00150301c1000400b0709a0310000c5207406007401400c0300d0010b00d010880703801c05030048a850604d10072a0292040d41358580c032021400c031007001381010411074284c800401c030600007188038804940c000342100b0524071094110300d41c914407050020801d1180c10f000089040d010341200801c03241c03c80070340d1045c0e079880301030000703644883c030004000440e0450700f03001a220381900007040d02030180407941032a0352311051442204094403101302103890101601b04620301088400c000c000241c03100c1f0040d00103160f448420000c83e00944081700060f591014100441e1400d0b01c006020240c02400081c04080c5100c85041048400c44143c50a00b0001409002d420f04207151103540551010112940d0f040 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 861339685 1250 861338435 861338437
    0x2010c02070b0a2312130b0c090f01050a0210051305100b0604150915110105071e030c110a0606060206070201050705090402030c121501030612051b060705030703050405280b 76
    0x7000c50350000007413025190160000c50410b00c505a031180b2070350a1b10083c2811000740000174000545103008101c54545601c61007052004a031003801d0a580b111100d1106900304a0048403900e000c80c9400c040203101103228031110b02c00d60150050381c08074000d2b02c0c100e40548581d00000ca030843c80411003080306164150344059a22040d1500d03c0c5000d8135400150214140590544009072040e00b40006c1d130311003840f40e143c20204034201f42c081404040307450000801e005a070501896541d5506030380040c01036004113050740341441900c140d012030b860540c0040c0f802d4050440103218100002e110a0300522401d809a00e0a40720340c1d04004000c0c0c00c02c00694802001300191540030310100460700c104212090090351074000c0300200070340350800102260b801c1c0e80640900ca80812022001c120041480d9101900c203214201c135190740000800c096218002000705107200000f600e0081c15403000251094440840d14003810802210380c4140103021036500d206042e0f8061403c006140c2080 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 861340935 1250 861339685 861339737
    0x1051e0f06010503060d050f101b090308031e0c070b01060c2a090903021e0a02180c0c0a030801060305010f0303170601091205160929040f050702010c02070b0a 70
    0x40c441c030803288031b80c0e554500749151085e0348403940c3d016241a01c5800254081d40d184c240d4511611280300c410030704020022140d0703100c0945042c500102146207085000e031070300c0381145a10103101c101d0401e15604220f5038004d41d0151480c030068000820b010348503590800748030340c0040024820f480c1c401381d41000c02091242c2001254004540003840c000c0d14002d40a03001d00039000740c482004c5811081c0e0313a500300d502c860305079904002400c9005a44440c468020f1041d51080c0a019542e04a0507500034800c66610000394403e03030651500305980094810305a448940d0140090390703840b0744804d041225400000e011420000c0c950400c45803202c22aa4015014985821300f966601c1d07036034104a00216043d503c40d0810203490441003d4225001e008168543c400c00103110742c00043c100780c004c0034052051079020382048030074503500c64024100c02e1840703e004004600b46210302030b0007007400310040701c0903000c5e0100018002c3e550505503850b0b080b96480b9941007040c01236407400440464 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 861342185 1250 861340935 861340939
    0x70302150f0702150705010510050d0609020310020f0403110612070c052104090b0a030201020d11070f091406030c09070e190314070f14100309060c0201051e0f0601050306 75
    0x14005100540d407021412543c0c010078513011035603000a803c0460035100018040640500f03411000c00144c0c0b80d0002a810f0103402c50030001e1a0080d510000c0e04000d45941e500341000c1c00030540014101c0d90b50000c1041700e120755000c15040c1090b40512180340115125406480103540020712120b00400c400ca084505c604107441c0715001c0c2641c40e02c0c41e01f00c0041d20002c4043d0200c3c02303200c118000c0c800c0180f83c10080359910442403440d80004d41d20742117001120b080000c151196410600c0c200050006413101501e0b2405903612558000c000304002d4200541d014030070350110f445801c2c0403409000d00b45002d050703004a682c6d44401902d001000404003900003407204408443d40b140c1c90f1459002c0e51040000001150341300b41c842e03103089010f403c04000302c40903000030044540c120314100c00302c040c01c1c3c0708100d881c0050311058000304082c00000d0580c42c200100c44400d41d50640c4414881c1040100303c0084083d60000c04d16003030011110a14036135140404202d0960050015513801500 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 861343435 1250 861342185 861342187
    0x3020904091505240319080408061e010b090a140303120a14010b0313200d050d0f0c050a02041d07030b0f0a0c02030a0f03060f030807020a08070302150f 67
    0x1440c0d541c001c0a081010301e0a03180e42c1d560044c45040f9200500c0b0280124440080c00c80d4010450700107a00c5000085500d0b400158001c0100200048039041d00c000f4901c031010364185140088444c58a403880c00110042d420200d0000b290a001000641d0f402c28006003a0012443c01c0c4074280c1c84a40c10700c0c0d00568148820700030342d03251150541000b413140c03c8845000c12000841c03d000480c040d01038000384c0d03603064188100070740c601440784800003050b0026080e40802841960003003401c1c040c0341004c2d4110403e08094401e00400042c1c2c0116040c0542d00c80950381a81c60045502604c070860041c00c0c0d07080340e401c4d14050b1a042d080700344c0070512920060505a0f800d000d00d032800004d640112034903441d110411030001c07032201480c0e500400251003440304207030510740251284a9211150180701982051001b254401e500041c064001408425545512424102c00d00d812581040784250744911011400311000325000c01103030f6001d08000380f5581c0c901c84150564100c02291100440 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 861344685 1250 861343435 861343451
    0xc020a06111312050105010603141504060b0705061e13030c0204151d06040b01080a090c030b09031e09010203032a070309060314070f12020d060902130e0f01030303020904 75
    0x2c4400284002000842c2112038185007903d8194255801640060f06140c5048903042d640701404550560103036500e140c2180000b5400000340041000303807c1000c03900008100002000000642c450040516503c085501200d0024846034100e04640003420846089100c01c0003a0207448010744192008101103404904100781407210314240e0710090f00700c2c1c00d01c559021440001c006a9401003004d039014440140e079400003a0041102605040403981da0350382d1030040c40502d26015000e1a8090714580b090b060840346159242c1005411203c054407010018140c50800c500700c440111040e005103003190740f8004840003107034480c0302140d0004250040c11003040d80304d03401003112601c680c54456a0909085000f0304440c040c04420402c0424136040c4101150000e06c800a124418602602d0b07500b00c40c1034001c064020b62180c04072031420003030f011540c10201c1d009821000d1400081c00d4a0903602d41500340000c4041d141a92003020690041c80820b110782c00900b00400046d1000c11030b9a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 861345935 1250 861344685 861344707
    0x1e020d1103090a0c0f030b06060307020c10020106231f210f1404050601050f0609121c050703050d050a02071a0106031104050a050f01091a0901120c020a0611 69
    0x15104481000301c9401030060f24003040000301c82e1001500c00300c0001a1068156a10038403001d0380500507030b108101c080300082d081d80c400c1152001600000d0701c1c05c12804007005020b8007811407400350320403039000044c52101d044144484c480c0c0e803c00c01002c00b0050102da0201102000c07003070200c0002c10040c6400c1528140e00d0b07180030098034520361800100184035041c081c040724240f42c55858600391040c18000840c5000030301606444e0101c0e580b6404100110000d0450722500702c1c4d894204038034000b01a200400810192440c0341400802c4c0360130710072554100c455106115000700070071300600c400c9007800f02d45d5000030740c8038150050042c80c101c06d6842d88602400e408180c8000c80e1074400c0180082c581c18010b0710120a8802c0d91541407905000020f62411001d0290a01418422850501c1daa00c03030150440100b4014140000700c9085c040c403991240e010b500818081004189003040800356031085000070700c100e0340030b065070720b503141d454601030004c088000c50710103006d0108500070 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 861347185 1250 861345935 861345937
    0x41e140f01050102030a05030a1a0325051f0e0402130f0e060d0206071403070204091110112a121b370e01060201060f090216020d1406070c0311011e020d11 68
    0x50304020244803210340cc1650172400e554003e800081c05403036041104c107082000800c203141e00040e00d04080d8035000300600480c000303000720320314080340c50034112000680b0170313030341e208402a50701807034a81d50309655102c184061040450b200940100042250902241000c04000781c0e04c0403410a8074640314a5400007416141c41e030806940311915106404400d2900c60540000c0c1152401c03c50310100910321100c0d286c400e01c10b001c4540300e401000304451500010b07a4a0114200105011022078108803c00d9940c4e03200744501d101d0310108050f18004d460203906240c0301c1c800c3e030500c20701c020302c4403514000128108141200120140540450038181110100e030192440313900009943d450412416a074582d01e601c0300e01000d01c10007207001001318201b0b80c81600d0350141c030700b0340f00700b401d9240c860420001c0301c1030041e8a015030000d2000160744410a1103880d800380c2e4a805c101d4000d2200e0700d00f21900501d40c2c445500101e000d142d0a5030107500a40b4010f658081c0020728407079103200c42c00113 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 861348435 1250 861347185 861347203
    0x210901120603020a1e0315290901060f050f0d0504021503010b0a0c031701030302210c03160203100906151401090e0a0f0603050c150c0705041e140f01050102030a05030a1a03 76
    0x51a00c1d140d801500d0b030600743e208e50034054000c0c02c2031421441a400700d08034500c18002d00080100f0b411004009074001d804980340c0500b55012156030303448803c690002000c2c103541c00c0384994000c103696011195020140da05030f0755218016898000c885a09484200c0384450440500060116042d00c00904044107030003140a0340141c003191030300d04425000d0716008814208244824010b0000068000080e0b8003080d244485482500381ca90002a02d03040700319190691090400810804201c0d2541264800c8202c8501540c43c2a4a9071031020410030020040350010f060f0450421100d03011002c5a50855070300d0900044001c8000080c0051792000d130800d6403e984810019601d505001d83e8100c005e5042e10016410050181d014584403d22803150300d20407510f4107800642d95103086c0d04c07000b1090b1110010401c00e03240e0460442814821559501c3c80210b40e400060300d940048121120800b03565940d614681c1c642c1c4000c0000d061020461041c82c0e060841103c8644041114501d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 861349685 1250 861348435 861348473
    0xc0504020319060602121806130815062b0201051308030322020913020102100f1a0402030705040501180306050f041101140307080405210901120603020a1e03 69
    0x1800b5240d801c009015128603500080444d413180402c906d0254500050341c0300034941d0903a20b0340300c083c1000041c401e40070720740c40317640c0008028000003480754000842218034030020381c0403203156071840c2c100411444c03035170140c0c1c006132000540c1c03100c85d68404101000c080d01c141003040c1050b804894006001c8420b40164200380d02c00414031900c0203180c441c0ca84c140ca8017400343c10640c03003164007041000501800002903244d42c5c0f0b484804580c001d1041908894000c0300400c04020850300681c00380c08800c14400c070304204100030002d075041078001c0380d1095141d51600c0d0720700b514210044960447d03c1d0650b9031059101280800002d03031078000c1602900c0c0d44180318585040905080c0303400c0d1003424019040c4402c0002d80000e43c540007060720360115241c10310010682d65070800b9400d182e07134407c2d4082510903c500380c1c6140000c40000d040700c203000703903602c500c64400750980c0e43c02c5400d5400040c1d8800f86d041010040c0b40c0c0c2011642902c3c4400249407000d055480e6501c01000c070b03040e030201c8 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 861350935 1250 861349685 861349711
    0x18061a060417210403020307050d02031e0f030310050f010305160f0c0b0106021f05070e040c020a02030a050601080106060905030307020420041202120105061005180d0515090d05160c05040203 84
    0x6507d4108820300c0a0700c1c00b120200b08490403a80041d55403500c4a4002e5900754103242c815000c508140102c000a05216060300c0e81c0b440c090504401c085e51038001e15100c0d02003208507808951291181030b100b0b8007007610350003217800342c1c0340103407802e0082000003030400c45691482d00010f64641c16040c004c0200e1703002040c51610410300010540705c8040000803a9240c101000500c13a4003540c41c4030710075415200018904010202282018643c8001a404d4410041c8940c20031100145080c100c4280c0e000800071030f80c0b80c2100701c0d5130724242c1c80396941c0341d8814404000985856404007080c0000320b058180c243d24007a0040d41160015405a41080c02c48000d01d001d6003480d202c000e4449802c14020005490880f0010b03100c48040000f040c104100442c400c1399544200c40ca5108100004049a142d540c0c40d141c655a9248901480e40300a80e81c070380450341100b0700042801800499072181410704403c41da94007001e6503c50340c01c1e2002c0b14114400105500c5038802035005a88880c011 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 861352185 1250 861350935 861350939
    0x130e072301020c011e051e070f02090901060602062d0907151b170c03040b0c15070504060f0e120f1c050904050402040207050118061a0604172104 64
    0x1a080c03e000410302e5051084107501184061417214800c0c8003603080d802c080751214082400c5040d801e80c01d00140001e00c40c0050707010144090200300003e207a10885034000e0642d540e1180038284c4d040c501c201d80c0560311480100c0d5540c000a1800c102070307503881804003d41c00035034000f170040f4801915001d03460340010009200540000d02c0d0a41b980049003000040c0006860960f00116403c840190108920103080a106800e101c11101ca0040041c100e84c1c60b140c8440074050305a010703862413007080c401c421a0241003055041080d00c2213605864460400b898041f00356449034034034001c1c0080001c500e161031001c1e03407a90701608040480b00b006200900040101c685032951b181c0d1070960804020414104243e0320908860788044240d501007002c0e180d0744040360281c0102c1e8030040195080c4150130038411102015440000c1c0180d000f0b20281c1c142080c0c02100404021000e50043c004000510181c088020710500c021144022112440c2c24450544506840c80fa15458020000941 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 861353435 1250 861352185 861352187
    0x602030903073002160b0c070503070605040e010503070f0308030a02120c0901020d08091207031b06052a0702010f1b08030109060504150306050403020a1514070509130e072301 77
    0x8a40140b11600040c00f031500751758440000e02c0120302c01d0030004200004c07584001c203010301280d0020240a01100c43c000d40b0381d04080c1007a0050b0141c600d924203c100002514071b000207014088602c9400058181d904540703d280007a80024402c4c4011030b020400c1070030207801c1c1e00c10107109000c1c0e41c1c20141c8401000000a0501000f241950204100601401030071000844c000c0e140c40d0b060500d061343c0c0c6280d480c058030031041a610800340c3c503080e103100c0401c1c005c890f00043d1142c00c410700e04010762050460802e4694174030a98101910009010440055014654801c0c0c2c8004505090382881d01c001103202d104805903000301c40c6440040010061070000d401840f0203000c040303406001307a003504031800c0e10381c0c07330f1520014028540300d4000c607091600038420041019040b0700d0713000d00c000f50f80245101403d06a00980a2040c01c40c0000c2c40c018450020740e0081d410040904a445a6020924003d410301b0f2a810000380201c1100084400a21165034820038085000b0540d812034400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 861354685 1250 861353435 861353513
    0x70b100e01030f20032d0f07031101090308030f1b0d090b07020708031c060e0c13050103050105010806091510110f19080c010609062301050c030403060203090307 71
    0x840b1109034144e00c0007440c0b9540800c4110303002c0d00500caa103000f4181140c0c1c0446280511544940502500c4887c041040d008034a00c1c0070340e07014030a8030b54401a407400440fa848032520024020050a1010840801c0d0009026801591150003440c0105c2e0030702c034a51b090761010b10100c104555402d0b1240420200000455014100c0e0028009c4c1728a000e0303400e0b071244142100d81590b44a614280201d40c600ea0384410041d00402e140e210407494240c000131441e6000701001c0c28520b980c080c0002c2e0542c4a80200c40c180c41043e0340d8070350240c803071406101004201030700c100c4401413030340700000c40740d12031400c0003600c200e690ba1111b9807079000324211424080c01c030b81c0008141d0000703002502442c40c244410400954170101e03050b038a05030f0b9005c280c0104056000300b1580c0d81040e4002035010307a40300100c92a140041c1d500c101c0c41c00074000648442c03091206540081e08140420130201d0070075400346030f11141c0c40301580d15200084e5035400702d204290746402200a00c80c4015016451503c1c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 861355935 1250 861354685 861354713
    0x14160605191a010f030e16062327040f05070302091c0506040f060b03070b030a05070e031f090f0803090708030702011d010e130b15040b070b100e01030f 67
    0x40c2c0200c030400038002c0020709141000da03e60090686496a41c080318408010854401241c850708004540e12001c004000d8824120074035007200c031884540301c2154080c0c0894041200985c00c0c07000f9140440c80409520034030106c482d0744140c0c3d03480c00070712901c100d000c0e0074400c004558005030b4030305a00c01040700807e25000001820360850070600006040042c4403904642c200d01040c0d40312501e845e250b00a00303c001030f1550540188000007618400301c101441c0101c00c4001c050101d50b8036404202c50203103181110b00d926510184810301c0b240c0c0364602841001e642c03901c020403090443c1e16180010351a880088480b01c0000041109207072041c02031704083c00404014511384070039034000900301e603200701e051b43c0320302407041d68500035138011411180803410103004000d9401840c1a658010842050708e50b0260700d60b00701846007044200200d80a80d800441c045050441076140c11040c080d00410200282481d50804903e204c0d0241d80d180c003c600c52005401070121510b00744065104c07007 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 861357185 1250 861355935 861355961
    0x3011e021b06010b0708030c0403050d0c03030e01051e09100914120406170705120708070e0607030207170a05030403120909090b0415021606200403031416060519 71
    0x42c00604c0b82440080469554035000344505403607884900030034840d44101e9100914038480c2c1d1030344c83c0c009070f00310042506580c0640c8081001c49903110429003a40d00444818803810002504070417001070040083c3d42045e03401e800c9a072000c0e00300310200d0803958036260a4803000d541a45d0040000800c1041c1201415140d222070304043c0350503000b905044049418400101840b400501c0c034520400a5036110b5001038030410301c6081160000d4031001e0151500ca0015941410300b40c9941070000403240311f160b00d98000e0542d1031038500a0000c4d0611448080f149000303400b009004074008202400c080c4d809107151903c032601c0c01d07602030001012a440041c800e0700305105507021030b2507c102c495000d500200385400f079621001d4410020b1040c807101220b80d10b0011299028400c4984c4010700301c1718a1030120040d1039601d80b80c890b19001c1c611000700014212400340541d01c13a180090092001480800720014240d41e842000b031b11001c84030451a849240414450940c5034054080d0850350 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 861358435 1250 861357185 861357193
    0x3060406090b01050706020a1e03050405010605030f10090c0519090f05070f050a030603020a180f1103010312050904110d1a03070603181a07020f1501120203011e021b 73
    0x482c0740081c0490007142c001420f0144d0105400c06058081c40300b0000c0c2440c0c0326029030080300d401e41d002d0007c00064509460325031801c50701080382d0400040c220f05141056000b40300007055000260007401c0d0990048030400d2904c0c10000f259180d0a016400c103480e0003e41d00c8250b400e22039140c0c1103078440c0c0c0400d10300c9424030041c0408039400c01d84a02c6291000c0c903000e0355558180005901408070742d4402500310518540000c0d00c004900c04125003144150030600c40c40b8514100507095a80c1e081c030601d4011000c000400006107610782604141c609824911300300190200020129800f040035040700c4600041c0caa03525401910900b0745041b00c8a0b0300e01200c0b021200807a607215101d000354820b0643d0341c811414030100d40901c9803407503a400040c0502100003000b2030801040152440340240c40781c2d03071080e07581340804105440b083c02105040f0b179060b860559040504081d0351401d98165607560030b40e0340515100c40d0540e548051906c8090382c1c2d495a860901866034076031b0742081a41d00 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 861359685 1250 861358435 861358451
    0x50a0b0906070c02042307091505071a09070306020c0303041106130b0c0f011b090e1302150904050403031401050a0605090d0c08030a030c0801090501060f0c1103120306040609 77
    0x50081078070f500302c0e90103450020f4840c0551001c1080c0d5900c5507a60340b01c0c038907018108408642c0c801c40003400d882080041800780d02c1c246000707403000c0c0180c21000304520141c0558800e0360307007a41029030b48203581a040f140c010340d99031540002c03a40000c141842d1a0400020407082c003010b442a4400440103442c010315003a682c00001d0301e2550f407405040c05c00745001230990a0104200000614018040000c01c01000c01c038000e001d24040841d0a01c011a2501304000b40c80380032184418828030b144681c0c50003001e51542007180d0803c0e41b51b00c0307050b2010f06010303424850321140309081c4280d10a807070000f122244580e0364007550005034803041c860518114180805540142900c040f004196041da10f01307103080c60b14403650009904660668800030074070011190303054008a580e0700c22510b94800a9803240e40314801c0c2d510074040d50b00402c1d120368100d0a031510515218811a00604000d0160031000c80003904028034001006000d00c03010052140f02d160601c00d00005203040b00081001c20 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 861360935 1250 861359685 861359687
    0x5010816080601230d0b0609060a0309050106230f330c1213150905060307030b030d1115060d0b04140304060908210d1d0307050a0b090607 61
    0x840000e0519003044154408a0301d540d02500d02c615028400e5165082588034600c0902d00316040b101030401d005003860b1640e1140d0410004440303480c500902050300e000c004000540c0a0185e80030103c4d9199642c0a00240c64840ca1001d2420781c20510300c4004da00c078540d81088030001390101c500c3d00c941035515140d9034110240c1c140d080600c074401300201c00c180c00031589030650302800d69005018001e9400d000d50030b048031401040e40d002030282c1918101e0315030710416950414400004040741c0360000a110f01d06c1c0040145500501520b400310fa041034900200381041c41500e200320105844121141c642c2400344441d01c1c03c554041c555100c42e1824900080064103083d401501c441c030640042030600030191000c40544c8068811680d4607640c400f0014603661480c0700c0c01556001e8045e04070345104d21070f5544000004891300060801031f800e0f03c030030f0090428417581040641d0540c00590002c0c0300740080c1a0150065002e40803445e054184140345080050444115400c9101040482 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 861362185 1250 861360935 861360961
    0x1f03080a03150f050f1807030e0d020c03030f160c0e0a0b0d1101050f13060804020a151d04090605091b06070302030706020a26180f100b0f0d031107050108 68
    0x35481185c124020644000100e5900c6a034013001c0902c0c035804004002005425410001c812510701003251074285006c1d40403a11a003502c1e401c141d00d90800c0229464941080c40078100c49a0309491121100c203240d5a481041c4000380e02a03010024020100f00d484000b9101e6503046103403d03911a40e82504d247d442c086c2d10303000035407001e043c854041280da40b200d00240c184d9101c0744144845400c1951508000b41007180111400c0384603035005d560100f1402e194400c1c00c2190100c517119210000c000e0040c0e02220a203103070a46403c55a038040c28804600f00c2d0140074060103456000e80200c0794159128461a1541e0800ea03004401c00c00400740003950000460f841c0b150400302c0140c480354600c004a0b000c00008203400e0020140e9241200a510071440c0a8091180e8807003100940c899050030a03101d800a20032498a0f4200c18180d140d0f0302c04940003845040c500510081300d1081840c00035443c40703103a08059001411044a440b405c0004120030005407400b401c01695500d06800b9010b0781c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 861363435 1250 861362185 861362189
    0x21023040b0703061428050a0b1e07120c11131a06040f030b250806010f23030c07060606050a0e22090f05010509150609040206030408031f03080a03150f 67
    0x80c0110b00400e80d03610141c0007998005044014500da144079603e90700f801d11500502b50f410404483c804500500f520168111082c6136401544829403800d03080c015150640c40301e400383d030b8907094075100589980d59031415120180c0343e0700c3d00041c00115002070014504c9070040c0710780210800c11040c406034016940c10811a5030107104144a603480080c0c100602c1e000e40c403aa046210900305688035150403580061088400f0f99034101149040101182c0011b40c0400500d03210070305076030612200001000840e0f01000380035036140383c003210f6943d04084880701e40c403480000e600030074406209030303000d040f00e200380c14100d400c0c013410781c40c58584a02c13480210141a81243d03584607428100010200e400704243d4200b03000300218507040c0c84158417807078800c3c640310b80b040d5940005010362400400701400340350094030b0310341143e0f920750356450340b0340c0041d050001c9410710740611a410000303042c000001e54411540f03191201c0d402c0401400f5030b2690f207900705c1e100103018000d1240d12000203412007 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 861364685 1250 861363435 861363469
    0x1050a0608011a27010f0c0803011403030912012a140d090209011e1e062106180e061317040b040e1501020607021023040b07030614 58
    0x3801500f81c480c990542c030400101d801644500d20900c1c02164200350603494010084c2c03204803a22000c0981251031000c0100d00a104120a10051003449080303203c00e4084c03003014003228a40011440001c00c0e400c201d03040d8481c642c1d110303d1214440300010006010210301c0710742c80c0c0740d040404030300036250207410718140b252400041494000002e882c8c11070312110742c0103000e00e40d071542c4a0240128001e01e0f000d29821549403410005000000707104880000031081565800ea0b5081c480106c80e12440701d01d0f08900b40c903504904044000d018410070300106100d03940c15401c0d070030074041081512032140036451203410141c200810340031502401202c0640c051640c0340103804280300c01409008640142c6648400410b000c69100c0c1900800d070f0181700d456107175440e440c4000004903524002206d080006820040111030941d0780303a0030510780780644006004000001d0044d090036400c08550550ba4808003500f803002d1070350144510f8007e081d1090200003e003960307802240001c490072403455 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 861365935 1250 861364685 861364709
    0x60512030712301d03070816050706050c010b0405091b0109150305060f12072108030916080c012003121303030e0c0d02040902010311160b01050a060801 67
    0x85030184940d01108004506000b100600d051012009043d04591018208a145006065210403070020003000020580500562400d400e0741e41e00d11647d04080c01a1501c02101c4050100041050001e10041c2c061079465680b54910f583c0300c3d0382996180023203580168036141c00e0010004010a0300d031314130340c55a41091407620354800100d031010415444a400c1424100c120b80400d5410303084240141800c44051404c804880c0030045000803032400d06004e5442903c04100880c20a8100d050150240c908051144100d44510b0041c0d48100c9000d40302d0f401c80744100c40f03c51001040003001d00520001801040c0400c00081c01009000e065002000b942e02c91920710f074003040003155272800074060342040d181040c0300044001d42041008402080c1405000809500300181918865000401c0004c003016550203010042c00500016170406454500b240380402d01300b00140b903c0305001115000c010380740e0a061074049410f1b00140e01c608100340003081303101e50240820f81520b1000c102a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 861367185 1250 861365935 861365963
    0x60a030c0b03190f0c090b0406050a20070902220e01140d0c0602070e0a050f04110310090c2102100503180a0f03120504020d03030f09080c0708010605120307 69
    0x1581440c2280d15843d00d024204100c41c1004803d0341c00011000c8010b4403441c41b91a151281c0400c9401a4081c28000070018050703030000501c140071850300306404c11070f05a0603170355102c122400c1000b0f540017080240d800089243d1510500c40600d0301d00d55124200384a11030411403002c800c400c2c10320039901c480c00c494801072116a56048414080340e801110304154580c1c4000194580c0d6080c031850a240a03228001082c1c50154001c940c401c44248812007038558843ea1100381d0b01c81c0c1024281d806115400c29201d4411552094055040c00b854150080700d10b07001000c000c081e000c1401c401c00070070b4104138200684810880003200080760818075200c0d03407000c180140d103c2e0b03600d850301e00d02d01c03642e01c1140c14844d0041c041c440b07140c0640e07216012880010000001d032001a40c009400078070032050b0001081c401d51099013804800c40000c500810b080d1100300b065040200040b42d40d402c014400c0101c05024070418005000c01d60700e1800c42d51280070190348900411401401d2944034150f0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 861368435 1250 861367185 861367201
    0xb0901051908030c0601140102161806030b1003060e0a0c0e09030708070f06050a140403030c090b0408070f1203120f09020603070507051506030304030303020c161508060a030c0b03 79
    0x100c540034008400c1240d44542c0d65004c4e940e0f13540c00030300c80d070a440d07515080301007520352010851000b070b1828401040c004600d07245007107015200040c40881200ea50f0080840010f40032102580540c0d001c4400501060550400f8021a14a03810707049041d4010f20b030b043c0001c1d900c550450701325804c0030860200b9035034009000c1d08512a440c8006c28138940000c0220800c40a01da8461019024003401c120590350f51600d00c0864180400046c84644044001000a4820b401040303200e45140780030503002e540d407180c1846640154000041c2038000120070322440700701078096002030030346262840b14601c1d00c1e02c016161640701c0b00e42c0c1e0042501d900c0304604060164000081c0e0903400303010075a0324a050f03800245180c005800c01c80c1c1c40d0040c050140d0607a0851100e46001e0f64000340514509480c558050700258040304480080380140c00b00c1d508120050764031513000300104040c4050f0f03502d40c070000905c0018000e1a05114903500311050001c624510b02400580c1c01800590717945c0d40391200 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 861369685 1250 861368435 861368479
    0x11715090114041b050d11040e010608012d0c05030c0c1f0906051b2505030403030206070906110705090403021e28020d030e01092c09010b090105 64
    0x909810240300701800204080c1e560410400c294150aa8240a81780d0080044010a91601034200c01420081c03000c9840d007984080c039054502400050590350701c4155600f07480781e2043c4d00e9130b400810300d07070021149001e00e02c9144d0444500020003901d0700600740504180000741c00b10192080101d200c559025082142c0d1040301902c01000419031580140100907104841007150000e0030180405d03900d80c15800d80c10313a0000d04140b418106003090080d040e164400951200c0c0380456885140c4c0440e4041c00100040d50080e80507018606e000300c40500782010940c030030000c00042c1c01c281c0701004000714101d0b0903140c048481c01400e44403410308074a401c070b980031040090041c030390410701040030014401141c06608411000e06c0c11550920a00318445c00c0006074020024102d01070001b480380d61100011001410102c541944500d40040c04640324044090300601d4a41000c00b2005481002d9030301000c0e41c0d000f4040807a280c0007040720302c00113114450040b03400034044101d08440342 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 861370935 1250 861369685 861369701
    0x3050c0105012303060402090109050a11070809011704030903030818011e0c02010614040c0c0f03020a051203044103270603070f02160e06090117150901 67
    0x44001d200958503400c0c00c410481c0c0000b00401c2010303681550f1070441c200800c8052040340c00400241032a840d103802c11018000081c0518045555815801c03402440740b0060705001c0d020f214020b46443d02d0200162982038450014180300001d00d04010000c3d60150080c0700b81c035030524007052140c542064500100c2440001c06000b542403200c0c182412909648200101d202e414040c81451500e44d003ea0803640e26000d08002e00c4001c40400070141059044000391040c5490150006032903515460b10464100500f2401a00040c410f00140721f81003014140704d80070310440a15508040d0340d44546083c8010014001e9041d011918165407064279408940c00c6150901100303994805102076120740c00034003a42200c0806100c55445440445a403000c00840904082d15541750b500d000e41f0030706c030611042d03800c520030900c00c50188070b0084d010f207004000301103900c600c5080c814100040020141c0040d030121050a550403502036001500c1040d905003040f408205803070b15110342d40501401 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 861372185 1250 861370935 861370957
    0x405031b0406031a040c0f082e020301060504031403030121060b21011d0d050d090236090d03110c0601030c0f0b0c21070b010b03150603011a070305 65
    0x103510b407041405080290f0300c40c5104001b5000050745500800d00e070003007140220341c49580200961071711010500c0000d030210101800c107012030405510020160380c000d13007004000490201d4100200046190b800c111900200c0c05103081d5070600084245d00460216602d0103144903100481c140300a84c0d12101403500c02400d8201e50441101d41070040100001d010b0916618010000c00079900e040c1400411031134400207440c40c030441c940110340310340040156020482e5180398150050359a0640c0c041c49041d59013041c00f0319000001000d80c0301e000f035820181c16004d84400c0280c0e1940119182004504030700300022141c09100d440302c07031030050214180d164070942001205100c1d00405000403503000880c0b250101c0e84a20382d08000b405603154503d480e03404903d21a8101910110708a0580c280720246404c0003001c2c1c0300e0300c01c03d010a80c80710784004e00000a121052060a0000e01c0302c2c0c10541c3c00e41d146501d080703031055000350000d01e55a103116010400ea0200361180e07045803030b0240c0c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 861373435 1250 861372185 861372203
    0x105070206070e0910030305130b0a02160510080f280501080f03040f0e06011101091b051e0904060e0f06061c080313050705060f1e0405031b040603 65
    0x1442000c1e585120075a00240407810350080340080340340480080d48100c00c0090140304907841c1d40c2d4150b40720f07006041e0031027100d1340e5090049001c00c4c814020306107000032540101301c07407a410311588080307554075040700d4019903440d1480300040780c00038400d94011001c00305e20390003580e5122400b030342141d0407019080480329242d038504400c80990440c5058410030800e80c5c1c42c034020741d1001ca07a00d101d584500d1030b00b01d485680c2084245118002182c2c40301060400c1580742614105035030868a46c2a021620300400c20140340580c8445282000501000d0305d24118440080e80c0c2c0c06400c42c2c80421ba06d00c221054000281004525000136421540340e070b080b00d04010081d8200f6803a4001181d03494082c21200045100141c40700c500c1c10511600f1170030861860719141074050314003200e0481681d02e4411b103400040e094640800030038503d4018420f4544034040d880304840f244001d822890f50208040c0710502c4207503008640e101c24603404110420741c4804010100d005814564006072040341 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 861374685 1250 861373435 861373441
    0x20f1c060209030106080601060f0f020c0d1a070504050d0b040f140303090f03031501030b0f100215092113030f0803010305010b0109140d05010f0c21090818060c0105 73
    0x1140c002c0c04070301c80b0840c0280026030300c442e10240d507101d0902c110400188040582140240105101130306d41c00507106403541513900502064103403080150442e10258001c100601305507403540007a8000c4014a8004d24180c940000510000810000030780307601c040790085020404d400d01850b41c03ca621542044400b4101c884645d142c0c1c1084811721210f005411a011081402001b16845442d0a120ba4200d00481500460051110710000c64201d840070b4809501c40d960340e44c5540c000a00b560081030070b05800801c605600308060038130001640081806c035030510000ca09125400d402d200ca01c1d0311030302c64694104803116142d0001c0d0490380300b0303101d0f40c0c1403006150007141a0b07030007040244400f100745801161800041e1017450f01c0004509004030891a0042802000e640240c00100b4980d003154900d004403800d906282012448284001c1c200c0248126100040e003080d070300c00c10a039115511100c0f8640319403410300c071700c1011106200c0180d5071050140d600252201008010360b02e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 861375935 1250 861374685 861374693
    0x90c050903062701020702090406020705100e0c0a12020303071101090306140703270212030c100605030606190e1335160f0303020405120a02090a0b0607020f1c 70
    0x181c0252202c442c2e0740542d05601c80c2c43c00050084912465010b4001c00c0710b84d40ea602d585000b90010003003101e01c2d0140e01a201c076180540d010303071068506410040c02400b55140c02300304548409900c40720007601d20005520140c2d4010084d501072981181d0501062851040100c50542003504000c203010f01d0611441c1310b241490043e21b100d03c106032010008000b00b02c2c0b01d1950503001160445c002c0307071800141401801c08845550705005d1810869007081e0f0314200c094145440c0c01a007140c200d9a80c201044245000c010b5148c2001c4162840c000c00c000d40600d142c16103809004002481090201098580a5212800c4ac1007074010680300000e605401c00d01200c101ea10001003000394131384107600b00001814080740e000d1174031207800340340c480740c0307640d810000301c1010105505043c1c0c01d01c8005a66110810303050580f20420020344111071441c4108020424041d040d44c0c400c2e890b140c46000140c40d07850450300b02d607030129007510048091200180d00c605800f41840003011a400c4440204 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 861377185 1250 861375935 861375961
    0x90209010306060819080904151208031e25020a08030f06030d0306121b080105040b09120304020a030f0c240905124605210301090c05090306 62
    0x3591280c426107500c2130300b41243c400c05071034018029205881c20890411f1a10f0554096000000c4426807181c1d81035545004002c4110500e0054449040000400182d904419040402c081183c9006145400c0c0004c401403d6400c4403295400c1030024100b084007a40200492944282d01c0f50b0b143e5507030702c2c001020312206103040d11068024070a03010324116190090080764251030640500725a0072001e911825481c407403200011141840315040440c03041c001303000b09481a0b000e0b000d03440311805e0045105240c100d0b0210700003501d40040c01032100503a2200e0942044030b8201300070700095030540c240508a00c030b85912450f40001e03d0000f1100d00070380c142d4200c41d28101a05c4488559a6540600c0040540041740344240e804c4809490004200c42443c1c0024243c6c5000d00d103a51042c0000d40703d003c1650594800703c40200807200004c0210800400901c00040031095002c02c0318682407400030301060080011450712907200b41443d038400e01c141c43c0c280c1c0340141102d2245c10300100d20146 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 861378435 1250 861377185 861377189
    0xc1401020f0a090509070c020303030a021b0d05041e05150702120f0601060e01080415020f0d110702130c0807050c0f150603062202100c020415080d030b0f120109020901030606 77
    0x181d070170b500000340300c0c0b4002c8031140041900a0042c525565034001c550000750300c9818400060304ea41c111261046c28100b1400000da26141c07505551541410111108030040a0078448030f40c0c4100c40600907915071060140e201503007152469240c920360700c000ac080240d501c154000314840e002100050220000c0d145040b600303039450f16000e1442d500c00454400400325170292200110440d24441284158010b080106040c041b8608101c021440401a194120414156224045480f500758504a400c01d00700384131401003004140340013039015004d0f060081c000380a010020681e5600000e090007041224441e60342a16183c41c8006a000014002902d00764024450440055421170001d80111401600c10901100c1a8190b03800c00056500d4a00340304200000c0c00c02240050f16a03004440800045410b005c030340e42d04001703c1034a040040c19600041504014400740c00d511100e44600950209440100029003826041c0c1d015201ca000003c1d00104d40c00f00000070700c001503005d41c0c2 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 861379685 1250 861378435 861378439
    0x60402010f170f0705130305030324090604050c09150d181707021f020604060c020102190c0618050610060305010b0301050405100b04080304170d0c1401020f0a0905 72
    0x50410628604966401e24203005003401d03490003002c200f11081c0808501d0f44540b06103012403500d042d00510b01050382d0319a200b12140c2e030020040c450b2145030b80050551541c2d4046d07003018800e0b00180000d1102c2d00180086000c6d50303880c004901d0b0784030039004958260700302402c1e4100d904007001040601e03902c05589010464a00b000384042c60f10410000084550891044c0040c1c020b0b5030420340c880c0d40260300407640491b01c0481c44c80d1320204400107581c450f0498001d84028502400d00506840000c103800d004c5910400c9241d03988070700411290346105580ca82003c0b100114602200100a140310116401d2a18071805041243c0000c2c0705104031482c2603402c0310595289000d906848081c014200300110503c018040c1d401c0c42c3d0b04c00355000024642e48440341d940c852207042c16074020b40210140d03420014007405a41c29029913480001c21034002403441b41d10000d0000d2040f0028080240019110100300b03228002c01d40542e506560890b40260342c541d650040074010091070700ca00780c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 861380935 1250 861379685 861379697
    0x30c0605040513060b04050108090a0b0f01050108070903170c0f031201030c21080d09020a0b220509010603020c1609021207020a050a030f1823030d0207090c090b0c06040201 76
    0xf81214034501984044407641038001d4101410000103403822500213110540c50300c038580320580031171210360140d0301402e440642d482c40c950425000408501c802003004051210140003000044d04c00c114019018010122542d20350080d60754030f50502c0709045084060340300104089510959585a0b913040728410100c1240a40e079a144420141c064054500f103841d9600030000045404c040050068007003040c00062000c1155000644000c40c1d074000b9043c1c048040f9004011135504d6410300c4404144180b095201860f0100240901405001e0941059004a8604001c3c0010040800d1400300d60340c1f48041c0c151910381d4400290010b0608a00d0810ba4501155901c0c1c004a0144500340d0020b001e0241013110b038805594031443d92044804200c00010100c442c1c0c01d00c81c566401070841d1541d002c2d10b210744031884030786140d08940d847c1d1103900100d030701d07030340c11900091013030f089642d00e030303c08140039880c00000c0d54296400e501500310700d80005241180f40401040c4144100d100741c07114 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 861382185 1250 861380935 861380959
    0x4050d1110090e04060207060b06120415090b150d0c060302070611070f030c0203070f08065a0a0902010212030c04170a05030a050309060124050c07030c06050405 71
    0x72140b0140611426141c0e4030041c3c0890041900c9400511000b40222800304407111144013013080c036441030035801d070320400540500003000800403124425010341c21082c0552217582d100c80e4151040070b000ca09083d50b030349400f6040c98440161203614150802050b000050742e544014010354458601250716518140400307500c1039020040d134040940150700303d51143c03400e94090b5042d031601501a03a00d4030400340000b803400d0610710010080d00c46030f80605120b040419180d040d100b4050700566100c28880c00c0218178940b42c034045140328802d407165221008103207415040c800d15403a000e401400c2d4880402c0039040340350f0009200580b00b81d00f20f44080f01c95055002d054001510075805043c0100f1040041c1c01500585000068a05059034000c0000703a9605207907030701c0f42840c94085103000c004c000c485002030040030300521541c21484071140700965040f520703c65100003503040c0301001c50074035560752040245101071940103d446682c6605c50030094103507005031040350312482615440c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 861383435 1250 861382185 861382187
    0x120e061f1e0e0a06030501050c04050a1409070c060b04060617151c0201050f070c1e03030203070201050c1c02030d0e070b1b0312040f020a080a0c03021504050d1110 72
    0x186411004404030200881c102000849075107000b404584030f40d91180d0300070020403c01e00c1001e01441c0304c0b070381c419070b100c0c901814800003640744d500440343d03400d004c01c40351f02c1350b120707000f40170392101191401c24003002c064904040103084504103035821a280076404100c19030800000c40c200070002403201500e03a240b0a440141c0c0a0090110781c0010411452090188680070380781003240c0b05042c49400c061040300b4000032a0890b02d815a5811301640003001082d0102c2c050601e481002da0143c0d01c05429a14003960364841c11900030304000d070004803455031043c2806200181881801d20301e194031501d40700207660783c0201039144540d078a00010380c0100500000d000040742ea105a040d402d06010003030301464400c40794000510303400b0030440b205100c1c41e90280c3c0da10a51155040840b081514010f000031445603421260343c80c3d02000c0d0800205104140143c1143d0b8115071400d502e1503003114180c158051035001c10380103560404420300b00030100e8209100c043c0e040d00c8214010307182d0b0704 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 861384685 1250 861383435 861383459
    0x606091107030f0e030325170a1407080d0207060b01030c0306080718140109090c0e040b041b0b07030203031f0308071203111b060c030610120e061f 65
    0x40003000301d1145072030001c0310f034014400c3c40b49116005003528101015001200b141018000c2c0040c4030580010746842006408080282520110701026080904071b5402030482503145010009407600400c85408001c24802115981300180c00159264103ca240000261210310f4620340424103158140c51000d00c24421042201c800000a084c11403a041c040300c13100c0742d00c8400c95109904e40000e080d1b50b40c540141940200760340100014028144d04005407141101d07000311180c07013149005d11001c83c0c1d6012101d900147c2105070780c110b00140e100b42903000122580503120030240440c20f2824142c010002e5407180c002d100f09005801241526000e4400303d6010082c42d0901c00d11080b03020804160082240d04c409050029005104074074001641c0c01802032007010f910460100c0844070740a1208541010400344040d0440c1006170001d49490540d00b804000c0020580e2041d0914005401480c600c0b0202d209660700d504004500840b002004101e450700740e40c4003240040c5103000c0703a03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 861385935 1250 861384685 861384697
    0x108010905060d0807020604030b010807080d08010e1518070c1a07051911070f0311012c06090d050a03080117060106110c1003021b0111030606031305030706060911 72
    0x24480e15983d0410341d1880c0c0103403c000300503a080700301880044001071100300410f01800c50600148451803410660a103440341021100b800c004170040100458015040340503040b50641c40c020000901c0c10020900414407400e64410003034000f01813201440d00940c1600410b8001c2210801c0721a03540c0704000020000d42e0030b103002410400c5082e405008601c2941000400c91a001e4110410008182e02d1f100c080d8100041002c92100c1c100f0820014281100c080c07032003805d040640e5448140e04101c81d40303820b55503070320389100e0500c1800c00c0d5954504655000c04000c2403c03c441d0950b040850b650010144101e0208081d00b00100d14804207e400d441c01f602e41c24010b146076820714000316807600d41c4680000180c4140806010117503a03215440d40200001d030390040c0c5800f101e03d0341c0d04c0b10759241039840303056074506030080e0404861041126803001041d5800c90f6a5215421007211104070840003908500000c0703a24020050540c103c3c008898409c001407083d61809100020300d40720745 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 861387185 1250 861385935 861385939
    0x12060e1051080136020f040507030e0604081308071404020d1803022104030503120903070507080115060e220b3006090303072f010902010801090506 65
    0x124910700010311400c80302400048024a90012a548094880c251401041c0725031512052204804030741c0d40540032140200451058089412402e40110790500b6038241141c1c050b40d03c2d18001912540640c0110f107010481c00c040314280d243c60308000403d07400842d200d036080310003180c1c0000c10701000190344055070942401c0c50140080310003004000e51103843c0c03428400340c507019822004541c881121450038083c3e0041d100c90600298940901c0b0103002c66500e1010090206101150001050303c842072030050f044c00302915912a031500d14090504018003e106241e808150090190044d402001c0308945802019485072400d03200030100c298500d410123010001848042d20304155071419a00406001480032420800706040d21851111604100611008040108450006400480064000303070625050001e140c0d5280d110181c05003080003071140c0103481c441c0e07601054841d01c407410001c43da2407048049a09002c0d00300200c090340800c032402c000003000e0b0341c0c1e4082e441c41004c1c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 861388435 1250 861387185 861387281
    0xa0f05010b041404180305030a050c0c0c011116031a07080712180206030c09030606120307121e030b010f020a030207050d080408011802031204030c12060e10 69
    0x404100074550f1102c52407450303005849040321204824080280345103140240d0707c1596a19003085e0f0801610405800301d0303020501000740081442002c1001c00b1140000d2070040401c0c47c10380c3ca80303481c2121082d90030707000c8180410004200050100c40c64424290781c10aa0125038407a001944c1155048079010081f51101d09011030b0568142c1c8040701000940b140c030024500180c0114400303810842c1d00504d0104001580360191a0030040c05030700c030808075215181d848080004688030300030100b00800780c804075001c4c040300c5402401c4200710301c50f21650700c40904807001c50080140102d040710a01061200f102d42265910204880240580503001002058501428000c070300800801c2528001010300c0003059003c820f0089021150400c402611072910030300406050003440100d01090388001c005c100300041440d0030540407030380002c208003c0c11405040c124081c001c81001c0f04203500902000c01000f070ba00d984940c510903c0c01504201a00a00413a0078003200914034100c0d01e450 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 861389685 1250 861388435 861388439
    0x80a08040507090e0606100512040c0531050709030629030d1707051c050403171b0d020f030f0709060329041d0d1b030c060b1c0b0a0f05010b04 63
    0x1f481d0b0381c0c05c0c00713985441c580780b8540b40c00c0300104150b0071400d0f1400c980380980078800300800c1c034141c002400750b6815480c20404030b25220b0f9840a41806001e1042ca850343c0f18000110315501500056006540021041c0300d48003105600000c2c1c000d44021884c03510314003a40031891401c0c005031410102247d40c40d0a540b800b01d084145450076802040c2408015081018022003224400d03001c14004140300c0100d100e050900d400341403050440d40c0366081080403070410000e03180e00710400f103210b160006800d56500c5102c035181c000c0c1c4a5448554a504000800d01c1141030401c8006441a007050761403100083d241d2804805540400c00740c040c408000d80024840c40c0396241030f090f420702c4000c0000642e0400d070010551105000060030440380c00403030000381d03000d81103000549001500c41d03d049521200b560080d01c2944030040141c4050f070303200040ca56546078048400074035910710f80c2e10390035a45ca92621500e40c0034129118694282000b1740300c60204014010181640c542c0c801070f07801c2074 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 861390935 1250 861389685 861389689
    0x3210501051e03070503100e10020717180d0807060c1803020906120f1b1005040905070c020a0b040302030111030411090c040308120a0b030f0d1b080a08040507090e0606 74
    0x4144801c05500d4003698600241707654040107010341c00501c40134081041286440c110f418100302414080384240104041c00004110100d03108100c40104e8207144c681c4000c010001c2100700380300c5810341090541c1d240b801840042c82c042c016541c801c66061040c2441e065040b600c2c0b400086002600440b184804d000616054000b1359110202034092241080400500d502e0b00c04c3d02c07143d0300629000b10680345030408203030307681656988094441060401c08141300401c54421441788143c10b41c0e8810100d20502c0c810f249200794650010301501c11a900d80034010259881480b0880c4690320f08a00b000c5000001c605492240d600048081b4003170b2204018001c4040000b000540d1012081001000007804400640440da907d040341c1e04e514a0410310300800c850300344020a200750302401d0f406406240c00240800e0984662501c00c52a0000700c030b1060480c0381e2020028000d200100b4181c5004e980400c555200e240601e0480f11b0803651108100100c07131415885d03600707075000300001885034 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 861392185 1250 861390935 861390979
    0x41a0a050607050c0904030305011724060619020d021006080309121c1709010207051b060906030a050f13030c29040b0105010908010b2206030b040321050105 69
    0x250084099400340c9241e5000185d00d24000c440840229a0741c00060264030548100642c00d0180c0d900280105842100c400350701c1e45e03042106521a180000008030191644800da0305103920f075854941e2040901c10000e9222409007135100018842c9090406d24007401c1d018010440c0c9121000c1c5141085102c180b14030800100c18089252042d42c24860024034100d0520003d16015554174071030414840844102080190039588244c0c010310a04000c40e40100e0b54031046210020001007010301440460f070705004021055a0043e408410050441c0f50380d080103100e01e040401030000c95658400c0140110791003100680002c080a0b0303c1c02c0020044107002036030803141144a042c804170524945001502114101c481d905c038100100401c2d40c00114010107010404000d006000d0200041010080c512000c42504620b01c4516201c2c1229070f03103c1c1b0049c41c0c00c505241c0301031909040c0900610a148418072590380a1075044611040c00c1c8610b6068420003880a03041c94185020a450 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 861393435 1250 861392185 861392197
    0x50c0915160c171203160c0309080f060a0e0f120306130608010f0f2904060308121909080f03100e18010509011a190f0603020405041a0a0506 62
    0x44040308600c1a00400c1580c2c0e034200061004070255415540c0141c4040e080120314a410068542c00b0710a00c10800d101246a80b800c60b601d19000e81c110f10b4509046036444182e5001c50384a010b50710102c2c048580104400780b003031218040a0018940d010b9142d6540c68101c03444000c146c00240010300005400300045410840040c00804001c2c2410741010480c2c1e15940711590aa5685894007000c500c1e0380a6007400d500e49050801c003800128003003092030301124241d41e00b0400055442c3c10565110f0b4084005140c100c4d40c801e03114054500050503941d02035961001280f21020f01c4581d1040b02d00078209200c0c0d1040300c41c0c0c00c0008040f0290450341018200146001e0400c0303022808199030300103244a034003060b0741d00f03414030300715668075003100c83c003820403001a410202304240181c482019692981419a401d48150000708213211307141129070000b01d03540d8010600056495816009071007680c2c0c1c1143c0400102c8080c0304072807803811503018050342250741460200000d00d082c07009848 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 861394685 1250 861393435 861393457
    0x70303140c01022b1a0d081201080d171509151329091303120c0c060e0f0c040c05070b01030c090b030303010b0313030c050619050c0915 60
    0x400d0426007602107003640c000b00044004409401003a21000d80c01c00c81120070101126001c0080b10a03086040d100a42092401c602461520a41c1c1e800c1010080c01c860142103580c010489079612400301f00d4494402049213000203160084c1c0802409081d40d60070702603603402604201d011040c005212208038014141c46e402c5103c0280e8006c191038111400858000d081400608c5240b45a0b9945000002c10040402201107652421603500c500c401c268101101842e052505100b6140448048801e6641400030500b80410a903d081d008150302000703920801042c4203103058103000d03a40c0c403440a03200c252594004a4041000d003810361128060045500d0300610703000b42c540781c01c6041202070340110f13101403106004114000b054032480d03070808820cc000d5899545059500100c90001070700404d00711990b5a07040d0300300350049864105503940403094449500e0480550724000c0c4065244800ca103041100107031581d40c0d010100c406101c4024100c00360380c005081c0042d029001a28454 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 861395935 1250 861394685 861394687
    0x5040905040c0b0c0601051e0a030807141b030c0409030c030f2307020301060603060b0d0b06090406080a02040e010e070603091a01150908070609030204020c010617010222060207030314 81
    0x442c2d8110000d0080503041c84c0d86000304255454181800360308044d41c00c0c0812080c0320980040e50700d41d0340301000f40c100c0303801101043c2c86952900340b240d20748022482e10905440750703041d1009540512011000c0e0180c0407005e036403004200030706100c240c2d41c8540005001a500b4401403000a0003164240c040d04c0a625048641015400c881c80249450040300c80241c41c010a89108525090184a01800140c6014031803e40f03040a01140390150a081030861911950030492584440084d10741240c80100140a01507031340910b262580d5681074260b019900703008141c00c141c9414015001404020001800414071b490800c400030914044229458244003600100805121034003602810040d5214070034449003c0019100041c2903000090a41140714200000783d005604102100e4044d0781c0566102070040c0018018581e940100c255009800803858034a00158060003840345440003c040e511451104640c01d88400d200710401a03210400a00009219070300243c031050006a2072 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 861397185 1250 861395935 861395939
    0x612020301030b272a060a081306021e1b0d0806010f031407050405090f060306010302040c050d06030326010b1617120f010b07020a03022b08030a05010b0a05040905040c 74
    0x18034101180708200d1809030f1180c03d1039844542c0300500c03071240040301b12541c2c4d24050900c40040d248410041c41d00303000c3c04034403600405005554049a603c0d00204846804140d480d8003a260b4613003140b800d0403101ca4021038062101c0400041000a94907941c80d01c03100c940d1020011512000180e4120041503202c1b038a010104039442000b50141d0340350340714107444506043c18001d038400d0090003051a11001c0091200341d460204405041d0794050300c000c60301c0700521000790b0f00d44c419103040780070561800c54000103050b48814000e014207505405145455441c1204000601c3c003801484519542042070300300041c040007003240d070340e44034a01d46882400d0406101c0d00ca9003103604841c0c0d106186508003d1503c21440380ca5024090003142d150501c000c81d000304640c4041070100074010380c4c500000a088a440031302501840c404190041d100c2d4280c1d28000000e03030030944032a240c940c03d05c3d0012401c500e0820580b401c454450352600d0a1030710b02150b00021300710150054400260000780 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 861398435 1250 861397185 861397261
    0x10f08360109110117160309080a020a1e020f0402030a0615110d0809060601080702011d010e0c0301060605030411010e12061501021f05190903090612020301030b 71
    0xd229001565000018585070078101a180b203019015514108030f42000c49100c0011003160307190700070700c5062801c91200484002540144114603015040b6100031407140b0341d0030f60019030482c149104010000b01140c0c991401c4c02c00f842d00d04170096000e40e9001c5074004904055000d598085c690210101c0d0003503641403010344003001c840c8200d001440724031201c1c81039002082000c45044c1545458052841c0818440fa2666000b44c00c0300e04010b8a44040b034607a82c403d42002810700703201901028100c00002c20b0038020802c500101525008440d10b286440c075040c4685d41c00c4038003d440c0c00786196520b035501c0c9201c100046106041c0041030049900303075203620a40050321003241b0014601410084c08540a100e59101079034119840107543c0c510f20014802078820740034484102186913190480d13030401030b442d20800b03c006685005540800c0c541c7c08901c940403074009840d828002c142c0701b06110181e01c4240405072507052075402161000743c140c0c500400321042495202c0d030022547c04 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 861399685 1250 861398435 861398521
    0x507152016030f0b0114060403062a0e0103050f0121080c150f0604060b0a1b1509031e0c02092802040510020c030a0308090a0b01091a010f08 62
    0x9952034401103003182c0c10071259613002d50152106544035884203200c280024401d1040c0d010090005071100f1240e294808030020003140002802a140c810b8130003588001c00e0014038000c51070000b414140422903000b90030350000e050741da00c1362246201315412500301c070410a4042c01112040c0b01008001c864103414001c19140c4010241e002d0264100903440c1c0500c044007515080c0f00d103140610410241c030404003225088445420441c50981c0c0400920410a04071070010300ba526464507903541000d15039128150291117a11080104100048107910264480c0358072804140d01c5400003016150000500d503002c0c0021740c03041d14101c266580045c03a48134100ca0f9040c420340100b018001d51600e5000c0e1040b8903600e03c01040461203040c006651f5131800d8030041d044c0216000856040e032414400c0412140c0c008011064039656140b90b10f0080925000300c01c02c800e910985a420b56110b00482c008405803551500c03081e0300c5a806410740107050a41c0b092540c04584080c8401e503400712 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 861400935 1250 861399685 861399689
    0xf06031017030901110d202e0c0f0f0513150c050d030b0a05300303070e090420010302090d06140a0b0307060804020114040e040507152016 61
    0x24040c58480c11070b540090711500301210862580c0c1c200f045030303d189541c406481422040009078a1f0b03601c113481c0f070500c2d0a206210a241560084052603206003111410b400c0c11028074281042000c84007a450465580200307441c1c120024000d0302c680144030348030300701414262003880b6540c51101c0e81c903148040308404110701580450500310816003480750901410001007950b003028032200c180240000c80c0040b0b02d000e0a480b9a01c0d80c040034151002d984880240030402c02c00384030a8201c040103541e45d90700308a601c40d0000d200885021142d040051f0303910f0055620101a100310038492502c40e541184224040b810168284100d403829521a00d0348130203a4010980051b0443c4030451900407544020710b900d42140c204442d28109031000140481200c4803032500c0d4407a51078500c01210900e4010a00c0d000b00b140200b0040385000c810f4503d04d0295200f00d0440b0011a91080080526024420602c0101c2e6140c402d0f00c82e244840400881489540300a5941c1c1c2240704010201040c2c480d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 861402185 1250 861400935 861400979
    0x306230712051807030201230f0c071a07020609010c08030a020d05010b0a020c01080942040c0510090506041d0903040e0a0f0b030601082a0f060310 65
    0x180d1031140001000d1062a8101039860070207241035140d06102a40d4801074400241046101c1c90a001800040d1440310315a05c3c0c04a43c2303540e12080220600400e400502c0815424043d0f40e40014142c100500a001d524048c2ea040c2810035001c5c1d0200300040c0c00031000581440387d010796450000e0040780086115060404c00141c640403c2001d181c210b48058002514031a420440d416007107400040c1c0510f241ca09281089a503603644208500740905104030003000d0b80089264491402281c0118190300b2108000c01508680e9824600c1c0300c0000b558041c000f034006020a00040c10410301d5031b032644046080c041c482d59038a402040c140da00c02d0713102040e02d015071103580c894518403818007600b0048580042d4240360418049150300703c005030600805540e100c00d13941910103e42c102041c05440103003070703400540e5201b15080d01d4413503042d200d6249140703460f8103111700d244043c2000585207005e4801001580048184103841d03001401d40300d4182c01c042400600c1040d0141c9440314102c1c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 861403435 1250 861402185 861402197
    0x15051e060d120f030c0e0901030f03090905010b04150c021e060c06090a030f020706090612180614060402040e0c090d140c0a050105030108031624050f09060105060403062307 76
    0x4203c400504813410100314600b045007003e2003039869900c0f140c1c9107040d640c2101c1411006621072605036106a40c542c004503181341081c0001500b022800d016004890100d801214a0200ca6400b100d02c0b00f00140029031044a885c3c142048c5041e8480d01059903001825042c07600400d0381900d40340c580304a4410031142d02130048001010b80c44240c01da0b02030003d000510402d401d0445c0900001964001c0104020b0b400c0d210700540704668100c14a05e80d107d41c0c2c4400c90708241d040c4003001d01030075a404842d0300c01e90300102e11181003500c220390803120307041d4820394640c0b50140e02007902d60085180903070105001102c10041852107540d0811500407000902c04074826034103100d41d03482240c0c4503505014041c40100700c01d44000c0f044401d4203042c4c0c0801028404185000d03c802da40d1410fa100d000184102c000c00c2080c0664030007805019a00703604c0015a40f42108542e80360024007034a50880b0301800100002511600922481840b504080d0020100d90002030036011044600d1000118 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 861404685 1250 861403435 861403457
    0x303190b061615020f0d2406020318121b0d060212011505030402091302130c0909051332010f020304110901030c270204080a15051e060d12 61
    0x1003e0101c01141e14607000b03040d070520710f05e80700c20581030007040360f0100c0198503824200c1d4508240fa801525080b140400901403030b8441700001d50300c0d0880c40f24945110090807002e9440c1c0743c4280c1c40a0410301001c02400d0a403102c42c18410752400003030000da0451244407ca800040e104e0000e4142000700c04002d451a6140210b002c40c040600180402401010420b000140e213919840070b40c0075048503141d094102c81480031a0801110b0203601869900d821002ca101c2c44e8054200740459001c1d071420703c4179071034160110f000e1440400380200316000107001304a031100c008004030382071f031844d20311260400940e403400341c01d4600405041c15100d03800010041000b401582e000350910342030721452a55810345d628646498980e00841070101048064807001e00482ca11420540b40300810035500c0b01c0c0d4840d1100d54031128107004454107070848500034000b85007880360314466400c4850b0088545400d001c041211400501201e421400800750a000301e40d0b0210800c0d00560b450742e525602403 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 861405935 1250 861404685 861404693
    0x804080d0c031706060d0b032109010311040807030b060109031401140a0b0d060509030d06031a0711030901120b03010c0924020a080a020703050a1b06090501020303190b0616 76
    0x181006006802042d91201480007a413520410348911a421440000c0c1104104c00003d1408208019015500d03011210150b209d500805c09000c02c0102a00d00f48400c00c2c005140860b140924003641f203040d0f01c50741c4c0410100d0340501343c030380c2c000e071060501c0c290392610382d02c5041003210703a003074841407c5e1f44803560b0300e145c5c440443e4101e1b4032501d003000070001c05d5030307804c0015582c2c110110080c1201d5240c10110320381d0303041442214400401180c0420100c0d40c0d9240c4000004450701a900d841c2c403110000441a9010300310145230380001401440c40c1c11350304001569514414907421520030b640d1f485025480d14244602840c3c01c0c1b09468a440d000d02c0d00107013010360240340c00c55228444044c1e072190002c07030300042c140400301c0c0d0042070140c0360501c0d103808078541f107003d91014126110303450205042c055201d55551030303801c3e200d02c0c0d0710304030b51078000986101e19a4807407580141d00802c00a00c4103404d103a41c40c2a0202186c0300400c0d0034107c900000d01582007440a40f049100d1500c4102c104 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 861407185 1250 861405935 861405947
    0xd0c060f0e0310112106030106090b010801030f1b090e1209010516020f0436020d0210110102040b04050a0e01140108040f020a1203020607090810090804080d0c03 71
    0x8555071070710028012030340780400d460f1510409010b0529880d000c018560320000c00684007001070445190b174003411380070400c907600101524554040d518003600410f191034070703000b2504078003010385860207280d203955502d01c180c40000d07405651102c0340c5040d800b45100d101c00c1d258002c010340c0a02140d01c01c043c08030f8a081a8840c0310707a43c0b104504110070010b69800c803096580f1948960041844040140040b81d0450f00d5103120a40c01413904d440c0c0b06040c1e80000000702c0841f903003292103526011207490803484058800c0c1c0030b07510000c40b4110500510b0300c40004100c40c14186444141010134102c06826a00190009102c00390041401d018030304100c5400001801300c3e038265034144d4540341c0f1a031100c1e034410302e285040120a070001401d10100e4449910300d2607010304101003140d80d4802452222032008400c030014001c100c00305480c4c0788100040029500d07000080c00383d4076403401901d002043c035050100c40000003444001098a020310000c0c802959548448030510070502d401000c03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 861408435 1250 861407185 861407207
    0x90a08160b1303080c090a0f060203030118020c06062806080601020d03020f0d05040f0c0308090f061201060e0a1a0309010606110309010c11030615040e010204030b0f10050d0c06 78
    0x71602c070702c0a40004281e2006a6580001003074000c0d0780c3d075003108004910015055000840e1000a502d00000e0b0300c1d90000046040360800f1800040e404804005030090344070707480d0b40510941c00200419541d06c0c00d0304062010b003d410004a10140c0b04015445003404540c0c011000f00301c0d8001042269601841080c205000c80c3c50218901480f585440410b805512681400035542d20001820031001c006100e980320780200c295100d66035a8074100006901003005a40940300410b40c0148505003413042c2c4490b000b0185030603c6582c00d10004a4201c0c0c3d8a0741040d5002e5613082700060341010208036043d071520300c3e40c10240d6a1800c0d1401600b0340d2025032010301000a021160983c0d50804002c2e100d4096091030400400714490030559031740010b00b00c1e031560502030501802640e4241c04040029548140c40c140324022040307016901b02c1c020303448042c1440a15000003040040d0700103060781d00418040b064006071f929600401e004a11500c2c084032104100d01d824400960080c2041d01 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 861409685 1250 861408435 861408451
    0xf01050601110303182a040f090302300403050715020a021503060103060b030c0a1806020d0c0c09060305030d0b0f150705010b04020c0c010306090506010512090a08160b 74
    0xb2501d401201155903403000a1050034400c1e9180c10b03242908406114003109860710a0a001c1001005082014409808451030340b045280c010004403d4017503016110700c068168020349001d044503c0ba80c040c03440b4110342010000103003c940040011703480c0c00b40010310b00400050002609041d469913800342c40d502c003a820765101340d410100595503540003103c0b10040c0c80303001e5242c0d1282030042c1d0140102c3d0304000c0710750001104200d500c5602c20084c01c0706180941c0c0f46551940c8048601d0400c8000f0300400e401600100b13100c0790301d40c0c01006120f6400e841b5907954a841e41da00c440c84811035135160011103031504001039845030004180202e80546c40d0440342d4652809403100000d815904003404403200440118422051050070361205ca48120050019907440070b00c240030319125804210864086840c1c40404101b4401921030144950f806840e00307860240448a41c600702040100348803074900c81d945624000403050009000d085251780307a0052108910b181040c0c040000801d851 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 861410935 1250 861409685 861409697
    0x1f0309170a0914090103140f0601031a100609060e1203030702010b01080f07020712020f0907080a060608160302220e010e0f090606130b030619061a0a05090f120f01050601 75
    0x1080d40c0d500706411781100da0020054240e0100c0070000c50404c0e80321881c05205000d080000018020100e5030070450352154002000b40d030340c2e4850f80031012030b038034000d82d0000f502c0e41209010071f5001e841c00240450008004c840c0c1c20702c03000c0f515455980103c0d19000103035100e43e2090311550300092002e07000300e9105144022464014070003943c03091139100749604500a04074120a544801102e405868000341c1384002c3d510f029507016001400698495801500d031002c0010b00d40d10402c0e03824050901c0e12158513030801d000204070003035005000d4000000e01030b01c0000b010485620180303001440030280100e288d40c582050100c080b8801881021a5515001000b26415000c203078180d02580444010306a100071041c42c40c0181103030203010b905071203650b040c0000341c038400c07a0003046040d51504c14440141c807020582102c041082e0701405040080c444a089140250050b210441c406404220740c81600f0000a0310224034848851540d080714a0641c1358104c00e00403164069130a003003031 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 861412185 1250 861410935 861410969
    0xf060f060f080a0e0a1101020d030603021507080c03030a0906153609140c0102010b180c0f07060c0f0302090d0f02030c0603160219021f0309170a09 65
    0x1034810304460119000700115440010004401c0b035014100c440645021200061710510f0300c04005011030350014050b1081500e0445128402d010b0b0900b40ea90142c900c054082060500c08003a8010345411501840c0c00e00c9420303202042000558070400301021b010480c1c25007410000101c0d500c0b0f080c1c40400002100c4280156540d079562040341d1070246907000d00080c2c1000052070b040810910751041c00d420014030a041c010f0220740d2105000f0700030181c498282c0701030010f9003224148c0e489941c104100d8884c2220105005150343e030b202d5680c031000c1749000d010307101e501d0b41a808081c048405603907076031110858540c800700a034000410790608618081032000007030b010300003084000704080360000000b011501c1c140710002d107416024200301d8803410200145900c00c07400748915001480340f08031699070011540c0d0100c90f025006444044203510415180c50240a004034104c113041e02d43d031003600081e1a0010421141c1c03d010310301502c6041d60b43c0002c0001c01c455000503001d403510700b00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 861413435 1250 861412185 861412187
    0x6010e06030715050901020f03040602070614043609030503180c0a0b09032a12030a0f111f02190c02062209090b0609010e040c0306050903090a08010f060f06 69
    0x3e1510b03145032070522a88035102000102c1c5031181480d140501c5001c045000240d03550006500001e0b50040c0d21601c04021812a5000741801103100e82550f02c8900003c05111103007081017402444003040046c098050780074a8281a104024000c0b8000b510001c100301514450350b40d005580a085400f82444a100ea00010424511070040420058000541c0f5103250380800c10808400700c88426650515a003e0041c41603516440700d0078000c0c5002000000d100030b01004803a400c01c003e403900307850706070501c20403a89105c95000d1003205119a03810014a4075112036210700700c803458000540d071801c140d80781120081c283c1900d0000e101010440d080142c0e0f07190159018100d482002e142d40035010b00e20f031800415158040121703503103049404c1050254440b0000d101c0e0805a81c01c02c11030760303611114242080111006040425644e006000188041c0c00c041e8000303c002007100d00700044c0100091119856a05c0406960356918a034500103c1c00d028841c014100f04800c051143e1170844 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 861414685 1250 861413435 861413459
    0xa08030f03240a05120f0613140a0c120618050c1003060b0429030901060608070c1e1511041403060c0706050601090f0b180901080a1709060c06010e060307 68
    0x944d403041c110180e82c486040030410444409440c10f00440300c05003000b00f40100c19a10160040d1030054403000d8040e82500005034400302a5448240c1901d030620b800c05510600005140031980c081c1ca500c021700052020b0013091400b02d000340c0241615040318400c200070728078482010390506040100c1004048100425981180e4504044451980a4141000c000c0b4401e011100020704003000344044080154004c200b0744585854203603d41c0c44481042c0c1d4403580d20b502c004e1050320301a44440c0f0980110324401031881c410010256844200c0c50108151080010702880354400130a08100c400309001030a580c040099024001c6803d100282c0029445083c0000d418581c40300081180c5134403441244c001400e0034280348001d107866107007030040b943c0303c0c01001c006885a0741058800b031600c560201e040390241801040c43c00e845a64010800740d10301842c000d001414000c0b12166240d060042c0904030708000500403c1d81400f00b654002d040c045d01e8507010360b105031401c2c4030705480c1d01 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 861415935 1250 861414685 861414689
    0x803071206050a0b0a05090307080d020f070b03130f060f0203150f04050405060f070905130e0f010510090903030b0603040c050109090b131a3003160f020a08030f03240a 74
    0x81b0b002d60350741035210b0100f45800100da0050900d40f20303046240401960100c2c01034802405801a5103d190741d40e003542140b40815180084910803c44a5800103541802d2865081e80b00f240d021641411943d0290f04a8004039a219441010781e80c00000e0342c0b0313010034540040b00d001c442c1040f1904090f01c0d0155100e030000c08120010203210003181c40c01d806529810010304008040c8450100301a500c58081c0081d1481b1411603c1180041820040d042c041c561003419030728500c184d0349140a8a00c009001000b20503024941c0e20b200010b090341b00e13000210701c1140109414040203180c03a00050124000da4000091586011417034040c960740c0c00c041c0f80d40001504408200f5440d50b01c841c250118103090b1551b48420b00d0304e404421209040c0d000001407408a40300c40042411080b01c944030310646401817042d40c1300030320030400100ca5403400d110190000d04500109601d0705a41403660703100b840c12180c1d2040100c00c115402c17803c030000118951081d00c9400c540c00d16880441c0c0300c08554 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 861417185 1250 861415935 861415937
    0x30b030f1b011b12030212011d060603280204060f2c0f0306040309060e0105072303161a01050a0e1b1909180c170406090803071206050a0b0a 62
    0x510f00d6016079000301c1c0c040343d00f103542000750064000820750f4003400030b5000714a01004000010000284403010840b40c210030a0300c60094001c0f542c50004010041d800103000c440b905002c2c3c1c24083c1724003900e4800c0c1c80e201551180061b5528103103031b005004c0c0b225000d8031070108034003a510a0215001e00343c01126024080c800050722000101c0090542104807656580500c503400401003815404900c0c0350460381c068882600e150514001152036100d1100d01a011074010040a858565a00d001c03002c805101c41c02c0c4d03810140d0440f80030802d000707620310540e00d802040c20703030f60610401180558014031007240d0030000140b51243c12142c10788010703d1000c613000d0038000303086d041c1070302011125034284061034070300520801d6001401d000b100e40a1111103040170a858460200b1a10582210f0300ba0764840320400e44101c00e858000400040040f140240c4400780c200008103174401a50250390f00d40c98031211000098060b00c100e0300107620071842000341000030042c1350f441c5401c4803241011 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 861418435 1250 861417185 861417197
    0x4030c0b0f1e09060a05120a0b0f010c0c120c14040513120c060f06030c09141f030b040b0a2f09060f0a0e030f06090d050307120c030b030f1b01 63
    0x6a02d41400141c0039200b103013600580e001034550006913002c0e00600e0441926459000c407501c82102c1d460448510b0080c0c2904500d00c007809500a43c005c1d00d840691302c1c4260605041540c4034410300ca11218074100841ea00e800002042c40101810380c6081021082980e04010030b2400700308500d460545940050542103901850010943c800c0d641e104407550404400e204078014001c0700c400612103480300760b0b1400c0003140003103029402405040501c503041503400b40c10f81c0b101c0205000200c0644080081c25640d4500000045e54844d54684900c4c0100100c00c4540f0304100648181c2c0c05c0070303070031452804807600c2c10000c20035003900042150b8540c071581c0f0340341c4803e24007186c964420602d84c1d56100d00c02041903211241d000c4003060354100190b06840080c0f00c40d51626954480c1035076610801d4004000c0040361a100368003955000100f803030042220741c2c410454608543e00c210380900001d0f02d81103a51654202004520504840c0c14000c20101e4416140c241c84000c0b1403c800f070410075 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 861419685 1250 861418435 861418477
    0x10080a03020c10180602031c090f060231090e0309030d180918050106170303191d010e3a030204030215070c0e1612060909050304030c0b0f 61
    0x122138109034a075110090f403440e200b2525414040c0d0740c0e8110587e94a0071200245c061f42801c0321900a90303003090360010004d00341c0d20541c1d6658010307400100038002039561140100300e8802680c0804000c604012102c000c0031402d0400c008150354008134480180e900c10840c02d107042d20000350410f0801c07024501407002040c042c01c4560044c00e554428400c450504050640090120140540c0c16200d40c0080200c9a95078200d452198070399440741c030302600140005034821280b040c52616032010307070b44002072500e006000e200e0494505404080d4a80d50350f0510604400c0c204013800c1d107509026620380f074901e12100070001c0701409110302100e030314a02660004550094050b100036581c000c080c190b00740882150720740150440042560095405100090070400541d00680651481c06a05540c040a506c0955813003c81d280e68502403992844d00203040b4941d48140001c841c46a40910307611855400c0c5805c90341c55541003104814410010310002081020490301c0000b210415511048 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 861420935 1250 861419685 861419687
    0x906130311100c1b1806090b1014210910060e220c090204081f14010306020307110706020c011d0904171207030b01020d020f0303071812050610080a03020c10 69
    0xb040343d9001002d01c402c0058006031750107942d04101e00381d6180c1c0c08100701800380d40042000d450720121200001c201c52011580b1501c04d05002000c07140c40c00508100c1c80d06480350b41c1140141c084a07100c803a5000003c800355042c2070390094000a00300480044030301d007412514002404140005c42a48000340314100d000c0080000040e002414040011515141c0d00e4200c3d0383c585080b2080d0300c1c0c1c80d0301c1400d4400c02002c141c1c031580702c1c44140c044200f05242c0c210783c2c2d0f21009600152100060041340250070304803100800604002d80303101c2d4082c000040c0010005000310041c4a5803042a2600021480440e11031600481d802a00621900220704240701e42c02d00910a8080019048201c60100320b242d41d01904010012034080e400c40c0d8140110400407607c45202d000340341560b400810208088a02c26840080d1075040b96030785a46032550b5442108245450b41c800b1074041d00300344100200b0740c45445070740c40100043c00c00381000c0c842c565402912a609510340e141315a8014815916003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 861422185 1250 861420935 861420983
    0x6050d180203030708030708071701141906020f16031109040305070605040303050612150106080606090d11090108030a0903060203070c1a04150b031c050906130311100c 74
    0x40781c02034140c0303603900c04506028980e544101c4150307000c0380c44203000c04d4419204101103103d58001c1e080300c0e155030342042142889a011004145d0f0700c01a01e4413403048036260228820020102038004140494164070780743e01703082d60b4102c51903c029191400300003142880d95400175521049031003003c16a0f951809407064021410050040f07031404041008040d0554080c2c0d02480086550060180030030311802d54410032480e814001060741c000420050380118451500004018051360a02c90581c0200301240c1c6044400d0f60102c094420310140c9045c100c0d50b25000d000800055031504542880c0034215013058480100303450350000005407011b100315180d020741e44d40401103070101e0290048110726444203840507030b200001041020f8101001d032285e26141413018003d4240c0d4441d0740f040c0c4000400c0c03520008244801003181c0c04d01079407060024034940101c0208044210f00b181460003000015461183c0144c040b1300c1c420344040d070801c0202d900c4591000c542020821003540034045 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 861423435 1250 861422185 861422231
    0xf0307050a020907031103010e04051504030e0906031e06190b010f05030c070f0605070f0206060f13090605070c050705090c0f090a030c090b0f04060608010e0c130303051c050106050d 80
    0x106c4000803001191040300f071000c0d87c2c0034900a4003244c00312080626010203c01c03064a0080c00f00da41c0e0421820a070501004280d4041c1b0700405587c92080c003841e0000000c0880901c410281d0040c03010000c0f0a010241c000c801007040300820059445e5901c00606001c030091408400c5c05408000203002400d210125020558801e006004203801450f108001d40019649200030610322200084510310008006200300300040c4101800750f0284240700501204ca400580303860b880710140400310310703140601805140c0541d5072012491850a003141041491f42007079208414103030500c0300d8024080c00703490f44244075041c0199202841d0000400c80401390340000c011743e2001d00001110001540420800ca8082d680004445540d80c1080200e951a01030000421300345001801001c58581305d0b0342e80925203c00e04d03481c0880101038142aa510b50380224005040024401d20211220060074115254000c2c10312655041c10b50191260050380703110141c943e52179410415012450174000d403 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 861424685 1250 861423435 861423461
    0x304140703120309061d120705010e2b0203040e0a050703020c0106091a04051e040201020a0615060f0807090915030b041a060a0e06130b1f020f0307050a02090703 71
    0x81c181d00ca024020f000752403405400ea40c1c42d450061042410b408001070b0f0607039200c0ca0000f8040720340c0401d00302c83c150b41014809840c55903035010349a14210080200c1e201c003030010b12030424500707028944245080002c41c0744400319007040c08108400503000c0b5509802004054012400e6a14504210300902600006050560801e000050744100a0b4040d2015810920088265540346c0e8180016210140d80f901c54440111022441808c413071018582c0280c03052041c0c6032901030985841b820303035880480d520310048180700200002500815048130b20059814804014074000101501c4000d0610580480d503480c1c4440c0e40e80002d0040300d450195522074000c0181d81464240b8122090416250b41d00c03038104040403420703030702c0c0095002003199500340e0302e5490b0f982c4030404e001000900010701420700352500c42c110096030300d5218004448908008130541507000550081c40c0c803c0040803244c91341c104200a03404182d020624034425034041e20714100c19144c01208400400301d00705000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 861425935 1250 861424685 861424703
    0xa0c15270503011503020f09070c150501180513030c150e0105090f010b0a090f09080a0c031d0a170c03030301030c08010509161401020703140a23030304140703 70
    0x84414011000603000340c0d101500208248028448501080d0b00e003400302960100d800e81b5130b220320f46001c4e992242d110400380b91007044925650f88860790b0750020042220383c261524014050106200c0304189640d04500090296003021904840800f010348000360402224451a20520010202c400c03005800d02900300611015441c1c0e40d03000300700650340841640540c064550460704140582407541c44010418101503150080e18402049060203c0045945805c4804003045046c030280444400c036440b491040103661070000c011510101950302800302d00320141c2c1103500c5404144050301c410003d0490079158290131286401207181d00540d052000200200400181c031600c14100c0710b800c002400103854442002d512030081e41c140300c1a40d0305003001007240300c0403e040e2040343c01c81070040d0f45226440f600c9001c50800d502c056160f0541c00b10a9000030004a007481036107020401d0484810741410085042c0c4a20001e40003904103000705004026064040c000140190351001c292 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 861427185 1250 861425935 861425987
    0xc0b190306030c090e330a02070c06051b01060909030e090103240603050d170f19110c070b13060903050a110102120316030c034109010e0f0a0c15 64
    0x400b91b03281c07400a141c2d0319203141c501055a0f12001d00a944115038082c0f2551001070071710310101c40b03603007020000303031004142155142c024030750a20030320380a440c842c02d010848001e241009052981c556415900a03122080100082845410108a000300074a034140584480da420385001d4405a00050300a0041003041141141c0000b6403401040350142002d00341e9480c03040800288000301c035264a210480c40ba0003885182c1c035840104066005078885003020700510b07607240362149582111110300300000395046000a1806040d005240e0341c07810300d030700c541165101c41c0c68840744440141100b108800b540c00580c0203100c4488040140c80c0c2d41e0f512440d042c54070202d2112000c40c0c50020900e010300740098140320b400b0f5801000c49181c2d03125800400130340a200e104448032144c0c2031002c00380340840001c020a80090b801038448000208096551203034150074040700c1e02c00e07808142d22124810700014a1103401e1001c0f03d400461100c00031b5603541054a2030100c450340800c5000b181044 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 861428435 1250 861427185 861427243
    0x50303010f0312050703020a0b07030e030a09080111090d080306030f1f0615021905100906020d0615080a1109040c23030709090b0a030c0b190306030c090e 68
    0xc644110703402002a0ba450004402040d100d0384179800d8040c005811a80007000420604614240c0264a51400241442001030310500315080b001d6181e0010f12800320405c8408400d000304030403042c1030103040b07241001402c0060404c901541004064a802100141032550240158003484082e601601c92212100ea01c1e003205001e0841e035050142e10309000460b202c901100c1b40000303a00e850f001000510b4141038680d0701081c448400f01d40e240f04210040d8100e4072503014440c1c07034031b10400000d620350b105c041d41c1e00141c45060300540240c58111900c00d11581e0311140d01504400316410020344410041000c40071413180c100b00f0350b00036041c0f24500101660000d21320910354030550000f0030000d034483c80711301c4078402940c1c010006040c01c0401d001c0b01003180d2108010b61401069440300c19501d5480f0780d95219507902203d554540030400321220041483c9043c0400980c3c03070100700140c11681e81c1501545c05000325954203580310010b4500083c00c00042c02c0341c544050329441c010420901c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 861429685 1250 861428435 861428459
    0x70506011a03010b0f07050109060c200615060a020705190e0a0b0108060105090a0503060f0405060f04020618030102070f11030c01030b0d030309030c2a1403060708060d05030301 78
    0x45120030307501c0c1840004000d02114400c1d64141c962100034580390100c42d0600700040d8200100036034032556500100c0000450620609110401c07a4440e200b04a00e0744030034000410110402150790380000301040748001c58841c02c0090300100b1100c960300c1e00c1024400301c0c900b4109030022500002d82d6403030086090148100e20040310901c4506c1622695500b0582007581c6e4951407460115000c1004101c4075070240300034209042c409829000d185507100006880d0401c00c0c0c41c2d5010312050072081c0000d008060020035072103035071130041c1e5a00703007001c1e40880c07514440c04211b55032100c02c401c60105e00c6d0f0381c00c0d0111074909402c207001c621051094101340c0d80c10700d090707401d40744640300b00c041c2c640095000303018180d5144801041307045141d500362015000303068480000c800304581590540d002401203128a8894003100100351201509021005581380c2c1036007040c01103525000d0030461564001852a90040030f614111a554036001c002c40d000310155000100345000200010440d00c0c2508 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 861430935 1250 861429685 861429689
    0x30903040e090318041a090a09020a0308130f030803040303020d1404120807090b1b010905060f010f0e01052416110306070c05070e250806010206010807081005060a0b07050601 77
    0x40e084c503055142801c110407034481c00c0c85640c000302c41000020003850044412a80094402c1e00410f0202c0d5542c0042c00340e06954104441c682c8020030190a0701507181c0104002c1c1094582152100707007152036060745404001e00003400c040c0c0005114400019070f8101c02108030350410150124140b624004103040743c015400710026061600141e00c1e207203e4040c601c00c4441c40c14203240740035002c200c200035210124034000150364a83e02580005a010031042d803281c0b80c01907408503203504103110076640540a600000044110b0b80042c0065500e4940c007a200c0120004050751880c09048900d400d8062005403030b03002c0303500351241c50900078004a00020071030200e041d1801a61011020707541d8840311a005402c56000d04070600811071140e101035008010000d4005601c4107804001680200a80c0c40c0d42c0000c080005124503940c040080c03038094107500c000751600d1030408048540d103c070500120901b194541022a034030b61502e1031208054018110701c140c0d00d90590a100d0341d6000c081c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 861432185 1250 861430935 861430957
    0x130909061506052101051e030a020319060b2b03090b03072f031b10090812070f08150d0f030302030613090305031504022106010f02031e030903040e0903 67
    0x78912004107544e50004038107070b4030010702850038612820010304c2c09951030703403c20740c052140051400c00b5903010800401d81c403a119100c0d201070384d028500760064804c100500d9006400e01444200f480f0b0142041c030002c03510041500c2d80880ca20b0030116140d80d42c543c000f0203420000414880c0e5203510010030b11041005a9081c1c030305420f4401c2288035118425000600b5400c09c1c0203203070321030362004010300340c0111843c1141c949405014480e0200c44144808460480e0001046088030f40e1034046513a20080606140311850b502c3e2401808400340244004250585410504402c0d40c440422001541c0c0201e080003c070340ca140340c0070b0300951060780c40314841c44640040031400b01480c002c1c00c080303a0b85503817402d007942c541c0800034024407502104c09071311903000d2001c0c01d0b0400000c1c4000521550760502c542181c2860b4002400442204410100b150804c105090841003d081c1008481910022069403941c5084203103046018030f03000343d043d92000000340300d44030170000040c00c040d041c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 861433435 1250 861432185 861432217
    0x213050d0615180c180b1b0628140109110706020c030a080112030c061503051504020f120601050d02031e07080c180a092d110613090906150605 63
    0x4080e90603102500200c40c40d00d82005c01c40340c18459020000040d044c504512892800074600c0c80221a003814001c40d0100c10707083d079500580c3e80841c454403900798003101c21303d07040201c82d1180c07032143c51403201401521003140d01c0c0e0400044a40320b1070b040b42c0840350002d4007191aa81c940320300703d440b948444880000542800004541c84c0800c901070b4600c03039455119903600a8180d41c8180142000035101d0440c104000400000310b10207015030154410500035a200310702c1d26204100c4070300b10030001280540d800581d081104440010b03000d05440044071402c220205510000740ba0040e810403801455a000d51030340e000e42000507814081c8c0d62030038151030315100c1c00d00034004280b80300480c910649000c000401e08522480c0e2018000900543e40ca00600c401500550000c0030b60743c1c0400c5400c03030404920010710040101e0080e205800b00d407040d02e4464102021480c0308035034041d41c45c0c1555a41c005000300305c0e10340d0140c00703807066a91604c0f21065440c0800390041c1c202d80208607403421 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 861434685 1250 861433435 861433451
    0xa0809060907060f031515230a0e0d0f02060c0718140106030c181401020f07051005031515031501080609130524011502010213050d061518 61
    0x8046141d00554645a50b0224241800541240503040051400414400000012801e00001000841021411748071401c0c000340d030b031401c041c48070700e40003c02d560b01c0c0052081c501503580c031080ac1c41202208075a040034030fa000d03041c810030125480c14005d5125500103000a01004081210411100301e03000d408114140702c0348210035504d071a0b8042600c240820018805280280c0c0030458586261800d00c103400a002706d081508115a004901c058980c0e40c500d20a5680c10070611102218034000341c01001d2501000c1060300c0785511003942842000b10020f5448059004202180e03800100403c00c20f840d29480700d0f5a80c0c1c4141d0300340fa400010728000c0c2c240b9501481265008980290404445550b50048007140e00541380044665026030f07500106a00000c01030202d812401016070125549092000e07600c02481224000a41e40140099071650520340c001008031001a079008a800c010f52426a000380142c1e003105152040201d00444c4000c04600c109a80a0f03c41204001c121 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 861435935 1250 861434685 861434701
    0x30e0105040f050d2a05030712030b120f1e19060641012c0910060906180506030f010302040e03090f1c0b16080a18031103090301020a080906 62
    0x81e041500410014000b10002020003200c05c1000704140d0103141501e00704030940d560101c00c4543c600304c010000c1d44510a50b1020705c0c01c0d080b120a00303010003005200c030b800d0720219252140e0200c0348509810300d207031140c1c07280c012081c4141450400d8568020740031895500d072580060000d8010300c2c1d02c0c3e07441103440d44d05d401100240880d0010688542d01ea603100c1051001d248021944121810130800100011021050380d5400c207103000c0c0b0001d070b40fa043c1100418000c40c1c05000b451002c29081a28081010581000d1181c1c29a200f5251011708002c4c1c030039070768241c208070b0341c4480c4d0000f2000081200000020003103c6c181c0b4400c480034025174406000c606c0c0d81c2d0142c6410340343e1240390302e40000242c2c41c1003c1c1c40202501a00c441c00030030140c54483c814010400c5800b546040c00694042128039030040015521001d6500108418422152400321b8003230080c0c0c000b424800e0b006968649054100143d400d80c81c070080080d0755400c4003020043c40c100050310f5007041c030302c078100c0815011 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 861437185 1250 861435935 861435947
    0x90c0a080d1205131103122d070b041e08031503010605012102070c0503010c11060601050a0804020f0a08010203010b0d0605060703141303060c030515040903080610030e0105040f050d 80
    0x320704505030304c442a141030b01c400034801c80d5504400e80c10f215140b4a60400302d03080c0094054401d08558409181410040c0d9180040807074080b4400302c0b404101d04000900c10350f54942c1c025030401451149056182c4002070302400601020b40003880210070040102071040c56104c50b4001a8024080740390b6036030064031860a10301121101c03400441c42003040340010342c050309880c1d000d040000d0000342e8030400700782140c000307803274000000303a441045c184070309020030419811800c20f1803d1440c1135020742000348410005400244500c4e40203000900c641c0d90341c80600c002d0b18440c002103540e569240344d0b0f411550300034005401041c0c101078002983e03281c100c007500d20240c0c0644411060f178115490a030700c80d41c001000c407156442141c07004800700b2020301c20801628000c0c4c070005040c0c1404048010000d150b41140d500c540e05084884002070b62100d85142c001d0401e858040340030400000660190199444041140d0702e840704000c24019450b60314041d00c3d0040042d6580c603191510202da02c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 861438435 1250 861437185 861437191
    0x20f030606060318030d0c0306031a04050d110c192c011a13080c0108130201020a060e070306110901090806010b180103020d0903030603050d050a0c020405090c0a080d1205 75
    0x101840c03d00005084098040a000030414820b0543c1c0c42c02442d01240c1c03048400d03001d10840002d075039504c00d00c1044500305410f480c0f141801c80301c00341860b0550b52690b44e00c007184160f000b0000a0700c1540082001040104036079440240782e641564580d440b0ba0010100d188103605403240000501c40c030243d012102d10990044010030b010903682058142101c420304003821070308400c0204090f0118a82400403100034144000207403000281c0d01c4001400c046029200c0b0211000d03000300c07280180c2c2c000858120807541f0901c045142c1c43c820b0111800e0810070b0f071020300780d1800c1400c204419241000201880030098803040c101c44c9d1208180e0355a108240100540c0075001c01030031210300c903001512011040e0500d00135143c42284141c44041d54469401200480d440d41014030410a0902070188103520500e800c60501c0c07400030000300010140103010780229960404a000e5110600c62000a500040d007600d11541d550380f001643c490f80c1c0d290103c002050f03611054900b01c550300442e80 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 861439685 1250 861438435 861438439
    0x60509041509030c1a040b150d02151c0b090c0c0d0305060a12080d0e07150e03030403080c0d0906021204090902040e0106060503040b07020d120e010605130204031a042f0616020f030606 81
    0x41d07601d11942400708010bc000000c45158100b030041e00d04103e801c1c680710454484c0c460011070400d08d80340c24000c403008040d001f58030b0440180182145600002054a4a60042c0c80d01041544078900440e102c000f15400154643c6541c0303c0706802d106003d00284801102880e04211074040c05040ca40c60b0001401048494540204010180c1d1300c10070160303100400082c00c0d2071502c2e90f07950303c9072240c0c4e000000e074802d40d42107143c05006042e0040000001000c01e40090640000240781103840740c07090b1f0242c01a0507944440c00010354449074054007003080ca07034008214207621502c001d07100f13400480d0101c0b98640d48000081ca6544041034002c900c06507901c41c0c01c0390561407507162001d06900c1400111b90b41d0780301c1c4001040d594100d5403030203d24a005005903100d065007003034a80c5140c01c0002509912006c003d100c0061215017040a6440b01015841c58614510200a00c20b0f80c440c0c504c1c0d540b14101203101e0804c030900603400c41d2464800c640e00c8031554940700074191a444200c1e0659 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 861440935 1250 861439685 861439699
    0x31005060705010b04050a1b02150106050703030b0303070b060a1a070204050601050c01090c061d0a170a0f15050a090218100503060f0703060509041509030c1a040b15 73
    0x22040c1400005041064400d070004181c5000e051301240032504112022540c21392685808040c01000142e04960b0075181c1c07002e07002c2d5072511800e4150500b010310484041003c0090007100340361099200d000e40300c40003000d5a503201028140808808000e44110303120f58200d00000840700440840010206888a10b65090500c19020000149401000c0c00d0500c00c1c10840400c0da10000e21485003801d1107020030351101410860014001c1c145088441440000039580d03810903032319051220222401510641200c032182d815203820405c02a10040041071122442000c01410710f81c2c0011000180404202540d00c0514180079501241c8029400c00b613420904200300384000b000b107600c07140003920004030540d0b400110b40380034800c660101004140c0030074006403a03403601581004180842d40c0111504050b220f24408100403143c0034209595032001d40105805144241c504a4000b60000310784206010101c800d030400b164116000c0519070001030341e1070f10415480c0a4040064151 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 861442185 1250 861440935 861440939
    0xc03020a021507080c0601140303090f06030a110c030405032107060506361806010608150603130b01060527130e0d02060609041203050601030618060e0c0310 69
    0x200651010540500000b00d07000c1202d000400c002c07000502021058400919007903141800000c2201d0800c0d00540c0f01e41c004008055996030741382c1c0400c4180d9030072560203940b80c49041060000301001e41801e1081c51f000301c0e50b065102000310140c01250015000e03540d186c03000d010014208035920080c2407180c60305101da0001300d45594025030344004050716081d9101d0110a18800601500a140c00c840c4800c00b40a0800810362008a40040c1008962400c0c2c000e030944144e00c60f181401840e00b080100d130006444180f207503024801001c00580995581d051140c055012246004029100d030400c1500000e41503215508664112860704c2c01850000208080c1c00750383c540482056034480604c44081040403600e00c0380c503104001c039400400c40b6084010020707080002c02015603126034800c00c10440030410b000d90030001840d80c0d10b030000d05d5558100058004100c150040c4000d0903114941d10b0309a48160700070800e0300c0d00c2c883d250031160303035107580701d01144405c032009101c0f03010030442 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 861443435 1250 861442185 861442189
    0x1440a0317190207030903080415090f030302070312030609111b071a070809030106060512010603061d2203021612110d0f081602011403060a1703090d120f0c03020a02 73
    0x6484414824a0f102501c82d687c1d4503003c0f03007a0069080040060306204101c10019040980c2e0340c01800d13a011040c00d282c0c51502c01a4580000b0301c030182458940018070180b00744250703c407202407e203060b0b0400142c000790007400525004030141221140c0e951556910000b80055440200c1d010160070f02c02c002568800b1181c40c1e00260f80c01c46031500b00380080d00341036030300b030241c1d5000d008199078480d203c000e07540c030b18561120b043e44400309262401200703015150103a03940c40d4010090605002580d01d501001100d0388040c4401150340e04441044e05003050b43c00319508014083c1c046c0040a840d44500c0e28000391000c103840100b82100450b1003c400d803c1c10107002210718001c0302c5c4220b2601e5141c4a40c00d41d6070100822020322030b00c0900d09021903802c03411410000c620500c1c1d5604500d051004520b44881070b02a0102124a07500804000b520410484030902c02c0075010944141e8945042c660904c210b0b110314000c01e4100f060441c0360b6100345d00d40c500c40f5070194003c1c500140e280d02 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 861444685 1250 861443435 861443437
    0x10605090a03080f030402030d080f01060c140f0d030c260411030f0c010212030601170a020f0a030504020a0b210903040f08060604110301440a03171902 67
    0x1400d07500708801d01e00001c04911010007130700704441a0406907a480c90284101814080c12100a4043c85600b00c240004014402240e90640c0c110341019041802c1e5800c01c919801081048002c1501c13500d4100c1104560118540e68440c62548050100440202040d2406062080e401c41c040000581d048050048204019001b80c02011300c2c40030142d41002181c00d009004031042940e501040c040b1421f940c0c10013a03c0070f40e0b01c10070065411410320000007001d01c85514151210b48540c00701068201c040380d41241c0a601c0d45440d25551841c1807030010340540b03021282179110742e800f50800a100c038a450219201d41032140681001c0c01021902d110181d5000b400340302d01031005100224039116800e2410000d00781030002010305161030000c000941741d802006001004050004020403990626981527200f800042884c0400190900c210700007440b03003100ca01c1c240841e0010559a0001c194a04c419000c0c1c1d44080c20813002e05199085040c054070401d0055011400c00801082c03558 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 861445935 1250 861444685 861444697
    0x30204180f0b0a0819081b060103030f081611120301180f060b0f0c010e3703020705060a21061d041e021801080f01320705040305010c0302071a0f010605 67
    0x10742207410845944030351007600408111113002236203d44018000e01da0030130f138140203540c128a020305403807600941c1c000000a9106000d810b2040400c2c000351030b64020302240500040140810f9141c4da0b541c0b102c1106002d01c2980312101038a001078400041075140101002d80d13005103501880c0c0411140b03803c505030301c00d41400b1070a540e294000d0080c52400d0084981403801000c500d0f8a040c1e030742c0b0501e0000e2040c196420391104858580300c1c00a90041b40c0101161003c951203601d03034040d0751045da4108078070542080101400e00e14a030070b51046500074025141080f00e2900c16980f1402100ca170b081d0292000340000080150340d401100d0910340607030f00944040d01c5040b0078041c1c42600700502c1c4080c0c1000303a09400a0a920380c0400d000d10a2501c4a5a4492480021003051103200b180c00310820b82c1c00a00b03507140b40060016401542200c00440d4003d000700400c0c0700804000300250030a1408070354050714083c0c070003441410100100c0c0980582200540c490b4a07000c02914598008 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 861447185 1250 861445935 861445943
    0x101d0f07081003080403051507031a060d0b030f0a06152d05040207030206150a0f1811131503050f07030b031903090e07170f07030204180f0b0a0819 65
    0x90b03008400218500701820046100704018810022151111080710000408090802d442d040842c22011300c580d035000c007014005d0714100d0f40c0f107442c100c407440504520f504180d010b10510356a0480b5240002d8800001400b9010070060820380346038091002c00300c1c4c85100345031007807440c21101c089881030880d1080a00c140110708440d81e6070000c02c044c0e8100302020750140c0c001400f040340300c03100c8603402c03405908216100c860003810b050414400d40f00901401c02c030068400c002c1c4403016115030100c1200509058041e8445000c0500083d00e107a80d07020704140344042070078005607a806802454080c115200410b4000e54940900320010101c0c400345072790611520f004c8038203400c2d6036010490507602a0340c4042465040100010030302001414071010070400c0030140117142c0d24140d5140d0451185103103200c658440c000700300d001e0b000b103820668540c4000800c500d402d0b1b02c82e600045041e08803110600c0408405820800359030414803540f07120390403406803083c00805010700c040780e151007 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 861448435 1250 861447185 861447211
    0x4060f0e190308070b151503180a0c1401030b0a03030809010f0213080114090703140a0203150708060a0308092701080a0212060601090b1b06101d0f0708 67
    0x403818421150090b030068449150010304803007404030f55550b19520919500451011481c16800300d01d00200070b945000c444540400817545140c000d520200c1c041c103855044400a290605004d5900210b61085607100c864007806080c00e5406800741202002000380042d41c501e04c1c64400383e65209001b040f5011075541d40b1081e207400c5803148003514011038038034035580d51641485646406c444102c030180088840c0541000741d030403400140c40c1c0c1038a42c032194118441d500401440d24080d148070b8029403500a100e080840602c40300042c902c0307403c0c15642c40509031600011701c50400282d010140c461740f020040c0800600300240d101005008842804c40d220803000080f031346084003a0072000094100c1000f4005624240e4640100071074220042c1882d800c10030000780c09441c1d0f07807086025501e00450042e940d1215940c1d00440c400c2e604c8152580f9241141c0d040445820324012441e0f09514241100d00070a81008114850100d8807449107854883d0350040d00c502e00018504600e01003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 861449685 1250 861448435 861448459
    0x2030313060b101e140405060a050d020d0506100507030921020616020f06041410030207060c030e060915011e0513020901031b02030702130b120f1204060f0e 69
    0x4403103407040c00c0311207a51360740c0000d00108100f2035070104243d1480130800c81080012005154001e0448040301c90845140750388114281d0146c88074011580c88030190f03440403422a030003220755008244169021220342080031030080098909000700c1501900103050900282300034031280c000c0e82e0401510f0b140d404640035450380060740c154480e444010281701c1074407520085041c6610003900541c01101c815050a00300800305a56a1034003100600c1541d50100003244603009604031021a50859030900485550113005409021140c2500810744a01c00004103911401709403022039010850382240749919280c540040f00c1b000c62581e0319000b00c20200007034241d40703001c804200341400c0079015031184a01030016080361040914011103415440b0720390032855003c07048812003581180c60840d1501030000b860010288010f0b03868100a080146010f460340014000401941c040203c45605040480043c000e00039845081d000ca04012050040c050060000140e07604015010041c2d8503 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 861450935 1250 861449685 861449689
    0x6060f06200f0708031b0105040f08030601051324020d0507060e0c0a08100b04020405060a121d100b0d021c0819050a020f0111030a0e0c0901090b0102100c02030313060b 74
    0xc2c840e0350110700c0c5548001030900886101e4035114005461b5a002041246000c0e185c0c0750f46005d010b4001800001d00200050643e80100152003604540ba05940c03100c5850340a400300007080a071801407100c2d249800e2030070f500e20010302c84030350020a588550410070a81c1c1c401d40035017107102d0000e500d802164081102d584800d0b0501000f031a038403004120700404003022038125400f10700071500440c0100011710035030302c520040f92080d00c0c1c50f190800c00308110b055284000c200c00b24002904008141c4d000003000740c0054034250f00007140e981040b4101d060000c0010020000c00000d4002e51b14488862080c0c0310000b01c02030090044485624080e4a04200c0d50804541d0203094040303200801ca03402e03440d50402c81701e500c00e0b800d00c0003006000180803884000f8000105401e00080d1078000d0401c11070403d0040c4244001e000e040c1c629296154007451001d06101c1900a0040c451071a082ca031502880c05000c40e800119000f5510b5a1103150590140400140d02070b42d01540f178020750003c0d5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 861452185 1250 861450935 861450943
    0xf090c1c020912010c180f03031b06090305031005010804020d03080711070e0f01090515060903010f090b182116291008061f050a0b030406060f06200f 66
    0x769203c00000503110556200078015403220b000560880c591030303a080c010700e203042602c1c00c203032601800c08088603218100c1d40303040302140d404000d002d141003103415820160002c008c6c1d030250352003000300204071f605c1d400110340c52441120041c0d03000c020300c00a03d0209004000720764011215251900301000c0c01e1001c9842c0c03807040e0744084000042c4000704401c1d94040f1841d68050502584240042d060006918009008202840d0f11901000032508182c0d0750941c00f000b82c2c1d069108050110070340504080f041560200c40d401400d14008100602010001c19900c0303050049040c4491035440120b59070030b1940100000d03c0845064844510100720010f074424410501b04100340340c40300d8050302003103182d00007401c00e0440144080c000d0001280101e00180d000650364031079154007110303500c12020380d60740390310181d00110400b0300130504020344402548035a01484003440200d645041410070602c01d84211b0b800119030100701a00101d0850040a0704c0c02c00e0740c00c60f00343d090a08a40c500f4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 861453435 1250 861452185 861452209
    0xf160501110c1b0f010f1d130e0d0c17181503041202030301050f0114070c0602100b09010501090e06030f01020a0507150c0801030305031e10050f090c1c0209 69
    0x55800500d451102c10009981070302c0414040d9a41d90048031307080d0000e004640c0d180e40c054103000c406c01408240000d2012440c000d0070006110f904e522030481440001408000704a404902400c0c00c08080180a0303021403050941c81700080c542c01103c10304000842d040522a448203401000c042e901c0c55944607000501e01140d002d1455507030805260282800e0740301d40c4041c003550400c0c0010420796484103214444035000b82403040c4031030442e0350398038a80e10400d000145050078400020451a0380040c2e00702041d00c00c031604009540a1000700308401d01c0074403419001580b8600f090009684c90032016800c124090111460310316031030499800e82e00300c1d4400303070001100802d0740d01c148110100141132054100004104101104034010490841400041c0510000101180c098840000000711060703240700c01c141c00d030a1444a041c0c1d54289031041134402d4840c0f412007405450b0a40b4164040c0715840c5003585802010500d441c00e03019152401d1401c9035007801902c802d40ca582d400010 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 861454685 1250 861453435 861453457
    0x1c02070309140904050c0411090303030709030c0e090c040905150a0b010314060303031602071509030308070206060d020f0a050310020403060507090b07030c0c120c030b07050f16050111 81
    0x241a041c0000d20742c4403070700d14650500c625030007010f00001c1040800c45d0000c580040d100450a0000452241110721440c07101503054800001000100b591001c114800d0b07070302c00c4031254650740e59034042d101550b0058995034001d4000c0d8004645501e09540140302141c854020f1758001418070ac48030030b60260444042804a0315603404442540e1305110303a200c44451195000f00b14184107000c01e9603400024606c1c042044407400a203400d90081003c0401000d0720750350310084540d2076a00622004191004401080903031021844580c00422003a10508024148040c00c40c065000c00611306242c00203290400705420001c00c0c0c585080c024500300092800c0b0240c4c0d2685149002c0040b200d0082141c41000449030040c413182290b00200c862643c3c0500d84201d2841c46400c000c82e0150003540001120350001c40710f902007003907030440803003124064165964282e070365035020780e15445a49050403003143c0c00c110300a45420101039070002d141c02140000340c00c41160005000035401241c03089 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 861455935 1250 861454685 861454697
    0x50d03030b010e010536060d060320010e010e011404060c02031e060106141603030f0518030702010c050c0a0308131401090b0d0e010c050909100b07081c020703 70
    0x6141560440d00900703c0d500c0c00e00c0c00914007080e1100028138072180442c0e11a0300511079800c40080320b100d0890304074081008000e41e45d154060101c490017041d4622007141d4079002c0c14140c01c5940c410803c4078840c084182c44410415411400445034901c0d415006410701c2080030004080f007603420060401740403c1d80741d40095980b00d00402d49000000c80e054048840517090340e03e000900030500b40c2c1150200d0400c80440008426580018060351480d28143c20716200700e1014035034076801440c84803599050401440d114840982c1540b0600c0d4110000e650040100c0c50040d441003086c420001d01542c00c2d10094903030140020704003506540b003607a007440c000c108040a42c8a041c01074000700f005e40c0714400300418940018040d489948280e070240c24011440325040c0c196500b100041c0e1800400130050f542c3e00c0c0b103015143e504221566402860070400045400e0a140c90300d1056641584440f42800f03e00e81c2c86030f4450307000c0c1c003e56480807000808509820201c0c0050229184251982 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 861457185 1250 861455935 861455951
    0xc061b050d020d02162108090306070c060e0f0c150403061517031e2d0c0c0904020315040212190624141c060204050a1203081f050d0303 60
    0xa1405d003040d1001c44440400b200100b0407000c8007001d802c0003042403465201c00e196681400f11042c0204013130550980151400c124245a01a0340c2000c4139200d2007040000c1e01035035100c00c0d95040400802d452650050f103059059287c180b0700d4041d02d07581202c0c2d840c40c0540301e599101c142c9078403078076000c0c0703403030321034205004180c506a42e0180b01014000294200182010101c1031020002000705080038001540210b0401000b002104242031400702c00c19020b591006200c25840074803503031000c0c003c0341924225850034500080c0595001001403007500200810a40c9072400507100300d0b0300000c90100c0c181014405d10a0141c120302c1103650584a164505041c030984000203045245034074010b40d05007001c0000ca0a50007507941c41c56010721140b254101140c1800703200900341d80e80d20043d106c1e46082102540051094480a41e024170346250b0340c1440400c89030320310b41d00a011400d00c00c002400c01d00766042d5600341e804141c1f011580c0d50340c2c03000800c04401543d0010340001c2d44078001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 861458435 1250 861457185 861457187
    0x8070602071109040b0615070b100f12020f282d05060d0e1204090921120b06120a090302060105090705220302061303050d03090c061b050d020d 63
    0x160003941031040e920f150441c03405507501184c0c0340c0020191442020306d4022088603040700816500d0036903100008040703071304080d910088100701500c0790081c031014400d800304080d00300212804019038064182401041d5400c10880e600c840c0340040e00d0460200311480f00150302c0c5c0341200004203001e48a00016855541c02e0460110703603a190381c010700004150810a0741c403a901140c010003145c4800241100d4a240709504028a46500c9100150081340c082444800c552000107203d00c9200003107600c40189408503c90000100c40e8004140e4080c0380344040083ca80028191100c010280e515001007900da00e10070b4002620811811680c4082c00c40401d41c040000e240988802c0744d044d0402c0c507040b00d000701940300d100d55a10240451544103000c851110750042d026644c02408551110a0303103114009100d10f501c4180c420f031140d440aa030101e4001d12032042d045030403611400c000c504200e8162661602e0340c0c104e414403100421050041394050100428490066024054200304908 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 861459685 1250 861458435 861458453
    0xd05092b090503030301030f0623090d17060105090d0f0803010b030402120a051e12030901020304051911040207050c040908090f1e040c050d0906020a0807030b0d0813030807060207 79
    0x2100e4007944c0300700018404103113042c100c03560035584000041080328181e10031100250144141d21090902d01381804480c0304003003902200e500fa01c1d41ca8900011003040304a00c1d10300142e400700d010500401c90040e02d070814026504040b401180885401c0b0030341c1c3d46840a0398400da0041804a5001c8141300840c503010b42c41c0d170781800f070040050031103260319100c0d030f6111a1841040c01d003c005007035240a101e68148003011802c40060101c0c0e403a4584031040b80c2c041e6000300c904547c14001c400c0460030003502c00c0000c295407034008100d03030016008082413100960280c0e0050750300d8441c0700d18102441c0d80e1070003260401da108501c01703600e5810750001d000c0500c40180c100d6202e9500958a0911450131190300843c03541c1c00c8501188821041100f0b5a03184101c40c90181d1842c18a01150309102090300204000009030386c5180e050b0350b440e40110b04491854014a50101d609002040414260300282030b10100201c550b090056a1340d84a4003e0f9004e02402c940031500840e0a40078020200 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 861460935 1250 861459685 861459689
    0x311120a031109152113020f030f121315030b03011109011e03020c0d0804170918060102010605030706020708120705100f1503031110110d05092b09 65
    0xb6105041101c1040042c1d100f000e0b5400305250440f01140402c040200c0d9011a84c4e03644980d0070381c03466820301d41c840c5001e40700d0800080c0e00031008070320b01c454142800200482101800000762544020a203103146841d8861307004030205805800380801c643d400403200060f902e915440000d5a941000f080c14207440d06040300140c103c0080c4000d00b810b0b41c00222401034940b24a00180c146150403005600030700814500035107500c1030910070a482030304641c0013070081707000314203c1005c489601d80152007846440c21854210701d0182401c0f1100785c642c9031142d0052390500000c01c1c4a612072000c607240500d01c0c3c4c080001688080c1c000c00c01407805201c03101d0784507080c0da030391031420129032209a65140d0054141c168580c1d6880c04d01c504108503840a9000306980036114140d60703403404c0041c003280c40402500413502030403495440240ca41d205201d03803000105112814041180c0c440c1d030003404010140040c60060400306004412000c4040c240c1108200204a8071540c504d0004d1100d0165 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 861462185 1250 861460935 861460961
    0x12050f01080d0c05070f0e0a1a0d0b100b03071d0f030c1507021807030e0615100c0803010b032e03021c02090709060f0504050f0108040311120a03 64
    0x1200040c40039850100e81280380007014105104220b0f10703440e10500d0f0082592010554030b002e0080420030352054900203004040500d418001020f1090003c6100c0c075100184940c000600412800007030395000034554403c42a000129001b41d50301449012684103e80500020b422243c040e100324409003000700f91050142c0e60714600314001d402095540c100d030624a4480d05448081c0610000844101c44074207034003030602031034003044408204104400740c401d100070900303150020752441e00006040c1e110f4a2120981c3c16841c4101d03060101030005006240d0801c24000124008550703114002d41c020405800f0045d903a181581001d1040700c10004643c0007004144190401c0704080365004040c6d030740468400403512000c4000400e52540c3e20002901324907050300700065581c0000a40049a500d41c680c105203409007038084956104030300038035901c4042d40c00e800758107500c101039903617116100e82010203484480300041890304026280303c41c400d480c00502d1011240d89801100c1c800b1903e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 861463435 1250 861462185 861462211
    0x90203240d0206130f080109021c03090e06011b110f18070e040615180501030b06030a020a110604470c040504151a030f01092a1205 58
    0x920000e88030080c0c8070400782c81003038040b0350070301005210300048000f01868810300e40701c81d031b82d4500e090207010052000d074031488440c04004412000790640100d640e60540c7d0302c0d04203905009046a540c14054140381c100310b180030034000d1600c480c1c4100505a07010740042c000d4100000d080181d0461990a00c6001780007007007074011020310500b842a0000b0b4142010340d4841d078000003190051803558004546001c810410015541d00f180b002c291841010580c580080d89410041d0300f614900302d40c8641001080002551a5005070301900f5010120702d0b150b042c01c020464400e140802c152001c1c0c90061010649103041d418201182c0358620541c0c2d0500e8079100c2946080303000c0310f02e0301c100f1401071102d84000380b43c4a608200321006080020802c00c800101102e511824402c0c42c01900c0d20348501504a0300a614510241d038820700302d4020040c400d0b07080118a80240c400c45042480b20319a00c81320f41200c2c0000280e0ba47c8a00c406d43d41d1010102c42006080e003a43d078050031204440d02 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 861464685 1250 861463435 861463501
    0x6030b010203121b0703050c10020f09060c1e0d030501052209020f270c12010302190302030a080307030518190302070b0a0302041d01080a02150d06090203 68
    0x1030044282d45078000c00c40c106403c0303036580e10300d5103d6a0046040c2c40f034052a0000e412010950050080d00038401c542084a00340d501d03640380c84080f88a55840f00d9240341050008040500e07040008222105222058a10103804080042c21400808070080110b401c5488180041a0305204160050008070346014003021b120281d071000d4040c01180741d1425858100e9070081d92030701080390300c20120180001c2039442030107104e444c80260062003101040c0310311011a141c4040c031401c0e628007696418111207540d01e5942003081c8000d56540480c070030328440c20000090f03581800521042402240003e0f039032314001030020100c0d40002c144c4c009081d5078040258140c180003030701803a0050341617026000f540c405d041c1640303012010346c814400080c000030b4110400354560080c000701c4620081510004080340c0261f4055602400384140380da20826942001d4a052481000200305080e2004d2408903d001081c081d603000c1c0d0845207141750004144921200e092955400e0340307104ca117110f01030007 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 861465935 1250 861464685 861464687
    0x60a1e0908040308030403051b01020a0912050d052503020a020f06270111060a0605030d0f05090103020d140f0403110a11060306120601030f0605180c010309031101060f090606030b01 80
    0x40210700020705003513008000181058080c208584034218001c00c40c3c2c0c40440d041e80c13158041d60251415800090510100003010300c0300c0340348007030380c03503400000b502041185402c1211a03400c0403c40000019600404183c501c90b100c01250142d03000c0e5015201e0701c0840e00502046014016030703540076010400010444907010450b0740340710502418a16009c0000000403680d080c4420106d41040c003848052003404c02e603d5000c00100c031400e40541e251260081c41c1901c4180702106c0388804242c2c00c220208032580300b940203090030003c2c0c07400000c4000c2c000160681c0d018041b907104003c44070300b03810b2209141d04038081d23f0740f00055000074060507402e60f844031203281a5086ea180590000b2011480a907a10900f8103001d00c030102c1111301ea5a52400c3c40c50840c085604140c070502d02d401c0110b80c50445102040c840080303017400078034507002501c0046001f00220b03101603080050314040740700010300a00036000200703403003030800070f40a0038001e8580071a081580700c001803614048032607180c0c0e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 861467185 1250 861465935 861465937
    0x3070f050a0e040509030f0d0b030f0111030112031b0b060901080706090e150924090f040809031609021b0d08180a060204090228120f0e060a1e0908 65
    0x45200f5a000b14294a415202c80d1a46c01032005054104202042045050116520145480d44101e04075191103131010011803c84100b25029450206c041006015001141801c0f203035882c03003860b210340e07803811030b0000b921940641e52044640d49014801d0203824502503003c075014220280140111516144024150603e41e1154001707081c1d150002070983c2d5003050010301e8000b0040c00028070303440c254181e0f098090004d081c0c88003200281c4411035107414250308040c07088844000c41c142c40d40701c0351124201604001d038029072500c500c0000541e47e07103070040658024a061503025840c0c400c03a480c00d078900c10364201080360552040c0e80b851071096200d0310281c0c000d402d81c0c00600e404a00400324500b84070000300081d003101c0c000600010300208541c001d10682c44448481c81d10007511102c69000a0840700c1d5141c00681002e41c8000020070640c42000722240681d00014480540b030303d09400c00320100c82504405a9030001c18001c088051710781040d0543d82041005482886e550300542 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 861468435 1250 861467185 861467207
    0x9030307140f040f0614090307090506040207140607020f030712110708030f1305030c01082202120c0a0b03090a030e0103060506031302120f120d110403030503070f050a 74
    0x8000020288150301d2000e40120751100d545140e8556445889545090440c15244200b2000901d00004021300c10210002c1d61000000200a0200c040c60000c6400107040060142d9a001e6800c0001100081001c00e03942000c1c0d00030005400c80340341c0801e000c0d003042846103032072000340c10170480000003c4000514440450320350800400800300340545e58039004540e0082085807000040707400080075440060001c01c1c8080441041c0c4a880720300741034031441e40c4800e00d40800c030365001150781c0c1030001c131038044101e4100300c4400139000e19400280c030a0f84641d48146154008200f104801d080034032004000c1c001d00220103107075041208c1040d036145100c0714040c041000b40c410320f80131a8400d41000c00100f00003001c4e69101c0c140002030a45920b0940b5040740300e0070340099407244851004c10350001554600c00980107880a5505590f001d034010390810103043d03910071090310305850000282001e18001d98407030b82c803071800c41d00147c40c03440003820704014000207100442c1e9403903010740c00b04a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 861469685 1250 861468435 861468437
    0xa0201091a030a182a050a031a060114120105040c0e01021c09260d1809050c0d0c020307060e2d010f021b1506010503131505040c060f0809030307 64
    0x8070550b800768801806907040c0b04c01402c0243d664840c6800c61805040c0301006120040803061455454003007064018007480024040140096000058080200d6850340304070181000c0c40310004400c00382c0902c0d48000b011400c403226020041c0940e04051043c12102039060402040060050f0700107591000d01950658030740141c0c00120f0111840303022817400a0040c2c1c0101c107035459260100610080c0c2000c11840a44903207884828042c3c8140c46801c0b05689034808015a2070900040070b001d003500030b080e860300131380401400001880920032480a409603602868a44070907141070b00c190740e440c042860382a40034503004844103045003880d81a6120320644940c407481c0011400e80905407442da450500d0f0b1002c41d07151034951900324183c00c40c2080d07000ba00c182c0c504e40300d0848198942a150503001800600000d08447c0001c041a24000c1c0900c43c1d154107110048000310030b0b680d08682c01c0f50711084880c0d0421981d90008e142e140f1884503410318101d145000c0340c5507940c0f400003c0540f0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 861470935 1250 861469685 861469691
    0x717030a0b030106060f020616091401110604050a020913110d050c0a0807060207090e06010512030c0d030b100215040201120b1206070206010611150604021b0a0201091a030a 76
    0x261030441181e0011601a4002c0e00034807210307036200c10160005440104007005800f511002035403421080c40354495862036034840401007400e04c2c40c81e84042c00110001414010b4542c00c40050b03243c10000c0621407403050300205102806d03841403058802c0c014200c074607030880341c50001000420a641500c2c1c1501c041d0b07444480e000581c01c0c40c030301d8030344844000e0350480c06902002c1000000420240d05486003902261007071380d921407455045805410005800c0d810050060016207004e15101c800401c29904403801c2c4290300d54102d050070005d024590100e60394071141503041c105202224800701076400a0016202d9441403c0344a8100801c02030400c41022001d5062001c103a002d00c0d40000b001e000b48e440d03280c03182d01242e038a100550f84800075110b420000a41e20307120300061840c1242000c0070b002e9044505100704107a480c0a0b000c0e6901035000e000341c801c5c0746903032905464901c00110051407034100d0b9000140080041d034004200c00745410102146107107074041202d4002d80403040c00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 861472185 1250 861470935 861470941
    0x4030b0f071e02190327140a21020301090b0c03010303030b0a03080a080603030408010227041b0f03060509130215030c0421050a0506010303110a120813021507030212071703 76
    0xc40e11b2180c0076030b412400c50310f410311003402030150100f01000d4403c0b5070b1112816084580410214041500c03420341b00141421601c00d40300c40001211600910140c00480c10a0180ea6140b801d0003084561a16022002c00108141503040c000c10f0700e481c2c4141e403c40702d51815616040f40c144101400e00c030074405c48001080490b1030400460b170041c00400c008548640044800740100c20305c022200c41122415803103e0b0346481d10384241e25131801c0840d90170155000c518400d44920350350480b08030615076100b04c0082c554035042c103d11301c60f40704109050015400d5204105005241c400e40c0824040d00313000300000d6410b16030455003501c0400c0c02071288040080f05044081c504003100a005008140303403041004400201c40307050781c6c42601d6500303e910444206070740d00d4410400103420710f0920241803072528000c01600d6089040364031401ea0218154002c9170840c2e03200074100004c01d4001501c14203042e414041d466a091001c032101c1c1c80c04000740c40d000c0c40c03202450307108841d281c400804 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 861473435 1250 861472185 861472187
    0x8100b040e0f070909021303110907090e070302090405181014060f0406050612010e07020a081206012d02010c0e0303040b13091121061f0504030b0f071e021903 70
    0x901c0003041403c1741550ba030208000001d41c200d403144821556103c00c2c0702d401c3c070f007440c1195246108001550b642d0b140640b0b8800409002d1001401c0076080c0344c0e0070815107000352100c0c01030034400d04080c0d80d01000d01d0b0344402c00310300e0402108c4070030701c0992506500b6010300320100e40c1280c2000048980620609290000900074501076110342c0d07002100103a494540d4071011001412180d0340c008091140e0395643c0d0036a16150300d41c0000b050075108002d130540c0e0125900b41c0341d07005041071420864003031032480520018100d010150454504c040d0681c51025424025120549001d1628086180165011940c0c82c000c0340640c584504d0085040e45140000313030210b00c01000804418808010161300382d001e81c3d407000c0880401c5501c1c20035a440311000c070345810f078002c0202414254002c103c50310510034600101d50114100070301000000041414005494007406201d044043d20342040000980300c08409000080030948031607810b440d558000c030381082449041001458410403901d0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 861474685 1250 861473435 861473447
    0x30b1c050c01110d1e030e011505100503010b120c0c0105041b0503071d0c0903121c020301030809040c090b0a0905030d021c0305060d12111b060f1809010608100b040e0f07 75
    0x4600d1f4040d0720700405007140030150a0414204d40c42520107001200c0e00c030700e0807102407000340628428490100070f403101c01d01582c11030b503034400035680300c00c1e040c0040c0c42c240e036094407010780c2d0540d903100c004014620442d218000490050000301d00030904e4500d0030b4a65032440a891820040c9c54800c0c01c00581c1200c2114101c602503080281980c1e8040d119045103d003a810000c0030941c0032000b4140c40c0e516046d2032007143e046c0c03a0040d2980b8106910f540411024000b040b10801c104a40c440e00042e4a00c0c6590142440344a5501e861044500306014185000d20201415045601c440c1c5010f080061044c101400100640303004942030f507c0c200030512096603200b0042103800b2580c07103c00e08540c8175030800b40120032201507413800c44035100310390003001c84500c0403a0f0048040040444416106000700180321641e030242c000303440b1450008400000076401030001c03a110004000e06040118880707000b904070452514201801c041c00100c0c0540000d1000755001920400328202c0c5002e40307 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 861475935 1250 861474685 861474701
    0x19050a0506031909030f0305010b09090c0901211a030a0314070c0b1b0606120309130623100507051902010c0b0a1a01020c030607030b1c050c01110d1e03 67
    0x1203091046403a03c4c43c00a085c1030042e401b110010385460000b050f211041c404644481034003c145c40815121090501c0c5168012824141070040500500610107804003041d070141000c41d8002442042c00f40000c0694404c07004100d100b500904020400603070811010206404c000d420261202000d01d404046c0c0e0308180c01c00d07180700001290155404c00020070f1083c0c580288000d0790042e03280c00d024400805a00c507004140d5820500c115206814034244e01800300754109400b041c855030342d070242c803400301c0d03001c00700740301c02c10300f546030a00f61306103981000c1e00b81c0b0480c03404629011142d1100c94954000b0348601881d44008145241560b110308100700790782d03030083e040088a0401c548484010100e01504050300c3c50b009a02e920385600204d1030082d10800500900103a03990302204500034000c030041f066005200345c1c0c80740f990500d04040c11003007510030f100605043c1c0c800310014000b6400c0b015811900d510000c2070840c603a6020682071550501040c0b174418840c0d1003441076020b01410 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 861477185 1250 861475935 861475981
    0x1080f0106050a03060b0a03140a02130c0806101403040804030b0f1302060d02120702070503010605150f1b030f030106030f0204150c020103180317100605040e071211030619050a050603 81
    0x2701c4240c1d2500312002c11100401031017161015000c14212000e14150b034004401c120100713010384000382d15424880b04010b20a24240380500b407181d0307e42d1403900683c10545003a139104070007040c14000c1142c3d030389000c2e800010b440b80d60b0513140340c0a04100c4441210b43d82c028000e140101d481c03150f01806405070f03101c0c1103002c4d10185107481c060030025680c5100380704041c4030b5820201d0004283c1060328400e50301403100d031000c900e402210410f41d901940002c0303c0700f540480d00d07400c01e8020300c000d10281450b0544595050b82c0da500d4808020305641001c010071b11264410001080000407908601c90b6040700c1c0d08061582d002c0c5030005070004d01d254a14962003075006000b600405a10443c0c101113209042801d0005480750891080082840c1c02540080f8904200901603404910301a952181c461320307040301840009041c01c0e094502109a0700600c12010081c45154a05007a22200c43c0c00300940c0c0d00c460b1860440040c0d0070602c2442141e005500c00000320700c2107440100703502164008 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 861478435 1250 861477185 861477203
    0x1202090907030b090c0c032517040e0901151701141005090f160804050c1005040509280c031d0c010210020304030c020f0613080601080f0106050a03060b0a03 69
    0x81c801034054070031680028421445080003070956210300e0256081e0802810041d82011a24030b40c0314001650007801c1c0d40d40700b402005940018254611040b0300b20002e006107502e0314a841e59038110b124024003603c0c4903034109140d4544608192454208075901020440383c05100401c020b030040c801c0000341181e001061003004500e14a82c0d0700002120b00c1561540300341e40d00c0b004400c103902d00903a04030b20316000302040081130300c0c454180c460300580907900384c4e80c1110706600040d40c003203003014182d0089100454200941c0c0745c507585003544658258103180c6101442502d5107401d101990782929407a0340ca5188503000c1d03100340d021840054265290300e1030080c0340240955507512180d40d6600521811a042c03040c0e1603580260713806150f0540711090b00b80346030781c00c020741e041404008035041310060051155200c80410900c000302440005001154141442a82010300310380f07181081c2d80c18003104000ba82ca0310b20b044022240c000f0000100843c0890000c1c4140c400741e4405800124 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 861479685 1250 861478435 861478441
    0x302011e05090a0f06090e01260304120f03080601080601020d050d09060f45080c01021204150606091403210901031503020f09060a1a0912190312020909 67
    0x1d04d07068010558201d07481e5001c0140ea035030742c207551144e400d0140907044000c060b00c442c0c0b040b080c071b840143d101e48281d0540b42001e80351a544a20301780c48002c10b44803a508000c2c40010705800c1070342943c010000b864101e84a20f0950b002075640c20001415104025001800241501d281d6100151070b5034042030900c10075030a851040c001d03141c0a50141020101e601d050001c4d840002000ca10024002c0901507050540c0710780800a11030360182500c00c01340400414806c0f400038030050521841103901c401c1c241c1040e0400c4070103243c100091105c41c3c0d00c2d103001400800e0f041f91294040303c0030f00740c0942280380b1310300100703041044200f1031404801d03001d0140070140b020701015081142003030781c0030002018090041d00102d541480040d4001010500c84c01d03c41c200100b5642d8808005401c21840701c3e40d586641229401d890b84e2001035a0300442d00c2103003403400348406281c52042c4d000a00307402d03843c0001c0074241c61a02400034180080c0c090311005021049d0181c2d45c03110001040701035549 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 861480935 1250 861479685 861479699
    0x240207060507020616052203080c0c030102090a032312030910151404110408150f0f0c130306021305040e060906130203011e0b0108090105010302011e05090a 69
    0x5002400115041400d000005042910010ba90b0344168a480b42c0450401d403203032000d649560100c00c12840107030082c180c480450b281604074400461160b1641c40d40c852940c1c0504d030800e019960303850300c6a401084180710907950070310010705481c0c01074580e2003c0c03000c0349004401c1c24520001b0004600070007071022030249500c40607621800d6580162140481001c0390402101c06000c4908075820007030788140f0001c800d0710f20141c10b10b00040d00c0011008c2501221303032141e421a13840700c0e455034009540750030201807456a00f50414000c1003c6074003400e0429601a40e1071008100103208640030845840c01141e01c2101c00007160071081c00c650303854143e401c4074000c0400c1c3c0211801a42040c2600c25840c5000803014441d9178620003a00c1c50791111418420700d001c3e40d103c02d0364559200c180442155070b0310809440f0b104a1070f480080c1c1034041c940090a45000141044480d924080040001d81d030405099200300c403801c00082d9948207501c005444c540129400903070004510f05021070700c5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 861482185 1250 861480935 861480937
    0x30f07030201090602060f1918050c0117090c0103050405101404020a050d11060901021e03040509060a0f05010e0402160c05040f020a050d0f02070515060f0109030302060402010c2402 80
    0x169000b070303840f440c90b9901d50303506a82d900d0080d1159524203400300c0020380402503a06604003003450100c40030505102444050b0445146028140c880740c102421150040d80c03c890521f16684051507610f2003446e0000055407a44070a80181c0d051548540001d010004107125040944a58403410010b030031810031044242d00c1c0c00c035002c03401000304100110b45460302d0102c05c00b03070640c00408a000e5181000611405030446c11255040d48121103180185242c0b500f044551b081c030210065403100d00d8902041064900034250714091105600140010680300114200782c923000e0820740c040601200115009204141140000400d07034502d0380d08100050201300100c8104079000e0012604d2500700604030f02c02c2c42241c1e0081007080284c240703080c10030780040f0809501c00d0f000500306581c07500c81c6400c1c4114203103181d19004085d0308200007890001c040d0011142d0a10341145c8050442c1d42c080c0d603070480900f019041c07042d85030590b030800103500900808283c8400386904c4080601c40b424005e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 861483435 1250 861482185 861482189
    0xd09030f11060d1e05190911061209010606140f0307050405090f04060c2f010e01060e0a110711040f0f06081b040908030105090405070b30040209011401030b030f07 72
    0x402d10414989034a07031409500e0166a02c88881e010920300130041704014080d0020480c3d40034038202008c041c654541c405440e0300c4a003404049000e10300003001c1405c4407040e4001c582070050300348034212030030801c00942d4041e8248550340e541d262207000d000c4d03a03240196400386170320503404002c00681030f299580d030074003581c403e600600c010740702144150f58103121006007003a4908408104100030a2084181001c0024100009a541082c840650035262a50005106640c0c94410320803005018482c0454040031200c4c820304050389599106883d0325403440041c42251540440c0c201c141c0c0d150b00114204110782c6080105a90303e0005544821080310f2009032104101d0b00c1d0300c1181454050311010039400311402d0700d5030713007404200a46118003800a40f964400c0d00c40c08a028144140201800744040103c600040d5040201490800c1c06444c0c40d41501860818000140c40e119480d506641000301012642c00100300120010024506441c1c2d0501c1140801c0c21900070120b0b15100b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 861484685 1250 861483435 861483461
    0x80c0d1e06080c0a0b030a1802130507021204030c0605071b0f05040f060806010e0c0408150f01170714030c040f0e0c061c020306010903080c15090d09030f11060d 71
    0x45120fa000c020003186580600c103420120704100300140072041c0e82e40c0410380300482419162410400c580101b03074030780d40040012072250350315018003901d81d40400c0706503174040c1d465400705d1515045030b807048080495442080c0601402082000400c03035448003030901880002c004400c1c4940c1d900300317a140031400d4840c40380150f250894400807507a403402030310181c68001d001050a40d180c0f00303000000da07800600000090006008c00700d04c00340306000d90100103c424020591a04081903240040b0710103900815110708108940b00c442940030900101b00c56020071440b505811840c0820305042150b910340c1e80c800d2404484140400107948005031008080007150401d4035a007043c010588a00380c01c280301c0d030186002c0c0c001920341c503800a590169062412403c00d80d0781b070399459403d0300400210326807600004407091074141e02001240d408104c007030050100303510030b440c09000c0303448a001c094121100c6141d40b6082c40142c5040b90914140030b44010340e2061300d185440c0c001c00c03003904281 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 861485935 1250 861484685 861484693
    0xd03090b0a0f0806061303020f0a1a04050906120a261210050102010c020a080c030906070b040204052d0c0408190b091f020304030c050316140706080c0d1e0608 70
    0x80d10905185003500c001c400000e002c0a1504e00719001c00904d03006400030f5a9201e42040e0300800cbc6101c2986042c0819203111288a84036400c100c10400c62020080100f4003a0001300503044000c00000740c240469a000340800d02d010070b159105c21054051030000c0c4012200000f408048080800b4606100d001d168507145413141c7c070381004a003a100d40c02a40c0b40107074803d203000c5001c102910001c008510700300c811245004852408281560021507051300c0d02d446180812095040a0217243c0c2e0141180321141d0b60f40c01e0003c14010003101c0303c0c03494554103403440e000508031070782007048402a02d81503048461100c5456041140e541d01017404681000b07411000c21000b60000803200c0300004260315000e034520104071a01e00a410040082d401c0141e002d044402090003480104802858400c4545a501090600414108040c0b0300c03c46268042c000421205038862401c58100c210300f03194a52784c8a41c24800009000172401910504000c0f15540b02c41004c9580706904031a004410b0b6 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 861487185 1250 861485935 861485941
    0x912090f0b0316110f01050406090201080a111912060803270a15051908090714060f0c07030b09010221090d0e061b0106030c0506180d03090b0a0f08 65
    0x2624650100381c0f00c507420f841500c400703d0240c074080e034032000e0a840004100d03105080311a614074207450003502c064405944d55100072040d960b01c0501d159020a90110500c5a02c8009285a4142c4510001c502a4040d500300003041a841745442c00c1244010b0741060007070301c0c0c48100c0d0944a5101500c4c1b0f0f286800c500000c20544148054401103101d4002d03c0060298a080502c9100255008045007001030412403900c10f605501443d5a0000465990309040c1c0391040c011440c0c80145c0d081054030085141040e011a030700e40084407006c550740c805031920303014071039161882c000c65038100604642c040400c00600f00301c15800b8100642009010a071801e41114044032044000e9902001a401c21050250454012840003100031000b0740301510300300701706400221a008001d40c2d8849a51a00c00c104240b24903c2d0040e00a440125031240c5011480780d0000e2582d0405843d1500895034940b8641c1458046c004100c001d100c90104144d95803590003000304140e1b00c00180d00041402c44000c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 861488435 1250 861487185 861487199
    0x206060a030b070c0c09020c060702070603060b070230010e060601030c1205100b0a0e0405010602030901120e1e0604020109080f120d020c0f03131a0301030210030912090f 75
    0xa014210394000d20703040702c19198008200c2e8100a102d8041d110a400b0520008400070301e48001d040c03900000001e010720b0304140900900f041a2a80242c040504080007844031030340c0802110042a070440750f200001030820082c041c0c52074428038440c0b0b601c002241044001c6019007204813841140001d644007036940308015021640507585090014813100d01d01d071228005c550206400130101c010340c400701541d03000060125070100e00300e403000030000407401100c2c0c01c0c079010301750140c1418000343d801c0185801c0001c0c010007651846604490703e0310b0100c03804000601c02e0000c0f46c50380007951480358001c5820165245016642240010942c200000e03105001041406408c075614002e446510746020b142c3e512901700b6490001219070800c118006603d0400c0f90001e6001200065a1200c515910455481843d940803c3d19882d01010a03850620742030100e1b415660b0490718003250041007441200203102450009296100d40706141103055004054501120401c5010b400c2907500c40007 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 861489685 1250 861488435 861488449
    0x90e0604030c0f0323040305060c1e0a0c0c0b0913060506180f0907030e061b0d0e010b040f0f0b06090d060c051215040c1d0405180319020606 62
    0x140580040c0049002c81c000814032040440c10302d0181c6008400c42a200000b01c00307840704400326081d4030030001410401c02405101041d40460625036107410b0980700d400d200700074040c07056150302921000a42d0159540034010481b4100c3d044481ca40c031030f42c0c445090240540c041c13146103205854040e00c40e401c074810390140200b42d50700688018200b00c031a003c4032822110501855910454550b20840240ca0f203a00c040d110303141d15079020640c500005581420810050007103008002d9044010900c0b0b4500c004948442c82c0d0b15100107141c0098904a90041c6001111207030701a00342840c103049062030f50403d05000c0208202080003c18a400308030f03251140c2e522160700542104e801401260050384a820451502d05005141103440421550b980c5412211008154000c050400641c2802d12a0382e03070100141c10142042c403028000100f621a00350b10f03051180d516840054030208a407030b240c0031180c07564030449840e10b00210061400c2e410300c070503074001403055500084603464028 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 861490935 1250 861489685 861489691
    0x80115050f100e0f0a121112060705091011030c0a110a05011202092101270206190e06070308060405100302150c0a0f110f150405061804060e01090e06 66
    0x82c0f00e10701603049003028032492000c04850b659211150700c40000d5590303005102c0403401c078890f10042c4001c400d420100400405034421410300c0d54000350801c03003415040b00c00c803460501c0803950401128144001142c4001d0b00c0041d07403004d0b00010404210075000010b02400c050301c1001c0780595a1886000d11040c040d0900c5070500040c0d12002e414001401d582c0140540c05c40a421402c04200040c00004000c02d40810512980e5641c102030804102d02c29050800c107002d090400d2020345503400041e40e5004104620300356171000c03c40d80100d1401500e075a081603002a100c03030b49138801d60401070003a45080314194015420200014042c1130254040c42c1501c0d801000a01020400c0d10321166580281c22100100c3c454114440e000c251020403010a080c417650718a05458100028417401d2820886194061400201e000d12401442c00c02c0d541070300c80549045407201c0b07034100748203d07a281813081d0310381003464800080350020316505014140da07181e800600110031510302d040e90f200821 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 861492185 1250 861490935 861490937
    0xa2a030606390c1e0506270406211a040f0b040c090603082503080a0e07120302030a091203090608060112050702010c110c030a0f0c080115050f10 64
    0x2c0000746858580180300782c2d08102584503510300841155555040505a40c0002d814200c00e000d09540f0280c4991018019010030742d042e5041c054203000100780f4910381c5031451594201d9030700543c4103031101c0d0322040052814000c4a070a1000c000c1e883c070f6481c0ca9409040d20928105042e001d10324000402c81c0b0b000d2540700960410691080d00c40002c0707450f0142044841c0024510001050661070180c000a54054500b0301d90707464008030f10015410181e40308021044c44481100c02181d04021071310f41c402d02c002404141103285001e440e080c0310254000502040d0500342c40b000b499030000150100c42c00381e80391030000f26141c01207184042e002c0c880c000d00240b00841c007446440d20a081c0c00d90041c4060401203038200640c2105000d40c1c00c11034025006070340d92084c04401c1940b1003225104124001e0180120419020100c0e8480368000702c0903000389800d403040f40401072135042e00001045000c008000704088410040c3d8055001d2082610800501c611810140b4002075103000807195 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 861493435 1250 861492185 861492227
    0x2220f0b0306160c17030109270f0209070e0306090d02160b03011e030f0f06050601090803040306050c36120616091d011802030105030a0b0a2a030606 66
    0x15030182101c401000f80e9017110003001041451441600c0a4042c5000e81149040400d91159103500410b03040600200080d40040f110500342c00b159039541441c0c405601902e815042e5980d801c800e86036040400384250700b620400081018400020504511080295081d40c81100000c4070007042c80040d409110400700c401c1004100344010351881c40c4400c52013520304885283d80c0c2d25582d410207410001940c6950b03a40744070710100480c0d4803d85a001c0001d00388080d076072781060105503490096000050110350b807000859040003070282a00c840404000040e00d00d62154028601100c50307004ca2210802e02d05800032925140030340c2c8510603c0c0600b00107010550710318a10f118688041c611b04824028212004103d01d10541e1491001001203607142d0699454000c640400502521000da4442d00c14401406150303400704003984c0840d013010010100d070303d40b441c6c640010a000001d50150745040c041e116034060400d141c40300c0801e116101001220780d260030640302501c0b0308001c0141000e03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 861494685 1250 861493435 861493471
    0x20906040506100f1707030509120a1b020418140d0206041a06011101020a0f1209020603040b07050c2e050906190f150f080a05060601080402220f0b0306 67
    0x221030481d50070b43c03021300d20300400d200004402c103100c885800d49203440043e41f00d0003000300c000c1c0c040091034002c0c510034000b2490080703442c400a202d02c07010139083d401c940c071240300320066517201d4108400350390818580c40c581d16100d103844650a01a45c04081c1d481c0900e41c2403080450021869500c11504404840c1c6070394030034001284002030003031090b41486031051200020280034400b4061580064444050761100c1460140442400f4961014198140700c040d1006880d41d0050701c1d0829031000c680722007a2aa07400a0391140600c0e03042c0501481518114400645c00288010103070b00c9103940000555602c0e154001070380c1d401c07500d82e103003540084082402c0d02603058103540410540900001d80c1500f8100c50000d4440000129401d0140c4000501480b03204231806c0c4000c152040c01003100054603500c4030340302d03100106407a0500400000050954a03034903824401c816001e000c64840c480d900601d50f0080214500c1d20200501c0c02c0a48a5507050002d0a1b500880d925006507040720 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 861495935 1250 861494685 861494687
    0x8070f090203180d0908010e060402030714060706090507030b24010e030f0114012d1505040504090c1e03080702090901151d07031b030e070810020702090604050610 72
    0x50300103440c00c41600700d40304120324483c2d01072000c121032081c0c90b40c2c1c65001d20b01e0030980c00d00b5503001a25a00068001e5024000160760000da841c045a006c4503243d00b002881800080050144400c041d05080c03d06081d001003080c0412000c050302c6c819022250161a07003409549005542d806074403040c070b07501e005000558040c081c4c0035503c44000301151b070036098108400d030a440b5015001501e88141400600c2031445800000d09044203c80140750343c2691417201c614020401d10a00182c00c148649401941c0e104008980140101400030300403d070191070300e40204100c81c41184511401030f4905082203a407054102c0c102c07500310b03010600b4603030309800300040036038041d1524a0541d610981c0c0c00c1a05008100c541c018001d03180204010031040c0711804103940300400400c10036181c01140140c115411400d52a10411481d002a9282060601900c0c1c1280f58000191a11651080c40245801e5800801c0b00c3e1f8030030f644040e810b85802c414407080d140140c4545902c0000c036a0815030075 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 861497185 1250 861495935 861495937
    0xf010605180405060616292419080d0f020f030d0b0f030604080a02010c030203010f0e071110020a090e01050306041407030c060804031e0e0d06110d02120108070f0902 73
    0x70490007000c0030314000450f40160141070b100c542c01c482d15000c1e500d04500070030b0403900729804647c1c007080a941c9031034129a0120310304040403c54500c011703145a110b0481e210303400301182c9403605041c14000ca0352903c0c4001c3d0395500100741c120000e020520180c444610110300d1520600c0e82c00011820b2060700c9052030042c04105c0d00694100d40902c070300c039000b542c0411410f07000e6400345024565500380804000c0c2035070003140d001d0051600405c010051a03160b43d0444048811090420001c1c2c0c0341c40f0801c80366400510b02c007800e18400c40c030b460400000c4940c0200700c10100ca840b5103903001c0c1c0e40d89041d00c000009203d039a515810000000740840c000a0800202d40a02c1c8107599016403250703681da12548950b007000c000140200d003004100740e00600000240d201c001441c0c50700400600c0d00610140b40da4049074003032484100d0308030070031505400100d010741c0c5207030909407204409a5100c00940140300c214405100410001807034070400304017a4261a110501400384c1400c01c0030320006 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 861498435 1250 861497185 861497191
    0xc01020d140715020901120614010f050c0a0b010f064407030b0a0b070c172409010c08090a062a03050402030106080d0509120a1a0f010605180405 64
    0x6885420000900010310583c42d05a269049010058455035002d000400781c1c1c0d01c10742d4010081d0318000c414854040c140d0f5040d0782d50342c000d2800d0f4940200c214011603c1d40103503610043e151040b441090104071642c00300605072004810b2103800b50b43e0740c05046504103400f48a6401c03503081c1500c07840d0b52040c48401c0d00e070210840140c410400c144080c102161503411201c160001c0d40d10400508036207010002d084c01410518107960800f01c40c1c4e16400d1a0300c2d0240709090034040c7c3d18401c008031394404d1000e69000d800300b000c0d21014a59000074820b410400b1600d078506946800c1d4402c0c2028082e40085005010040c020403e0b550555100802055440350304c080040010003002c0f10201c2414190403851040d51f40454141000d205050a483c11a088038405400c0000c28044556001c1c0c10340d107451030304545058503c2903405199080c21b103410000303422403000c4103018003c25082000740b0301804440004400c241c1c0d1b2140e080711907010b0f0880d02d840c1d800b00c00002d25040c1c6400d4100a0b0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 861499685 1250 861498435 861498467
    0xd0503042604092705030d09020f04020c0303060405090d09270c0309150b1302091212070b0601180501180e1801050a06050603010b0c03091302040e090c01020d 70
    0x1040c1c414010000250416807215240c41d4461600043c0910b031024042c118241360022294480d00c15520381c0d840c1c0c000c0c0c18a40442c9035446c084001513580d0041e420402040c046c0013150b9800c0f0720807516849a10842d0218011420500465a0050b00040d040b000d090641d8440510b642485c070580c2c10400c0d4078011008101000d1300d042c20084061103021052080354600140e42e80d403d10305440702c051904400b200b513518042d081c040c1501c400c901020440d144010050b5101002c00c00248000000e4a185c1003921039401c0c440200d940c114028040203001d24424017441d0b50345030044502c041c0c40d1080c0301101d440a1302c20002540908012030741030b000040c0942d401a1910390340010120225501144601903c2e41d0044e682000e121741c90b040f086112003400034505142c041211840103104600c420b1200060003404241e040c01900c10088008140000703100b0685030b1302e000303500240a104403420003a40881c0c004000029001004141a00a0300e07080303640140c00d540156184501032 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 861500935 1250 861499685 861499733
    0xf0d05011116030806031218150304050106170303071b03022103190b090417120c040905011205060f0901090c03060606090803030702070b181f0f020d050304 69
    0x2000ca08241d0182554105003102d5a80075500c6060040c412507002c0c102e240203030440c0100c05010000002100d01c0000080c6805400750900000705204d515283e80d0054103110200030302c01041010342080c0700700c8107c011411004051340300c0315522848283e03420b078041619420b0480c280c1e4024024500602d0003030069591110004002d40e003030f4016158200e4a028000003080f040110b000d20182581c0000c0b2020020b144050020401801c0c01820140c25140c10000b0302c026040c0c1002142c0210703c1d42c0c48614024100080d9180c290740003030083e0741509007000c001103010200040780350300450308140106450786070340141444841000c2c020724031395521410340e00c1c00704000c00c4400d00150f03c647c500091181ca801f2004003001290b4000b1400c5400070002d103c41968000381d0001517460764000f543d5103c0c0e030110208520b10305030303141d150400d0761006000b0306a01c1001c040280310b4200e8845295a00389200100d0b16480b1945003503001c20b00a00c0454089840c481507618020720610f259 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 861502185 1250 861500935 861500951
    0xc1b070e0916141305040506180d0206010b1b12030105011b050c01110309060c030706050601030e0a080310050d1a0709060504030b040606050405130c06141219020c010b01140301050f0d0501 83
    0x1084c1920344c1205d0540b80c1d94481c50502510705280001185e041201d01c000c2d10442c0e1051a0007074603184107104001c0502804900c02441c01e1841040100880c1e60300c00310b96100c2c2603c545100550024884c00e0301145082042d40505034203415909129030340726000d040582c82000040d1002c4020815000c0705200c203000a00c51525400010f1180f03054110040d0740b03070340592804006441000380210b04050030021861072641c00001c0b6184255848088503807680d0f2103150110503615541d1000f648000c4d510a81c50034422810505400e240c4200124180380c0e841c00c1c4159000c880303a105000029004002c01c0000c1101005c010383c000e4424034002c02c2207640c40c000201074400a0f40c42c078800c1c61100440c481008611034006004155504000610754003603007426443d4010010030303412805002000500502401c0840ba00101c48640d0454075000b80245a50003803140c1c4c40d407035010944101d400d809484102040c0c0f8100c07603008140c0712a80410310700b0312050150f224011507c664981c943c0f = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 861503435 1250 861502185 861502219
    0x90309080d020c1c020105030403080c0c0604120809010506061803150f180d17090118030503180a0f0201110a08070f030f1707080c1b070e091614 64
    0x191140c0200701c0d0740105044600082044545055020340d1042005104502001030b604601941e52040d01741c10140181c3e9281042d4902c81d10071854421114001d0404000c20001c5034121000d200615a403645450303614201541d00b02d4000380c0d131190f030101c020301c8402c201411103181c68120f1180901680d2000344c45c20035101001c00181c920481d460b021104000503022080c2020054020050081100e9010074030068410025400c41842001d8800c000500c440f10940008102c00014080204118038600300100360381c206031030b0802e108014101d18070347c0c114000381b5106520342244a406440701c03294019140581c031004a1030085c025080000d02141d20400070b0007000740070b825203038410702c00c0d490010140c20041c2d00010174050908044c0020014980c9040d5202989041420141d00e800104070000d01901001c416420900c00d081c030b40e81d83c004100001143c03007140c491b20385a00d4044030f00f0745403003842c911083d02c2c2462030001c01007070807001483e00c44d10101400219804400c1c0318 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 861504685 1250 861503435 861503443
    0x20703170f0309030316090f090203180307150b0d081204171c05010501090e061003320106020606130507050702130b10030e0a0b06060c010203041b1e0909030908 71
    0x341c0f551158001204000040c0c00b0790312511342500007854108640703400d01c9150548050b490082803102d0340d011000482c002d078180c0e500c04281d0b0702182143d80340c21031381c9014820785140c0705400c40554140110161942004190100c107298403802d054188400e2030a49001c0600c014000d48400c042e03021030f0008580c200004119803180c04240c0c2800751446040b10040d40c0341170b80f05504014100d0342c1040459404000c46421100c2200c40c11480d150b0724004a014024005034400b01040203000d595000380d902c0144642d84516403401444c03a80d956200b640c44800442c2e1003a0403144038940007490710365603400340d40d1150240c24aa03060440540100e0300c070222102d0007180ca9a9940200c0c0d2031392510140d0a40007142c1403505020f6078000345810790f242c045014000388190b240502240066840105603000e05100d0802152a450907040c00021485440d0311102d20040364400461010400c4403500c1c000e41f621030200040900c0d00481100521076050250108202803a0106007104280 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 861505935 1250 861504685 861504691
    0x7050a0b0307030c180504090c05060a200d0806091308040f1e080309010e040908070516090c05041a0705010608010b13060f050105070314191103070201020703170f03 73
    0x10219120702d80007070064112034964240c4000e10000080d150ba0301c1c10660741050171b5620a80c0c0116104c500c80c68061009001900090f5000710045065a241a0710641e042c1c210318000c1a030f0404c0e00022074107103031240c240c00014400a421070303001400310300b05020081d0300700e0041d214800019070540c840c46445d420582100c0c0160070321420030060f401e0700d500c04a04c0c103e4410704544685185c10381d60f070340d00d01c1038621a506211084d0030107100c41c1d585501c04560aa000172110340c0d18505403410703c0c0c40d404044049400004003150110702081244a108204152078039120b16160070403480c2d80030848a06500b040c031034805c00110000913804c0c041c1100900c84000041128002c14040040f1403199125000116140c10401c00c00500007520700b0049072000e0921030382d0742c5410b050440c0c03030340d0b85c0c691f5031241c445000808a0044c000201711031404e84580c0c0e605000a0040e0700f4254592007100d6020380142c0c444003003440411008101c190210715030307542179440c043c1104d001c61003d41040b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 861507185 1250 861505935 861505949
    0x30c0f07080d0b041416080c0417010f290f0a032015210c0f04080a0516051008150a0305010b0f040c1d03010906110703172707050a 58
    0x300703c0060541854083c685981c426240002c40601c0c211008100802448980d001000180008125030700c805d10103c0f4042c2410086290f1078035591440303580038114002d12018058038281079401c0e4055100360700741c10b0b408c401c1c2c00c07040360039000c408100b0040c0c264580543e0000c440403000000071104a040c1141c0a04c001c0001c200100c00020000d00031903426901303816100400411001d940c80c0101502c2880c000d0a07204241d80303480318082c4160054115046d20a24001404249044001140c1c400c080c856400c803100358030070601810644034640f044a070850001040801410300801078550f000030f2080080b0907a03800330f00000c0700c2900f0340d27005880d179035950201518641419113000600d00d00c02d44080c010407002201c010488492010250140300e0441da1108a5580079042044c0c880d4010b2424400c2c07182045008074181c1c0310352000c502042c00807480c40d0b01c6502c40300d052480303141e6181660342804800d00080950800181041d0098080c4403070120f800d80d5028203001c050710700 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 861508435 1250 861507185 861507191
    0x203030103150605130906060b03010501020a02041503050d0503190b0f04020a02010f1508060a09110d0c0e0103080405091008061f080313060206330102010f0f2f030c0f07080d 77
    0x201f818500201d030000c3d08141d0500f4003c00050040d66000989000030315030589000a000f00307007030f220f040441010381000740715000e0680c141c41c205a2140185000710320350707542c0449001100d11001d003160543c0e507000d034100a80000000880c84c050f4060448509140000f180f281b4114403c0021030b26203002c0b039a00f03000d24040902034940100509071f0300c000001800c0210b07280c0c0741c9810000791181041144110031001c1c84c50b0400c1030045030300000380501101c0d04d203c2d5841e0710340070030303036810500840c2c0c000c2140c50300203001203140c1c01048080310b4000000d8030440c0c840700c502e03808011812f18100040c07101c00000150400c0208014041012083c00784044d03141000d00003400c00c8005010080341282d56084078043c540e00b06568000e40fa0150142d5421408440c0140d000d001071341c580e0503455250140c90981420b035030304407000030b0425440d68240e403c0fa045d803002d0ba0360700d40b0512140c1800c0600001e8001100305004050140c0300c0e0b00f03a1401e0903443c1d5916112584401012015591 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 861509685 1250 861508435 861508451
    0x903011d0c010c1a0c2106090f13112202090f0a0317160618021002012306040219030212160f0309030e0a0e01080f060106020303010315060513 63
    0x100910028194000034070381040103c4440d141e100c0c09482d035465003d840d003401d01c00314945040d010104c0380081e418100364945800340d811410342d0681c003100d003140184c002800046500d1280003015205642086445180724440d40741e0f1401d4020342c0303016582015849034a80c0300702d101c80c0021143c2c2002d0700780c00340e074034550b4009014800f4610b0070001d0140080714014000a165400003043c1450344442c400d8513032100707058092a491420340043d001c45c2c46c000e0751428203d4000d11140c4140e0007503800400264000504070300f00c4220401c0c0d01c40c103c0d801031218000296214509410860007000903007010840c0700500750000c0d18080760400304e94000b032420941044164940c1e405003c801c1551100020080007078041d80700040c2460405035110785078410580190070410f88c03110b02a0440401c0e41c0c4465a4503100b1a00f802100642d1007803650424210302c00107a054141c54150f4095030035079295507100d440340c0202c00722401483e501c0380740105d4a6101c0e40c004480c03e4505440c0451713092 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 861510791 1106 861509685 861509741
    0x23031803070306050a0e0f030f040e060a0b0a091401050a050904090f050601090902010324030b0702010f1b030c0e0f010c05011103010603090201080a0b090c0f090301 73
    0x2403501c8280000d051280d801702190444000460300c7d024440952a0750302d0082810941c41004100414465010125401500420040c1c4103107411074559000300800e802c06241003000980016003003080081d03064813406440001e080c141e20784107140000814a10410032860700070f0761151509400c100c0310404420751241c000040d00c4095845251303200c081c3c4020101680000d00b4034512040e0211071403a10500c5028404035180d02c941307165608620414002c0c00030003955039075445440782401c28000d054021949107805844035241c0c900240883780c0844c486c0b410446141c003a5a495111044120440802402c114054002034a800c5001d80780c40c401c1c8a0611001000029035245c05820041c2554801d0301c0d0b02489690b0356281604071090680341c9030340001030002080f1004140d900900c400940b80540501c0d00f0040d802103801c3d160f04180c4042440c05084007a0a00 = true := by decide +kernel

theorem cover : BRFrame.Cov 861330935 861510791 := by
  have h0 := BRFrame.cov_init 861330935
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861330935 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 861330935 ≤ n) (h2 : n < 861510791) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
