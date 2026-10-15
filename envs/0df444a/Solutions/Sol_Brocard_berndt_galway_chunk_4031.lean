-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4031
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:22:52.052863+00:00
-- url     : https://prove2.me/submissions/a2a123ed-d95b-4ec6-a16b-a4a7ce3adf81

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 724820143 ≤ n < 725000000 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 724821393 1250 724820143 724820221
    0xc15180a061b08190e0405090102130306020f1b03031b090d0305130b07030504030b0f040218060f0901270c050f07032c041808090d020d12080717 64
    0x101e8881882041300500b40a441000501c00a0241c0740305201381e0501e000701c0e0000c0c0c0103200300c80440b818001c901001500d9651503070003941011f807290f0505801840f04000d01d00c0ca80170612500003102c80076603a0f03490080c4c04010700a2045400012000040c04030240359241c2d031140302c55058050520700e0700d4414441000d02100a181c114440d589408a001402c140d0407030091310035a80305200e880215a034498403000914401c45000e58072040c511400b440b40c101c90b10006070080300150413514510040c00100c1c0e2948401ea00038042020020b5200c0610348002e20f500d515909407040910400c00c2c000002002e50040140347c07440040c000600004250086250320050520b500c6016520840240f9004810355103040180c0282d00f040c0f18800404003060b410004194455441410010740206100040d002d10100720b0300070441c200c40d040030803802541d00c070325201c0320303070f6036509528040c84001d2510b2080c50360440d00c084400123000300f020303002c00031401607072880e21000c2c0c0c442e40d80c03120703 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 724822643 1250 724821393 724821397
    0x90f04090804170f0d021f021201030c06030b120715020304090c030501051c050a2301060b0702120609060c0306150a02101518020c0c15180a061b08 65
    0x514200000800107039a651801c0800c0c64003d103074040d01c00c41644004034079203602c001040c110046e0401103220300c004542500d8900841c40c48040141002c07402c040f00d4006000a8205031401002c0c02400c200d029072501460321420001c1d110780c00701c03200d16071409035540128003840351071440030404010040d10820540c0c00900101000f4044401b5100340540100340038001c050040c14092044288590454409502154400c00812002000342c0b640d10100d030756040c00e04800d41c5248140709410400b4011213001c1c0004808003541e442041c0b04101c0c107030260940400b003d410010400203160000b25015901802c01001d6555a65592000640c018041c00756071584c1c0c0d6002c1580c42c00340c0e41c000399009014001d004104000701b40751500c140036504038030a10008403c160b688410094040d00601541c10341c1c0001c0341e43c905440f40c006801180000181c88070700c8804101290400c40e80c0d940078140c03400c242e402450441c104031b030080c0207401c1c6100446c68030f5601c95030b40080108d4002 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 724823893 1250 724822643 724822661
    0x4050a14061c08030c0c01060b07021f0306051801150c0203100f1d150124031d0105010b03041a0105060702042f0c0709020901050a0f030e0102070c080d03060b090f04 73
    0x8901940c0b407a249400315171503000000c001040f5860200c01181003003041c1d040360042078000749044410707641850000801c80c54035114408258a541c000281c03a110410b0002d118000341c82070384c6056051a1081c20007510788100c68040083d814501e00150b00c0116001400c0a80640041680d0100c0b0043c4405071100442081e011030607a0b060b001c0c90100415058001c0d00010723910465641d07542d202c3d0070b452605032181411410040b00e90f041e03141c0241e2200030000d600c0c0d006c104442c10710841d10360031070310240d0104c1e1074040300004200400560516440902c3c02d210310200d42e5504000c041005030003507150090185c0d6941c402040c402e29030f02c0c52941d100b0322880c091a0b5281d0b03040d58000060f00580175064080c400c4500c0030405102d54002c2e07440d80b04042c4e5405040c41400c0e4000c443c410090310f03440c01070640d60b0070345040c008420b00080590718050301011542500e490a05445e00c01d4807500c1108052401c0340501105e00d1980031543c08240031a13881900f206444001401020014 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 724825143 1250 724823893 724823903
    0x30e09220606180c0509010c0c080f28050703030806040f0609020405010e240a09031a011409100603020918180c120309090705121504050a14061c 64
    0x16003a000c001068001d241903840c518820900d440081e40000141c600c401015004101c0500108440d03520601540d04040d003d1200611309942d500c41d6582403660a01c004520f503001443e02e04040454402034003141040141c2c4c00722601042e03110f041e00c82d201d60000400700f0041c40046031890b5555001603100e507007011410044c4a684110f02d00096005104e09404180003426040e420721786000181e120000001180b038900408071510815035100d131895000744150031074084041160781082d02c5e404100440c959a19505018200b40240e0486a00c0c0b4469409101007014031240800030804a0341c007418050703100c29041d0700060b1140c40106140c141d103d0000100302082d4046055105960410701c00d6590001032401400780740705d4800c9040000d903008010b031000c0b0782000000f16600c0145032500d1403e10b00c04907181c50b104401a141c8228491070301c2001c10b001c2c036207071040c2c0747c200c41102c00030091111002c081800032500180350501c1541030b414201031105803400c15001642d840 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 724826393 1250 724825143 724825201
    0x4150204180605100306050607141e01140a020c1e0c060d05100902030717040309050406150f03290312040b031807030201080a022101090917030103030e09 68
    0x110308914000d090780d103d0148140507081600e440c0e0b50103407003841d09507040505824600300d03194031034034014410b071601590103100d00d40204450510b9107081d5030703140307904400100d0203800c038004200c4a039001130030a4122910410060140b000009462560350640c90903d00c0c44010b00c1959a0510116040098210100040e60f403d4141e1a50180344102881591444695102c000c004101d0100f25002008030b103142c1803c020b140901040340f98424403c3c81e205030b00648803070219003590515406200d02e498002c1c401c0c04d500c0e422806101b00301070741c4e1600704003e08900c0e03501f100c0841c003c048414414140d00011429403000e0100e0302003041d804000e26606c940d90000202168405c5804400901101411009074180881c0d80c0381101e405941c0d400040c0c82c0c006180c4000e40c840005202062a1040214001c1003004040360082600c0c1c1c40028140c0d0503414002c1204032409402c09071210104018000285c01007504000d08009071080031080e41c404201c500c0351003c114a602d920404 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 724827643 1250 724826393 724826429
    0x91503010516080a02070308040b0a0902210c0d020a050f0d140c0a090c05040501031d0d1206050a0b0a211e11072303040b121f03030804150204 63
    0x2c42000452014055895520136074494554800301d001d00440200000d5600340401e02240700d0203229a00015415000500c7d401a5030000b4010040e080000b01b0500224003540701d4034405201c03a139200b0f582079404168542c40c503400690711040710b0050601c121111384085585071140410150060340c081405074a42400b04441c0381c0c0c0d005d001140ea4464000e01c40041180100c0740100b0084050940710141402c0c02c190065000d400e06440440c401d00c4400404042d545040007000142d20840d11503140c41d081c0043e0311016202c050300210300a0031004402c001050a09045400c0751201d80703002c04120f219050701c08850f850b42c2801306803080c00c1c4445c01030040c002c800b5142c03c0070000c48042015040300d8a81e0031480c042c0d8003016054500c1c0f202a2300012a01e89500c0c100c84000c5019245401d86400c1404401c2d0090381d003c8510000483c02c0003100404413596442c1889000718001415140d03541c000c0c0070080c002c000415009010342d20b210030b0b2516405680150440c2c01101c1c9407111 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 724828893 1250 724827643 724827661
    0x6180c030f0c0803040e0a0b0d1a010323070b030705130f1d0c0a030f02040b0409060915050d2d03030c020606011b14070306061d010501080c090915030105 68
    0x980d03070301c1c1614140c0c800440081e203c0310000072501102d415449134051540d6403041100242600300052350405001c04e00d40b0005140020460312428140900c2c40555046062003425001c06d050381c0011100031001000644200103208021641e040450305d60b01c0c1c0c1c031110125258020480d0768102c070510305102180c4211003004070300584040303c050046440d06090a4a800c0318142c4c1e4400c1c0e82c8004002041c002c5100341c1140d12001c1d02c910025150036601c040c5801c0e02c0d4000d07880b5000e4550740c1c04090011100c00d003c0c2165091840350303014903a07424480000c000c1811b114000f402d50090740401d42041050000310395400c0c0c41e02c42019002c00c1076040140282c1003698854006028680000d5450360203929161558614807a08036010003080d075070b2884211100d42001114420140c0c0080003861600510003e404600722010b4802d2400d181c0b0100810103800840c1030109074820010505d001c1015030b0341651080311a20b9441d141c50000104403245801c516030036509010400ca140e20b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 724830143 1250 724828893 724828913
    0x140a0b06270f0a06050d0f090308130303140a0b120c03060f100509011502150702030a0c0602040f0914070507151a030a03050315090423161401080705130306180c03 72
    0xca0500d1080c1705087c2221910f101b11202c0c03010080210700c00c50003040041d0111510018214400d060001e808a07200804420b04401207507018900303602c3e42c4100f6898140040c2c503010b010403510040007244804000603480d900000d102c0c8900320310450000d82c0f1044c05904003801418040d201303c031f882d611a851901c505880300034070702c00b5200b41841c05491415000040344618480d5010b1400c184500c0c204854012040805803100c2d50203020104500409955000080035901c00028031814948034650f0489002080034083c0b2105002d0840030681014000c2803442c001c10300056075045a1414000342c940d240141c64140c4210039802c010140c000000718000c09162001c541c13012444420030401746d104a500a0118504650427184945000072504044415100f0740f600680083c04107000d07034080d075101070707100026000c4140329540c020089a401c01c40f02e00c0c03c286000040300404040c00000d10005008641e09e540d00090b0f524010710b0b03090000c1d403008242c07a140f966814602010 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 724831393 1250 724830143 724830157
    0x30910050712110a120b010513080601050102151302130f0c0309020310020a050d150b03040506150109031110020c0a03050c0a062f030706140a0b06270f0a0605 70
    0x6841c3c1a41c49005203034200a540d000d40c0c1d40d540d181065528550404068119480d01c80d050007c14071204003220900d074290400340641c10010b010f03030742c98030000900d40809000c50b60000074a0b0301c02d01500b174028805406082da0141c80c1135010102d40450000100b1010079020380107454440480170301c907419007003040450b008900f10390040c141d031000c08040f442203a4620002c01c808000099500307180fa0014a00c200031a0b1f02c910710240d031020080c900c1e91041743c0854042d0000420000e174151300d401e0b8040010828a0619041e81c1150394484541d440c17044410701c83c01c4400249801948200480000040060a00c140e455a070386003050b41c80c0310302914680b280e668520003041c1e0f6446400d010480d0b0490045080000030030081800403c0c2d580c2d84e01c40d100d030004110900c0410882e0141228105200001e03080a1400d503c0174001c896a44003d2407140804001d504c0b1891f020b040c035448800c03c003100a001030b104001c00600012441001942c02440c1c041001031400e41160180c42c0d0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 724832643 1250 724831393 724831427
    0x3241b031113051201091e0b010801050606040320040c0e090a050f0f07050403021c060b0306070203041e03020a060503191107150e0703051e01051504020309100507 72
    0x50050200c07411101e601070a4400d06030809039240412880c5004000700781115010000020090001d0700e030070940b00a9450b01e01340500d520f046402c00c02c0038001419005160348002085030741420000509a44078500c80940380401c1c03900703603131210650340c00414001540100100802d0105510141442040b65a6030384503010860000c0d0904406000d554410680b004800040e56103402808042031805400303001082824400800180c84d039140300c1e0001220001080708047d06850201c0949050030f407540d021b40c200c1030900400c950000251000e9840e08080d00c80e100326009107112044683e40c1c4007a500148820000a00035008001140030300c01010b0710654a000c900f6230a001e489000c2000048440100580b8001c00c072040c01000d8a5000a400461030303008a40540d8540440d6800685864010210b95010050382180c0c0300120741204001b8051441c2004540a0040030107a83c2c40c09141c0000001d202c0d200306004036a52019000400c00250a1400700100181c00024007462 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 724833893 1250 724832643 724832651
    0x120f06040606050c0601120317010f09050c0c060402131e09170403150c121d010b03011806090201090509010f060221071104020d0614090a02040f03241b03 68
    0x5900d0b01ca00111600c2c4a071350802030220381d10302480f00480140c242c80540400c10242924414000c0748040704d4000c02d280c01c82e14a0b1281005007038011500f0240482c10900820484003400200100b0915406078044605e001c9018560a10501900b55444101800100d40e03018005030f843d182e211703840c05409084407a840300ea40400408082c4118000035003000c145c181c40c601d20022680200040b50060300d000f10031111044081010f0318a0120500e46444074040141803d0400f41f0448480f800708030024000340498140c44c10341e124400d0b030064542d9450712444025039004440603002020041e0502c103181d07959002c0c0214500a5001d10001406865400a07000c202002002d000e0100300070a1031400000c3d98820403480c107012a000d401c683c00307000805080b08a4030800c13000700020103400940743c1011080201c01c403001003540403036520501051181c3c01e000341c04c0d42c2c19650b00018038015a10b10020701c43c020845064000742c5a4105451102010050b440110300900e180d24184 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 724835143 1250 724833893 724833899
    0x1020c070906120f0519060b10051c0e0708061009150b0f0309120a02030a031103010305060420060415020c091b1308030301120201180503060a0c0203120f060406 71
    0x1910702d140329140e0498004031910000c0f415249101d60100d2251013207489440c0c070400034829150f1940d8040c0c58982c1e40d050303410814100580c10311494a50391400317174036160040d44800740320345455445034a41a0344400b03000041508001580182c18103c0444840d841e142c00d00da0511000c0380541203210741400300c14101215610540c07010fa541001c081414442c100180821903003004111b405240300d00c1801c10304c00b840c4c100007041d030f0b03800682c040d50b903e028607400a826212060150141c4000410042022500118003142c02c90b50041d140400d5a2586840c40d450944840b0401d0780240b00050000349038803400f501008000c1c0039000d840110184804200c822002101d501140e0240c0312580b80c8903259900040c200101d01142c5031034003540b5600300500e550002d0300725200c407860f86000311081d5038004512804228120003215802820100882c1d2101c80162841305190303100e00251031a80e0003407064030347d0365117100030a003040d14100c0114240c250381651b86038000d5103006004 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 724836393 1250 724835143 724835159
    0x16140c060a030b03011401060503071b02130c12060b09120a20060f04181113091a030a050a11010518060904091707110a0302010804140f0f01020c07 65
    0x910a5800400c0c03030341450200c4405901410714040c8842e41950b03a40e80030590500d48007102c2d40600040e0341c0e82170700d85c0b13451000581500b20340300d004c0010f4512214908016500c80090300c1d80d03a40041030205155400040589584419080610bd06030078054080b032078801c008003801075203074110741a90701505984c42032500c5600c5524040c01600c4480c04e00903190360364160f1505601406845a0714150104688192940064004150400045003621914205800b510f01404c0b482e9405620b89100e40200c000440c0d06480703503c4c0e41c04d440e2041c5000e04910181d180992070000350944030051003515200c1d4482e00b0180d000c8403c521036801511955126509a41c5c10394500744460500122090810250781c0121511503070050b141c0041400003580280d046551203803180c51039856001510304068a0401c0401c507030701841c004281080941e9210a410340c1154101c441c4003442400a00c0309800e0060f5000400050300c1109450305c4585415802020f409600c0b4094407200c030789650b15 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 724837643 1250 724836393 724836403
    0x60203120109020703080f0403021212010306201e0d14090601090b060406140c0d08160203130b0c0f030c150105120717010227091510231614 62
    0x21700041c0c1024001341045002c41a465000380c000c0c01201c512001d04004610203921003000b500c11000c8081c010410000f03d8014491161405060204090b03200001c010941c0a0070542480b040320b01c2080519022451040310b106042102040c01081c0344e0410b0445030120aa803002d041d1f11a4a0001401c0b1180b03200b08059103030000c12151400389403041c1201d00340f00b41c0300d0208a40070204039001c1001d504215524180d146038540030150300d05074a0300428a161812688195002003040c01c800c101005148420368000246054a07441c5607080342c0d1804101d24222840d80c80300140700608590001160002d40409000e440856a03d680a0000002905d10380140f264880b010621202c410500703050a03680d40c0d4000181070014510104d16601140030350510098043c680103c00c40c00d1030034055500c040307021808824801c1c8075000c143c1b02c04002428204020b2b0b014800c4054056103592680b1410341c44100c6510340795410304040c80c0d12100c4e4011070780304100d44a040300514000c52 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 724838893 1250 724837643 724837657
    0x9030203030415090e1f0905060603040f0f0210020f2b1407171908061f090b0415020106080f030412020402040506180123030115050405090106020312010902 69
    0xc091801c05252200300c1c000300c2401c4041e0707030920420031004907150050240280c80354111a0111032048182d1040c2c1030740540d00e80240716443d017818100140f54071524200c94001da0b014400c5c00301300c0802d0610702c0d24010103501c000c0d88031020301010041c15900141e5200d4501250b02511202101c600e45400714610680000404941005c8004a41400341c0c0c1c1702d01e03a0440c000550791402000b6030315045180400c00641c0300307448010036072664a002c2c0820205c4091054180342100b0705005c40090340d0303c04408000f0071011000e08101c03030010302c90328020008200394031074241c45030745620b0090365031020030342204010740ca8551b00103240c0500190907111210318030044e515107803c0c5800402010359080f016604942c00f004001a20f844860003806181c0380700c0c44103d00041c42c84001002801d03608a05250b804840c0404043c00030300d1030883e41100c01c40c3c10f10501c407030b0403402c065034540142c2e4840c0e030b0710078000c07400090b01c02d0b008070040482104c0c20310141c2c00d513030300c03039514000b28024a5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 724840143 1250 724838893 724838899
    0x5040e0c0d0803072a0c06030501140d1104020c07030512030129070c0603240612020310031403040303030608060f0a090f050d0c02030f0f0316171b0607090302 70
    0x850120100700719600564210b401440c0010704050030001c21404005c0d1141c0701c2403d041d5000004e01404120b50030003010b040c041c902800321354900700251b5000420714103001d200e82c8460440c0420084009420f083d101c0d0054030541d00c6403c6002c083d510707410760f80310545a600488000880150404048a06940320b105140d0f0384080000103280e1030403ca080c26420782001084040c02140c18814080d0003410566000f14030400d10100100c0100c00700398400c03074180c40c15401408015000305408000040300c50700184c5a60782c21003655100c0b500c40c1e1010340b5049400703440c2e15041030040001e1043d6800b03910180222582c890000c0d40c2ca80080302c4003661900703544040380c90100b0391b8008840300c41c02191b01c0741c0c0007000341c1c03200c41c28007000d9200000440c080700706d142d04504040c00003990506048001d41075030f406441c80725031070f807081e0300c250300960f00480f00310720400940c8442e501e080c0e2a50824036032540c01098210858298000d4800014402c0000003108a031045101009032a409 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 724841393 1250 724840143 724840159
    0xf0d031e09030203060f06131b0f030603021201020301151d01050c15160f020601030b011a1605010203180105150405100503030705031b03120c0304030311030a050105040e0c 76
    0x280c10038260100300612035001c100e00120000003580e000c200d458010a0542c0140005062003420400210f040c18070315030145082480314004940344222400c0f003c601c6040000740344c0000f4404800070045900001c3d4442c07450301750351203043e2056024605803503400004801d0008007070b00903071310120008034102074044980c08140140d4410b8014040701c803000d10407100c010000c490200e840d148111045450700302d200c41303c014842c0e07020420700c807441c20b00e00151401b5411915001074200c414050080c24101024107031160050050803103955903049403202a40503454a0064081c3d8420b854a007450b0040d906402408041032080d00c0c09044842030345445400f50307005210150400a00c049d9403c00450030004640d00d05000416205114501860355620b030114900c041c1c5141c00004002980240018071545c4220b1141d03903001030181c1035407a280c1c2d031140ba0413005803800d199145d404840110501c1102c00e0303070390001410f84108031400c0c400c0020180002e656601720301d445c0d0781d0100e68 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 724842643 1250 724841393 724841417
    0x702100c0c2108070303051501051201140a0b03040c0f171c11010c0206060405010e070c080d18081201060503070c031d03030a0816030603111e0a12020f0d03 69
    0x1040c1c1e030844402440101c1e079540b05543c0c03911989900140c40640100e038868041001a0060308810303d2102e03000d0800340d0070604165003d07542540140211054296641d40c09151a5114000d000081c210203200c0d42e52844c1c0f516180300b01c81c2886c440c96a040c8040c1c00046525928104411102c0f10181c0080641030064031650110701c03c00300c8144180701d402a40042111020b0081d00c0c0c4001070b64000303103010b0411405100494005910040c4041c041d0828031000c00d03070044024030781542080e505030701c03034a0041e40130000700b100c100e144610303003034001c0d200c0308019a10010b06400303c03940b03601c41811382e07071294151403600c411a4944e000802c0e0f001030000107400742c20100c0c800c564203d02d030041c2e41301e100082031965000000d4038020528080c100054851020109540d640080c5001d200d03c030310759641c01c7c2c1d8421404034032520540105c41b85404c100078000e0003280c000c0e00140f1040300544d8507525444501c030002c0b800d0b40200b111070440f00382c0b4185076000c1d01c85141c0c169200c0b61500d030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 724843893 1250 724842643 724842659
    0x609030904200a0f081b07150608030a0914030102160305031e070309030e01020f030913110c0105040507240c03110607050901030b0405010506090f0111011b09051c060e0f120702100c0c 81
    0x101032023811030788035912500804c0100c010006401012903640710306a106042510307042c10040c00c02d144500c030fa8010400c10204040403c40c1160702a45030030015203a44440740d90824400240f502d0f0351900c0008000c00481c141e2603003007007040300e0207503d848140b548201d00480e110030780f0400800d030030313070040004007010304040002c0f002018000000103203401480355540d842d40e02a00551009a44640c10b00050080c24810000103010708541050391242840c01c2e80003003100c42c02c5407414402907800c20b0f000c1c540942c10020880200c84203648a500e003130b02018120b80c0088031158006403501c005003955052503c00e15050b070301c00501c0b0b14101081c0004018400150141c50744c1000310042d000346030200240110344002001c0d01d080c5001c92070f070701710040641d0310a6010b0b0384148103840080c0c40e6119084552040c4640102c008180082d20300b181c0c610700403105d801000c85110780000411000f9089001d0591144211050140f28a1646046843c5040404080c03c152106601002010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 724845143 1250 724843893 724843913
    0x3080c0a1403040503090a0e01030b010612020702040504030908010c020c011d0103090f06050f0c16022e02030c0601050301110a030c120f02120105030609030904200a0f081b07 77
    0x168180390050000d1050381da00324060b0410b0f50103d07510703480825103080516012042c60050900462914036544c13441d100e51000c00410302c01d01050210040401000201980440349040c3d0090000c0c0400c0c24186002446a0214440c0680c2d952030541402c811070710100c0e40c5641201c1c140d49072071450090640f802d80081a0340c48050605075600c2e20040092a00440b407140b281c007800d000902440c1c070240b107038600b001c000d0075200e910004200b0844c04c40d623002d40c1c2504983d015220403001d10003101d003240d8061500c4d100001e0b80d0301100c500080c48e550010041114074005004e964442e41d8501c00c2c1420b0701c1002c001e07514280c00520407452190b05c0313a403002c401c0106501e0b000b241541230030414412100646202000103400140100c5001078084000b401000c081d002070010b485c00f07240d400d4581c0100d4a0141c81141c590405125402200110012400140180513654001d1035406050214042c01c1080442c074171000280700009203500c1030301500e00301d4100528241d4140c3d1058204c03 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 724846393 1250 724845143 724845157
    0x10507050310060810031a0106021501030209010b07050c220e070305030405011101140c071e020108011206020c100b030d111b03010f060e01061202040f061b14060601080105090403080c 81
    0x810000a0001c040395030400003100086000c070720764187e5410804020b0412441c0d03001c44984a080700010001601c0d00c000b45411640700c1d030038aa850f1001460464100002440800d07031220078103c1b19484c0c00c1020b248581034800d038a03c2080a036a0b8920081e8440009100181c0141c200703000401107540200754106204962200001300201c85020151402c1c0c001c0d24000c4c0d03102c00c0450a00104040340c0c010b510801c40d10188003511b45180d80c0000c1100703205020b072034078800c3c0b5403491000b085400d40542d400d00e01502e05482c249a05c00708404001c00c2c400a01d14400e00c10f450340c2c550003902a43c1c02c01001d0300c46202500c0342c00300741302d01d1070f407810038a21000d90990350301c500a00c10440b10b403007100050b040c184011445545000306c020200c0800e10b1040d42038034070420007000085624914882100c04600f40039500301c100003a64402807a41010180110340500d1703514100366004120507106880903200c900e51a41c890b4213010342c0e00001c5600902150003000410f1003189841d0141001d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 724847643 1250 724846393 724846411
    0x260703060c0c12020a060c030e0d050a020307020306010e160f0e0108100803071b0902040528170606040c0807020c01210c0e030c03011509021303140f0105070503100608 74
    0x540d010b80e500d0300e0003d80f0800840340180c000b000c24408102c2680500680074440746414030000020b209025100d506441844041c441d00058281e203190003031094401050b00181969003130744c1d40310220807001c507080360314140100050000c1000310b4021401c4001c410080d0752a2443c480d44072006440510f00500f030f8115503103050800050403002003000701100d42c4281103410141412000c1d03110700c520035400200f40a8010301041c0003540b501310005101d64055003400000360001d0800c5840b20100350010010046c55480c4000003400000760350340901c030241c40070800b002030351034100c4841303809466540068220165034440303984148850465550303144813541c910803000320721720115558800108045400c04040080341c1c036003030001c601091800d500900c61620b213119130f112001d80d14011340100315804117101d0201098103100c0c0d4055540000069000c100d8022565a941c002d0058000c080d03091000107103c062203202528040c1100542922155040071404d8a070003034020440c0d05 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 724848893 1250 724847643 724847657
    0x80f07030b0103151407050a080a0506010c02040f020f0301121502180607050c09130204050906040f12090302270a0b0f040903141603170f13080c06040c260703060c 72
    0x5c0daa520410a140c0181e00703c0c0c5846694083c010006071081b1002000d041074186403901b04110341c1d0b000300c011901290f04a42c0094040d04084098000340100201402216800f200214003031280d00c901010710360188401e031000c80020f920b144181d2292072802c0c2c912401e22800bc0c0c0e404e00303204001c0e1003030380e100b0020f880a02d0070b0b51002c21740040c41107d05c01100648610f0010641c04d16108142d000f415030302c041c05443c5441e8032200e114690300c80740240821140d820038591548241d0604001e907500905124984a1403207035800104000c0920701ca89445140102e40848003d104013686004c02424110b1484129410400100f640131000d8007405081e81041c401e000f20b09000b4002010a01c4065601560724100180b00c20070313000140c03c049020706e05000074088000802c5c3c3d4815a03441d62000d000c4c0c2c0ea80360603642130181c403004180034801d020900040198941c0305000341e45c825030880100001040110003c0498654542181d0b0131002c01800880c513141c200401c0c8145604281e5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 724850143 1250 724848893 724848911
    0x1a12030a0c1202101a040b2d1801120b0606130302090c090603010314010c050a02060411011106041a0a2007110a0801020d050709050f0d0615080601080f07030b010315 73
    0xc070544011700b11460015035a6081c0700d41c28641407084201048090790301211003000d40d10a049150141d51403444070401e0039410031002d0360751003050611017040701e1a41040d541e443c41540c1c441c180138102218450755900c0000d406050034030996542e00c03a00301c1c44030556840c580a208086102610b800da0b00036040020208a403070700300c0110f0007184200030381441104010401821902c007904d001b001c121007040080509070340001c840e03400a81140c44024214200401a54403c2074504080c00900030501000103002d80b51740e240740540c00411186801c1d50318418450111000800c0f8054141d00980c08100c40030380100c00350044520480402e642004694005a03400e00154850f407400ea40006401030452190b0044a4001010381454952107050500240e45900040106c6000e507811142c03080a12005030804d44809400403000351865484807401d580701c440900441740307244a4414039100311640005c00001b241d801c40d150100ba6400c650303401c1e07500e501c1c0b860340100b40380d1268011 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 724851393 1250 724850143 724850173
    0x6010315092c07030b0c032205030d06050a05030d0813020d120207091a0105030603010f0501060e0102060f01240e04020d0b0405090a150914011a12030a0c1202 70
    0x85100c03004000c04a00b0b030802c0c0d000000e0a4048090b9001c0c0c56800003501080042d1111a410703401071210860b040c0c5903a100250815440c0f450540e4031403102d0301e02450300174854007000520342c801d5403840c103200150300d640501280700214854240c069202000710b6049074400c00803560420164402100d006003190000340b02da00440380e0030b450600041c9085c1801540410400e4000c0c80d5584051000d0395811031720a4001640d5010141400740004c002082d0390380031341c4a00c42444400400700300958485800503e40504410058054030801c00410005855000712504070303011107242c1690300c0b10014140300003502c407100140c24802da841c45000c40b603840d800600f400d40a20703080000c4044502003040152600030340b20541541000741c0314000710b420500508007084121030b02080086142c90800420101000300303c105502c2c21041d144044100e4102c2d00d0880340031103210109400501c40c50b03840f481000105e0010441030201c030302c00a000d480c0451315104580c01929000300c504030300 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 724852643 1250 724851393 724851401
    0x120f06130e0a02061210080703210c140102130e04020a030611070b2401030e1018080309060609060603011d072c0a0602190215091309030f0e06030601031509 69
    0x70520f108803500c0c01c02814000f0701c0441402884000001d2041914585036039035001d0495542010807448030740400e020902901c0140800c6501c33411080c8640707101c5240c10300070341000c4458180318044450014045842206507809641c0045c01e0700b1072185107549940090a003082e2508010300217103c02d801044031003444074800c080790011040c00520003101c2c0d40480c80600e500c941814601820048003010010740403010042c070701d2000a00f4402c0002c40915000c2c9403a00800140d00001007003004036000c075605000700000e0340c400d00035858a10401c1010b001c24011007101707403130710030b90640c014807030802c0c0c03c0e0420751506118403d002c2c000c843e03400340110240c400d014680c0504030080c1605043d91058000c09103803000e8008031207041440500051a40b0020788140141001d1425080401c0200c81400200402d11011540704041208c09003031403807000e401289507503880c000002d000c0c1014024111004148034034603a0b0300300055004101810742c103c008459404040703072403112442 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 724853893 1250 724852643 724852657
    0xe1302120f010e01060e04030c1203060b0d090606063b09010e0906180d0305062704030e060403080405041509180507140a050d06020906040308120f06130e0a0206 71
    0x4203c80341904145420343c2d600740d01039200d8004c408200000301341e1054034481031f80d40c01002119130000301c1000320090310240c0c11007105120001030302170030102d0310b80c0304500710b038425102880001e5885909960381c0120070b1181d80c0b88001001240e019915501e84034042000e0a41c920600d5007070400071541c810300980010f10b400090b00140000401c041003010b6002d90060840b0342c06940e031321261500c1d01403035a6040103041c0ca4002148086d03856001342180c0c0d0545400048409140714022440090141d40903400f080440c1c541030064182402150190ba80000c8454542071400341484018100c00900c046020407010011580451500420b84907100c0725105034039581c1c031070402509009503640000c90301c03030000890592039181c00055000700d54084031180c00e44441400c20700042c0c890b190881d60701c000001008404c2000035005000f40c00d00700c0680b00ba441e51172500ca60088281038940507403061801c19a1400401944c120f00c40c00d007403610507a0409685036000c030b80c4542041c4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 724855143 1250 724853893 724853923
    0x60b0d020a110c06090d1a070801050a14061c0207060c091502150f0c0f0a12060801050403080a0f02090303030f06010206090604030f0f0908030a0905040b0a0e130212 73
    0x400d11501c662141c40e804031021444050f1400d00080c02c00601c4500c00e5181d10350003400d20041d28001d00840d050985c0340b6070b1007014045564644814014030900303003400b984c2d1203030340000804640340d540c1450b200202c641c0a00360601d42403551f83d503c0d00034550f01c008109010313020020640024a24001c6198410003074507100689424140480c101c1c1c00e001e10604119881038800d00381100068003160b4210320f411080307413051b80f15405000114482c501d100c0005242c0010524821580895807040441101000b0032109850b180c0c1d5900342c5c0e405541c05000100c806011a42d0300440740c0c0216550600010300500e000b0309100428156041140d1b150203040042c400c100782e658041c0b00b60f5520110501c003404040c41c141c1d40103014140084120410070140e1603611140c80d00450811000e00718039001c0300c0d260103c1c1c1c88014440c0840b4001e590059041c04108001400c0076540b4509035042d01440700d01c01d95034041403600c01c00001100f640d0000f01148284500720080c00070300b800040c01 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 724856393 1250 724855143 724855147
    0x100806010b0d050a0b1c2a05060a0e10080f1014010e011e031a24180a031103011a0a0b0f12010608041a010b0f0711060c1005151c06060b0d02 62
    0x19060105040f8200207c0322501c055507110a841600052800c00030754204640d40d0b40c58422a1504540c03284191443c0c43d00300c40200381c0004002d8000d403602e4450800c0681c1204540c0c0c5d00040007005410500c11138001d04114124018a5801041141034146041c03402030103245000c0c900078509001d540320000400d548407026500e0f050155482001101e00740c0b00709138401281c44c5c03071290744108000018040c110201e00841c0d02c48006c2c0d00080d092500403c904002c58403803c10420305000380b040d1390b01c07035840c3c140c003511802180103600d404d4a00080003107580038640082d1800d141d0002c05100c0c1906410400340560741c0d2a607180602070601c07683e804100e440e06242c100c030b00c210b480706101c0c4452105401003240140e11011582e13143c1401c2c10442d01d0f581249403030007184400940c0d1310b503c03c0300070606410030103001800310143c4003610003d01290715480c649601c403c119600c4141c10102c0c40803550003c00b15401c8038500305210700c0380003905036502c2c58200e21b9034000c4200100443c0e00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 724857643 1250 724856393 724856449
    0xf061d0601060e010206100f05010804030c08040306050601030e0a0201080c0703020304032a0b03040b13020f030a080306010e0906030307170d02070c03030305010902090108010311220203100806010b0d050a0b 91
    0x81000b040d87c0c800c603130f0000301d5195820030034650445c01d0244103840c10012a000050205882030001030041684001842c2c3c8035511b03071414002402d8100c0d0340c0c50000c1d05cbc028400e1102d620004456070281d4041c0c4070b0907501d0b106e80e010701c142980203010036003c3d44000c220000024041c032007589207000002040201480041d444c40303d803241075030300064062100b4010301000c60070806000381c018a00c9442d61603661014070125032445407002da83c0d40e050142102c003c00303101c130001c01140300e44401d90707481a64001c14000c2051814080c3e0340c003a0503920502264000980c071044141c1c08403c0003001078100a8241c51842c166841030000b10740703a4404d02001c204068040c01b1b6030340034195820040d03040c2000a000204034000520016018080e80048000107490340d4100b17400044041400c1c69441d42d4195070701000c0e41c005c0d42c3c0d280c0341600c0e403130780024401004180c01e4141d80c00c50391340c90300c2c0500b410ac0356000f03002d010b013007030003256a1454051000d94030100c25280c1d84540e00741803448692 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 724858893 1250 724857643 724857647
    0x60f051905090f120705010e090708060609040f022208011812031d030415110a0f0602040918050f030f030c030405070b04080d11121c111c180f061d0601060e01 70
    0x200505422701452018050050030360b040340300710b648040b05540d0540c4a0074104006005020b030000382240c2588001400400e8525150b04030003001c2c400b41c0004c11065a40c0c005500300e690352541c000481d04403002d4400060038401045440001c24503000c64035414085000010b400d0519484450764800141000307080a041a00c445420150402c26242c08410501544590080c58010000041003030501c0c2042800d80c1600c024020075602003011401c405403a000344640c100c016a00c920a86c0c0ba0264080b4000003159001c0c02c210060030700b2740e215020480100c0e00094030403142400340f40c50224108039540081d20040c4501002060b48000d1664044e1114024031240b04440d0815118440c144030744070101d0310316000d20b0400442050002d402d440003271000d4082d110f900900003400c91040d03d040c1032411f007903902e132107020800500091358100c064040c50748000c0112000c0088840422015804148204845002c64000748440c499280c1812070980080c0c0125002c1091042c00d56 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 724860143 1250 724858893 724858907
    0x803030403082d070306030b091b0406081f02120406050a0e0a1713050904030309170a0e1302070501050907170a02090c03100305030f04060f051905090f12070501 71
    0x5075080304001000d01501c90800c02d020f5101004480c4001d6500218040c40d100f40d00c980700854001c640805103090200c038141c4c84a0f0100804040c614407103012000074500342c4140740c12076800100030310100a040780000200456050003100e0154240b0880d56821107800306144528480c090005041c0b42c0740c4030100442c0c00b04101d606480e44189103d10000381d81500c03c2501e96010b0f4103240c3c85054050b02101500e1a540100fa00220750304188400c264058001e281c2c041d11032600c0b200510440c4500080c240241039240c400544940780000b11410810001102e1120600025140129649519007960000e485c15030a81c1d01940702005189001840348045070100c2010704814901500010558075014010f0401003100201145400c0181c1040c90010742d0f101080c0c9450344916880b04070550028130038200840c0c000303126412940d02c68400c0b070791603904030fa03241e1640d1a61258121042e0b000325203840d070003001c1c40090155660320b00d03c19200d00d2048000814a0300c1c1080c000401f89 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 724861393 1250 724860143 724860151
    0xe1011030604050c131a040503011b0306081b100e03190b01050a060c0204150312020a0506010b2d160b04140c240f0301030b06120c13050a0e0601080303040308 70
    0x13600280032100003500c202c0281400c541c400c48845006800d031098001c00d91056600c0580e141d1720b04074501c2203a9a5804203000b00e800c0d1500c003004036640d2188015101c022041d285850f960a041c442d00d1146848101907101141d689460640c800440b00481d282429030040ca20641c0d00381129402002285d60b2141d01511095440a803400c3c50000d020344005400f00c2c000b031041d9140c0340d006c0c1002c4682016000159007001001341e101e07060801c065201c00c4094016030f040e000340030010030200d02c074408980c201c3e0146002c0e8107800d1056890fa1074408407071a0780c075004050801c00c40c0703101c5103c41e0203003407990f011706844a000e042c103141000b9064195400c141450300300004000e5203603107041c9102451501001450001e0700385080742c1202d0f02c50f00e54103055250001c07001200b071040310703100ea034400c40c42918105034100d01046071917902c1202080e010b51002127001075a943d00f006401942d0451003511010400404078801581810426001805554004000c03c010306034440306680e04 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 724862643 1250 724861393 724861411
    0x3030a0b150d020319060b27090610090905070512060a0b2a030304030309110d080406030b0f060a0c0b010e220f050607030b0109270e101103060405 65
    0x1000d8a8400382105000709181082d001e0b0740807000466002c06041d401050031101541080b203907485880d1200c2640103018524105a244041703102080064100340e440490010044d00c500e40e1003070104840404054014030400130403090008181f5168000e19001d480035031242502c0e1010445401c80700d0340700030142407080c4c5a6403000c103c51140031003103542e82901c60750100001908051070710855060340300c00010511001003004149035165100c0c3e13820700d110300c40791740748100c40c8002c000c10040780100c041c0003640200810030180303009622940c05018040c0a03040c008210400060b1950024179194000ca40d601180c0ba00b0000240340c003501500303102e41c2c0e0101504143d84040140c01410300c240c002c0c1c0c90350b40c0c02c0c8414031101042d10010580e201c0111045440c26001c0280a4003444030301c0e601194101c6000308000c080d1181c000c004901030421080c0d02001c09a20300068010001108a2070003000480c42c1c542c0c005006503488270032501043c5a032030401c1e0f4240004c442d001801086 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 724863893 1250 724862643 724862659
    0x312060b070f0221102003010b0901021f022115130b031e060609070207090f020409050907060306530105060112111c0605030109060f1107021005030403021e03030a0b 73
    0x4030329446c10b41520b043d204140012600c9070710040040c0c2c544404003510072207256011104030348100301a001010b01d8800944645d220106c07000c0c071122440c4041d9818108007034500c072514502d0030642031032051000c21800209403c0d83ca480440d00301550100c140b02030907425164450b48060811100380c105c01e00b03442c000e1181c617101000035181d840c00e0180c180d000e41c07640c01008803140207030140c0e00a0071404030104403508107081107541d526224030440d000302c1d081402c0000e4031600f4480070001001411074a003840040342902c0c0c4142c0c402090605c084c060291040e1100c003d078132808401554515000081c0d03030030118005054403101e807007010a40e03401d02c80d5a514074042c10701500c0303c541044070749261580d414054607000d01a0307508869007641c6000c0c285000c0c410107400c00c0141c080f11620411843c04080400e400078895000060340100f0000c098080040c46180150b6002d1300030300c103a07412440c18100314000ca01020f89481d14582c408414041942100d20034425805800c460b201 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 724865143 1250 724863893 724863941
    0x42105010c170a05040305120c0a020d0e06220b070807060e0604030c0308070c02060d06030b010f0b1b010b1305090c030601180b010207090c0306030312060b070f022110 74
    0x101c45094000c00f150308964990f80130804042c012800ea62200702602da10b00100e14080f080c00455800c800110740062250103080340d84075016041109441d000900f840f4038204000c03225108202d400e078008070030303500c0e00c0000180d07070418100070b04500e501c00c100d895994410380c184032044e6040700c100b00f02076402c443c0070312001030340001d560341406034141030120303241d075500200703071902688058065044003000480c6007115402d91700c0041602c0c41800d0610159803039221419200c01d5034010001c840c401040340c00611001128080f041ea03095800105c0d10b002da0001080311001c6255800d1401500c450130320184c280280080001a00242c0003001c40358504910f90740142c2c4d01c80b04102d50395036100301e40c03012a44240224009403c0c003401c240b000850b50003008004000f44c1c4815000500380f40b550101d40950b070b000d684229045004034034149030746600e0b000f401c414401d40890380b1000d80c6212100d0355901e00d022015a240310f001918070110580e1400b0140e6060400e00c0142d080c030b0700840 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 724866393 1250 724865143 724865177
    0x130605101b0b04031112040302100806220203220c171203010b0c190b07030b270105010f0207050d0b09070f090e1002091311042105010c 60
    0x4048208a6071418005041c01140c12440200311a44064250800c640c100000d00d604030300c240350700c200f4240849980c0c041451803ca0315024500000b540b003044044010100b500c1340426907000000103001261429441034a01d8043c030800c95805941500072040144820046503041f25180301005d8803424a15a80d80b0000d180809d40039000c40b50b016402c02a40204041000c801c5d06268641002c2e504e50b111300c0701c821582c10070090080b01e4440c0b1004042c000840e180c0b0140c0c0716511103181e0790711303444010040e400380804491542c4c001203183c800c510300c0310f0f0741a40c0c1c5040c10241e903a02c01c1c240d4100000103051454039207007541076500c40300e82001240c980c0d24000302d10680010081210b0380301c0c200707060f09052a1b40d000c01c090104280010134045a01c1c1e100074208501c06040380c80d910468500d00050b8082c0460165110075800c24865aa040342d4002040904030003446a241986030f049100d0150f4190480180c00b8030180002000c02c80248103c0004c0f54860030107400c220b03505116 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 724867643 1250 724866393 724866409
    0x120f050114040e010209040e0c0f03030a120b061306080f010e0c09090a15032a0e0f090f010509030d060b030609070c0311122a030d0902010c0f03030209130605 70
    0x466020b0341d50b4140c3da07800b2200070b5040d03484d030807401442400001440d44e2400d13034500d8100d44c085d1180e05418441e504c02d140010032269a44000c0d2a81611a40406aa4030082000d0209107820020401200b11984010b012103c0070384004e450300310f280d0501d04440000300605030412846510024180200e400d6940b096940139501264107541907034802808070060800303520307454800400100003104014075a06d10781000b103444034200c844140140b0303d44089400600c9054503580341200442e408400c0702a0700b641c40895042111010701041c48600d00f10b4404031502e1603607400214901829844502070103009004040c0024158140302d00010503070f0a010700030401748480e444240381010b0088030f100803400c907483d040d1032283c2d410707903104c540c1541b1a805404481c8195412000d00301c001d068500d858420b00301c0194100605c2c500602e005114100c01681804003985c604000502091b00b119003e6102e5a40583c80c0c1710544280304804000401c2c80c02901c1c00e11105010b26100c0b100 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 724868893 1250 724867643 724867679
    0x10507021902040617012310122901170106080304060309170a17070c0c030b07030f11070501180305090d0f0f060c08010f241707120f0501 61
    0x4540c810072400c0e440003400410580d40150140402402c500500d400103600c01851a405081072403041b0340120000304800608440d4100a2103110700c2c00d21050301ca102550030918444c0720102d079a03100401802c000301101c0d000000d4102000380c010300c4500d400310b042c0030801410400070f100a9091107a001c4e1030780594000d400425542d011280d0034865071f0f00d03c014001006c100380e2940c0d292418001000510303400300f00510b008120740418081407040c0c0100c00d41980051050039018110350321301c0c00e4101d020348000d0803d61184501c3d50041c940d8416000001c48800322150784041610b031060079655455041402d014026030702a01013500002103882c0e0038001c46012130360032070038034110101c0061410040c5c80314440c154460200640e0307900185400050752962045aa03031001c03003000aa0042c0507400440c100712000005101c00d01691034840c80b01c50408884c00040039001380c42309c1e030040718240300141440002d10791080c0c0c1817241e405140440c440500180d0305200c2c3c5000c0f40f043da88 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 724870143 1250 724868893 724868923
    0x70c15051f0302063103050a1e05030d0c030e010c02071401051903050c04090608031315140d140f1f061d040615260f07080702120412050f01050702 65
    0xc20040d400501e417860103281100d20301c4801822500c03820302c43d50350a960306048800c82002503120000088841000c140306034043c0c0154034120010b02c1c04405414a040c0e03040505803504032442e803d41c000c0c002c0c072414522950090140a24002840908010b03a2032014107011042002c0d82040c5406504800114603604001c947c5441b00403a0349154402c580c0180f03186458240045880703c4003000034608001e200e00c43c0140c0035154000000c041071604941c50104001d1950342e41c00d941120b024100c0f0301800040011841009006210f004404590302d4586000c0d02d0f0803c1180105548400e030425aaa5483c0081c40e00b01080903101c81c81e61051100d07414035070040d4140c5646c890304001702034108030307940b00c80012604001030314184c081c01001d0240802c504982740010002d100443c420b4240318420445501e03128000d440c8404083c0441707046001e80502001e0030141980140000c10000091100410690801c1420a404207010080c0c6904010600403802e40c0000d080b46062416 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 724871393 1250 724870143 724870177
    0x1306080c07060f020301240801061d090103030305011707050d0308090f0d081504180602070c0b040b07111002060606031906030804170601120803070c15051f030206 72
    0x1140390304541c05003400003400740381821002c00b50020b00e600030703604840c40030002c003500014480c0c881c022842000100c20001e4084001084010301c04c1061220614185004021a0039640049460108247c00650200f62034600400440768102c0ca492600c51240f40500111800c0c034000a5030030329251005010040003d010409504081c0602482000d508048420018451101802d510403c8501d40349028141180e44442e050502500d86403241d00c05854044000d02d980e00c40c001d400c45181130f80d40007040000401c441c022540140013a180210000c0d4075400280fa020301804800850710780200f04490600c0f1101c0e40004036103802040868205481c5e68552692601d1000e110b9940000380703080c101c1c0001801060380c010800d0f144030580340595001d03c910043c1e41e42c0d4080c03084c060040207000e003650108140c500a182c00040e945131183c11242a03840700e401071140440764940c016a0b600500150014450440e5800c80001080390b809500c0c5800241d168000d0f0184100d4003111 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 724872643 1250 724871393 724871401
    0x80d1106190e0307060c0801050315160201090b010f03060b0607080a08040201030e070611010507020607050d0b03010204121a060108070c030e0409020607080c01050a0b0a060e0a05040e0d1202130608 87
    0x3034024520828040c003c03241c03100c0b0b880c00c041014004410002002c01c1e841000803a8074200840c41322154a400f08404180d5110380c943c04248206014031101155681d017001d60001d82c202544074020004001c483c0c0c0e000d419810042c040300c0c60065228480c8500b0884070340041e185000b5a04c400c1d04030b007072002c515640c40c001a00503004e091155900e0780119a40032401607004007400240800d600020011555180d1050b40d540c8020b46881010607024003502e40c3c0340c40590041501000007034000340c1495075602d010740b240c01c2046400c58034284480f06051400f0080c5c03426a500c502f00b40780490050420500140a60307a00c601301074208200890141c03910b450b50303040300d000755034064201a0ba82d2103e0920fa00e6a0f040000b200c0029402d09001c00c403508058014246078110003014046180d00e8036005503a0080390352409900292503a07400150b81c3d44600c2041000d248150191001d0a82008020401c0c2c0f501980103801510601c200000c4504802c003100c1940c010b804c01c403501e911 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 724873893 1250 724872643 724872691
    0x120c140901090807150e030c030a02090406060b0a050703030e062712030f07020706031b080720030d1503110d050a050d02010c0801120b1b040302060c010204080d1106 73
    0x100b150402e4207188244000001c0c0102c03d030300200204201070780e620000f0905603080584404c0c001101c4c1d43e05a002203001d20252810341c003155001071241000080e0300340e031100c0b0f0582c2e5400c51420039000c24004500780b402d00d50035001c4ea00840b280c04028091501c0d0103407521021545010f202d03210600018401f804c580810040c2400b4204401d200c4da40324a001e66840c1c803544400c0743c41c03400501441d11b00044041c002e00400c2800d200343c40159000c42d210032030031558400020001d07820442c0c1c106480c0c8150310786808400170442d400c0c020350b03a0380035002414800d641c0704601d917840e40b02c1c00450410200d9007101d000000d00d078089030340c3c164001c694100145080c0710b8a1003d007203402074003010b04055405600c0003003440065119060143c1c0c1c1c5102d039051094440c2d6000d0260001d40d400217a200030110313011030780541810307001c3d8101a00d940201c1d041e90000d06105000381e5000505214140003000b10aa540c1c401c3d00e0030341030400c1c1002c0e034180c550401400d03000b1548034031140c40008034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 724875143 1250 724873893 724873907
    0x14031c0f05071a0105040b240322030e010807090806040609060204031b0f061b2621061009060509010504091802040c0e240f040f06120c140901 63
    0x141c02201c0f229003100d940c90700c01030200d8288611031056240485002050519046031044000030015240c100900c00b80590540e5000a20300328140400304044501d066100200c43c0e80705001c0d540c0d402c00ba44219001605030345020b400c03201480510001040f49590014109500650007200402c616002d031a01c50080d009a400c0102502d903100e50510305014444138600172145000c02041c0c20b550fa41d0429504203841c08207503401454110300d000041030031042074285c2d005681107100f42c100c41108000915030840424140b00040514840203581001e5280d00c2d0400001c4451018034145c03c500600941e205106540c1403080120310001681e00078004d440003004e03038440c01e000c0e40000b00c0000392415000e2401301c0c41640340884c00d00142c3e100c3c0c41c030b0385002800500000740781ca0528403242d010081880248080d800104445101100a080600003d0034501a041c0307138541404c80241941003158000010507140a14100710700b64008108150103540e0343c2510341e03440040c40122001 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 724876393 1250 724875143 724875157
    0x61302120a0506070c030201060e011d19050901020a02070f060c14070f0f051f21110a03051b031e07021606020c0f1207090507020a050607030614031c0f05 68
    0x94010f1104001c1d0241e0000c000301c00b064442d038001c00c006a100c240c80100d29100303004144099541c821450142402c01a140e078200b40c2101134005c01c200c006141c01c00b500c2c0215031038511a5008140080315613010070410025200d290000001d640c03c11000429074014808094040d403407a840c9255000c1003801210064688880d42c82d0545842d40050700070019184035503409030700d000d1404040c900c02d80300c0a1910300708075a220f9910880e00b9208100e812044c000300c101c15a65022210b0741c00a0f450000d150480440c1c9020131249000c50003a01048801c1c1114643d82c1070800800407c4034036800d1040011907402000441074580c400c049160143c040040881384904400c0401c0107500002c40b0256404100c0e030741242007410070b09102901000c200e82400300e500000d0244007910442d08020b82c4400c4500c103d0718000d040c0c4d242d0318a080410385080001ca031781c81005005880200c0d1801d0101e120a40003400c0742c0310f00001e11009005107a500d0810007034051907100c8114429400c0b1920 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 724877643 1250 724876393 724876403
    0xe0729180112140115020118020f0a08010207110a0602030a0e0907261f0501050d1a060729061c021c0501060509011a0d0902042012060102061302120a 66
    0x110140c40b9241c15011801c0c002d440c02402105c4405c54801e20501501c91491840385000000b080a90300780700c41d0a00100c6030715400713102c0141c0441c03014001d1001c0c2811501031220500d0368603004040c800c9640b000e030440c0741190800c105200c3c000c0d4008499508000c3c050740d04031015980c00728100c82d80d003003200b51000c81017041c45818000401c81404107001c0c03141016460700e500900c00c80f400610001e03104250101d00c081c403400b0400302903903001d01c0181c8030015182480b280f052001038003c1d03000c0700b001c0710403151802c03c034480290920521601c070b84030080600c000c1c1c104880052a41400510605446d41c590840c140441d112642d003110032003006403415402c61442c0c038043e4040c04080c062503008443c910000a0b03408921650503188209442e44ca81c0390010501034800070b4034030300c107003a80c0183d101d0700c445400d4900c80c10862620100840c2981d180c2c0d41030340b08d80d007185002825043c1154054414001c102001358496426560304403880c10400310400741041c1032140d00440540 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 724878893 1250 724877643 724877651
    0x501021203041a18073501180f0b0702070608130212010e030a0e061204081e1b0c0a051e01020a0b0a0b090901050705030a0207030e040e0729180112 65
    0x800440c0d44d0941c408054000903140c1164450710442400083c0400702000c0412400342454000389001808280760709140010400b403128111344246c5880c070040c11202882c000142000744440e000800781c000401c4c0c03000d0b10b121454503c004105280c0030f0618011030b90085114811503880801840340c0074001d03402400703005907850742d00c1d840307410510b001c3c004603000607030801c1180b4091045540c0107440d15090000b5880b2a150800c90340c0000301c0d407800002c075103280c0d01030700c8000d5400f42000c43c505070101c80c026100c03904541e0820f85070502950041c0c1d1102c4050080b982c990010120141c9500c00d2900c40310000b000413490409880d501418541140341488440310894124059140050340e46202a444441c440c90032640215a404005001403000c41c84092144e00240383c5c02d03000e40f030040050110140000c04a03040d0340c0c40c2c0000742d409007000b007102c44680103115121404203000b403002c0942080300c0c1160762095400d402003c41a050141c0f029a000c3e600b51340b15807541c401c0400c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 724880143 1250 724878893 724878901
    0x302160203073822030803040605191505060f091c1103031303172703010b040b0d0602030709030507060f031506020d0e031f05060414010501021203041a 67
    0x2c000c1c2181c1c1060b80000d8001500404070f04150350360403520045031000c40a00d409004040302e001e1a02100307100a0b01400ea00c1c0c0080407a80c404040e601481c0194000107243c1005804203a138000c00c480102429030902883c68100c1d660803900000319203060740c0340ca90319502c0c40c490031854403c0a10255000180043c0500f880740042c1a8100161081d403401100314000010556a0701540110404a4000010a100081201c0309540040036500203850818440d0704000d8800d400d00315680c029554154250f0400d0315090040721001407094070104035407844040851400c4003c3c480c0a81569000408514094841c40b4190011a0030030140c50a0640305d440003080b01540740c15010000341000a40101c814640215504981c07081e0018218032105007000d1b605c140807028845c1d8035000b0b40c20200c0018903041d0440c0f485180740c26000900c0d03c0c02000b04002c540c400d1031540300702d050150052180d82d80004400c540703c0945840b041d101c0e03441c3d26042250020580d04050441c1d8004180 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 724881393 1250 724880143 724880159
    0x20408011a0a0b070b010909020301140405010e070b1614120406020d120204141c050601080a1704030302150a0e010908030a05180d03150806040b1807050a0501030216020307 76
    0x51203100084580250107590f5800c080c04034054807201038901007a000c01086941520362205002910103000072440c02010700d26007486400031903040c0c85594454100e030300a10000c3c0440030140c86403500c003908040745045284190b800c0070f44c0040c106a040c40d008486900c04029994040c03142c003003141e0b900c0d91140c0000f5114025141d124000c01c1c02a11500c12020302d50027500c0942e458042290b481c00b035030904101d0400c3c007000c00101160901c2024401040050000078041c15030b54004080c1407150346010420b0b0001900a10410082880207100180d4041000c1d9281d04d84500248290b07200c4484c0d100c000c0401c003070203806a6203040b40010410078110095880742045034020003180d0303115010761306101c00d045c00e4021117030001100c0d561014087c3d404101080e0203480c0d0460200c0e241c840700351071b2440940b03090b00d10140e41da0070001640780e9800390440d111400300c040c090251134000412001291401620b051603000329422031403246c0710a4850085130000d01b1249071594074001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 724882643 1250 724881393 724881431
    0x303110a020f0f07140405150a2304150e09030c03041509060201090302150c040503010e0709050612070b0f120703061a0c060c0f0708071a010f1401030f02040801 71
    0x241034920f020750620b03000400c10100d0380388100c2d4019842068069624000c01000300f4000301000040100740c142c2111580381c20a07101c010304030010515103803a040640000500c00d140050502c1141003480c50003200304c04072040000c50b200e036500c505c015281c40c14003908501135003800d000c141c031011038002100700303040707812000700031098031110310380d940700c010480c02d03541583e00c0980541c1c002e42c440f645480c00410030320ba100804038103150800d03841e1800242921010bc42030000d55020356420700c030080c0c55210b8250841021500220b000000c040e403261200e0161007a41107800010421659400005044445601c03a10782340c0406841c04400c060002e0016014070002c0c0070113807983c840800d403140300b103900c0a04010000d1031980d84500da03d01d81039000900140c070024003404410b0000d0b48000c0601f444500c1756040d802d149030700d000c1241440405034491900e044121a08200498403140c141e000c9a0003882c0c007150300411002500d019100315480007a040d0b1900c1549908d0101d2406 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 724883893 1250 724882643 724882663
    0x10c0f0b0a1b1d12010c21180b0910020706090311010213052e0f14030c041203020a050f0c01031a0906060706090501020d060e070c15090303110a02 65
    0x600b040145816102c0c641c0386800a00c814000c10362008214442d5050410581c0d0150401480d07520a011454846402c0d2071545000d400401e4081c4e0700031411000200e400e5042c2c2d05400c1c0c0c1001030300743d0034000745c040030321102d00940052420300c04035001003801d000050f1901c281e50000d56466140d4680ba000030b12a016080c3e0000d82c0000840080480c10300031552052540403001d85080c0c00c102c204407260701c0c08221260003050004c0d0102640e40e03400005024502507450710740c0e4000c0c0e1841c000e00b48e05070355104800e02c88400c00411000c1c04c2c400050f102683c00c014440003010321a840c0070f84c40c0903540e0a020b00341d44941d407504100c0c07201c0054110080e120a80e4240314402c0e04101d007409e40303a10060744540c8055014002007140c1480005030401074012600490743c0c9000c0d45401d406c90f4050030344040015121001401401107440c040d90f04040c141c40c14607013040d115180c1040d101e61302c5020541d040d0300d9404803c2490700c43e0300281381b0341c00602c2c48503999448039074000c0d5440e98800 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 724885143 1250 724883893 724883911
    0x120103081b1c0f0e03060a02090901090e03162f1504032310020406080601090509040302071a040b0c0d030c08010e0f190c020705030f010903050d0902010c0f0b 70
    0x950141c0024002151411240c46102c842074103212a0351000c0c1c0c0e4505401c48501c04100c1e5290060595580801001e4003441c4209801640c56043c00c05105064405803c00c4080600380307842c40884080001c111108034440b42450a11885149881c186d03060f1407071070066803200d144c6e140c0d96550b8650021300300c8410040718514494400700701000007900942c0300280926034401801c242019205080001040b06a415101e090210000c07000498000c0e800c1100006c80e40410440e907541c000c0612400b0304022140391100f0f141c503a80095960b41c1c1402003010321201145106540308a480c1558041e004a1140315110104556400e5440d5501d58038000024101405650ac040c0160380b228181c42484120011941e9004200424850040c0550f01d2180218900904080c00c510038492118910360140c0782c114903081c101441d000303d01e0080a400e0f4544160316002075002412078041052002001c04d0811180c001a03d500807202d0000d0071814092520004100314500d4140c811600b030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 724886393 1250 724885143 724885177
    0x11505010201241a0913060501090b0705100914030408010207060b0414150f12060f070f0c060b060405181801110909062206060813020609060c0312010308 68
    0x207400741c03400369143c220240000640f40c0410302002071071502d05444842d1650300985046182e00c04900071070a002d02d1610816a5000213202079079101d4a002c005100d41100d113800d040301c0e51a10303501c441c808000404019038036440d410130400040000141c443d005400c3d07a80722992000154080d50080324112030035071801c0c2e411500c41c60540f00d0317080582c5d003850000410355a0007944c02c03c00303000803403030700ea001c0d003110700340595a62181d04c02c0d400128840050310356810026220300c0c100001800f140103200c00e00c1100f04150b80c0c05502d5644064020070041207003a51100814102c1c8100d0704407540018000389040c220030107044080d401070a400300e5004021020351002802c940510b40751890000c810040c0c11024900700018681204008000200b43d1f403865a84020304014080402e1745a41c03510310402140303030003a5807194041210454500075821503800a03889219520f403d522641000c901541900b00c00c0007901c100c6498010301000c3c0796182e003403010b0690014070802a0700484 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 724887643 1250 724886393 724886411
    0xc1512060d030e0907050d022b0b09070f1205090106080d0e03030318010b121b0306090c010f0219050a021e150a2c040c140d0203060406030203011505010201 69
    0x1c0440141d503a41555602c504111080200001d039600070744903400300b080601c00104503204a01c018a03010100101c48800c07400141d0186410b61a0400c0c01e0f040c01d8505040c2070740ca51107250340c3c6588000301340341c4201642000b032000d5071910103508005075410b25100c00c00021010540c008015144d00382c0c00c80704001010001110b6000d48801800e0701138001b803000c540d40507250142040b41c0c07522100003090107062807002c246001c3c28031101d003244d41e0048050f0065801803660010043c03000390080c00191604650184e17071007502e5800b9904011502c03406800d10741c8240004001f80c60800302c5000400c2190030502e0ba00c0030783e0350003030b8480c5203480c07814200031b050201c00c030000c3c000141030f01480041c15405034400c0e0b04040350036018410310242070a0510305401400c2c44002c0050184490001520240402c44d04103910301c5050180c4440304903d4604800e003a2000000e0345240542d0341d80d02c040219026100b2070388029015030815004869451000a00030300ba10800e0f4000c100304030b8 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 724888893 1250 724887643 724887649
    0x6040f14070905190b090a090c0e1207061706010c0b1e0f070c0f0501021e0408010c0c0b04080c0a1e060e060c070b0c132306190807020c151206 63
    0x2c80d0141c0900d0340030722101001100c1c400b0f17002d0042c2c0d0500401d0016050b076102c4256050300c461101800c001121040880b80e10701d0480f00d1000045d4100d00209480d9041c80000f8141082003601600312490210004205038419628180c4c05d90703002035010207604280d461111584c0b400d075100c09000d040000040c4080c203c04058501c2001c0b80d41e1850b41d0b023203c5440c0d09101c2124200280e9107550200701004814080e06020785640d5002803455a4803440c02c0b07500c500b110704040707035041041000c00c140343c0800c40c0f80b41247d03041501b242e5010743d00c508004809d89003102c146402001600c1d0005039030410141c8060840b0241d000b43c40a0003070001040c55152210700440f1100b82c085824011400070078800d6080c980c1c045174401a6a1810146211161211070254001c1400350081c110460003055114241689031100759060750520010004030b207070150b000c0c1b41c030702d0400070003400280d2414401c0103c2050001d002c0c222031f01c2c00301822881c00190b0b01a0f0343e0061761210380000301c3c20b181 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 724890143 1250 724888893 724888909
    0xd03020306090c0304021203030c040603150324180605040302061f120611030a060812030402060313020f04090b0703180512030603100f0506102606040f14070905 71
    0xc03004205100658840f040c2d00034a0b00041e10580e0080e900c40e0203100c400000b0001140107035540540711352650725244004040c5c1c0c000b25040407190350380040800006411143c0c000100440c002002260420303240d0740f1000304212030106a1b5504401010300a000035548001d0149020340e00b91180e0783ea400403604144150780483c100a15903191040004084a41c50b403070845100e0000444c103c001000c41100c5074006503204c03807400b03607640020088508104031180402007600c40450840c41c3c40d80000d230702400002c0428070300d02003104560007150703903e072480d9207440c100400030440d075403c90801d0b042510b411240040030a244c9406102c20940c00c0d20105140e0b40c0c028024012308440e40c0700405681c05c040d12194152288041050b02c100c81401030004c02c10a641000400e803400a0030007081c1c1501d180d0007800d001a4031440b0413480e020351502081c516880c4890710300d80e110403001c14001d00b81d403441c07a0051440c5c90a5030104216010105024070720640c0c0c0c109070182c440f4200030f020 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 724891393 1250 724890143 724890151
    0x12010902010f030513050a0503190807020615060702040f06230904060b030a0b0c0304031404031520120108010b0405090304030615051f02010f0b0d0303051807060f020d030203 77
    0x2c10504054035640a1181c0c00107548142c0d04c2c1c1807620049160b03501d0303910309034900304103c072150004074240402c0b0000c0c4001c403903824907510b080384103814034000180d20f550010b40004485103218061228a031642406c454826078050810045d2516020451000340381b140103091401500b00310310680d894808203642802040103045000948940e500e810061000d100301075007501480d15a13102040441c4c0313900d0310502c1c00e42d82c01c607541c0c075003894018501401038a20210071882071000f030020510b000a510801c004520002501a410310440c981c1d0f040b09801400310340300002034a11000141c02c584904035405600248404156402040180c400403644200307694814401000441c2590704410600c0c100d04c407015690540398004100c003082c407035412801410106010300101039091044040380b5803280000c009100b43c03480014184d204030302c0090105504c0364080365604078a54010212a58480c046400c41941c4080240a03c09a0651000540240e51080340303910f00030700840e481 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 724892643 1250 724891393 724891397
    0x10b0f03010b130917030108030304030905010f0807030e0f24010f121502040308030f04050c09070203030a020903031b0609150108070302100c0f0605090c190911160b061201090201 79
    0x1a030810f0140c82d41c003d0045401c02d80b80c0400082c00c00d8410707a02000154080c0103050040c0d6500d14040c01d0140c64504168015410031408141d2481c03032940c4407100b0f0b9000070561502007088455411010301c1c1030a220403200c0c00d8001d2216029085a4801054900320071000310341c1c1c0716a9032a000c8510141461080c165881d441c8800100010707144003010040f40e08480740141855101d480ea0b120507001152050001d81d50417080c0000d00c0300800404d00f5071081210306d051a40b50600f0001c1d101c1c00090400341002c0d40110b00c00100340d80500036990410b000080907540c0f00a20605241d8410003070300c60715080e01501010031141c828074228103041c4d4441c03c00070f00d18540b55509001100101100f054100f0410342019800502c2d51070454820a01030341c80485c650510f041401d007030413111141d02c1c2c854200c904070045041d802c16200070840d0700006d00040c1c225140715503603603548603c1b07010b40b41003945d454804007006402d829050107800c0c16903456a42c00d01e015580c5088514004010b40 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 724893893 1250 724892643 724892659
    0x605030a110a08060403080604450803040f1704120b041703040f0507230907020a331e0c11010903020c090c040e0c0c0a14010b0f03010b 60
    0x10444100884a842102402200402c0e030388010007400e00a094a00310b0029624000b404650300c0d10740503900c440004d84220312041140d120303030030b40b081003070701980b0840035030003012032501031003003001c100b075441c0c020b0314480c0e40385024030f03000c400003a5000b0202c500d0302c56421403503020111541940c05039642100d00d001c51202a4460070700030a030061044400102c0320701d07500050b48004002d103014a10800048800b00141c1ca0310908203511a04111050081211440144280104035032494002640c00c42d11640344c0c2c8004034204014504040e040d03e0b0603004a4445a406414139150703070740021641c550440641c004042541c2504118520f10040320003103d00f5040c030381e440f01c400000e26081070300b112001c0d10003841c207441c454001a80036802988440381e0300d0500284c071507840054034034024600741c10b0440e00b42040401818103208104040b0b804007004031308000c1c811000d604244040388450b010080d45011301800c0600c5070085183c0c010080240c24140181c1894940003000c0c40 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 724895143 1250 724893893 724893913
    0x90c0a0905040c05060a0309020f01080601090b0d0605060c07080c0a0b07083a06050409020a1203050f04150e010824030319090f080609030a0f11010507021f060503 72
    0x440541000b4000b41e070105a00100020160344d80001801c02021540b07022441c440140100800c049440c038a050512958404000490781d222204a040da10f4200040d80c84e480040041c0c8001c01142d002190000d20005403003145100020310001100c44003030444200070b59032028800c0054042c818246d43e00300a003d40c80010346c040029000001c03100c41003901d001442e00d0310345101ccc16040b94809085040241038140c10305203000309409404162018043e1190725404648008190b214903114007124031109001c151180b400c94015040014156444070f890308580206080808809004148110030f142000d50184185510486010000c0541a41c80c1810886206825156154540000c1060724400020052a100010f0190b0740d41c040ca207023452038916030107225421980983e0f110200b0802c48060001c210b511270300252400e000081e0038410705403440b4002070001d02e115424030041000c041d9001031510000038850300103401071a1500ca01c0c008980310b03401225090f4000140349 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 724896393 1250 724895143 724895159
    0x9060e0a020408060f07170127020304150e071701020901030b032a010c06050a1b090b07120314130b1003050a020621010807090f0626011d060f090c0a 66
    0x1a8410107d04103082d00c04200c00c003144c04400c00342c1003040400000840c28030680100c0c400c02441c055100c50031403650601b912040c08480d05c104004e1011500c0701c10161400e50244aa4002000c0c030098002200c0d1401e04074601035045001060f00007441d0000401283c42c0c00034404100403004500080c15403400962444808010705400d41072180d070341412000524503128180c814908030070002101543c201c8060100200d810304c05c0100400c02c20244042c28540003241e80d2079512942541d501070a142050b800b4000d41d41d101145138024104124841e0541900c0c11381441c42003e220015035601d501c62051071a0382d000280c8941c0c00104a00c0043c20702400038901c1c2c0f40b000d0482d0000e01d4280320450b0b0030304000d070005039003078000b040e0800141c00319002e48012000c8640c0140301c550b0502e505a5098200303086d080404d15090140ca000d10306080d881060420b0b506040106107154001200ba55100c069030039000002c12040094023504011400030700030342d4020285004a81b4081c21 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 724897643 1250 724896393 724896421
    0x405060f0907050408030d02042d0e0a060f080f0d050f0d0203060303070209040f0506011a18190605040f0803030103030206070c1e0c0303080a0b090115020309040609060e0a02040806 80
    0xb001840300c01c01c004942c813601000644010b4218000250703031241000392400850300202003080c500083e2503400d80300d0000e480210025255103184511180d0394211200c8060300a6500a800d401d00038040840c19a80110f001c11200c5112401c560400180e55001c0310b0a00c10706c25515400e41d01480310786500046900159045500101180d040810380e400041d2ba0f0001518202c070174609004188081101c01c0c4101340c018038141211015880080058400c1c500c5649040003001104450b42d4116070b41e1240f1071071031403061040061343c180e181c3c10081e00a601500807201c0301040c107000050400000800c50781071341d50560241696484184007510401507141d403c4501c08041c00c140c03040c10404001c19191207000d0b8144511340d91850601811066000c0d1550390788030705000d05035040740c03a81c09a6074111404900a08581041440c049056008010300b10b50f00170b08220000030302074110741220381510f41e07200c000045600e44900000c03c912a520540c02c2d190000703400100310401c840e41c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 724898893 1250 724897643 724897651
    0x9061d010f06110705090a0509100902030622060501080c01031d0c041104080a080d0e011a091f230a0e0c090609040c02060a05060a05030703060e03090d030f0e0405060f09 75
    0x1311512141c8820000303503200021107032041d00aa03140c00308001c000040008030010700e00e0000411203140503402082e01c40c00014205031a0085401580c0d5282801b5a484a101c6401180402c20355843d031051949031510501e5141c0000e0400c441c00040412050000301c15103850802042310300e199800f40000781217066141034403603405000014003002c0038032002c0741280c41403408655403498009601c040320361000000301d03141e260582c2640020003600b04c2c0c500511040391134a115980e0901c44a81240e080e41c01101f007103050710400915503041038a00e125443d1143c0850480322200021711011070458400d0f0070031140c1500200c3c000d0450a401000d1829001e0b2040b0f160541840114080d0780d09483c80c000141d0204003080b007000750702d00c5001e402c0074045500400c442d182100081d92617145001c041c00c902c0d41c880101c064180f04200702c0d0807184010300a01a030343d00504001e4a07007132640b20380038040740d0b00e40c214421030315080c41030b9442080c00800280c280c1d0410b605021070184010 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 724900143 1250 724898893 724898927
    0x1140f0d2a03050a050f0408120c13091a01030e0d14191d030d05090f060d09030f110c06041205100f02070c30030201110409061d010f06 60
    0x200c8011908a2803440401c041d1030703100410b150134106105011036200034445003201d030300b4405000008030004104c0e14107038800d005c40302054075113000e0308d00507110780000e03900c3c1c00303441000000f142d035020781011907016032101c02c0320340c81c5040ea0300641c1911020300e414001504801858182c06025954802c040701000c0780c030f54103009002075221162011a441800807035404240d16031a070711454000711081605401900415038001000307400c41c01080c101500c40c60b44044641145d0322003030191000f24043c9401400801e03e91304010385403500410b089000103440380301d0f00d030340c03401c001a82503560403000d42030f203241615160b50502c0d80b015030b4004881c10300a41600503543c02c402d000e000c0028402c0c080060707031901c2600c0c0c42820001d0550026213108080c0291410392100b031400c100080740c0c0c02e80c101105070841e1400700d00400a455110380d070060b0228000ca00b1000f02e50044080e18261100030101c1e048010504640000034480ca40c00e803131444005009540c402c14600b005613244d1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 724901393 1250 724900143 724900181
    0x70507050910080a140d02011b0c0204090c030830070509010c1a060a0e09060103020f061c1e090f0624031203050106050304030e0603071b03090501140f0d 68
    0x403c1c3c070904090144105480c1c6142e0b801140c10016018421041400e5040c002041040304c440c0c0080b03080106c2c400003400b4400c200d00c242e030544d210b64002c3c000031135200b03071054806522444c0428503600310041e4180000c00c003c8440c1c200c100c0e010240c2d50300320a520800091a0355080c41210640e1040c16964104801b100201c00000d95607074410806030400b4510840c03610b020014040401d40300d42c41081d0007001d6906200300f40401203400c40c107413901503400c40404800c400214803588984a03c5804900c5a43c841a0184c01c0076409600c6e07008003d42c1c00c0e100307482503203110f03402c0e51100708001e4241064082c4020005401c0e6020310540041181c803000150174680c800d85d000103803030b80b0a4030045c0d10100072000c91549403169902411450801505600b002d803030003020009180400c0b40079100020200385428092054020440c5030081c5042e40c0800a186c001c0040f0590721596001c1810300c002c41a181001505550002000303090f01303402e2078079404e500c1000d00581849568220341c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 724902643 1250 724901393 724901399
    0xf041e150c020619060e0c090406051003050a0b0904020108060f010e041515210e032502090105100516020f0315070f020d050703030b010e04051812070507050910 71
    0x14081e940700e560340d50b000341c003451070107054070007102400b0754040100a18200781448019041080315400071002002c0e2038507449036034003040041015800507503001003c0c0d030040b443e00d43e054202a100f0b440d148810700822180700180701030034605071002030128044100245003030500d800038081d42c0300c0500d4000c42107598000810101c86409405c0910801c0c8044240a01140d2a030ba940e040259460654000c04005440b04d000680101ca000300243c0c60709841e0035815130400c243d48420030b2189030001c42d91440c43d0070608410311300c01d00320b011f0100300000248900d8007050400d0f0446060319050f2070501c40003d03501502d6581c050403688103208400042c0c15842c0ac01001d2902102000060303564242400701502c41006900c080b01194400c081c840f803d2a449410340360308075850b040100d00b010b040c000594480c000b03044000c2d00300d45000c0801c510308059000103110908002d050302e802c091403502e540498130613840c1c05441070b401203a0801c040c0c20030401440d446a41c1b01d00308120356407 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 724903893 1250 724902643 724902683
    0x20a020d24020a02070e0609010e0106110f070f032102030904020f0c0604052404080a26101514030114030f0102030702060717070909020c01060317120f041e 69
    0xc0b01c0c02c03590050b40f0101707040c0034240c1070540f29034003d0b0007150509802d40c5080d040c40c40310300301406510f040040e00142d14071701d1501048000420b44540e815903044a8650042c894200400e200580c0d0210107805c6524a421042801503074510841c2d028500d0f01d0107407000d0001950001e012a600c1400070405284119424003071a40164440c4000d843c0e03000d0000c4d42c5401010750452000103802e4080144800038022408071201c0c9081424040319130034600413000075120020a550a0b2004c4680400042c480610608010385040d48101058030700c000070100c40d80708010a80c2e6550900400060040101d03045000c003100300d00a0407101a02070001ca241c0c2660070988004000d07a1102003480b520313a400600b41c441c2054044000703480d901e025040203190406920522040d2640001d5045003528290400c0c006160464265601c940700c0c4130240c6150f9010580d45010302084a020480452801c4029802507811400302e00d0008858244a0485014540e04030b402441021061062031 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 724905143 1250 724903893 724903897
    0x1517030d1b080c1c0903031b110607020c0f0f0d1b03050705011e2a03080109060b0a09031205041d0402031e031b070503060906011401020a020d2402 65
    0x4415204600e01c0c1c0c00c12600c01400c241d4000d0b18005584a05000c14503e681264059030007010051501003600b00710b82c20103800030404503c01c01100706640c1c00300d030300c01504081400d40000070b05007100c40075070342e00d01c089072a40e01d07144900740c0c0110100340c100384518256080d03414001d801001151034000560300c2d2144201c2c0310a441907094560725081040c45418007034030005180a0a26400029a41404508140401d2106424001907071411005180d0766001540840f50300800c05485142505001d00180d800344900c05826041c042d01040030304442060702c000284035100c001e0306a09540e620080c564008100c0c8040200034000021a210300d0f0032030255805491034080c4030f40c20a030041c0360915400103864030f9000c40075091030620307a400000702c911001c2003a00c001103210b42d0343c040d981803404961003242e241c4544070030b10901ca000450001d040b6908800740c81000f01c0c01e1001079032200d58000300a0b600060044018000c9801d10380c507405174020000c1203074010805500c09804070303 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 724906393 1250 724905143 724905161
    0x120c0906060810052b0c03081824030103080c10050a0b03010e0a020f10230406110c130f0b0a03050f011802030c01050a05070804271517030d 62
    0x164400b0a2200c02d0840881a80140805403005600c003045013480c03490302492420090400e042c5000749100384400458540b0207075500084580e40c96045000e840c88100b0100c2903c0c2c400d12103a45140201881d1070590385911140030106030031a840d540750005a60000030704110580209181c803180f0b080b4612400384142d104100008449035000145421640400036401c21980700705c2c44040541c2d10b01c0d04d0300b04c00d51802c0780c00c9804109115005c807002c1c080c0c5c0c40380702c401061002580d40303040d070202c02420036111f5036030711003401c8413802c2c0d0301664803040520075641041c0e88030011801d04002d40c0103280314003410741010400e0251100420f0f0f25940a41c03050360b0b03d4004030442c03040343c40207019040394008480304a0703000900703580000380c8071524003051074103008d40003600707145650103201500c1c038a07a085080c00d61100e42c1d541e482c85c00203d104107648521841c90041c501582054803d80a51080c10002c1240043c1424030b001c81550482000c1c0f00700e0700c402d2000c510203020030f0282034070b8 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 724907643 1250 724906393 724906397
    0x1905010803070b011710020f070812060312071e020a0803071b06020a03360b0c1203090c2e02030418090b0f06010507060e0a020f0307050a120c090606 66
    0x6034102c1400d0414981c441a040360100010103e0000b00480300095564268a0324503001641c580c54200f44010911908100405000c2d0101d210b2940410701c0343d41038440c0600f64144d9207465241881860207200d4800010301d07426103803078800052504815070303101e050710143c803075400d00b515a403529142d03802904048642100f0350800d185a515020703542801441c240c00102141e14180d54094200011070712141050003c00803210700303280360340c03c00d9007645080c1200c40d0056621401854119800211a90071074483d4420b201000f00d6444222032041e034025000d018401d04500810500b44001c403802c4900b04203150341c0f0020341082c100002e581c007100d80c006540d83d514280891007500801d0740442225803802c50510007044080100e91307070080c1c0c1130395503c400b86d86e818010386143c0180f6101500303891500d681441c0301080054a04c00e200d00803600f440a5081d040101691078095000f1241c01203400c54040024030901d401500c6100c0c41078820b040c2d0962201080f501b2981c007903200d100 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 724908893 1250 724907643 724907647
    0x2070f030e0405060f040e0c04020c030a030c08070503040b060f0301110d060b0405090708070513060507061a1c05010b1207050112050f2d040b0118061202091905010803 74
    0x208050308030034500e00403101518144418a02040050f01c4d5105460540340515201c0d1100e0303402103c1440011101d2500034811511602c4403910640e4a41026440b04080391400300c1d2a000760717003c1d01e07115100d5100369591900c2c40d9030315a5103880d41c1d5000f4025582101c0c0480c240c000903030b400e000d1500e580700b082e096162514844a9680c050700c0990380a41c216900c200418440d984540b01305542c0b00e4000c0c1054101515410400c55003803180414241001c5140c0c140858003a500000a00b10b03103010b4130091002c400d074529050709001c0c1d22990654458070707841204100090158003011602d003d8000001c00f10429004141000c9900e240c03000560011070303050000e5a04078841c02c00710255550204900c0c6031003105803008000c06419021240b00d00752180b0b01c2040c410039016400010032002d62594146881c0c600c9601c002030003504901c00b09501020702c0c103507070343c0305810489003544074070001c0643c1c0e40c090180c0d00c9030242108030000312000d200302c0d94034007a01a550007040d20000541e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 724910143 1250 724908893 724908923
    0xc031c0b030c01030501150804050708031201260c012a06060504050106050f090d140d08071103070b13020402070f08040503190b191508031c050f0c0705010b040207 72
    0x1802c1901010b10030303041c985003400600c45041d010200546c2c1c111175040202043c1c1361418460316001c0250b214041905c400071b100401515001e142a0494134003624560001400d54400d40c0811000d040503540b550001e4000140340d03105107204c030060401c0810380101f440c0169502d2940342654041a43c2c465101ca03070170401400c15118450040c1402d11b0180e0502c00c200000041d42d10076403030b05901c507002882d610401d110100c031491030030b0881002100e21900c000c07030b0050500750080300e20201041180b03000c02a48000030048402e0b00c0d511030342801140d0380344003108282a40c0d002007640c202e0341c04e0042c40300003405460f034810b11a004103041a2981d240108144c903110307100909030504803501d24102c001074541c070380c1c80f0b0f0008031034111384e40300080d00c0684030b004040e55801a40c05100f0070000045d8201c002c0003c040c4100309004148030741c101808400240c40040e1080301c10428800f001401c0005860b000c1e0890503c5400080380b003c1401000806907001031800b643ca60781a81c201d1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 724911393 1250 724910143 724910149
    0x2210d0f09050c0d152a0809060f07121d0a1b1d041202010906020d1a0604030c06080415061805090f060a1806090c051302180103020c031c0b 62
    0x4115044001c8500e180c2d00c1c801aa1191440e0701d1700d01c0c800e0807140d110b0320510140c4450142c41e039403100c10081c104101100900008220000c1900d854407503008070008258243c185003a02803080140303840c0c0981105c1010340b81001050f4440c1c6400107001a02e900000c552400e200c0c00c1c00e1280540c07900d80761510026461080e52803d40d03c4030781e02112003c0d084403001d0095203080e40c0141c01c10100d943c485007442e000c0c0d01518054200801051000402216028955020f8410101d84400000c0c2c2c140c4058107000c3c40748500d001c050310585080c202040924031424040307a0040c8114400b007000130850305000181e0f245a0005001d18170320382e0122842d08424810103a20298410050846855444c1d01c185c5801000c0c00c50a012502d8045000341c8900e045000b45840307a00c1001041a9002410300c000d0b906440d001c3d25102d04213200080f10050714500a480582a00940c1c18415070402c4005500a40c0700c03002d400c415010178040b0354002170110780044020080c05c0c1012a50070701039010 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 724912643 1250 724911393 724911403
    0x203040e070c050a03111504051c11060105150c10320a0c09050910080d090e130f080d0e0d0f0503041407030b0403030b0a140102210d0f0905 62
    0x7030482009520020b05022450005514040710f0301402c10240da00c0c0392910072424100c1c80300c080707143d400603103080c0410000001403505080444803507940040c0d1b02400d04a843c484d02c0c1c82d580c6a603a0004005022a1910844450005560320364440c5002203d8007141c1c00c0c100c080301a00c3d400382d40c40c16036a0120b070040d40d00c0c41c034004e900a00c0030640c1c8041c0d420410711910140c01d010410b9680c400d000017403030046a40d18081d05c2e00400903100e61400c14444c00c000340050007103400a005540d07450014a02400030030b003c0e26014006018555911075140840d000c00800030340d140d1418200d2100482c00840042019902c4200c0c04038400990008040c80c0402c074020100410030302c030036010102a40320055030b03085a40302000b40d80d4002c24070805803800d0f0b4140c00140c446040c0f035013400101078151b07000c3c60703082ca0142c0304801c41d1951100708141b40d00c1e940a035103026070442f00c01040e030198804c003240411404950140c0c11320200f4000002213454585200c10b80a41da010f10b03900307010301085 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 724913893 1250 724912643 724912651
    0xd0b2d09060c0a02030307140409090f120809030412020d080408010e12130902090a0f0b042909060a1701081510121e0516031e050c060c0c03030a0203040e 68
    0x89145443d80b0200025078a2200a150030708004600d0300040401003140110340080c44503460a00c800d84c0740e41010502d070740b00504121a40702100020746206406005100d101c2c02e274034006542000d00d000c103108040200548101c0e40400c481030000001010900600060503196000182c40000d2070003040c5030803800321400c0c03d902c04c1449507100362545040e60308103541a0403005a140d07070450011446022040e00862400099248081145480b40c0f001c0c0045078400c149103410341e6402d415440c07038007240c605142414dc0040000c0e4190382000001440c0060940c60034407244540c10800c941c0006007030f0000f00f123a402c072648006c0b00c11040070001c0c0e000721414500d000f00c185052006988403410010060003468030700400e00e106046075000e00c0c00c0a07001804d0300c0d51050260b544e001030170b0305030008540c0101241c1020403c8882095541c1401e03510000502c80c0054038000c208041d049107058420901c12480318000b551400d0001e800184056001075450760309220b00f000900710014 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 724915143 1250 724913893 724913911
    0x6031e061e04180b01030308070f050c0309060315090a022703060105010807120c020c010311091e030a06060306050a0b10020c01030507092102091003020d0b2d0906 72
    0x314040080c0250905101c5504822100081c1100d5410320082d01a125a000940103008040000061580205009119800e1075a0b0b06040072245072007665140180c1942d03140d1a44280300e600340c61b080800055401a8034010201c41a000900000751145400c407089a8030b6038022655482d6100d44030a00c1d590f1400303102060545456a40100740c3d6600305214031410042d0305000b10303d0550040c280c0d5014003011030024000da10381a08040c0d501c9400d0b5100d140028540034465921484c2c4409540001c14000c01c2c0403d00070014541c080820f84c0b0116041e4140a0b0030101c0001680520440d002144100d0001c1401d15191101500310303941804118082c15640000e50040395010130040c090700402d00700007a8648911000700c1d4035403410742150502424032520000d032001d80c1d980ca400b0141c07007216648038690b10300340c480c001c200c10307440001d4200d13501e541031f4000510303c0d50a0b030303034045e10302c0e4141c80c417081501c1000002601103507459100e007040c41052010000d801c0c450268400703681 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 724916393 1250 724915143 724915159
    0xd0207060306061706060a11030a08060f041127030f010f05090106080d1815180801020a1b1104020a1101060602030304021e0f1002010e0114070203041a040506031e06 73
    0x444000c0b29001300c01400c891080000145041c0b50324014244071207010b0300042200d40b29122521702804108003a94880d11401c03813500140b41903d4240148880000c6240c0c0075801c00c0d10962032480d501e00a2841244944541869641207031010480b0310b500b071069100100c0c00101c2d144200c002c0700c00242c0010500e0741080428814a28000794085d030b87c0000e40341402020f41400c00500714401c540d007100086800c640129150f030f90384500d40611650300e90100d000b9440c0d840903861300301d100d036a201c10045609020711003120a212510010703914080c0140e0414240c200000904030303070102c4003983c0840d070405543e0500030024815040500365a000443c50341c20305400240c4016040300384807500c00a1485048080d40f01c0460346401054094581e4906012003080613000c0c0c05e40b010099150761034440018640070060350f070f02e0301604182d005181b03002d06041442c0d80007150030700c610302444010840050103032524002188202e078445146142c042c281c108040080710050b24031840340c120 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 724917643 1250 724916393 724916417
    0x1f030f05090c0102210d14060102100912180810020304120f021902040f0f1e150e04031715150307090512150c070b0105090705071e050d020706030606 66
    0x540b82000c0c00c4155120b000c3d0845c040501c02c518482c0c8401444030904101c4140c40d070300d120041c80d84c045e5800b60240d50b44c000c1e83c2c0b5221002c5800414001d012448940c041c07150090180d88005c482c002d60700c0703c80b0000c584540360546060f040b998010b080c554000108028003402d240c1c0d51101030901e251408401e02e800700000e68070100201004841405160f5803001c55940b58040d0b107c50f03250301404e0107031421210707605005005507156850030480d440011055004c50340b01c1c0303c0840c403010207900c640300d040054a0300b400c00020001c90a120341204000020440d48080c1803054003005801820007e0300401c1c041d070401a5082c280c003840060042c000040e82010f429070a498003511308696928a010085240070940c25048040c0c800440500c040c0c244401c00405005010b0301d8803400d607076642c00610405000403030f8134500290082c00044005040882110f010150104403580383e41020b4450b1400c0101c8045a1405079000740c1c270400c41c00da05401000010900c505100009106c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 724918893 1250 724917643 724917647
    0x70501200601152c0a05040c090306050a0608070b090109060e010c2a09060503061602100506010c0c15110303010b1605030d0207081b06040809040b1f030f05090c01 72
    0x906015920000c0d40203400400003500ca030f4101c0401d5141e4200c05080258113800c03400d80000003081040c0520040600401c25007440d00500c844007880d50360300b44000b4511340b0382e8001042c002c4c1800d4a030907160600040c04001c00c10551000c0d144110440d551106e07200005000020594040320500103000d4048040f6a0001c0701903001d203408c9030680340c1080e00d050303005400c00c000340340040c486110f58001041c4080325034010019a1810740480b011916030310480e09d4422280704400006a201686081910b00f030398000c550400381c10304149a0800c40341c1c2c6c070030755042c1c00b0fa003190040d260401a94110300758080046000c04902c0000b4518650600c2c2c05502a440340c000042514036042d6203103003c01200708211505640f001d0411034459007549040e0340c040e80204455102d00d8a445002020742c14003083e80350003982e028090924142064003070002506002c0b40240c0c0c40864405410035624400c0021100c94041d0380e00002c03002d101c105400216140038002d00031030b511482020780c1c641d03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 724920143 1250 724918893 724918903
    0xd0611030f311112070816090b030607053a0c03090809060a050c070803070c0b0a09090c0c240c0206010e220501020c010f0522060507021005010807050120 68
    0x580c0188103000c01c102040c010480284d51114080c00f0b900c140301d40080c81c0080420103503240c0021000d000c1c41280d4400180059680d0128401c0d810707042000410f54140c080c0c0e0040200c0c01007003a1000082c8141201d49441c4c01d0400010340e5951242f100c1025802c00a200d541000c20300c5080401000342c0030348440f0755600807040e1450080400151181c0400d01600139107602407080741c01c4582054032080070030f0310398000a0b8102c54414481d040415140d06060a40301650015034802c09684d20b810b000d00d014110302107000b0140320030040c101000c608140e20b6600e8903040d00d944080c2ba103003048036206c2140c103a690500215041100140600076a6040540d080300442c4044401d0703e01440450645000c0d02600a00c290304c0001c0000300d000c07043d0000c0096105008040060380e41300c0000e454600055094034034110f0340b40e9032034400074034940d00c0207800004c1481101c104481c2a01444103c03503082c1c014824a90014004221540e4000c00c070f540706651694008c080a00d100b901c0325514 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 724921393 1250 724920143 724920241
    0x190311151612050403060624020d0806011d100c05100207020906040b010201060b0403030206090c09060d02150409110c070506070b070c17030c03060a0f0605090d0611030f 75
    0x9012424100d10540700f00152805550814800c00040e0fa4522a244a81c1d18801c03e2829aa41e1030321110242070020928000d182c40a44440b040c5541d1751004568504d0620b0550102140d030f20500b00094403201c00b1004106c11715240d034020074000d41043ca25003100414070b00d0486004102c07902c0141c0302c4024441d004042074030082601e60701800143d000d042541c01104580f0f6001c00c2c00024540c3c00542940154418020790304120311900602c000710030101c5480f60415001800c1c64018208844003110303154040141d607003440e07210105002a42d081180b584070201002c120b0403c0c40d4010700c844c000410301111100e00d80340c09682d652603c40c500408810900114035448000d1201101081e40200c000890155607450045440c0205030000e641940c0584410310300403954510080122054440c292601818800701074104020f07100c04c041308454039a01c5204006681c04207038041c50003980840038103503ea1408040c1c03808125510034064000380a40341803c3c1500c084c1c0c201d400f0035 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 724922643 1250 724921393 724921403
    0x9071703120406022b0629031f060f110a020f10030b03060f0412080402330f03012d03030c020f031e1213090b1903111516 54
    0x2d0b5201e0500a00034001c100c0c0750300c02220031820000d01d8a2814000c06039404c40326904004260700c51240307500d00d008810b04034003040c400c0390485040e001c00801659010300e0030ba042641c00814074075070036014031095108034042501c10b44241d0009420070460380160034043c008100c0c800090700042d40220240845500a038581404030080510941290300000e5016048400301c0c10540c40c041c04110080305c003a111000b2a002d40c2c48010311030780c10076002e55002008108014458030040d200d100a104031585e81c5a4200c103a1404403503c14060186503850010030758030396140c101c111070022101296145104c426401071101510a4810641079039014941540c0520b05440440d0301c011180f201c0325414860040ba2890b5409074921484105900b0415200001c500000302a058061019020f8241d50145c10500c610b042a0b0f0088510381c100504500c44070000340650301c4c4a10a0707070000d9230707410b12800041c0713040d04140120103000303140440e9180c6850840c480202a03c0314006000708 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 724923893 1250 724922643 724922677
    0x100e13030f120603032615060306010905150712050c0d0513050d050d1101090b22080309031222031d0a060203040911090d0f030909020d0509071703 65
    0x4480c0748100002c6080b000d40303103401c004036620b03824060082c254004002500c10029880e0a508880d100c007101d014041e64410009108000800c10010390402801141000803102002806075184c0c0883c0301e000340c140f200d003591072055013400300c1c020541d0f803c0740301802410010096807840001e4a18440070551400310740300c014521151441041c0e81e0302443d030040c50b10303008805228000c90640e5078408540c580403102d900c00880e02d402d840740d00c4000381903c40305ca00011016152140b100c3d80320b89103180b803c030b4907a00c29a01c4840c207400c155440903c80c5d00c04078881c5a5827001150081e002144513181071f8a01481402a84040c0304a0074010104000d5610842e1040804402c80c5502034006150198403501c40c42c2c025580d401c18441e081c100da0418080e0014085004221222070303101800e07680144515468091034036601400440400003c0070703000954491501c040d00c003500344040080390b00e04200940514144580c0c1004a001a64205030403598400100f100d0902a402000d80 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 724925143 1250 724923893 724923917
    0x90310150b03270d030c0801060e0d020f03010510080d17180106090c170a0207020a1a0c0114040b09010608061b04030c030308060a0e10061d0315100e1303 68
    0x4410004400004440c0380303090b80303600065440070800740540882c45d80c0c00c0107881110311003212002000e10540c004105860303089492800c00070a07000107140040c0100d20746200a401080c212101200c1c0d40c640303019803400610220f0010b22859100844614003a400c445807900b00030a4294050099041a20002041359404e4002c0d000303500244607040c801c2200154401003d8401c02460508150703002407140044c86881051003a20407003a000b6050304662420305010840d032288903400251035000c00d120790031080c0d00034080c841001d11826884101c03420b1914050040150190601ca0315906000d8107111a00300081d00030b9205440029803041200098590205840b854102400081e64502d006c01030541007c5030700d00030324094510002196994150b240c0c0c1c404140c0e01d43e2003094107200304000c4540304880d031125145040701214000e0a07000002032a00345035507208500d0300454010401074402c2650360000519600d8401c0c070447c40d001c46515510310325907030010284548480d0035 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 724926393 1250 724925143 724925161
    0x30c09041d0a0303051b04030c0905041b0b0702011d10030c0905030a060608060c0a0806041e090f050f01150b0d11030f0a0c050c150a150902090310150b03 68
    0x1d01600740100140c8080850500340100039104c02c44101d1840c10b001c035a06812107480000711004c49030020864a2190b040002000c003400d4007902c1902c0710040e40c01005881c51b44111100c00a208a10b8070310740c1c0f1412880090045264001c0c00441c04882c088946016120a41c0345085111246400100c101c117101d0b042c0c1d920801500107a8141c4030f80b00c911030410066500c4001956402812500540d803401e039078500c90310030301d044500000c0110340401d91600302a0865079034a441d8144007005a001e1316082821240700301d20a5403070a468959178070030300c02e09001901c40c50b1211030090000441e1a000800d00100c03520800c684130700001411124100c144d8003021064022060195690500010390803201c4802d40d41c514055140643c80119140900c007291000000750300503148020052140c855014801450074034450340300c080c96800c0700140003602003d401003042c0141c5594580042c18500700c6955010310b242032a100d04108540c40c025446000c4500c60032611303680355118412 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 724927643 1250 724926393 724926431
    0x6020c030105132a15050c1504200d0218040303050a02090a0e0612010903090f0510120f0b150a03110901050909150d121205060120010e03220b030c0904 67
    0x1001d09500446440d03120b50080c02400003560f0f00d000c8803081180c00c0808c41d8800015600103007504503014123003c1c40c8081220f08032018100511151843e1440c1e00822021140b03030840321810010031081008158141c41500e8001d01800b50843c1446100740c0840c8140c1a603005074006401c642c40020b41a40d200e40e00e40300c0c0008d09200901c42c1a4a501c0d010b0045d07041400b860311510004c00c4013041c54240368031116242d0b10182e43d089811203c00420318010000c0c2500400c010f601d48201c001180c03194000c502e020005540308070341d43c0c46080310040441d017030710881c03074004c98040200550300d80e400400d480c001c000466074041140c9580341c814408c001284003054200c100c40c1c0780784090101911003003148506940310001e4a8038083c03484012204116841c138040780c9290881c90647c4024800b410a44c0c1c00300c2c0000800307041105486103907801c080020300244c0e0f41d060300c0503c200c251144200c01000b050303e0a03400d41c1042200361002d80a203110085c0116602c1c130b860307030b40f503014005 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 724928893 1250 724927643 724927649
    0x120807020406151209021e03100603050c040b0301060e010515120703020405090705070f03080901020418021b07080604020603060619180501091d15060406020c030105132a 75
    0x1c01c101403691101000300c400e110031110400700c0e90080e2030b0511039045025505c07545900400b4103071030408503000343c40b84000b03a00c6100c0e050b2060f107166001d041500e1182801075801903004000f0b10358211304000907281039110f036600a9051041c20490b01d60101101c0b4191070341221201c112022441901109010fa00d03003542d1450f6184045c0001e0075010390040c425a242a0b030f54040e00d0751000d0b0141c1d00da104141780141802d0b002200040403034800c00c1d6641d0001d06240000d0b281964031000700b4820449034401102d0740340c2c0091003003541000b1241840c80419280d014100d1503181010311912407000a0019020302000000200c042d0b03542c42c01c80e0302c40b8034503001200001800c02d0000700940400c0b00c11106412614a000c11558041d03c600e0080301c005410120742c01c01c40b00c885612484001c0c1007920b4444182d0b00c04c6c0720307a41e62035020300082c1100f075008000c0c0c68404030070182511409800e00807040c40100914001c40c9a10744081ca00407280d800412508122061000c072a0031164 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 724930143 1250 724928893 724928899
    0x21f020c03190305040c0501050403050d030c050d0e010b0a0806010b2b09050a0303060e160507080c19051002030c0307110c0310020702040b1e0d110a030f1a1012080702 74
    0x102c2c000000750140d005500071401403e151b0303151a203c00054602e0310660001078050b502c003182c6402039500c00d4014807083c2c2c50038a0510b0510750394180d9241941c62400300c105481c0d45403500203605080c0070404070000c0556074001c00555260202d600c0c250301c254403689941440041c00d56800703010920a501c014003415500300310a00c1642002900c450b1282e2013140000e0400c030001036800b04180e50140500f02041e48110000401d4009480540c030100d01101e40360303810f100151013080705005103407003c036150341314141c030515a160243c1044c07103010203a01803910500034486e0f013410348016a41e01100c81c0c10304420184a65402da45001c2c3e0306040b40354940b142012000d280083d64020701f14880c400c2c0e400340181b00c0349004004078848a01d40741c060303010103030351051220b190132004840c2030b07030003411b143d00c0c403040d0030001c101c100728950000d55950f08490150700820940050380c07006000c00751340032065801c04181100c0c0e90003007071045191042c0ea001051050055071021074880756801 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 724931393 1250 724930143 724930177
    0x2010f02070e010f1e030c091d0d0801080d080f130201030e01050c1e040e0c16050a0b071b0201020d0513080105011205010e071d2d060907021f020c03 66
    0x140c2100305280409014140912003005414004030b031750b082000098030340c082c41001802341086107100c0201803486544446209040211490610a00038404154840ea03503c020941c10281c038185070100745071920081145c440104602d034155814620b0300400701e2309484200f411180012006029030750242c45441d440e003070500102c01040e070700510500042d0f42c61500c1006000704201e05034015403284103410342004001660b80c0141400400009602c2d107803555400b400303500c65901c0c00d08a22421036401051105010005070441c440c80300320f080c00564a15407003000da00003501d0304145000b21090041c00329100f481280e04109031009031048034020080e66039540b04d88039546043c54019652540303410f1660659480200305a4241c450081c10030450140f800f20750501c1110050282400500314950983c03031b445005000c01c0301d400d0315606003413541030181c100051541d026203818150b510140d1014800110420000c02c0100981c0300140c442000914103800d61103200403140782080c107 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 724932643 1250 724931393 724931399
    0x50c0906130f0b0f0303251a1501090b070305090d0507050312091009083307170f06030a0b0907050d0b0714070809060904110d020702280302010f02070e01 68
    0x807a90050f0076582c012110800131120402c1031580300e200790001c45d244501c0b580d8483c1402c1090003408040c0500c10001c030400c10306084030f440d02004007681c1d40d0b6043d50300000e0329a000d6074080300350b0014200c1c00404510f0b0030300c40d40d80500305104103081c80d0302401404101c5030070701070180460070040002909940312060b0482c4504d26035440102114880e007101d080e4258400d100b8144031064800ba82c0081c0b0404503140704100e104141400042d550109070320104844082220465009003540e454401c100010411009059000286440c00c031000c420704101d1540d800050038080c150300401d500a0b6900c9009405082c070080ea004690404075032005001000080e10400713200d00b10070303901e00c54008040500d44440c0d00c07400d031014120550910681c0090300d0000001c0640c036070000d1000408c00c0100c59403241903000481da0505282d40403d800b0150b00b000c080020080104182800b400840024084100d0085000180c10840341f488041c0e040c500030030584001d0102891090425030b9 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 724933893 1250 724932643 724932671
    0x5010902040303170402010212071b06030e1903050412210f12050103050601051003020c1f151d34110a02090103030e01050d09080a09060903050c090613 67
    0xc0725200031000500140b04801020f8542c50b06940255416406005403990406030103080f40c10204d01610802d55a610000c4241480d00441d40288041e843c0450b5803503007490004d040403180da41c0b02182c80c11040191001950040481d404d9a0712148103071850042410300c6002c0c2c00000c944645e54518001410052035002010203003140c83d1a0b0307503182d10000740c0b0052070a841c020302c00104107504c4640140010f02d41160f9a030025802460018100307849400c4041c50480d511540d800c1c8210045400304410a00e402010552070380240c40302031061038441000d0301d00b034102100807070944040c0c01103901d42c001c03140456011507441405842000c01c1108641c610b0802414440120b0b0111800813030340c45010032403140240e0000d20020f1142e18644058078585100700115040010401550b603403801c403486050300c03050094000c1a00d40780c010002405501e0941c001030240305240c001000040c40000e01103112100c10f072100d0015458400c00b00c2d44814080940098140c146406d091602d9 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 724935143 1250 724933893 724933897
    0x31008060a1424060714060708040210030204050310200d060510030c05090918150f06040203040f12030603060207050102090a170c09090a0206210a14130c0905010902 73
    0x118202c581c42c4800c0d210030030190004100103401c507030b0662908810740c42c18070300311014010321400385130300f50a41c4022079030180c2051011504100403d0020f4244000d60800107584d60700c000031801e0440c039003405c000001e03170384098903410440c1d01034a0343c1856608001070091329400112002155403162800381030f9401400032030280c0c0d401a0050100140b03240d11900412040071242d40301c0c0d41c0391003c0d120511910520003450128041000d003900101d0820030000f40540c3c03000d01410b240a41041000e80c0100800070380403d106e280144148008242113040701d113901b41c1e000d6003038480e04618410550242080d54005090b19101060010a105064005160300e100c202c6409141c00c2d110222001d1407a504e00300c01442c2c0d402101e4251081c03c5c540c040e907802c000c1d04011501c10015a5001030000c1c0c0c4950081070b40310303901e0000f0105034201c001d521500300381140003c0c044255103242e51254650010009025400d50441d07c0007071242000d0b2a8003d803480c48000e0010703684a83c401c0010f5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 724936393 1250 724935143 724935161
    0x1020c19080712120f0603080a110c060f09011704050c061b0d09031e080f0f070609030f020d0809030316111b1905030c090c1b06041205070309060302031008060a 71
    0x2da405e02d485030603210024400e85c41030301d40c44040c141c14411150000c590700d802654042843d881403c0d4691065590400907000d41036041a1030b540e00c440f14000100015000f20b0184400380107001800300141c00450608034814054607455124018646400300c1152404081c40d15070140349101ca103016407181004081d02d00400e4401c45c8090030600759120801d035001e0280c0850030a108070641da04400005204101d96148180c1c00c2041e40c0d00c50380308440550a0880105010303a001c92031560301071001c58008142070424442030f01d0100110360312803200900104000340030066180301d00e4080c50042c410700d010802250390740703440448801d81d900c007845001d41c400c440c4209204007111424891509861b8080e000d017840c10203040611402d4040a07100018180c0301340401c45410709640e20340d4807408034107001000e09091900b0a86600c608043c421010410208407280110b500100341c03800b19102c80c500141d403513031050901030003c01e840c0c00c05c0c900e07401030100f440103030710f000e0b0820114 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 724937643 1250 724936393 724936427
    0x70309031206081608030c060c0a111005040b0c0c060c1605030d090b010b070c09090807140c090705190c0503090d1b06030204050901061b02060406030e06060301020c19080712 77
    0x50180c0311720003036590703000c0c01451070300a40c080c0703000510019440d40680302404190808800f0a40150034140c1800e810140c006085980c0c1d07000c01c42403040c5009071980080c01411103510349100c00d4601610384400404800780c40034002205100640dc0486158000341c22401756500d130003620b20100d02400910100f9146030b4031041c00480c02c1d5440c00f085400c010327031201040f02614a40003082c40a081c41e500191000d04040c03003900d0104109001041d20708152002824105500d00c04004202c0d50160854040080901038680840000c52030240344402c1410b0a40c29800f946c60403620b03501c80c400c01144c000c6005d81a40d02000412050b1800d0780e5000d010030303001540c8a000441c01c034042c40c42031991086d40000100401c5000312400402c103158801180350102850700440c0e40d99106a02c00c80000340d80310004031081130203015491f04504108c0080d442c10304040b1100b0354a00300d802864401c0000b20300e0f40c1003045a514112811545d0102443c145003900c0040039107400090090509 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 724938893 1250 724937643 724937683
    0xc0105060a05010e0d03121b0906021908030103021201090834020105030f0c0409020712031a091501020c0a090b0a0801060e0c1c290301110307030903120608 69
    0xb00d035070240341c80704820761003d402c243d150001501d0484155284d81070304191340b5640e0101c55542803142070141940d08180e251541c4032407820f03100030b1510f003183d0b603158030940c503107019200000c82010480381126012a8000d2020728400034060045c840710314000c207a940005802c2d02484001d1a00440c3c482041242003150001000c0e0046400c0581d03c00a000410401c005895030b030880c081c032604034480000103801c241d281c800c0d01d4100ea000d5001500d805070f03a0f041800e201681409012050b44c80c4840e1810782011f8400131a14001b00523041446003103a003040c2c05084d0b4401c000810381e50400414070300c00700c0e5480d616a40101502c00c11075008000c0c0e540c011802900500402c4221404480c024466642c0c0000030b04076908107002e00280b10200031100041c1d40002e000781c3d2103020088080301040300c10200b90132480081820003a002e42d040c080400140d034160019294054081e042c0840e84c0f98840c507040741c0940d8044503e2000030b00c0c0880201d0030700320010380e604147c20b860034280 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 724940143 1250 724938893 724938899
    0x150a060b030606030a02130b0a09090b04091212140f070305070206090a111203070c0f1e03080f0c0d0c050105072a02240d0b0f030307031d04020c0105060a 68
    0x3080c648402c80741180c12000030804228040b009900400d942d0369040701204001d515248d90326036661008849000080c829101401400030511817040e01c2c403012201007082e411141d503003c3c81200302401c00801d10100749200803200b0455040000c408000c1c001c1f0000c1881c001c94007a074550307c1a00c841c000207103410002800340d0700002c0d000f03005a10050050420344000c7e03031078400344185501e00c1c5420465044000c00700e550100058038107503101d44407003000039007426045c2100302040e50200c60f0104408011164100809203048156a0020744030f80e075407101c0c008081e01a00c90888051000e104140b4102451648541900415440307030b0000e011035120404100d5012201c81191301010f0450400c85036822441d200314080248050142040150618295803c0b0705201a04116400c40003c0880c250000d511681010700022607900c40718a500c000804c1e628010700c0b10045c10300c2140c4414025007a041810030304141da0003001956620090800c0364082c0c0340c04d54002d40074005981000c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 724941393 1250 724940143 724940159
    0x101d03070b0f0403170c0307080603030a0f05090f0a031a07090b0414151611041a09040510090309090e0f1c0e0d03052101080a23150a06 60
    0x48500603000828924241c4603a40c0a64140c20050000c6082c4880c0213684142d00c001960010b100706151b00d022520b9103444070016000840042c0020300c6070b00104440045141c01c44040d002050480c6001074940007404003241d4504000c414017030303102ca2000c800004000000a44000020780800d80702140e48030138805a612402e940204000b041d000d01003070156100d4154604200d2a0003044a642c040c00380c00140e68641c80914503044c1d10281581e80018091807110842d00c1c0e2406440400c44102c5401005004942000b1401c4c8941d0481c800300c0c00340142040031282c4005000303020013110600c2d1074045d1460b101c070310600d070060b420b01c05040c505010119906481070f2400c0050003010010104841c4101900c01003481403080440446039071b911040c2c04034054521a807105035681d800588900c09049543d0109001c1122100051201d068007143c4440c03183e60008081d0084150142c00702c4090100581c00c080601c960012242c20850f440038180c05140f017000c040000300c2d115099 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 724942643 1250 724941393 724941397
    0xc09080a0503072a1202041514040b01110a060c0909020d0218100804020103020904090f0b09010516090608060604030b280e071e0b1207030b010e0d0f14101d03 70
    0x21144d1101c0c2c40140030001c42c4002500d0700c1c81588020300008010b40400c41000030030308142c001510310944030000e07110500f0b0610622903102800d00303280390350f4120003400a984000100005000e039481c0e1464001050050642d5005014074001c00c1d5120501401040c0094016184d40d11000d003e1340000e0110341800e02030b081d60350b03090390346a1083e90303140d03001074010350f001c081101d03000342d0799134403135000b00309050f0707107118401c3c400c1c1100182400c10308130541c02d5503000780c004607890111940400595070031042c0074088500c03905080c02c4956034140000d550f0300855202500301e054103c00c00a10300d101d101c081c07101410906090002032041083d40b42282c0b00510f15052076400100c0c00e20a4a1a07134186108001100d498011200c0d11040c403250300f50020680a8407400d112414040c0301134043c0104c100f110028600b100c04240300e00c00083c4030b00030b14132014091582240540052140704400c5200c0105a0707000c5580c00008008002c0003848000001c0488480c0c1c02a4410740c0000402 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 724943893 1250 724942643 724942703
    0x40513020a030c090e04060e0c1c050601061701061103070f031e0201050108030a1206081c080f070c1103100c050406030510060f14070c060804050c010906050a030c09080a050307 78
    0x3100d80141c6e615a52200200741444001c031443c45141d0380b82e03140303a541c0d07807000200c0f220785d840800401c00549005c0c1e20307200d010780006041c07040b6080e001810a041b584402d04561140c42c10000c003030700084010f0704610030b44401800c0e0728140f249103030525030000311421480601040b01e801c1c000da504c1040b802c0f104203004501e01c40d04100004200b09109406030844100440c0e0001f030010341e28038a0320b14010710f41000c407030b10b0309903104180d8407242c000d02140e512200d640c0e00305074107185c404001440d1040242000b400039030300c50058041030b00c081204aa02080035401003101041048024140380c10030300c2642c0002c1e0070040003440f001000040389048441980314400503003580e0405072883d21080080000d41c400c00c2c0b0628002c83d20140e40503000b02010385403088035042170304201d41003120400703603a8184041c100040084a61000c121440c0905078a400030702c0c14080207003280c07046407503444071810b0300c694000c02c0240701e0080006c00103075103e9001c041e0340303482c03040081804845440c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 724945143 1250 724943893 724943909
    0x70c020d20150910170a05071e05030703020307050d05010b0c0c04090f030c050f031611030a020f040b040207060f020a030606020a080301050103050a290a050307050609100302040513020a030c09 85
    0x8030090b0004e0908208032543d01c00542040c1001041c030040d8032150030001c58407080301c151100c0c140188039410038000034a0174206880e075040c5808060014182d4400a89803108066000001030300d2103110f18207440e01503140450034440c550f0348002000d116000740b8044481c6002c0c034242122285018410028003546c010418103030b035482c81d01c040d68a150121029141801045154241d001090008000045603082e10002118207401c00c1400414400f88213402940035000380809607841c02c06a0004140803240404e000b0a1100450068003c980c801040030b17081c240002001c0100744c0184c103449490360740c2080880d69801040ba540d207102da01c0584680801c1005000d554400c1d008258003045901c00482c200f04103288c0d000188a1503881c800c1c45522240803240c5a01d4140ca506004140c00c030010181c850038000019603a00c203013200d8034460500f50300c56010141c040d4040c0c600900e0020300202200160412a90180d03000118840020389004070441c41300d4060308400e000c0c0c80e100 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 724946393 1250 724945143 724945147
    0x30d031a0d0305090a150f050408100506040f090609140a0c09020c070e010e04210207050409060e01060612290409020109080f07090f02041a03070c020d2015 69
    0x14080c0324050344001c60030b408000b001c00c05a0100c0e03c4500d101001015040084803000300030240080c055250b015540d42001820003042206070b0000074079400c440c006110028140d1580c50004004001c854031403c04a800c2484210510245030301040c1507a0180080160003d00fa0403100d0703c074244c6160041c00602c1d601030601c00d19400ba8050800481030340c0c221440a9162426010a00c4099000d0710314047c0c1c003420841044003180c80e6007620030200c0101e00c5049210240a515140b150061f1030086176500700300f00900c110345e04568403243e2503000801007241c03501d800030b04140640740c1c03450381c0b54240f445c005100800d13185440c0e50340700441e10201c2a070104104000192004040981c1046201c010119180ba03041c40f071034580d8000d440003000014038201b0340c60143d07001c4800d1485a02c0c8140000c1003c91544152028082c0483d0011583c80c2d803004415252078071250000f03500051000004001c0009c1d10000d107840c2e402002c00d095844001408008040894000300e0a040e802 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 724947643 1250 724946393 724946441
    0x9070f05190b1605070306020711042c070b280f050405060f0c0607051801020604020d08030c040f09020d240b0d180c050922121202120105030d03 64
    0x40350015180394201c035842d000340142c2d10f03104d0915003005604251640e80c4c0c0012285c007041500c09200b0031012040e2014000b003880d0b01c035000040f2104400100da80c0c0e11101125800381c41c00d201d80000340c0100c0b281c244c0c6803000c412944a000c8440040c05110f80380c9102000134680c020718a4220249082c2d03070b140c0ca040e04010074081c95404c10081c00040200501c41d00c1030900c41030103864810060fa549032a00c51000480c943d000d458041c003030506640011040c04007686a0b04820044035400c81a02c45c3c0e01e03100c000c4404500c0c810b03036101c8241800f02c03c80100b00340f10b4640091110003000750301804610300600640c02143d80055040000c0a5a50340802c040d0541d034000e85000d1040f1100051142d030107001c48203801c108902c0c21100c8002c2450144114034004100c180c0140f42006c0e1005c07243c0451804010403652910060b0030756080180604409102d0041007000071261502551a20046400607100030828020180700e030003080d69803c13601340300c0e200d11000c0a224207104250602 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 724948893 1250 724947643 724947659
    0x516260f09010c0c030f1b090b0d06090206190e04060b04050906010c030201110a0810120305030408031b1912050c070f050a1a010303021005040b161709070f0519 71
    0x11070041113070b41041002e40040810005103c0c0d00d80d081c01400c07201c0300c10000c44903a0341008810303040681060f00d000688180c5886004116110b03951242d030024000d800303030001541074000e0b81448a00401d6038940408502da101300d4603401d8090a5a06100d003c0d250310300101c2c0390085005e410b0b000302d03414002070320315071150009000c41c0e0300a00001032005043d803040545917010510382e0000c50f00040030301116802142c01c98000b0300c4843c0c18441200d0307455400502910024102030051135001c0041407850104480c60300d0502d030101c0040340d4543c0c084815040c401d413a12440300105c0c0e40716181d07440060090051610941c403e254046c07801c1d11955440003410b25403181500d4038415118100c8c000b40c6000206c3c0c250110b0341c8403402c1c0c0381d071451500a15040703800c00401c20b42410003091100040e8110ba445401c074050903050948640800d034125100c010194030100081c40f24414003030754820124450b015902459125000180c4580500003400d07803120842030440c4210b402008464 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 724950143 1250 724948893 724948907
    0x23060307140d0609060b07021302040308072409200a03020a05060c011401060c0c06020111030a0216061a1c020d12050d020d1517060114010516260f0901 67
    0x3800300c2d02c0004485032510b10b2207084601c1504204041e030301c0029090158588401c0d00407a038070706044298038150459580e44614001e40b0001086d14a42405c1b00c0a802c0c000813102d4811842000e040041b003030305042a26080803d030740400d075200244002c013941400d0442e090b005503074010b001e45483c5480d00051007403d034040003405a06541c0c0c0c00000e4010a402400c00e4020100d650b2907507451080c0303080140750b001e0280d004c0c005680c5021101d80d1401681419a031740700810110058a400c880301c26604904048400104014501441422441040040003000e0607085c2c80031068221540e1100208800030500030350702c0440c103143c81001400741641e8038100071440c54000d0500e4072404921060760030000c1e4540080c3c0d00c4440e000c02440520780c4e000c001f807035640301d40380c1055528802c0c01e49406040c012a9110391841030a01501c5c0d018108940c1445821141036000d5521070802c8032200f0855007110043d1600044102d2208910105940400d00a0301249140c03180800041d5190 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 724951393 1250 724950143 724950157
    0x51e06040219180e091c09080c040c05040e1905060a230a0503060106020d020c15090904020301060b070b0603060601050a12050702150405061021020d0206090301062306030714 77
    0x18030f01c2d280010608402c60300c11399002d02c860200900c060911800c2001e40c2c2800e0005100400c86009401c000081c2c00140760440c1440545000640000008046801e441203030800c08040d0071321024800c000c2c282d020a00303c52440c101041100b6103601c4104850f560031031140944242c040804a540803110043d45426154010080c0440e2079440d8003003405e2400981c01400542c01c075280000c00c0d030381c05019404a40400311003009524100c00341e581001d00641e02c01902640c2401d000134119182544a54040d22000c001d0f50380354040d5103441015450101d440e64041c0c05400040f8150b54007500980e0010401529070060305400105900c000b400002e0916007144131b81c800b50840030ba051847c6601940c00f4001410741c41c50318241246c03449000b9403000c50700d410310701078840406c40c20401d9031070440d5040b5102c15880200e400068017030b01928551640c5946003000000d00142808403981c2c202d04c2d0504005040d466040421065000c01c440400c0811507942c200d8001d10301c034200030511 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 724952643 1250 724951393 724951427
    0xa0804050c0f0a140d050d020d08010609030b041511030a020a12060b070b0c041a0301030320070902160804120c1a0702101b060b0f0a0326040801051e06040219 70
    0x405d841c0d80d103d4514050000c0c19102c00360b00b10b1031110185980c81161a13002d0510780c14070103038517440c50380c543c00200700041001c1c1802e100503025401441050300100e90120003031840c0f0340c036400c09070880402948074541030000729130346080e1801c495040380102c0c1c00702d43d841c14405090000301d0301c588203200c00091614400c000308010219111030503445ca902449202d181603038403903045143c0a0803421102e6900382c3ca00304000c00410403800001100da05542e18060096111102120340c030403c0c19110310000d112600c04034002c42c1003a8950000038249000d080d01001c001d549611519441e002c58101c0c50980004025440140c1421f001d40958071840d4a84845002d07040c6403042da01700b40800003152683c2d204da001c44540d103400700900c8002c8508980f85140540b40d40d6a2660340c4d410300140900d141002d41c0d0070058880b107502038900805000c0020720252400344821031086014030400c2903020003540c04604542800d06c296048083c40c60071040292440800a44200303081d0002c0c010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 724953893 1250 724952643 724952659
    0x406021b0a0303141606090b0108061603480507050c060a0504090e070302030f030a020303060d020d0b041a15090a051f03050a051b0d03080604060b0a0804050c0f0a14 73
    0x45c001200017a105d940c3d030b003d0600020b03403403c6d52900810510069200f4061341d4004e006200141d100300c500500c400b10740d81400250628090840e036000c8140c500c5c46901a6014424074003581ca07061b28135110003100c02e403100c500c003002c88016105401403600103401980300505c0c4410394180840180010941c40c1051428651341c2c640c0307401030710307251007901c140340d00100d40402c21400c00300302d01c40510400368090341c2007c0030701000079500d010040c4200d100d2864a410041076480381c0710104005900b0400c60600d82c5414140001d442c88400d15400007401540009a0400c48401c41039081a01c01801c050168a800e4201e0001e442e002d000c1140c15070810120100d81540b4107414001540f10324041c060031002401c11500f45941c400c9801d1400e95202c0c0d42d8609a41c890342d2984405900d030410402c16182d050108000340003e03042198080e00000e403108a580c4c105000b944a00d00c900e04a030341482200d030510200c1021071010940040f000c4c2070078000744601e03003102215080c014180341 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 724955143 1250 724953893 724953907
    0x507140a05041809050705100e090402040b09041415160f09091508060a05090d0c0602191e02150105150d14060a0b0c0a0f05210406021b0a030314 64
    0x120f140414191a41c200d69408880d801c1107070510000000b400200d030480c1202251000c003030402c035200311a0f5841001e800307000034110356a41e80f190750406006054250140360924000b412190101042c5101348074040e0300c0380441081c0d000c00c0303102c0c0220003403141d250386409009072b40d20740120b030340c1c4000d1180c410360105406110340700b04041d0403500c1c4010800e00b413800d500c1c641492005414103102c10b0801c81006902d00c4001428400c0102600d4041017410040c10480024002c8014882c02c01445082030403142e903200c1c0902141c01c0452118484090302e4200503660350381c1001131000c03114214001041907181014503901c144103d81005450711140000346400c440d03002d030343e500203101208244052400d1404510000d001c1c1c200d215880e200700340450b02d03559542c0c0b904c000d00d00350401804101b080802e12001c2d1000351a5814108081011345205049030064007841c0018442c002c0000e0800c601c115012800399005820b101c030480c00d5480446d208046c0650103558000c0400c246 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 724956393 1250 724955143 724955159
    0x5010c031d1206150103060803160f0c090203011502031908150a080615221505041a040c0c1e060908030c1c0e030922020c010f0f0507140a0504 63
    0x791001810034050491413800044030418509880e81181c10107290100a02190400108442d510500060181641750f15403829030007078004070000a041504144000800104030780213541a5081c200710314860b000b48440c220307501d00440c54140c0b4442d0014540307540d098020704640360010510106c1081ca00115004500e104007a80d0041e0240d86c850f0082106c850100d00348a410214103c5118085004000c640c0c1000e12840201890850740c0f5144010440c090051443c01414046c1045c00001d05090741d5001203949031100324015070401d410b64610034803500c1d1030408582d210a06e9034003211603194071010700c900e402d000c40c0d41c0c80d90380807aa00400c081c5400345100703c030400c0388683e50743c0d0719a000348040352000c000b64166a0074402c0c858000e500c08419034060342010390345800b5210340d01c06000092488040c00c101c3d800e1000419000303120042d0014800c500486505105d480800f0040908031071040b5441d80001e0540070a5a80380214207000344a05d0805244c401e040070744072105 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 724957643 1250 724956393 724956409
    0x403200c030d05190807020a030518100c05061f030b1b0417160e07030c0903140a03031a06030417041505030402190b030a020f1201030c05180105010c031d 68
    0x1040300070402c003080e00400d600f07049140c0d1380307031155614050403e03081c03605010356242002400102840004a1001c8120b000e00d01d281071511001815005546c05403000940100400d150136640e80c00780c40001043e14116042605048200d80c0704490428690740343d0410007600039200610041185c020f0305080c15945010344003400c40c43d03161000d2071140d0381e40381e4600005803942017545100c030201008003514050425600591301d0401203007408000300211100303030040d000207050300c191601c0600d00b2100001c84c04600c074800c2e10200840000491802d10000d1400c1502d80e00482c00c0000600041384a04185403003a038246205003030a80700c00d0150740c0549101028070010343d003c000c20055161400d900c0c1d880c030103100c3d20701e111181030406445e01840001e09060126800090040301d107644034040b1140380c421103a000055584918008941e034446124407403041d00340940a18030356001e280b049040b00d40586603011038544d43d07078007034850503000c0c00c400000000d040d011011a07124500 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 724958893 1250 724957643 724957663
    0x20607020d0302091903210f0207053106060f09080604021009120f060b04020c0705061e13080d050a020d03090f0b0a0522020d0807080c1006030204140403200c03 71
    0x40c1204a90060034211800c101107c00000f00700015808034046041c2c022685100380c943c156006040d050200c5280b0141090b03a2180c520701c0801d41c604914a50140d03800f10050b106103940d800d06105152004603006042c5002d801c0c1150004e034003040062910002644c4038813098140040c01a5440a5800000c40b00b50070a0350101c007428484c0b000c00049104001c100c100480d02141404c1c4941c0c5a142c2e940050301899000707020008a030b60070f031125014032030203981c011580155520050301004644100328400d40b18103201c4c0d0071442d1100c2c0d010301c060b90300322036081e8000d002a0368210000c0b0064003901e0402d80e00200f16480c0f0001168801c606d052003162a00808580d0382028000c2034401e01405a840d050004045e007040016a1100300d440081ca030030010300da443c6c040c1810070721124414520360448611460381039100f043c4203500001d0442c1d0080b1070401152828059488004104450040024814080d4420319602c84015400810321410848100070480d0011070b1510840c40 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 724960143 1250 724958893 724958903
    0x171906020a23070609080c2b090612020a090314011d0d0f0c11100c170f040312091e0311040c020c09090a170c0c01020607020d0302091903 61
    0x4070860340d0754215009600ca600a1040100310712596101e00005000d00d8900500150b200ea807890180a0441c00740c40207451310794240c403d046102044801c600b01401c8421207144001c0300c402c113144d4090440d140481c0c0b525240c42298a4650032280029802105c05d20b050040d8030740044089030210702041965022076000141802c100d408200d80c02d66030658032041503120760015041c099016401031802d154a00385a02004071514003198411007410380150840005403030881c020b54801c04500e0b000e03005400540800c0442c41c800b14083c451030480044001c002c010030070014025880c4030341100040d20b096a242c54075110480c0c020500c2552032000c5206101003802803003074202041c2c004000c2114200f0800f03816a0000c0c7d2500c001a0303c281c8038100c0b403c0000c500750020300c00070100707030344c0410100b001000043c1001c140d80c000b10080d8490f881400d081c10510750000a5144c0209602c1e0003e0103100c00e48401103010f54010003c06410210340d03000c1e02004103c660000028500c10 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 724961393 1250 724960143 724960147
    0x60f0919060b04050916050919170a030807231b100c02010605030606102003070305031006020d090b0c071211010f05070b010302090a0902060c010f051302090117190602 74
    0x48403c01c000b45c1c0016140031361a01d014580380d00c00f6604481203840400c402e854801e0000041500749181d46c2043d88002107942c0c1105500c003400c88041580c25030648a07840d99500d40d1036440c8116200c1040c9850741071340c441c030b1130080218840908040c02c14101d1519182e102c240e011140d140c200301c058441e204000e0384a1341d07102144c03502806a04080c2105500924481c540769000070030302010041840300b03019034000703601412101c42c20041d501041c4481241d648020614006206500c21100c0c1104142039410110350544081060310f10200c0c5076072a085482e041901c1c500c0c0356030105401468034450030400144107420840c03e000350900503440540c501080100260907041c5994412040160400906e4001001d038100b90307065a4040d220794903103540c1c5481c050012704802402961084021031180703075a280540000c070000c5c402c6803060000ea104c411901c0e034540b074101002580240144014040d40440c14075040181a2881c221000c40d803e80d92525440501d500f0b045c1e50080d00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 724962643 1250 724961393 724961399
    0xe1902010f0c15050603010e0303010b040501030609060b03041209051909051015030b0102120319060605030c0f0304050a08070c080705060f07060c091701090317060f0919060b04 78
    0x512035840101031820700c0d641540103030395038400503e0380c141018001a035600c003041403901c0c2544800022800300c0102e950b20358441070348689a4200380b160fa0b00082c241440462850356130b001d501c0803510000b40e1a030844c2c0340c3d5601c60500d00d6000d01c2240402c0340c1440f0004040c1c1c1c500da2004c0c40c01c0c501c035818074040c6040c85418010b54070020800014650103141c100b140722188080a0380c11540ca10300000c07104207841c0100d0070f00060307100d81c1d00c21400200500c06420ba125030ba200c044c40201108015441d6070b0101640c0c0c500007107031584450481400b9824030000000000d41d0311074400d405881d04081190303a50715064118501c2602e600d0160142030008020401005c806404210780c1c0d18100740c46504400520312800200402c00c50f1100c8a40303402a00400240002e0403038408920907440c00851140d0090514010950000c0e441480e00c600145100c1c6001340230f0794002e00f05030303103000c414402c0c44507940c0068034551451501a0750f000c81d0406030703c10700029285050040b540c40d49 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 724963893 1250 724962643 724962647
    0x20d0b07120e0f060402090703061e080c0406030302070b0c0a0206120f0a050112030f020115060e24070816060e150c0306180705070c080120040b0901080a0e190201 72
    0x444000402540c0c3c4030f541581030b01400040c445520a034101c42841069580718804c902400181d404001c000308040300c50581100901000d80c1503450358000c5425440d142802c00c800e4a026210150160304420024420500c042c0c00402d07001c600c5004442d003004590b404610154048025050103001e8002400340c2042c4000d10683c111048640500055050420022201c1a211001014403d4145421a26071700039000fa14245038482c030842100c9603224030203821402c505a4091250890380c154400f030360103081d00040a1803258440c941400740a548140321544190b1403901418496144500041c81c103003c0c90044002c468050f2203051036125410104070b01c081c03c0e0507109002442044100c0d02c94420500c0c0041030074200c40c520752642c503826038051007000c801900d8107102910200b550001500b0902c640d030041412100700301c6040c1e0351f2464a008600036800000c1c82041028129840389d41845d400000c005070000301520b411801c140b03420645003148487c3c803506c08050003590707 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 724965143 1250 724963893 724963901
    0x91a1b0c091807090507092103080a022a120409020408150105090a090224120603061e15120d1e0504050910030c030b0a0e150103020409020d0b0712 65
    0x101e81e400c00380c1d580040b068209620350865000781c6003000e9580000a810a1043c00c50324020101070521094003c80f440c0e5802e08042003075030540100c0c050001240500e600391084650003039802000030940c84030000c501020814141100c2807910a040c01c8410f249200002030004210044d0016036403841e1000360740c02c01c02c03103103238070380900042100412458440382582c56000400150000701100503100084110320b0304402c09040e8010388089240b6120408010030750000009001d07440c0b550758408040d6120401c6a00c82c10242e0004415030b000c5080d030f082c094014480c0d801080d84041240041211078070b403118001c05503070122100031543c4d0f0308221004d00c4003454000750b4210305003109005d4014441c43c80fa10340a0801a00003405a4010f411818040d5611903413019440b40e4a0070000092001074450303811a51030140003814030340001030080c01c00c540300145601c16a18607001c01c0300070681c9200036038025030103800b0b0340001240d0600781032043c10552510302c00001d500041c03004503 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 724966393 1250 724965143 724965151
    0x50f01050103030503010b070611041e050f1c03090b0f070212121603170901020c060c040323010e100204080111070506151c1a090607091a1b0c09 64
    0x5a490300340140042940700d411a8190307015880b155a0350b01d01c615000740244403904800c1031500703011402148038454100415182c2d00c003540142040c546620411400d0025601502c0d071150791645e40382c1d1900b01a441c109089800780c20026081d541e1344400854907802090360301e6400000143c8001180b03002000070454400780002420302114140c92004036220304400310340e0301d4680c00f48020030103200700d110500c0b0362050181043c50303080c0754184038080d4000c4140940c941c000d080005103d4030414094804982e0072203000d103e0a43c2c446060a2045282c101d0901103540300d1794100300c0003000f040b0b00d000250069100603a503901d040340c09400c407044400500707a070b010108130800101d940000d0054102d0311a0690020510464000848000160b0f460051480508140c4024403000c100f078a200e0980280079000190344018241d030722100700303c82a801103070f030007a0240709102c460300b4000c20741245000e15903c0c1465000c00b441c412510214040e2a0b1362003807903440c0c802d007002d0110b5904 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 724967643 1250 724966393 724966423
    0x7090501150f0824030309131a1002030a0e0117040b160908070306020d0b090a02031b0702030307030804050c0a0f0f0611030301030803070c02040e03072f0d02040221010305 76
    0x60f90402c8a42d001c0318145000032004000100c914000d00d03a0b509000302c60030000000c01c040c4402440c400c0c00303405403043d400724042024034071461450500b1b00c032640c144042c07156406140740291512082e5429400d00b001c0604101301140c01c0c0c000b4603001109a4043c0e4010f01c9001054517020100711507240340c000c2154200a0008006c00c00c0040001d13421059a034002405030319010329401a000a049080075207506c050317050306100049400b58011401450480c40116400c1c1b07642815a10520803118000d4040c0d00800c16400032a01c2004103581141c0314000743d80b0903100510006a03d11101c3d04403080c04000148104400d11010001c007009003d2420494040514500300359241d00052102605401c1c2c00000144c03d10300c0f41c84020382d000c0d0300400801c8800f06003518280d5079040701e80f00301c90381e0100080b00c03030f50340015004110414025120174046440d940050000005058500301e070025000e00c040040d0746213404d00614003031484440300d5015851800e22600e02640764803481c0c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 724968893 1250 724967643 724967657
    0x1020705100b100305090f071d070216030809030106091d1513150f29120606040e0a050a0f031b150b06190315091e0c0207090501150f 59
    0x50b55844400f459001d00d040742c20b000802c1d5a4100d04d00c2c1c104540180585401d0083c0240821402040c1c00c51042204424803170454a80d60b24200703a0740c50690003c03002042846613800c000003900e46c402400c408101400204044e079032a10b0000640d00e0300703103000e41600401020010202c1c410401c003e40f050b04400e1a25a40c107044c030030003000604c00e00c4040d000c50054a10ba01c1d485030305030080740030318a20403030810403e0302148800e444002041d2030107510007e21030350045181f0b010050680d50040c1203001d0b19190316a0f40800c0000e01e02002959150b0191107a11300109000b80400744419000c1c01b014240e070107036450000c090500e40099800d0b0719101c0d0203003034003103445c24075103141d411a1000300090741c04000001032000e004004041c00c3c01c21122140b24082a45a001100c58100807142240303890b4940c51000151500c095140c0740c0380000d81441031b1070004640000b40f00e0034041c01980d0f411621001d10005440d0240c20904000d000084a90b82c1140c0c0100c07250003100712460404 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 724970143 1250 724968893 724968911
    0x6030c03150c090a0305060c07030e0301020913150f0e100b03070e0103110c010516030b030c22060308030109020c0d0305060d0f03050417062418040813080102070510 73
    0x222605201424007050048086082d406580b40d2204c00c0340515088802c441442c500070304040180d50118000f00c0000300c1d24540403480341130500a407106076000503d03840c0380036403011520008010301d4030078030f400941201d0f00082c45030300d2920740005045c80481010395031821102072180e4004642c408040103400308100000c4c2903000203005285542460302254500c01d0480e1401036025a44400c01c1e294a810b0a02031100c10b00c0b034184810001c9901c0c1401940840020952500d07640301040350031244012130500040c80100103010b1142d00c1030f400103601900c0c1d88402105030001d030045161036500180e003100001041044140c0c0207450315081c8103038984000401d0310304041c144000d080c0c401c44029041050700a0003594085d001008048a56010306080382c4c0e60384400355108a411601281131004c2d000820f000111100005400348100c00c44c04010b40510340d6000b40f043e580090103010749c00d25410407503080d10082028200160300d0b0062420b2841c200035000d8880f07052a45804158 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 724971393 1250 724970143 724970173
    0x2b11030118030c11030304180e0d08010605040e09070b131e0b040306020d1e0603140d02030910020a05031324140903010e0d02030301150f0e06070609020307090506030c03 75
    0x700d1603103130b000c085480d20034480404649540101d401040100d250200a8202130003158050f00c1c21021283c22130700c400910b000e043d6028082800b5160000c0d0080000707101094403014030380c0e048500401180c0c82140c4d1070f220220705400640114400a0082500708100c94a0500c0c000c0c2640c0c100d00010169032a0899100f05071040e440010240c0c0d4001c145482101c7c0180e0041117542c01c6170344040e01409180760a040204507d010445442c1f1108070981c00b030640010303900d004001550025403a15465800700203103800890460001c40c82072280480008100f88003905150b00503d520540083c00c10303081c11740d004600000c0400030fa4002c8007a4080950200241518200031f0940303d80c0c40982c03602180c09007819480b090024840c0005070042c55500200440c100c40450b0018011048500c004890341041c070305040c00019211110901e440c0b5147c402490b40610810000900140c543d001ca0700f8849503034450a901651007013003101a040502070038140c203000b207002c0d01072a6070314100 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 724972643 1250 724971393 724971407
    0x2150c150403050a0c0c0e0705031e01140904020d0c03050c12010b030304060c051c0e12160302061e030f060907080912030c0d05070206040c06020f0a06050406090c0311040b09010b092b1103011803 86
    0x25181c3b00320b000d00d010905648461880c1d00ea001d07008003105024a440c1e0a200c1c0e5a602d0695680780905403800c200c81d199034042c4225910340e80d00a0140d0b03e13051038000f007191007203e04c1506541034001d83c03842c1491a142c080010881110300c3c1c8a61121102400c1080401c03070a22080030002e4004029503650901600a88030549504561440c0c0300c450f85a5201c030840725041080540c0c2c54000240025000040c5246101e110101e8040c070300750361402011100e261054488220a03840084100c0ca5940200d02450780001c6051940381440c0c0482ca0314070507500c0a40d5400d025070080014003061041010040e0301030a030b00d0004025420641200b50343d141012032002e000d1301d507141c0c0407404100e440d8003c8a280341e08400d060664a461f801c20b10405c00d03030010000e2090f49171014070038490521803402c504946000c483c050078150108103100054403080d11100c0b90800b003080140b10386c0c0b6112280070341035014943d0381c22502440002d241c02c42e8150519040038504800c8808002548094 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 724973893 1250 724972643 724972679
    0x115050307020d0815030102120402030c06133f170c0705010c08040e01060206182814060108070f1e150c02150c150403050a0c0c0e0705031e01 63
    0x44e24100701d64030071654030380c03004c824004558554000036294100e045170644490040c0c1c0202c1c140c42c02e1342c41c0e070410001d891207118600360821801c140c04103e41441000030881007041d0114000e02008400147c0c0220914488408610320010240e0f4050040d0305c4462500301c000302100ca40f030301140203816640c43c0748502c511410000707180040b1040181080c142d070018203041c0c01760700e060b503120200030b501d903402241c0e241a8141c0f5a24400d090410015640810341040c041c888040d040103a0503245601e00310b00180c44143c0541d00d52001c0d6402000800d0003092481d015000d0700341440020180340025601890720700d240d1041c04030141140344032480880d401c4c102044c0700038821210075640c5a0350684041e601c00204d100c502103002c5014020101c4180400c00c0c4c0f049107200e81c104150070702050758043d00041060180b60005030003800181e01913409141500080340d50744d405e18102104c1259800c000a03400320912440c1c00c01c0c84400c000124200c5120201581881211780e10400c56503 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 724975143 1250 724973893 724973897
    0x3081509061e132703080a0b2107090f0b0a0e062701050a050409030e0402030c0f0403050d0e0d05101d0307050f0d0903020a09021e0a080115050307020d 67
    0xd044401c2000d000407501001c40d0700074106604415107001c80d54010200e09040c4102c0c51084442e07070011340e402002d01c0c0b040c507034541c407a0080c540301d01c001300004051101d01c441e000307044401008005800070b044401a9011000203003100ca0170801c1c03500c180d03156100c00580613420008000e84a0313860489440039501c08a1200c269541c4800c00250458000c1244d40310703407441a0580000d1054082126060702c100703407900450603070346074284011103803107141c060f00240382840190050324180d0025504031042000150404612003d4005150f22540c011112644a00c41609d1000c2c2c01c01500101c0040c1100d41c0310b040201a2201038880035000545481560380b202210000812409241c01600c1c3c8141207070344904103450540d40c0e689071100709454501c504501050220310a4041e04c040e03a502620180b0309519100102001c5d4204960010351303036078003031074031240301c24400050092000a07a4880c1c0c12540740440d20202c982103007800310208581002042102500011406800d03403141c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 724976393 1250 724975143 724975159
    0x6060f1809030219030e100518100302041a07020f04050907120f0c1701060e160c0203010207170d05070503070c0b06010314130b060603041a0903120406090308150906 73
    0x1500e0102c0c209078040d505101d44c034004002e0744c01030580c05030f2503c08034101540d210041d001c01c181e00b61a240220f440300e00105595448c86500d40c24101c950b00c824100340d090250a0a03147d1a00c01e079404051851200e0600c0045800800c3d440c0c0103104c1213101c901900d0410032170903c3d0104540710a84c2e405071a4008400d203018604009110354154401030300300c000109195101e40322815012410810f070b04440d07080c40404202d480d4007048250040d10100c01d4208403422107101514208030109013668155400e0295401044071740e02c20180c00d100c0800490341e59410020782c48116180074220354200601403041103042500510b18504032500010030301080d588040040300544401820305280041079000d00000541a541d1101010b2103000004001c0d500e500501400e80400c4078050070480e05050100c0001c181990a0b075000884d00c01920700d48007105c4002d6581c02026201200c00301e0b40c0c0c21404087c143e0040d40c40360840301c2ca0704060b0450f1000380c0001d81e810000b8124521030642 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 724977643 1250 724976393 724976411
    0x1150e0106140c0114010608181906090c170f030c030304020609060c2b0c0c120302070e04110f010c021509121501170d12023406060f18 60
    0x2e0026102c19041240007480410380c90720440205a01c00c0c13140701f01182c900004101c00b0f0b03110445501e108901c0c10000c1c48102c0074004802c000ca5000d03e01524490b50b103070403410109803510802d8018100c1c00c0380170ba00140180309114070303080c24034042c05810b41080c8070001494801204036074020390101d80882e29509854005001e911900c900e008240c40750400203401280c8855418090049415144d80300c1c82c1010760540d490800346800070f007d1021040140090443e4020032580340d4001e1048030038868540c00c6c0401c070564262419160100030984900c0c40b807402c400840c24242003882c0c041c05d60103a130b038046443c0c204140c4008109100101d40d80c0d001d520307a40c4030210150020000c0b0364102c41000c4e038241c0074080a010b07501c2d405100e4600038120590000700c014007900a555000e0021442800c0c43e0029000504088002c00e0380f050619a0706009450040e80d0600e80035091444411618050048410b203501001200341a240304221000c41e0b041c040088030380103140070816040b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 724978893 1250 724977643 724977677
    0x80a09030e0405190b2707020c031504020a0605121803130b09102a061b03050708071d0402030901020f160c091e1508030c010e01150e0106 61
    0x100701a0035003183c940350401400310400641e0101c2441c0441c002c000d241500014000140601c4e001040d00760b00d0b00b01d1440c1c900400700344542d40200c991040c0c07403030380e080000020308181c46079000c4c0710381d59a0007041c0010351030f0110348417005002e01d050140c138100d0090429481510010305606418a000c0700100d490b01d021300454410301030103140030b9099600c44890700c8150b0040100700d8000c000300900c0c00000750003200300c40311303c8889200a1800d140008001a9004100c0d4012a400c9071915603400d440382c401490394220310099100440d5038135100c6001000760360010446010001c2400b9040544d905495002004a134147c6002d43da903503480e81c00c580688600d08203601041c20015030b040c1211050100002074621400c0700c03c11050781e0f140b0302810341d01e40030f040a28a1050010600e03464060340e00290300c0ca00300008801d40e10b60f5036105182107401c21801031210303035100c1941201d424000c1c4107003806c5101582e200b041d407500b0400106a90b03c0c0501a11050005092100c40c3c107030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 724980143 1250 724978893 724978907
    0x60b070b09192a09020705010b041418030403020913030e040b060307030e01020f0c1e210d090b040516120f0602031003050118022b06200301032a0303080a0903 70
    0x3802c3c4014002142c1d9101da0321030003540400e030241c0d0301e94606082d0b000a450f160107488054001000030f40c8090316a841c41d1800c801580c480405544010840000140ca13150901845800031010101d1048000e05010300040c4d0001c210f01d00c82d520b010914801a40d41d031040c3e0303800000900d00000e007203607030075100c6009200d03a0240e10140d1101051001ea504c0000403012024540c150405442000701c4000c00c1c1d450303110741341c403400d04101500021002001d11002d8405a2812400480c04c0c40150b00c950000c00c0003540d041d549508220320000c0b05c02c0d107540164009003052000c604000d81d254842241181300c240008141503000001314a0340e501038040300c0059038011008000784410160321603a0188044402ca0042d804c10601c03012000e00141c0059440a0309440c2c3c03406e10009503103e8001b00a0300f85c4004030301c002d403440c81703281904007006103010310b00c07030b1000840001c10500356041c2101c060100890081c1010001c2c8002603108a1264101d000080d01241c01d45652800b95011 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 724981393 1250 724980143 724980203
    0x4110105041208070c0e0106120f020d15052715030c0a0e1905010513240807170105040320030714031b121813060b070b0919 55
    0x1002d04091640e040c000c14078014403140c0d1040401c842c419541e030310301c081000c50902c106004540c1005000300300e86019004000b49038010742c001807030b16010344982d104403400b8808400c81e0010f4414284500d00301036100c00c0041d040d0889040500301d95004802010030000c0c00300d40c0b0320782044607030850340c0c6081002c003200481c0142200003454840900210240c0b040700c04042d01800d404907160802028401c007410307a54040c000b141428039050801d8040c0602d042000900242c0c81c04050075050740000120150026101800031103142c64000c482850249440c480141d1403d818000040d8210302e211140800360420249184001291a0f0440c0585003000d400c401d200a04100541c10200c0240140485024804428402d10700c001c1d9550850b00e502c107802160410446070103601d4544510201a002411003080c0754400700381c0d0095583c6a803014004810100d1a00c2c200240310315030a0340401000700030300c080a8040c410000c181c40c6014041d2021200111500301918000c450fa015 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 724982643 1250 724981393 724981409
    0xa050f130f1803090f03020f060723030a0e10050301150923031e060106030b0622150819051e010f170a0506011e15020606010905030c090411010504 65
    0x2002c56050240520201400411000110701c9030001c20200021000b00094a0300035240032903c00c000801c3c05050341c4410320503604203020381040c8107050104060020184007150186486840e1803801030042c0e015811414070a40d0f0704803420260035809170543c1e044584640030300f9004800c0d20700680c0e005031141c01c07440b1441c045080260350b00038203601d070101003072096044505c00100069194503031542c0940030251508000010880300d0b2107034220111b00e090042c5030500d0b02610b210b003002c0c140e489030400c86c00c0d00c1c1e100300304011007200902600812151801c050001d85031880b00480203840240d445200c103655013001c6141c400c3c141d11500001c21a810810010356151842d0002121581c0305280c140e810352500c0314030366a40840c4c800038444d404402000c0a90034035851210502d072010102e4800e905d08940050709103000441c1c0b0744030343c1e140e0b005480d0500f44980018050500c1e60841d038080e074400c0e04040955240e140405a1160b000035100f44d006c04802d004031485c3c810780d444582 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 724983893 1250 724982643 724982651
    0x1b0c03030316090e0109091a070206180c06191b05210f1c0501081f1a09070f02060610050a140c1515030a0c03030804020d080a0305060f0a050f130f 65
    0x1b07020f0459500c8101c000340100ca036504903641050310740d015280100c9030706005030401070105d04162005c106103103c0404d14001d0b500684c00400100e000c42c1c110300301c1e241074440000c00f041001d070740210503013400711241d8100304c08a030b105445132a56900110034440705800c1c00c4ea00c40088401c214103507210b0200c4044d40643c0ca52850983c0d082490030010443d0100f4540b50000581c1c842c00500c902400000490345400c200f510702d2544020251101801ca030030381d180c241210a59a07240b1443e00c1a10640ca0b0f280002e80c490100030f141902c000c000b5802120f00341d440c0420690040c06564050360503140041d00c000ba41443c1302d840f4020a05c00079907134400c2c00003906c80654140c05042c410709852038000e1700110034900301076840054440203004545504418004644a40340a0354004e001030000700084000d43e4a8904690046903858006a0b440080c000d0038642040410120217080751190758a07801d20340000c054842040d2054880c000604403a0004407083d0082d09500d80701150400c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 724985143 1250 724983893 724983899
    0xf140301031406010501210209120d05190e011d0102011506022103061516120e01080f01080c10030b10030501030201201f150b1b0c03030316090e01 65
    0x10b91509502d07058626010740c030008a4194400ca400958564840e00030000440707215551000a50107560080c5e00f000400180014089041000010412180c0d0300d0554529540c2a101c01c14100c1145410800503805030080c03c0d43c0e44813004040300c4500d6604507032131420f5000140d0042003600c02d4042c0060140b1000034080d40c01141820440e0340b200d04440307802c4004159001c0a1000700e601d20b912040345522a8002c0002c4000b404800b0308150f9038207800790154507040c0280c20f08501650005100110800155030301c054281d8001c03905d83c1601209505000825071074162410f075050044504040a0b0360300c9200e40c101c0503003800003070f008040801c4080360081c0580300c2400300b07034042590ba2082001150800402e0b0b801c80000c80007600044883c64201c007100d424041c11010301a844034201802c0d00742141030701c4020041340c0c51455884406c050003e5280f0103121407807882c1c4c1c02003100e800d400d0b217010040382c0d0f0241d5070001aa12007040039600303440c00700d05a0898028480040004 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 724986393 1250 724985143 724985153
    0x1060c12270f060e1516080f0414040e03190e030c0405010e060108010f06090608070c05011503020918120f04080615030c040c050a0c020f04020c01050a1503030f0f14030103 76
    0xd9083e104680c0c0c079190820b03c0e91060001124407400701c424000010001802204e05905d55400320500c520700b00da10300f1401103041c960b00c0c1c109402a121380039038815411228070b0107225401400e50104099410300d0352082190300d807600110070003810b102620390f054015543c140184518044018000c00403543c461785200c01c0c1d618111411408981040c00115900c203160926104643c16070b6104201c00e030a1101c02c0b50000c42c040d210783d040c041000b00c01400540280075101400d003500819070b42141c910300410110040103007100440c04040c9072510921a4085030000c816040120000d0707844c260b03009030b04210321541e4444c11107401124207101001e407600e500c0c40062482101101c0c81c00701004200000c49483d580a04c0109208020600100d40540c912704405d03800107080685a892841c085020790784803078a0000d05035540d40c1001540c1105204000c4030844060b078403002d16045a402904041d0311041020034001c0e0721000800c0b1501c1400c141a500798001e010580340c3d43d4915007 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 724987643 1250 724986393 724986419
    0x71205070e19051503090a141e0a020f011b0303180b01082401140f0d06020c1e0c03071a1e0403051c020303070c020f06070309080601060c1227 63
    0x3500d106400c00f8035020310131070216003902d010b04503030070151401c09580d03036440400001d020308c42c4900b802111000b02c6010444210150340c0703440c1c807002d404016814070401135040801c118050620410b01000c400c04158036011400280c2d0500300040e41c2ea0a503400515060b13003040f40104807002c00340004c6072401022542100c0c41140701c090040f00d80c0d070f203a1880603a8001b4060102c1c02c1003062558441d03894610840b400300307080070345132240c00356882e152802642c2c401e100b0100158400200446001100c0000400c24070150000d841801c0310200040d80f95000c503c0b41e84204105140308102d0450340204a41100c81201c03007003901ca0f280c0d42c0050106401c18442501d290158104049640d400009002102d99243c4e01440c6075076103044003034418154a9900b80e07045055201450402c2d1210002001c00a000361a1062050300d401030151a00300c050304a5010020340b07120310000641d10a104449252060030404062403020039030300e01082c941401c0404001c26100001005551040 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 724988893 1250 724987643 724987649
    0x90f09020c161401110d080a0b0d0b0705030106021603201201050403021b1009211506091d0703020d110d0b0a0f0908070209070504080706020f0114071205070e19 71
    0x81d04081a280e158000e919640d01000e010046081000041d40908c510341c401c141d03440c402480031581500e21780b0340120700b950071120314000c00c00020040c040150100844841c001c1e10204030450142035594050103c6d03c02000c01c0000350a1842009060742e07421040c13846007240500030480c5142608000f0340d190806520440c1e400903580012402e03040c842e0341041a820b940d02c844041030724241c100c401100c40c00c02c1451050000258030800159442e0300080e0364210100089850780c1000e41c001708842c3c900d0306481509020310240c1e03403440c2d00411b40204403501290484a440000d0400f40030700103490724025403120b00a40707000100542e500105014120000c020803003010040c01e00c00031901e950030050500300003442034030010316100100b00c0e8480481c0c500305041a07034800300c040c501001d41e0010409600f0003110703440c41400912030852407841c0508040c400e42020a009000f0b52100c0160144490315140000c50310390040004119201c1c0180510100c0c3c050940100c0151007140 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 724990143 1250 724988893 724988897
    0x80705071a0f27030a03120605120606090712090b01030c120507061119151b02070b0d1805240c030411010309170405041407270f0909050d090f09020c161401 69
    0x810300341403180740100d40382c400ac4010409512a801007205c1000c004040101700540c0c000e80179074070700f45400b42d418150f208000380186941903190446a84000e9001011034100e040d8040300850000034040c41101d44030f08020010605058000c1e007000310015400d00c48805907030b17008007044030401c1503984240d181c102c100401c00b00c00c0030003408001510440340040e400301105006092140c8010000ba109101d40060540203821690407164010041559250010128000b00300c07000200b402540d103601104811501d0300d144c400401d40006040501020f00070341521031703940d0180e40000b01042d04142c41480704c3c04d48181200c01a07200d40595070040d4141a0145001c5401000740c0d030040d161610344019000340030031040c2c0411158110307136101c1c0c41110070010700ca403110410f200103000d0603540400c001ca42401c0041c03400d2100b0303000303500b000400d00081002c0b810880e035060588a0242000d030b41c4140c00707034035140380c20180031031864086840b034400500561941000812a202a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 724991393 1250 724990143 724990151
    0x150908060117160f1a04080a0b1902120c0304080c0f1c02030301030c050d05100c08180f07061206051203040503010606081506030c07080705071a0f27030a0312 70
    0x10303003201d80301c82e640300754224010020f0303041c017091211645d1809500d00850030603003081d80d0b03107100d82e1a0500a003000d580303c2c00300c001404030565a10003802d40601d00d400c010b46c03810750203a074414a540700c000d050441c40390b0040041000c100320791003180c0300301b0414001c95050f000e003484803a440c4c440840d55103440302248044000d90a0001c002e8904070f03900001a4107034640340609012041e0010602250103001c0c3d1181e4600c1c11940b48101404080d5035a40d5030b070365141c4a64032403410714201e8142e2205900aa501035440d100004d243c0c0d06644481ca002400c4d00350b000c20204c0903000940140d940031005007441c0080000c000040d00440c0c0b800c170020300c0a16070360b401c255400e0400741d40701980a08071840300e1240e41804c000864018980c112060f1810301320761101d400d950014441110300f508405400c0041c550505907001b0500600d01155161402c0090a515507100c1c0541001008802c0c03850881d0060210b02c160f100d504016051b10010903940c07a00400103040144202072192030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 724992643 1250 724991393 724991413
    0xf020d1101120e060c03040c170c0f2d060c0d08040c06140409090f0209070e03010c03060b07020103091109190513030509010507051f0905071d01150908060117 70
    0xb443c010a94071001030400b0f0f01003503e0300c0003000010307440140f094480703000245001802010f6000c08034901c07291300307010f80030700041c1c0780800c01e82c140700d100c04c039200b80c2c0e403a41d4a1071100c84001c0d6503810003a031b0003c1411021022400310f41c150040c01400d2900c3d00415404200d02da0300120154070480c8034071b44044245445090640d1040c00e951511418280240014401745903903921a0014034010701020031060840d500080c215401101c41000044d400904400242030034012070712056114201840540e05041c441031701c0c1d01400c04085d04141d10703031070b018080c054a881c4112828002800c2484c0c1850300c454070180c21000785254151440c80d040004480c0000c80c40c8040707050758103940b0540f415080400440c1d0503002a4070a6400740910900100303c0e540b2400054405803910401081c060f4503420094248070480c2c1c03240000c000000d0795504d6080c0f14801c014156a42c0c03080d000420018500d0850310045150880d41e164451384001043d0080700c080052031400c0310030110340f1240d103 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 724993893 1250 724992643 724992677
    0x902040b0406080c0a09030b090f03190e040902030309060912010c03020304120315030b070e1002070510051206040e0f010e0a0618120f052b0b0a0b04120f020d1101 72
    0x705c1c1c05003210005181c08020710008d4400c0c9656030700300c0280422552542030a02800d800c43e40f156118403020340b9000610700401e81c00110600011100310ba0030003c64509402003900c9119540415100d40b40c00100c14401e0340e41c1c4500c01041c400800006c21241d018018050003c0d402903c3c01d442c4104e0b0110309500451281c015038410002240502c804285503a507005107801c0f002d01b20909202d203030482c04680351174401c905102d01c04180d00401ca03030341c9010207101d8200c0740b001713246040000030001c5266881840d00a2070300600c064a0025003007101c603447c6230410342610743c83c0740303e0350070b2100d401c3d01443c3c002666140c080c0109002c00100403210240380b05204400402081c0301d0502981d84082d81c024206100c6448803410003d140402401c0054000c400e03000c80884581c080314403210303245200b8480c114524805a03443c641007424440d8002090140d80300345000c00d51202010400c000030015002c5003546e01a080154403402880c003001c05517195030003180014030b02c101c3e00075046 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 724995143 1250 724993893 724993897
    0xc10050f07090306050c04030210080a0e03120c0f07020a121b142b0b10090209150703050708030f07020f0c1806151308010506040207120507020a0902040b0406080c 72
    0x381d4140c5800401600d0359031010003818000b0300d401000b401c140b10000150310b41488000440881ea65178007400d1810412030012500e41e0f1010942c560b005011000d0305121900b1025040352050340c10340e80318901100b81104510031510020b403c1341310305100107104880000e2480c14036110756035081c0d14615413000000c880d40d40d8400c540e9034180001694142e4102600309580481c49540c01007900c5e01c509503e66050041114100d9900c5010400c001050142e030100e00007400508105600e403805001c0003441c0040d40d01d0203940e070076000041c0300701014064011070701903076440411113445e03180c6603a400701500c008541d000c0150007400320400070800e022030700402400c402460403281e10140d00001c10b460f4002803046030820035010149051104000113020002c074250960000c00d800e1144080c01d4500140056000300e006003c020006105d0800044a007042c502c3c18580301e03003c81c000108a040781e50700030700900340700150218401c1101e100410603103180381c0b0388491640300c2d0030802401c1c1c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 724996393 1250 724995143 724995151
    0xb0a090602030a09230a0605070201081803030f0a06050d0c090c0e0a1e03200109080d1d130c030e01141b0304080d1416020123100b0c10050f 62
    0x10790b095405200220301e1781c070803c02d01011030050710201400903001c2124104107402c40f070003243d0040f55080456034400416640208601c4005101e9a45580300c207a8901010b07040118940c4003d00165500100b68000c40c02050014140c0341071060908041104200600a0070503071410002c00704c500340d001308250742c60400701520004416181c81c0580c85050f4190220507009220300c903001000c0781410180d40c112005904040c07403c040c030503001414141c00f60340070a2241d00184c0d8230300302d0590800007040440c029511020700ea201d00742d0004442840c41c1801c070000615100c400c41e08039515a0041e0300c51485a0020802600107e512904c03100c0211051401009080150f5000414070b0000d950001c3c481c0074014203180c00899014191100701c030000e103034541c89008000d075041c60240d21801e1008103000030031081264283c10540d00e0340c252000c8441070220404912607c01d006e1a0000805120064a440d8a042d5010f2a124000040c4280445003006c1c041880e500550207043e0203 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 724997643 1250 724996393 724996397
    0x1009050f0412030b06030a0e0c09130f021210050106110c0d02040c031416201c02100608011b020705010f0c0f02090403020604051002030105100c060e070b0a090602030a 74
    0xaa9032155203210800c030b0301000b0300003010b40f02d03d041c0f5601e03107031034014600507440c050f804625007030f0301c1e4825450715140500b5988244a140240010b801d60840b40000300c9410213201c80c580c404034004500b40c84030b0300c5d030b840196104940001007140780766406141079524564450b04410424107440344c1e0b03007000001e950707404002410450018540381d401080355106d10709000c94401c151b00340f459080b14003261608200c000140440744d0b142c0c1d210704500300e201048600d50000c3c48800110781da841440b0380d582005899242c06110025000300054618039403e040203101031030700d64102c240a80140303000d0460144a80d0480d00200740041042802d440041c1c3d581d40207250007420440318040d4000040e03e62002490b20310000d61202c100d1030f03100c2c40c040d40061802c1d00f0039107404c600d4041100c4800d6003042c03041c40140321907640c2c05a0886120440c0c0b810b000c10420504004c4001d0540100d60031152241080000b528400c04003c3d022200f2107850307141d69542c2c0e841301a80c0f24801c02c1c45c0080 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 724998893 1250 724997643 724997671
    0x1060f020c01200f0307050706020304210218181b06190507061d06070306030510090201051b070f0b1201050103020c0c040f020409060807080a11030a120503100905 72
    0x12855100d84400e0700c01c007039240e0105183c40c43c090807040c10300c1ca0042070b841e080d420004441040c0003003001800f00801c2c07584021490685410b00c00c041185c44100e42642c070521000241c415595016001080110b40004e20300c05810140499610001403419110260168444c901103071107150b0b05070114005c0c09411140340032600120000043d00f50904a01482000d110034000300b1214411150001315004143c28022000803040e480c10340c0082407102054201030080c0005040030072031b00c000d101050b201181c264058401138409020b410022900800e962800c11072a120000b800000c4980c0314010a01c665213034030a40c40f80384a900ca800500d03100f02801040154032941c000c1c01200c41c113001b5a078241c02603034009001d03901c0c141e0341d031820150040303001d01c03594005100f030800405044d0003e1400500d0503240342d88440300106c025009007898003107007400d914207202800d06036502c14072610b41420040320103001c68005a9142400741d10030003010445014038810f017030280c03201c1401e4413 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 725000000 1107 724998893 724998913
    0x403230a0206041e0f0b0702210904050601020a030c0b041509050705041104120b0a020c0312010e06012c01050d060920270f0d0605070801060f02 64
    0x20b0142c528585132903070000b2807004054030101d602420102c56a540d0300c1c0c0590074004c42e5181c90b559090248008100d24810400400c070300002150101b2043d00c2c1e10004a0380e6a481d0310006000c5801d61000380c2c081147c0b241c0e040e0340030703214200d0079694840d24000442075510116040b00d00380d00c00801800640340c18002c40c0041100f0a01d1507080902e810016248000c10000c00f6244500c4040410420055601140d0b1060200c0040700d65820340c0c29403400c1d84040034402c1c13184401d1070b01d0119101d584950006010082c0f550f28071842011280d402105054010000c01c0c140b190401c08400c0b002090301680004100d10000041c03c80048030310b2618041080c4c0022801c4030040180310402d6011402c084089004580c1044000c0d0b405004604604000d81540b9800103486002804200c0a50401c1e071041d280b958807410603903683c00045d15032039068400800540c01212001c = true := by decide +kernel

theorem cover : BRFrame.Cov 724820143 725000000 := by
  have h0 := BRFrame.cov_init 724820143
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724820143 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 724820143 ≤ n) (h2 : n < 725000000) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
