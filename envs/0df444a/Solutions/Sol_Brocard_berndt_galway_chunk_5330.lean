-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5330
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:30:48.699197+00:00
-- url     : https://prove2.me/submissions/b4b7ecf9-3bcf-4cc6-97f1-b6b53e3afc0d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 958453237 ≤ n < 958633093 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 958454487 1250 958453237 958453259
    0x507060b0603090703230f07150509180718062105010b041502160306270206031b09090c03042d060c021f200702100302090d050a0c 58
    0x5411140035140400c1002241000442e4200691394040400500780d0709071707000d0380700d403840d04e0780036800c54803d6101410003000005010f6003103c401402c160381c0e40307000603012642b034050003050381d4100025503142900940706600c0f2950018035458045212080c08903080d50344000b9900c50381c0410a00c001710303215180765820141661f0403445050100d9454002040c90300d100e40d200e582c13501613101400c0003845109101403404200b40101c0101c46917141d040000c014214485140c410b283e1000d00c40802c2452242408022500100017504564448260084048200454240c1c11004214480c090759403000e0f49030090941d401d482c3d841e85403d280803403548250009040704c600c5a1a41a0400641caa0701d03442d078103a000401207110408401c09920b000f048034168074502c50800641c841c016030f550300000e0b40f080200c40d02e060984030b0411540c0c2c1032146000194003c0b14070800912941d009400400c2000005000c4194004d0079071681420283d000200311548003244c0c5080018030140 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 958455737 1250 958454487 958454501
    0x1f090203190b0901031403120103060219030b01021f0b030307050d0807110604110103020f0316030b01091a030411060a0e1003050c09120304050a080705040f0b221b050706 75
    0x76881041036401010003c1c1c181003051100501d2504030084814219100f401074030441e942d05088101656101d00d0b00a02a4212550350109a5500040022407078880c2c050040301c0035068014100740040c20700c0d280110041d41410305c014a444005414880e10204000e20070309006601800c54034009040c001c02c0504090000010880240c006100c0306001203100b5810a03480385850158038031040050780a80903030f2503140c0d4145c1c1c003c000c02c01110b803600c10f4a6410256550200140c3c0c1c00000151103555441c0a00d03c0c1e400c505c0c0c40e1581284410800554205008034001081540911300040b46a848046c0c4c030000520015510261410031005a21100a25003803d108d540b82806040d03096009050b42c00b0300c103940c3d5a6512000316014800ca401400001e004894031a48804039142d80b40042d1055074001d80c9003044420b038503d6184203880c0c100c140244020380c4100040d14803060882d903c0550400180c1e41d4a29125016010f02d0303c0070420800d445e030584900107405c107a4111420 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 958456987 1250 958455737 958455781
    0x306010605090907050703030908031608091c0c0c08010603050a06050108030301030b1518013305040302012601090e0f010e030d0c0207030803010e0f01060914091f090203 75
    0x24000303024940e0f607405016034003044901e4020b480e9419410100e000c2d10040c2e201404949000040c031006038401861080b46240c907032160f40f4192246001d00707503242035900c0d20034041144208503030f000d544a103081d145854050450515100d8885103024210341407640102ca250303110000e050b04100d06030164500400c080c40195003103614507214504030450003000b80d03410340755078442a18181d0750021401041c88501540c00c1041da1500c5003c001050000326a4000c110420301c00246044000d400c000710a00c681d031101d0605241d0750065619400c0b11895285000c0b00170900100104e495514038020103200c64003089071382ca80360f40f15040940ca000000182d90412042c00054907001080ba60441c2e094080000d03044c003c1351040b42000315039040180725510000000070b0106603140321501420442c00080c0050b40d941c902a81d101c80756114031100050907219074400e518141c4020360b8003801d01d000d142e00c0f9020780b011390440030b15a0b41004544070307400f10500c01c1d215125440a014250 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 958458237 1250 958456987 958456997
    0x4080115090218011b060501181a030d1404030605160f2c04110f0d060509010e0c070606080307030f09210204050705120411030c060f070b0907050d1103060106 70
    0x1c42c402c95092110342a12000e06011014140c18000141e041c090360171181c02c00c0c800c0205585942400881d003140307400111525050000d000e01b1403001480b1405100d800900418001c800c10b501a9520f0149140b91a81408284000400b04146020342c6102c3c00d000c4074040444121244080c054521040701101040f542c1e000c1c00850b41e200751094000c081d00c00f401c03102c482070f4100004000e07018132080221038900100381e41151041c0c10b400b80c08000d0360f5040900965440f0000c0c052494024490800c491a600d004145644103000c0203046460098401050b4280c8a20905142d54408174040300010884070051104030342c0311503050007405034050300d002c40711a4180c0d20b9030b0303821051802074403582d980c001041001d8014404c64a00c100c1c2080c4044141c58141090788110103210030185c040e001340d52042003280b40680444d40d8140c1030070b031010704290440d294100c0c80030000f0107640540c4101c6402040703669a42200e4810300e442010500c03501402101410308010041e80042d081c02 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 958459487 1250 958458237 958458247
    0x308010f03150b0f061c060e060d0f03120e150c0306210a0c0b03160806060706020702010e150408070807030302030a0f0507060212060423071404050303040801150902 73
    0x1d19051003000c0910382190000c104402c3d01000613041480d400811a440b101c00070b184106008001c03070024071400c03003040c10807401d070740e5819107504c82008a071015808007030245032200086180241c050014083d103021a0900307022110f030021200e444440d00d401e58041c407002c2031100100c82620760301ca80914659802d500701000443c4a000c0803844046001c0030034a4820002e960402c030011070160040c10150b00b10307130345401d510a150b2054840140190700782d6603515540d03004202c1c2074040d1002620702c600e4001c00d51640002074000c41800c80c100b10442011141c156128040d411040c03034458140f9554a1401c44810318010140e4000c5000c0e801124042011135000f20607120354008908055000598030442102c05115a180040c886403022604411902c0e441c00807512030341c4166400c201041072100e0204a004003419440384c0c2034400e60010720158450740805c3c0310801c100c4001c5080c182ca83c40041c0c2103030081e03086900542c0d95010700025100c0c1040b400310003000c2c0840214030301 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 958460737 1250 958459487 958459493
    0x1a01021c210f050403090e01050d0f05010e0f06240d020402030c041a0a080c0315040e0a0519020f010903051209130903080609070923040908030f040308010f03 70
    0x100844104503040c02504032001000c1d00301c440309141420007115040111540c0500441c0050a0a030f40c1a4000f40e000100451003181242699060300c01c01000401c841010b69959054072035006011161075488102c070340c45080301000b992800b050620003400841c5000902c1410400c041151010015006000d10640751154043c0c03d41140c0c060b100542e4070794070b4880800c03107841142e202d0318035200c0c042071b5140070b070741906c1c09462005402d64a480c0340b519030320f00c20758035800150b03061082845040d5034500c1a160940c85000780d05100000d6031088143c4c1c4c1c88540c2404925050700143d50b02d022311403000c518120b1600c01001d60242464181c5500b03544800b0307541ca0540b01e0150400d1800640b01001c0d40c0c41c1c10a051011b680f84c1010320a0300e5080c41e000b440ea440c02e448660190040c075010458a5020b2107a6506681206242030013070409144440b8612031031195140e007096a8504400128565800031441181103000c6107030b26042c10700d030040c45080141e20140004038a01e03018000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 958461987 1250 958460737 958460773
    0x902010c02120a0506090706170f071d030d03050a0e01051611070e04031710140607020a0f0f0303080a02120114032518090c120813091a0102 62
    0x40c1c0564114040c59402c6948620b007101030034019029200f5042080764090780011004181c940655401003448541c032200c01c1001006e40e4494840c405800000b03000c548100d00320391540004484140302071418801017408e0810000003140082c4d29481040312025041c0124101709000c02d0003084103141007000840080c8404451408000c500b00a080a4481c2000650043c19021216015504242c46c0c090000301c20010a0780c140f244460004035540070340d44401007150203003401c880d24020300008000e41644558800c03640070f03080c0f00c0041600486110048043c10030502c802c41e5003415400e025014140c0100440f220764010000300507107407011102541100d0445034035170000300c03182000070300f4200c0c80e0428188003030b821100161034035001c2c5030b00c40466143c045220303000c0810000100940f501036001810144441d201086914000d40980001500440b80c880c10941224030300c0440c42915403000114a882d2499001c2d0100440101500c1c41024001811000701d05009012 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 958463237 1250 958461987 958462007
    0x1020a0e06122707120312140105061e0304060b090112020a0b070317070504090c080103050616020a17090a0b27180f040c0512070b160f1101080901090201 68
    0x8444600320030f405407030001d03101a20390350070301140c00d03900c41070b03112004c11290303440854054000420b1500344500039007044c401c04102c5041030003000310980c01d000a0010951111020031807004c80007000d2241500310801860055204010100304141c43d141048649030041e0085280c0000000c04200140d0b43c01c0700c1d41044a00a030303103c580780c0c002400c05483c1c011600072a001c04103100000c000300c1c503502c00d000304282c468411302007200038103031032040320640030902006149906c05000703c3d1440d40312140200000b0458411502410030f01c0c0d0361840306100050554103c60808195003a00e4a00084000c01400e5600c85540c01e201025140c6042c006030751604103102c41050000200030b07200c1c2180a10b01c0550104041168103104103d08035024003210140d60142c90319401040a180c80250409801d810000500f01701d8284400220654448010441084450a0880b00140c1c5d1130030794035091801100e06200204180d000540f045500078410100742e4589000d0f00e00503078011008032 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 958464487 1250 958463237 958463251
    0x40e0d051e0409020d060e07030b06090f12030d0f181208062403040203061f140d06090501051b21040f0f05031e090a03020108091c0201020a0e0612 65
    0x25015210244000d00a80b00d5908803d02250002600044082690704151b08a80640c14241c5003a40c4821040782140c8400c01d1481e40098100403510080c44d000c4640b20345a0301c020a8031003c44a070041e120702e0750b40500000302e45162140c0c1071581144152041144082881d031220903258126a01d4001c2030380391a41100900c21000c0c04038459440719020702d6601d03201c0e0729014440c0d800110018455401c1101c0480c400c0c450000018540454204c9103c010040e0f5484450050304081a0803506142d070950300342c124805404031000b0601a008903241203005600001c5c00341056002203504480c004801c1c03000e11010001c088803200321998940304114000003084490f102c41c5414202d000c115100a400400030004420a00c0000301c0240f00c0c28800000710660841c2c0c5612403481401a4880d840e0b000d0300322081003000d94021450b00e43e00a0031a0b0076504e284c020905001c40c04017a11f150000181e5022034904074851f00b01031000c941c444201c2e06a800c08201040f115440c0038024049 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 958465737 1250 958464487 958464517
    0x7150f081603051b03150f0307050607020607030c0602071a0f0903040b0d110c160f030f02041a0d120e030714010e0d080d0f0605090601090b0a020a050a0b010302040e0d05 75
    0x258880c503101101d000c01400d4800013603668101120800c00360b40e46a4000381c4501a2110958460b14002880d1002c69401401807030406241e9020080e05030400701003a414811030b6440c1078005010f61004201031841140c0d0a208443c107100c000d604814000d0030340318801c01e04e070288070348114008241c0b01158921402c1594400d00d205021000e08070300c60314a00c6400c0049001c03e144200410f10628500c0440f00c0011540c2da0b41031a203100107950312001c2d0051004141c580c0c09410079404c1214203503000d08420384c142913030002142c48114002011303240c5145800098150303503070140c488201d44408500800c1c129040c0090450940d07500c180c0e1070305001881d80700c0300140d00d4801400c01142c1d0000045500c44ca0484c88400151500030500039030713203103002c0002c281440c180c00c0c00d034004c10043e50b80038401c81c01c022108900740d0094207868194440d800e12040090002c0141c2c10055105003906442d80d45144180020b4a2070075080303003c6a00b0503c200d2000315408030036a056240c0200f12 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 958466987 1250 958465737 958465741
    0x102060a05101a0403060b03120d0b04020f16030206070309030e270420150711040b10021005090304061d0d0803090c030d140f1b07150f08160305 64
    0x80c2c541d4010040c0d010f5841010515010740103900590003804c1140d0050500384880c0d80c4a80030035840f00c1c40322001d400b0010060100c040705510079880b50304d540e140a0001468042c03001400000d5400450300861080031691591040503414050260024410f04080c0700424440d64003400995924807145d00403604071302e40742455241031841445007040203e0b40c105604040c00d0001035201401842c00ea085c0c0340b141410b5440c20000c240b40c414010179100c1d14144807040d42c030b91442850302c6003500d6100361104c440070742a075241112900000c0c0c0a400a00c250f005600b40c01043c0d410061a004641d00b00348010450307280c0091a1000c0718130103900210222101c50b001401e0b15481c000040c042c00004030030024540700c00a2460440c90003181100e405c449a9002205c07881104100405903c5040c041d12106145140c09840340850281118100303400b0100c2080c50031080b0344c8401500e5541c0b08940340304a0b0840150003900c0741c10725283c0454074001d890110202841100c2908040d9a000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 958468237 1250 958466987 958467001
    0x30b0604120f02180f01060e060706020a1202210a06081905030c010906050402030c0910171213030b13080306121c2001050906010311060c07091a0603060102060a05 72
    0x1030241100c1d58000c1404000d11030944c5a201199403c42d0035120801d400c4c0004105503010301859101504020090307032605881da070301da170060b40000410300140010800190030340e80c16400600300000d29901d524103404480910b2101ca54000352100201a1510130288a03100010403143ca0b820420030f41941100718600d4010301d103210320303440083c0c00e5180c45001d03c1080382d85c0c2c0145001d00d008504540d075181441c403c0003c941401d846440c00410342540c2044100b000c41c00200040003d00190360138030b424040420706030f1b407050303280d01090303403010609200f00303d0102d003031039080f019403251102c2c0407060b581c80d620310380720180259204614041214002c814200035480c3d02c81e42030540c1800100c0c1d1400041e014840f01055088802103140100688800c14410148103429140080005929545501c20f03001030440315143c00c080f0800c16440044400c01c81e4900034440c0f00c2e00001c0c01e400014620902c004030300c10407403140d50100305000d440d84e0f0000d181c2c1d40041c004a8000f9150311566 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 958469487 1250 958468237 958468253
    0x12301090b070c0924090c02032107022404080f07151409010b150a0507170403061505010c0b060a1a0903060a06050307173a030b060412 60
    0x41c0c0a8040c4040008802040005501c00d0700e0413541541014403600505101a04991246200d540081441600c003000051880e4001d84049484c600541c0d00c3d0294210b0411441d500341d0000c07284607030004041c0238083d6810801020110703528141581c02c14500402c4c15905000980003400303036540499010b906101c00c008072084207030b101c8c203000d00401d905861072014010800881381420001800650004010301648031a020001e020344514500e082d01391882d5000f1300c0c0240300b00503060091100003001c5c40424610700010f58820f50f1a07625518029003074520f16440d000c1e485581060070040d51344c120141c030050741e610001030304843c0d446001103170100490340e03c44101da0041030f4420720040303c0c1d840141341c40e210640548605030342c0da551000a940c998071800c1d0700751344a03180400c080304415411012001050382590207520310300a07646144440700c03440c00c3c1c0500004404501001a1f01d8942c0d4841c9603034201401100c0c125400074810780038070300c1600c0c0407683c08070522003000511 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 958470737 1250 958469487 958469489
    0x6010e07180626160c06020d05101406041401050a0c050d09030c0806010308070b090307060c0806130507050301090b0604090204260304030b13030201200a0e010801230109 75
    0x10300d030540c020035030b5031100500b0107040c0d0380f000c501143c54850203a40d036842105454818a5508800218080410421a1301d81c2c283c840a8448950900851482000340d008032406140010b03031095240b820852115080710381d011905114080400080061021741c100d40745080d902400e00c03585504119000340c442032a03449005003213024011005507181c5d00308004e5410340340108403410b407040e150140655918001c0c000039212210500006002981c220481507205855000340c0e0301f00415681c3d44000c3c1c0304c0c1d034074051700071038014002c1180c58200080c1204c50b4407041d003004d000e54140010007034a14807040c0a0407000c5030303e41c0c0344419035072140d0040f100140381c1900d086540b5a40e1344008c50380e0f9540d540c4e101070401c94030080f00b00c6940001017503606072508126107440b552110bd010603000c0c40c507050124155501c9183c190103010303039113107158010090b401c00c89a980482580091105003400443e60600c00745100603c8105205044049003840c0d8003441c6415031a8800161100303151 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 958471987 1250 958470737 958470767
    0x1d0609060120070306200c1513120e1c020f090c0c0712021807050a1d06160309050d0b01180e07080c09061c020d060e0d0503061203070506010e07 64
    0xc8442c000204a02035000c2c0100300c044050540d0f40da00c1800e58280d051181c044181c985034007005580c0008c1106a56032a002581d1400704407081103681d9074444880b41c61845803001c0340d401441899241807401c00002120034150781c004101e2516400501c070550050201401000110300042030455030350210f40903c849001250582ca50302c2140300c103000e600c401c04a001e40210f1840322030480c2c08560080c0502c0c0d0035251701c0d061052410302200c20b00300c0e040f00c0d4000030b0a4100b81c2e14003030703c801d8001c2a140084404804441c0d0107410064000c1180b503000310700800e82c440c10f210114a807015a0743c15507600448464401c021076a100340504813203941c0e010b55006045000400b0345000400c3c060000701600c00907141c1e55040304200741c80550704420440d005e500d0402e0001071038191645010244601d00005280c84403035141403600ba60150300e00c01041d000400e01c40c051601d01d0011135048060002507240299581e5103a8803000c1c1881144128488240400c250782d002d00444641400 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 958473237 1250 958471987 958471993
    0x3041a19060e150d1e081306081b031005060708130b03180102030601140a020a0c0f0306060f03030c351801021c12020708030a061d0609060120 63
    0x901d950341e0921215094a16560380043d20003010614200304114901103030b004005025030401c00c00b51001100e03135002c42204e40d00b000300242c6007801440310b0004064500c641d2100141e10b000003103203090400c02801a2680a0b0a2080010500300014a03c050702c01c1a0707401502d440d001d00d040403580c02006020300c51054918400308004100e8405144642c00c05005078596041e501800c90807840306440d03c40c001480001d0221003103958100900c40700d0342510454412440c961186980501990411074407014001410070510005009801c040d081c06000120014a140e8000c0e20a01c0c00043c000c2c80f400401854110801c00b15614039044880c81c04c000011240b68100c444a03503020818610203501010303850307089548005001910042d1a8240c0038100d440a0029102e0b08212300d158404140c01b000f00360000340b0b01a0165000301100000072403000d0401007410701346040c036150459118240d404000d040c0e505c0000340b136003000003800e00b20645605015650700c004912500e485c4184 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 958474487 1250 958473237 958473239
    0x105090f0a170d0504031a091005070302180111250b0301080604032007050144062b06060803070510060512100c09030f030509130203041a1906 63
    0x854000c84030525a1200760030360f0101404001d0a07105800345000150851007001100c404140003a111aa0410010302c104e80c00b00d12403011140507030754200e45440001c0e030041202d44901500703c0452450788400d00f000c84885500e2150a0341c1d0740803152113900e1140500d1070b0000319040f2990581e01628214900c00e60301d41e158440517544040a50741100011038240c0c0030441c030754010301c1203901e03c00d850025056141c502001102c0403c0c1480d440754420154943c0f417040b41480c0d0340000c0100380d400004095007820903c044030900c200a0455000300444502c008a01d0394010040304501110100c02c01c400401d03003001e200500c010b0304580c44600c80050003a090000028243c2c008500507181403107926112410311100d05080d9610108951100c0901c0444c0c402c541c01040303030380c0024a003401c0b015a41c1d480700600013200400503404580006501441070400b1240003441c0c044458042d80340d420903a071742c41c1c0101c032240d902c649094115008151032600f07a440861405040b16000c3c4415 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 958475737 1250 958474487 958474499
    0xc0e030d0203030f07170405011a0409021c020105090301090f051c080a092d02030708010e0a020108060411040b03010f060c020a15020114010824150d030e0414060102010e0a110105090f0a 82
    0xc0043c20250150905121008ad0040c03070140281d8020301d5006c0c0019010301c040b0708882d400d5103a1000101d06118042c0034415903a1001d01c01c5084890281100c605150344905141d41001500c0c3d030300400000000749070308011a080030720950400b656600000d0840194140080d8052040d0000000100300d84404104000a0140581210300071002c0c0c9031099595000207003220503106a944240d0052000040950b0040060356804140a0004034624200c007029405e154403035084110910341c0071005100c6424410003041c040c00081c24a050215595000148540001e100e900c141c00c1e2003800a4083c13138400e420441c03c0e40135982e80011256101c104d1640c440c4500407820042460706883c00b4a00485240030034000c410302c000c04101e1a800000b40400c040070740d032080c4e05105100c1c04904031a2250300c141d00c50310080f241e8403a05414001e0009080d101b07401540c0d000e03640b104000c8000324000040507440d141007407d0003981c0d146444042181c08242040306070340000032520004403 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 958476987 1250 958475737 958475741
    0x304062405030d0810170a0605180f010c0c06020307210b032104151e0903110906010f031a03071409010b030c0301060e010507150c0e030d0203030f0717040501 70
    0x240d0710102c0c2030700d90100c507540c0101d8071860111a003c01024958034100042610144001e01809444082d20705002c295202c1c1d4080d90300c182c480c4e450307202c0c0d84910080d00c0c800a0280301040300740e0380c1c000d004040700f0741402840007514403000391005500202242d4424061040110043d0505d24500d036120443c1c0c440e40c0081102e1841d01c0e0103400b440c00682141d00c10280310010b00e09042044a041034100401005481400c012403018401310780200e00310401c0c0207110001580d031940d0350603200e5040d407030041400b42c5019100380c01034040b04140400b0f81e0300030442e6200304425140c0080c0c1b092007078800d0409003c080302095058040c400d008900350407030f95820301a180080d51404e40c50399807150060480d120031a00d0500307c480c10b02c018005a44a00001241031034140341142c1040c6c0c041e103450400d45441c87c90080d00c1c99481e083c0c800c1290704041201c041c0740b4110003402c072008070114065120311000300301c000300680c8207001402c80790261014176144007401c07900c44041c1c6458074150340 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 958478237 1250 958476987 958476989
    0x6090c04050a18121103070c050f0103180204090507050d030305040b06091311061c0c031a0d06150803070317011203090b03040c0306020f040e0a180803040624 70
    0x202a03030409000404400d120f0007450368641100b01d00b0400791030680c403040c41e4001124005020420807a0f148400c00c1c00800280030600e0142000d0902c51b0302d03003410000d07483d016085079410715040c000758040041745100c890f5a0b25806403004a0f01070481d140403414500d160300203e5000c030f0107005030700034076034954041803040344200e0340f00380e035030302ca084c200160071a08489043c0c20031171504000300000e000307c640124260001c1c1c04c807400c003189668164035041313400e01c0d034009207540e0708200062640c3c9402032400c1c6180d45051901c4151b91b05000c00d00c00b030410000a0403107600c4407000344074944900c10303400003040c210b41581c0d282d44942c030b0010200840b14100c401a007041c1d80010070302a200b86065880d15130700d5221802c034a480c0050140e4035800090050741d04046000780000400c3d618001820860752881c07010703507980d0800003c034032070348000782054000c1480c060041d107903144420081180703207170000b41560701c90342c80e450320f407015003407031074405806100c080745944000c0d0107407407400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 958479487 1250 958478237 958478239
    0x11e0305120a11010e0c0d060b030307060f0b010905061b0309030313050939070f03020705040c05120408090316060f170411040c05090a1d0906090604111206090c 71
    0xc0f003080700e0710045070309850b103094900c1040d800c1024903001c9450101c40d07a8035100c0c414040481c01e02a1007001034116040f85006940268480c3e8080280000030700c2600307500340c000d003001c1508900340070100d000c501034080c01d44a5000150001548103201b001901c03070b140030013400c80e6034404642040c1300c10108144034150044c03801002154410808420a03e98003942400150300d05120b02d1602c0c8071030a22128202c9403c130100000380c0032a450342c401c920030a0298004249861400050008640084403000c00b08a0305124510030000060072241c4c2107600304601c0c3d522040c003000068105270b1096864201d00c60320b05400118940c000d140003000c1091502d8008021200340250103000741d0072140140011b8641007001401c1c035203640310b1802c210880c5020f40c100055240070885401d604d8001c00c1c10f1541141140380340c01d020107030840e07000310070201030a10741c1090090180e0b6540003600040460358507240b4803015031a0007200d40e03413000380340d000c4840a0901c200101c1d10340148014a0f = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 958480737 1250 958479487 958479497
    0xa020c0f06430806012610080115030f050c130f06050607020d06110f040308030108011a010215040812010b0d0510051005070f30030506010503011e0305120a 69
    0x10285445061000710b1103810740d482502c0e90428800d412540c42000904150501c071003c00703201c0d030741e80003504000080c1d0115981401c4d01e04011024010111007684205200d0303040000b03551f00070741450000e100316540f0450040340c00e0154a012418490306d0841240c05c0710402134400d1803106070780c110001c03d0b000d1001c00c010890302c65061100078810200040d410103404668440041c10662104910003d42085607091035030500010b039a9500c5503006645c4c107000800140410341080c40703400140d51040210005002c02800040c0d00d443c42d400700000030103840da0008090195071000c5a100d1280d00c180f400c600e6848100c4c00f10b20381c00000b0b2546a092519000415680b4420850b00681c2c4000704a01c01c102d400c50021241540b0100040702c1c4220b20403450350000e4078001c0695200d15000e040c0010300304266400d5000796001d01040c00800d81421b0612580e07903086401c40781502c0203050001e040c03d00c1e4801c8622224039950000b0030b5403146800100c000071a2a02422000c041543c0f5 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 958481987 1250 958480737 958480801
    0xc1205060303120114030a0203010f0f0b1807120f1803180b040504180501090302070305191e081207050318070f0e07021c090f0801140a020c0f06 64
    0x6060b40d0b4000e0300c581c0880d40c1031040050050300e642c1084044a40001402c80ba8041400e60219013590800161950115103d00784c0800c0010303140128840420281c4029035081c0c4000c07125200840007805130700a1044125051403860496049003240005050083c0102130404800000c0031010341010b0f40000e03010903823620690b0302c3d01c0e8120101d4150592080c101402c1c1000c0000a01c0c1c244111400821881c083d000090340070300504031801d021b5005060041d01c1e508003076080400040c95489150100003090b400900c1c03151001d142c0303007d000340b86800c040d201d02e042e004a100351460034070103888800400c42c0306580500154898264068078143c24080c04510b0f60782c426060080742a15160032406000b84901c3c03002c202d921040700c0c41200e8203032500305044240d01407030310400c10005204d01c034203016140751101e03013500606c02040200060030385081c10813080040600020070550300010030401c00c000c100320b030064001303c1c141581c2884c20800c0003c40e6080300c104007100010301005e4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 958483237 1250 958481987 958481989
    0x908010203060f0f01030f1404030305090303070225080f010b120106030c0905060105070c0602070503010b09160c03050f0a09050307090c140d0906060b030a1b12020f0408010c120506 80
    0xa072402124050001001262070004100c50080f440840e00d040555500c0215290b20b01130103082400850081440da450405007130040945400515105003540300308180650150300103040107240181804408500f00c45215251840c1c21f503501c00d0000d8460450f1051501e40190f104801900084824440c010b4640c442c2c01d09031405413001030902e0103948000c01050304640c0025903c904140b40040c5480340341e548178407012903560407100040e4000202400141024810301c0c0c04003001701c50740e144924000c88803101c9201185100401c1001d440403101c1003500450030b5a00e102c051001042e103501d4400d0009010000a2040324481e104031480000c43c00c00c02c0c801c40d48800c110360384001000b041483c0e919140c0d40301540c4104020b0342d401688001ca481032241d01e01910340c01950a40d241040c00b81c060a694052240c0c0343d8102805c2d030380301c10160300815140e03801c0f00004c00260300c40da040e4176049200c0c02540e000001e954201040c2444059122081107800e41c000c100400051311050 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 958484487 1250 958483237 958483241
    0x30f0d0e0c150a05181009090f02030f060402070221160b0a0504050d050a05060406090b091f0c05040305250801110a031e060605040f0b0f0304080318070312090801 72
    0xc90b22104940304211003840c0302e110304018010210501c8402142159035004504240c0c5210942000607460090900c007100250294441038000c3c003005509509000c0c032002120003001d00700e64452580000c114045440b800d4101100f10490358961840b5900b0381101c640300e20f00005101c0340780710b0b07004008c211200305100307546040b402a915203003000e00740018001c80b42c40441c01518603104003443d140000d041048203602c01c5d84107240100362586030340f4002060010181401e0029000320341980001c80407200c0c1c1c080050b0405001041c030400041c01500d0a21840c0c0003d030403400b07207203e000101c9490068180d2084c100c510314180e000d9507a91114200c0f0302402c07880e881628100a5181c0241c41fa4026890700c00022404035816001600404222010b980c81030010410104081001c07428081c0400c1c01010a00d41c003518020032981c2000452200500051503100d011002c01c100c04452244000c0c1c51102408656909459003481e4100304050300321040025800803000c2082a018 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 958485737 1250 958484487 958484509
    0x907080f03070314120405030417150604020d0f021305270613020c150402030f030703090915030c030302060a05070f080601031a0a030c15180e0702030f0d0e0c 70
    0xd5010354280352240e581164440d400c001349a007507400600c48084400c41e440c556078010391140d0b008503038071450a0341301154040c5241c45080399420506800b06c0151007144242e511480840700145c0d035003802401c640050402c1c154690f46c042c400704520080034903144004040ea0f5088442d0f1400d400c00c07401403841918101d001c41491890311012401d50b0034488079007680d0745102200942450043c9002521300944640e90079501e1400005000550809114100c1d04020380406103141200580707026090b60010310401505681d40c2d815403048118541c5503102442c0e0002c05c1d001007603940e007002552050243c80c0c5203d041d20b4180800c404d140221943c0a80c010907031110049903a680005400400542d1412402501050714100f125980c502044024601c070300c2c50b000240d03041c080301c5802c9038108001101440300022a14807070310ae030640030364100d895094082d07010b955080e030200c0c15405489120300046030081a20322450809800800030700c0c0101c001c071990005014100300a250103 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 958486987 1250 958485737 958485763
    0x4020306100f0c141c03110f090d050f0d120b0d02010305060a030605270f030910090b0f0c0c0a24031410060f030506030304090905190b090708 63
    0x1c5590244441e8050307201041000c1c52410071a038945020784a403146209003501e1410560042c4805880c0340c40c10001d846000c1c041441c08100410511150f803815100b001c6507290012804070700341c18142e41d141d140009095101041d00d400c0c1c030355180e8041c1d4422000b034802c40441d40a40c1452503078141d51285107119040140030715102c000e1500150001d0401401054001c0213450010000c00c109000307141c0a044506003845c4903000e00102c20950714004034104040b6000145d541210701da0001c182d64005100315482c940d401c40100c0c054403c000940c1c8546070780c0d100892030140000340c0c4806080901d041d042992400414542004240705085c003403c2007910f0350f11030b55100c42000103c04c209136400c0d801d0001e011441d5009145034020111600782000300c0d556424000d0961058018404124a080c1800759003441c02c0001d88a01581c0180b0404650314a804801e111080003004100460040c00072580c41c4541841a0a85030032036820f1228801e00c2c000098001000030780b4045180 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 958488237 1250 958486987 958486999
    0x60314071706011a1314011121130807180c0f020d030f0f0905010c110601030c06080a060e07020d02070b0403030504030807020d081c0b0d240213031b0504020306 71
    0x30030024030a462410602e001300160344240700380001245006240d002404154001c010802e603058001090120f807400d08400d5a0800c1041c1401c0000703100348984000343c11220700d030b211844400d4000030099680e203c1c2001e40710304080000e480051180b0760f07161800910080c42149900e40303042e24406941d1481a00507804408510000d52203944030b03001c4080a240081120780410a003081134035450304098686954a858001810760089002002220680302405c032540c0345407605101c02c0f08074402c0c1c605100c0300f90005030302050254041c0004c1c01c0011042e00660926901c020343d580154120580540314440020410b2001001680d0480354507071740380c51401c0d00319a503040e82031b00200c004a81010700c1480e900d001540f408041c048581e541e0385400e4801d00404000d0313040d109510301507070017107610031800c90100c1c02d000313100741c958520718a0bc00d0b119003c0c21038010080c0714809640c510700d0400c1c08040200203d444000380da41c40340805181002d84c403001004103d102c19100c0a51040d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 958489487 1250 958488237 958488239
    0xe0402030c10050d0905010e031206180c16061508030304140303190b12070b18090f0408030403020a0c09021b01020c0d080c0d0f0c27120503090406031407170601 71
    0x21450360000c00e20680700361b00204025104494062443e00a0045d0308100181a4204640c0d400e0020404518090080301c030701030b40c00c1041c0d07124514490070b0300c0302c00c8407142d0b0406403081c031000d60001d9410f02210240070191950f0f9070101902c94009540440f2503c4920b080349802e0b02002064074000c0440c2444040c56515078400c00b00103141c460300440e0803406581d01e60280f038106203d808020301c819030314540e4880384142008802091195018890080181800b240d405036501496010b544510455076036261420b040e4686000c03d42c0007005006410f0380420780c5803807900501a0342040c80b0080c8041071089480d10700780c1c013503001d2080555002040720f41c510362040300c0e169040350744420742c0c130b181000d6110039105840164240305070f019140d24002045541c0704200c124a076007654000d008001040d19590310308241840382440050b602c25520060090510403a149150002e1080103980d0ba00c2c98001e50000318040100100d001e20400080d0701c4101803000d51603062150b000e400c4603 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 958490737 1250 958489487 958489507
    0x30114060a180f140907080f0606010e0d0204050405010b010e090903191e0512150f0f1c11010e010c1505270a05120c0304030602220e0402030c1005 65
    0x80d100b0850103440141e240d0400c6040004079104490001902109200741407030020003032454200658010041a80a010046c1c05040042462a0050800d00c0e16004000a0b00001800207400340006944145844184410000154440211100700b0b1302c40041115040042241000702156003802a80081007800040708100c0e0280000b1081030821040042c4140d1303010400906500c01040454070005400358900b01c032041c8113601c1103403450600c0340100c0c03107070124058000250405000f0904070b030482d036045e0340f00700380c510400041c00c102800e400139600b0881d610104401a09000c200d80214a440713035407040e10418403035508213a081d86620064400c5800030b01001700502140407450800c90280217410794001007469034400200003112550800504240e40318a1200b5807810402801802e171a000c010707a02140c0c0c21001c0180c48403103000d1403020944503004c68101d031041645011407800d200a1b442c601460003901102e240170000414007804201210701600441d20034800b030260 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 958491987 1250 958490737 958490759
    0x901090228030b010e01030219180c1e0305150f0117061c08180901061d1c0c0f06050a0503160210111c060f0b0f0702060403030c02030114060a 63
    0x800c084001d1540c0d40c1e480d200c20800e400283c000c8412400365900400079490280701300b09500250325441c1c008d00d0b1a100064045c4085903154442158440120440541c001c42802c81d58030491542c0100782114010010010001110185540c80c00c1e55150442c07400c000d41e1081c10010103071039061000c61000c42ca904d240000800d500d6101c803141d040581a50303400110391002c1880b900781282c0f640c07480e02d080c0d0f400c000351811142c01550301000402007c2c0d0b00c1a20990000340040d80c81c800b81c20b0300ca01041c40c465a400c50006180c0300301c81080d00700075440c21088111034580c849413a08580b1414101c0e503e04c00d02400800088061001c11662040540000c969008600480c0c010a80d00401182078030031401000580b200041105034009900d00d90001c444c0d03281c5041000810f0810f03140780f8101d11240a20f6025280c04a010b80e00d10350860215800503400402c02d81c4c80b165640741c0101080034000c0101d00079424a0201c00300842a502d816010b240300809040403142440e9035081 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 958493237 1250 958491987 958492039
    0x14060307032a120501140937140f01060311130b1809160510030528020403031403190b01050d06090902010f050c15060f10090501030509010902 63
    0xb004008904100652800e072542c000003007198000310b0f01d01070594104a421203190459034450384c1820820462a010301042c0c280031104448081050030b194a1011007101e55049941d070090401102513009102c801070000075580c030f4000c2211041040d20001500b680c0c4140b0006004d201c040c00425034501d4440390916074106840000103440c0400030001e040c0c08281c40c655a80c6100340070510800c05018864403425207064007484c44054a0000072994201018082c0300405540d40e02246480e10151600c0341c015894481da20440111307980060002c0d4007030311084011034202d0a18910400079201901d10426030900b550842d0f4000b420b5110181480c2104941080710070042009803a1b600e21551018000401c0b0014909181c0c3c400505034212109041c002d019081c040c0a420175800180100c000b4400007441c240c0c0c1d151940030805001e820b01c15160310245011220600c5a40404400f0840720b00f40da06200e1381c0c440c41a418203c0e12142701c007039045440720700040c1303403e800086604c0c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 958494487 1250 958493237 958493273
    0x1e120f0e040902010c0213050105120102251e1a01051518030309130b04050c070f03030e0c131a010906020309010c1106030712151d0a110307030603061406030703 71
    0x800f050039550000303400c40542901d583e900740d9a223006101a041600c0c1c8140040041402149400b88101c8201000c1d68444c004215070319a1203a003104100941d41e003056400407034440381100f50758902d00640c03400e0004802c2440860381c2c0c0000100c80c58111f03182068000301c03040040c0f511408080c00c0c0e460b040700703401c2c4581601c0100302541c00303030b1543c822085140b01810400151302d6101010442610000782401d01950410301c030740400300c0c04043c0380f42d016039850308000410b59131045d03d06003041c0e801c410247d84031800c0115054601c11507003044e10040d20601e003003c0c02d000982e0054070a84098050100185c3c000d011050507940100001d180d420b0140945c01d22414036a030014409510072030301000058071004c0c505c600700750715000d40d158546c12400261500c0d07091040c800064800150f0044400210f500400d4081d03e00350300c1480d038800404c030920b50784d150404000d0050201c62000f00c808910702080300c030002440c0905103005000080241000341d155071152034103405218044 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 958495737 1250 958494487 958494497
    0xa0804050f0601060c060f0213120c091109030628021b0a061b09150c030c06090b010f0e0c0a0f051201060206010614070c050108131e120f0e04090201 66
    0x29071149241041018000c140c1607440400e44400b80c98610251000c14804495180c01401242d41c069442507200c0151120814071011944203400c20f10341c039805d564408001d240ca0078500036240041c2e2401032141880a078111140361303c0380f486252125442c00302504107229000111015034969800401980b010409007684461940d01c2c00c07030400460520858105a440340c80105110a4107000c1410003030a0070280f03241c0c2d14101080c0060010311600e40d04200b00700071034808060203075000048464100008104007200351604846400080c010000c2c585404480025205c08052502c3e01c00c4003480905d44c1040802e00f030540d1a00c1c02c0c0f42c910300a0000620841e41c43c0381c405103000307009001540c0141040e514010001d8802c020300a505070540c0d400300100d03808215981603942c21a4400e203011092650794109402d11201841c0d0000c0a90300108103411080b03c140300d40710381c9140a114101c040301c0703442000390780540305505400040340c2c80d990001c00340c0c54650b0280c1c029a00604207 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 958496987 1250 958495737 958495753
    0x52b0b030f07060201050609090d050f070f0b0f09030c2a060307091e03050c0d0309080d0c0204050c070b04170d0501081e030301050a030b090106081504120903080a080405 75
    0x1e040c00d0790040001034550120408010351a424002d0540104c02500c2561a500b050203441da240c0c0158500d103001d205001811460180a1004840c40301d90401582c50030b042e05450003480282040c4c1e65200811001008120040400300803203c00da4011401411040e62045d640d6029240d50014010820300022946106844441c01580300c0ca00e0f91b5500320080341428030250310511401c01c1d070294001d0301101800080d03000240b00300b04150464140010000d2840c1c21610062075070015862070169541014009d0f4004145541040c422602031096513030750b90011617640030708440900040200c2010801041c1180e0901d10128440e08020b483c10401c21001c0003960403e901c1500d1580c4901c41e940070607060048212819003050024520710b5141400207011070050b40006081c0704030703020200c0e8080d6800d5009a0082203000305a035011608011010b07114001100c2c20b41d800035a8007070b0324400c1403041c6280c0050700d901c12002801c008280340100e40d4400028400c4507a8414240 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 958498237 1250 958496987 958496989
    0x20909010e0307140609030703120203060d120c050c1905120f030703080f07020601080c04020d0f110405011101020406090b0a030923010c050909060d080f030f01030b07052b0b 77
    0xb00412489014650342038a206203004074920b821402480d80c4032030341080c4100e10000c0c2c2c0c0801c44010b54103200e400036860b51203241c001122082026001400c0310400311620707801c00d8022001180f0a8003800c1035420003101c3d0024040100c03d51001c0f00c03d003028611060180f40b40c2000500c5a6190345811108440318042a00703140d644038003010380115035020100000b501810f1881507002c09644041d00759540741018069a40301c41032121072042c0d80108003110095000c1d0300100c2c4407083c03c0300c14010900480c2600032203a01c80e01402e070003c0d0152054894190050086500b21442ca94402540300d02e888582080c6400c50941c44081589410108012513074003143c4407050251105070008007503412800600311100540c2440c1032050601004100d5581c06c00c3c1c059201c6002d64001c0e2400b0041e1800351501e200c3d071303078182e10004004070a0007000800c185600b81a60b11920304a0340c19161410203036220700480044882d0f0300503083d550045d80300d107494204440c0c014484085074154000c4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 958499487 1250 958498237 958498243
    0xf02060a090308070c030b01090e21070516090c110d080411040504050607110d021f1b030b031005010e06041a0307060509130b03061303051207030209120712020909010e 74
    0x44c4050b0350a10381040240705101542440600602e0070440400c07052280300d0409448002c0721862501c00d0714060b04204180d034884049412a030761120030760301c00b02e000800344102d10082e402000f10451400f1043c0c4903042c0190010440c2c14502d000408091841940407100c2100090040700d01852404005a668a582c00b403070f80500d1140300030780018074040c0d40040661218001802a0794001402c43d09640d40221b020407821041c07803824510074400d144107502a2481c00c1843d5540700c80b40107500006035159011420086003141035620f00c1c0d400042c8181039540a0154008c40d1183d68085030f4145410352005074500200b40c0d135a1000e002c01c1c000603090410b540d201d0000310b20b0006180d641880d10b480c039412148400301c0701b005401d0040010969031000106070080030f407100386000040c140201d09442c010a10803080340d609251023039001b000381d00180102c5015008841990906c01000f18079901550300006446d44601010b8003040741064001d4100c0340d41d0356032800c802c040460f00b4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 958500737 1250 958499487 958499497
    0xa0e0c0d11040f050c0a0e191e0f06080c210901060608010b03090303071809050106050901020f060114010309020103060b0d020403051209011403060f0a0e100b03040f02060a090308 79
    0x10751500424000c541060100340d031900c80451280c00d140104105503007025005070f45111a8500e000c02e44201110042001142140d00c1101b010040050020341d0a140c2d20b8080c3c2011800c448442c0c645560b86d5a03c03c902c2118062a0003103036003040003501c88040300014160030142c440794140d2409020740c0d03882042e10309580c2040d050b51900000d01c0004d42180c0710b18010300704090701514610f0300c007040a450b1b0101030030380c0040040000301c003402e000701c03081c400d0003400d41c081003005156514800a4410380c4110b120f14090300890711005d20800b00410420304846495803070712a0701607a540110000d001c0128224181661950081805200500a011201c880200040e81c950440c2441d51610782e040758200c684031340422800700300b0b99006040c0c865164644a810f070f140d840303440004c2c078144804403219802401c0e510000400386625020103000700d554041a04075680c4500480712144070458014002710207540c136400050400e140103051441c160f1411810040d2a0b513104104e0b5441 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 958501987 1250 958500737 958500743
    0x4030618020406031121030406051c0e0d0e0d030804080d0618050702070e07050405060d18030807091203020c0d0512070c0f05040203190903140c0f0606030c090a0e0c0d 74
    0x80700c0ea400c0d51402c003444205404081030382c0040c2540d4022260039508c1c4110b024503800c03c40003103040400040c07803201c04171181c40a0107090202071a4201910381e520041c0c003070407000840c58244655642449444440b04179056900c40d01c03280d41d951659100c55002c9400d06120659420300005c05583d000c15410203200c0300000811141803280000386400020b81102807000030302d03801c0c851040d030000212822510150790b15525080740555201c018040d4a03214050103200780065410542c0c4244c03001e01c102920781f200d201c0e25803688c500407401404018002c2c090303400510042e0a62500001080c181c07849041114500c00503022104401d8010120407208040404402e1042c540310030100e4026100c180c50841c02d519240840082c20714500d4811100701c1ea6514880782414410340e011001c8410b0208055070300c03000c110349641d5840e103001d00540103000e5040804c40c00d24010402d128040e40c02041000180c840c4003213a40100002d8011200910440341c01c48103607110b4001101c150340c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 958503237 1250 958501987 958502003
    0x6220b13020703020f101512020609150a030516050406110328030c02010203100506160206041403060108010b030d080915070306080606040e07150302070215040305071a0403061802040603 82
    0x50004405140c841100c440070011b9042555410f8001500000a0704440c158070302081c60480c1c90001c01d2003407141505841d0842c51030344840500503080e4005103403056031980c04110690f901d400c5079265003501c000110003c1d074108400c01070688500c540314403054a10382a130b441c1c29102e409900d0441c40b94100e08e1101c11048101d04607181d00f6206030300d4a04d00702d0000b0342c51403400140001d4010543c0c0501c61040b9400305008108100341008032a21030343c0035168954641e100e0314082587c603c0d00159600c00e100300000406c070316506000303008180001500901014610300c10503503d03510010305860441c803d810311404400c0b446c82065002e81c41070b40b400605a800e1450705410100d0090105000320300340b2900003801e800018450003100d580682000300900c9048086010344103501020358400c0000740007004c2c544014006200302e92041044500d2a07a5072014201d0a8002d2002c0d034120480c24841000030441981100645c07881041514a003810140d0002e0101d40d20b680056a1105c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 958504487 1250 958503237 958503253
    0x20a170d11010b0102070302212b0507020d0b13050109080702040501150f0305180f1e0a110d081908040b060f0618010318030309030806220b1302070302 67
    0x1038210340d20007120940903000340040b0f0002d600207540c0d04601d20000340502290b1210503462040c0e8512a4801030700b035026103001400382c0c0015547c0080c19070342d812459005a103100c000c6070051703003281e1010342d019050b03118600898456007a988402414102c501aa8500c0c0d00c0000b1307020310a0b80e00040c422100c107a2121914014042151016046030120740390880c9080140c681194405801e03081d20300d408980b0b5a6400e19000302d400031204401c3c213901c40c41c00040704e03035000400d0000284d03024070403d45040c12290f03c5550750f07044400c4050154110500700036601c1c2841108400c8150150307140310303e0451524030703903400c0c00c500c80201d00c0080c81d078005101c1082025100c00c0e0704048200c9295447c00042c40000d1122300c00c080301640c0c02c481c0980d0907426a4001e8000300000107803034000008003900f80c10084d01400b6070003401c030000350181300010035031302d40725001052a40c2c2102c1c1d01c00903407414140200080500c03401c05c1d64010f00041c4048514240340c0000c1248030b201e076000d0900c0c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 958505737 1250 958504487 958504513
    0x9090501050d0b060f0303130b0903100b10110a1e0c05010305011a0d110307021609020f0d0e070b0c0309041802090f0c07050601270c1b020a17 63
    0x59806070051803061031010810404952031800068010400f202c0e1880740084d01c0d00000d15500c0380e21401c1104802c80d201c0001c00f4011140500010141502070b00d170441c1d42010107104956000c9400e0742c1c002a070712441e00100d031007800d500f070f13400300c0e540c08072003c2c481d00d40c40e8105084c41550840c1d4000c1a0b10324840100a00000100e00806c02802d0034030183d41041d02c0003c100c203407424154182040426110421115074110b01e42041e4903007001a96403c1092000b51609007403c1318420001c0085800191903185100302e81c5030104100e4841d0811808001000c042c01c02c4507107c00180c03140b40da000c80d04803880380040100401721350007140c0e102da501c0305100940d0606400403020380c8050417030302c0240c0c84030148035900c19818000c01003680d80e5501c10904030b00846001030f041e84030790300010552076445c1d0644040c801a0780000304999a00103882810740e00c4580d400070000c0c103855070360700d2035a1030201041280745c40100b039070036019260140114007541910343d801c041d500402044080c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 958506987 1250 958505737 958505741
    0x30b0603281403162901090e1515011d0d030c1b06030608011808090f01210209010311190e06040302060c060f07090b0403020609270411010c0c050405060d0c03030909 73
    0xc040c80c5e2529515482c803400802011300c03101445256901500c1e15032640601405110042e0900085104030741c0310706050410f513684014200b03034140803034480d50140c01e164200d0403000c550068024681054000c2c0c0b554216001c080640c0101c900e188044200e0108881484904003e0070041d079000607038a107441421070075500300c124800c1415107804030800c082000c441c1212462241543c13010b11240710100101d510351442c80710000d1507881406c2e581001043c035001031480e02800d9905000700103041c555200d0f548512603003008103c101036490102c40e4000ca032158006240104001e080a640b5008150346920a010314000ca0700407000308800060a9900640c000c1030500e13220013440d003007400b902c80501c10707400081d03c104c1c00850540300c156650358800921048244c080f4010140f6441c04080155040d00c00720b442d120440f650382c200707520070b1007030349999500890800c0946190405100040c5000b80000790010040d200120203c4c1c105082d403c01580710ba529a002c0600d45406441 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 958508237 1250 958506987 958507013
    0x9071706010b09302b0e060a05040305030d02030915090d080402031e01050108060c09060406050903070f140a0510090603051b1b0601060c080f16120306030b060328140316 75
    0x80340c0c81e424400300c24254002c002c031b102000103483c21a52001403034001d840b5402241c3c0010118400014614010a001d8000d1401004640111075910360100c44038242c2900c21681c40d0400c0c0d00285101800c4d902c00c20505400c903001405456200056180900011007800c20319244c81e034440c401001003110802c801948035010a2100342447c20340310020300741d8400c0c1c0c8030304c001304000412070180a9806200e407038020311824010100d1103940300760b0314039103902d040e0306284110303001807000035942070001110400c0c002c5551081092800c0500613001032501421000c10009008012200b02d10200c00800c485084142800400703000c0420302460120160440d00400002c403100c1000603103034105031625100b807410350507103407159005c0c010a43c41c03840c0f04c0a00f16403428212924420b40540c800c0d01983d00882d050400d90fa90f19081c1542e59240440f1a51190b0003c0074030500046221004100b09114208544001100a1216207160050340c20803558020007000c100401c407031508800 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 958509487 1250 958508237 958508293
    0x10c0509030715140a110604060915060e01120311030f031614030c0901031b11070b0913020a141801092411030903030309071706010b0930 61
    0xe0354004405000a0825440c042d4000e13041c1008641035143c103010301c8406110404180883c1e01d586003906002c00681a0004280c82d40030141034140f500d2252409000305407010180c0713010707607030b441c240225200107080c00d030070703010032820581c10f540c01c04041c00101446410381018940b01d06101a80d100703580c480542c0c0d82d042c004a03560360340b00181d9150036680c0c041d22102d0a141c4560b1000c0c0164049e010420221002d07115413403001c82c0c415006458102c0c0c2c100382c5d034100c800a0b500d0300449851482030403411a402a404541e42d074065940341c00a02c10400c540c582202c0c420b08040c8107003501c1e00810320754600710f410b008501025590000c1403074010310107411018449550801d0403200c454510b5100c00800443c003860900b18841001100c646040c09400c0340e990b4640700015030b49840c40d90203040304a014003020f08040761070002d03030141a6076003000d40c42e1030300d10108100555401182c0e441c00d80030340214020544410180d400a03014207101010703001c0006c0c80f480c400030f0110051944 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 958510737 1250 958509487 958509509
    0x4050306012c15040c03112107022b17040c031a0420030c0a030b06100f050d0b2b110102030a020c01080402041d03071e0b0a051008010c05090307 64
    0x280c01652201003c0c0030034000c2c0c40010340300d01c0a4070120301504110110f0032041c040012401d032040c00220140c070804064143c141c41540b04c502c0100d032110415207280d1804030300c1c541e02101001c4140807104540d8854240407468030352204030705500090885090300d840444480410900c200c03002000f071604480c1c8018500762401ea554400164003c1c0011405140001d0180360750b51000c11400201c02c4000303110300c09950392032a0a84010700211910382c0506803580c41c8501650094515810790f41d01c80d112241002c2d240309019008101c0e003c0402e80c0071038880b508606001080c1200d1a0060030b50b03035a000c0b064900e0a0020b5401d5203022628115803081000950180d40030410002c40402445e0031312094a603230001401800a11454600074040c1a02da007403001000801001044d2207a00c05404196119912202001d0100300203054013080740001010001c96a02c142d9103c45000c110540c91a00c6400f541e084801a465510200d6070000c0c007242a4502000701100a140c0c40ca55 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 958511987 1250 958510737 958510741
    0x607050c012706050a0e030d0f0e030a02030307270b070302010c1701091a12210c030301140d051b01141c050919050a0b0702010e060103080f04050306012c 68
    0x99201a40b0300980240c80c0c80c1c0c4d0350000c1070a4041640016600000180499450350220820b20004040c0c4c071101084552401c20315152058000c020382d030074001690051411580c4004e0b0541c2c140401030300905d40c0310341c0403420780a002c0001000c031000d404400740342c0f612024585406800c641920300c400c4140301c035051416404000700c0e008541511030b042804500d0956540382107190141a440f0140d1000c2107617500d400b41000065a07803c0a080e84a2203c0303d05062070032041d09202d2141c00315160341082005001003940100b2070707115800302900301d2018062a8032001d0030b00303c20104010b0000f50400c00e41071a5a40300016144940400e04d65500d00b104840d101c1407a50407280320984401e86810025a85007010f014000441c215500f05100c106024544191260390052040304c45101810125400d14414415083d803075000d80000c0060740d0854035144c215403c81300080301c2c4813000300404251510140400b5000b00841d03400542e1070509055410038102d0600321081c00c5000c0c08003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 958513237 1250 958511987 958512041
    0x1501170703080d151409160801140f030109030914010e0d020906060405130c021b0d0b040c0b0406110106050402030405031804060911131a0a1d030607050c01 69
    0x4214049a40c400d40003a0f6581441d09200c0c068000a10101881807100c1000109a40c00f10400c9140c402c049500c445540e540c180d4425050340c0d10140c500014150f00014032020920140e82100303400300404070719440b44030b000000d082d1a41c80b201140080d056680030015010b514031380610f52182400c00c052a6040b62010070310a4001c0b080103846010301801040440c1c642d03400b11070240401034104940c0070350041d403400290002560040c014419880f18406040c1003680300541d1b4100100340d419049045e48030460941e501420a0303500031401d40f40000c010f80158010002050f558a45261211544000c1e90071180c40703074005805540100304000000d83d005c030486082c425401c03800e01c1035407003d00c08a4010306031070b000f41ca00189400ca40b4501107524101400310051f880401c0d43d080c6072107109003800f02d400d049249600100600040c80c03924003030046d6000c22541300400005030461000001d01e4032000340c0b140008070310000f0f00c81000c00c40070700480280030760414040060002140c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 958514487 1250 958513237 958513243
    0x1c110a1206140d060b06040b0f07110402030411060a0210020c01060302031504231006030b041506030b1b0702041103010312050a0206041421090f1e2e02150117 70
    0xa00f009061039600d100c044040c0e0798610580e405003096076078182c1c4070041400c1110759030b40018410343d0030070b000300841c403032602d058001c0b6442154000000320703840c00103109101183d044a0403207001c1d801012010000994944040c7c40d82c22a040d00100e40c5503d140149414100c00c0c040c043c600c00c0c881420080480c9131215040e6040d801e2440c00c610300b08104001d1820b080b21801355404090502c0070002c288400203c0d100e0207280111000844104491100f07004c440c1d541c403004040b2a905030010b101e031171915000389040f107600c8098034905811a4001800c9075030a203c0705256400c040018404d008403c2c0710065100710703600f8040d14120300e801003e541c640700244018101c110100740f41201900520440c112540d5100a6884042802c090240c164000c8100f2501031209002c800780e2034a03105050f4071801280364a043d0f01a144070040c8109415003188490201081c0409014248140750040d01d11b04100d501600500301d082c0309601200c1c80680c403040c0440340c608080030030f040001c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 958515737 1250 958514487 958514509
    0x30a05060117070e07050a11010b0904230f15062409060c1c030b04270515040b040b0106080c0a3603020a0902030c1c110a120614 57
    0x810094401004070b01107a4a0a48a40c03c00c461584100781440303911740d00f15000d0841c80c540340d00c8070103003601d9484000d8202d80c4424501c0d5808a4043c0115020910b000031007641600030890b0340c0c0140891181961a114240c000903003903a10405004e801004401c0c112600100200d0b0407030180742c0805480e6030440c3c00000d035416910301c0003e02481c40e40e100307011603225900c17034000d80315011000c0c18000e850740c0300151100b000c0b90800707400e031a8070320340303445000c036488803648112891505214540b81000404a002c440c180f00d41c02110800c3c3c2554a40903118900c6a120300c6503620b4a464146500c80040e4007000512030813a00f070000001c540016034400d062546440e6011824104c2c681c4a01e020050101d40f400e07020410760300300c4c600003e40071000d803402a00d50074407041e40e41da510800c9201c02c4402c0d400c0344c08140301c0c1408103c2c00b600c04405449030510007003855158000c2171002680180491404074040030003c0d8242031542c0a41c0d0020941c00704406415200030010580d800c05d0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 958516987 1250 958515737 958515749
    0xf06050306040b15100f080108070f0b030903120c18180103030e0f150405151905070302070503060717090a0803070516050d0807090f0305070e0606070b0c03070905030a050601 77
    0x1400000403000401d4210b582130b00789004103810102c1030003807405800011512030580008280350004a90104002441000c603010502200582c924203070611a00ba003000c2e00c0742c40680810010f11214407041c008041c014101d1098a03903a9104407191030072214503003540240035038540141c0c1c0982a010801c06070450340c260a00400200d001c4000900c070f5481401601d5000d4019000314001c54003490142064603402d40d14201c4040b02c6841c604450300030446940750a5542030b480702042c0d889000a0705502c0d2c482e00407114000e40301c1000905044007121000002125141da46405071002201d09400240c1d440203880001074944039803c1358030008200409011000a01154001d8840c0340e5100c030982003400d944514a502400500c07101c0d00340d403a0000103407002008551411081d40e00787c100c0b5072180051005901c3c0200c1052003d40c028100d580c0468107012420206c2c130301c040340302d1080e0b80c1c0c690259600d2809400192030301d8140d8205600952041e0f90f024001080052042c2c19500 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 958518237 1250 958516987 958517003
    0x1e070908060f060402120708090d03020903070b0a091521090c03020f06040b0301120506090f0a0f060b1201060305010e0304120605090106081c200604230708100f0605030604 76
    0x10700c3c00041030103031103a1020030801130703c0003041015060384600d0319400b4042d80c03815a812140380a43c00c0b010b0f1702800b01da044d855040400c04004035418440108802c00c0c090500d001c5031561110030080e2a01108141c0000c00c46001010056568190050302c220f2070b2640e08201c00a150b0b00c4501849219000080c000d0350b40c0403104115175246d00c140c40052282028040d030f04e40e140e40c8080215401b880c022103848c40b5600100c0c00c10003020456900503840c080c007c0400c1091074440c07a41a118505003aa580d6035501134400e0140c0310b44040c1e02d0501e05080c0085015855031500d5401c4030554002c205540d00309200c1803000300800c401ca003110b1a048040860340303494025010b401410103a014418501c60041071000c00d101071444c0b0315180c5030903110000710f10381d405c1d2072100d0004110350b90044d0780c2010700010001551807941d03002c810300b90040c840d217610715118202d24041054010309a203030710649407100030501e40c0c050620004031800052080519150109079a06000b91009249403 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 958519487 1250 958518237 958518241
    0x7021f030e061b0d1d010606020325050d05070c050a060507030206090304080a03030915020310090b0906010f03091b06110106051e10170a0c020c030109020618030a0b1e070908060f 79
    0x30a170000d601541d138040307200030444242d80d99406517503036100b0f181196035441e4804940c0916201c4040314410150400040e101c0039010b071004444603031180d5000c80720220004004162034686a01c241c0c00b4003819101d1696540081c14060702e03010005020000341d900400081c0002e12011035000c606540c14100400d80714220715055800141e6410200f8000744003008100709001c11303c202e082290001102080078101a1090103801d420840301180070401e1030085802083c403c1e40413207103840c014110b540804240c208030b42c10b414526446080002c0b034614100300030500a00c0b030300000f048201d81c140400da4950342412041c2d1400e004492007814110140c0341514041c8042480103040b0b8005500c036440d125141000400498412600510800040d0b20050a05200d0b510925400402c481e0608130101181d03100007100300950340d011700803c8040400203101e00f8000e40144420100c40e000301d07502d15045698030000424050401910040805c01e40c0004145a43c01c8001c40610001603 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 958520737 1250 958519487 958519511
    0x204090e060a09031b291602010605011b2402300c0c12031003030809010b130c030f0f05061801031a0c0903030c07080105011703030c07021f030e061b0d 67
    0x310130148190407010752502001300406d08840c03035100d0701916485001c0c2e000b442108908030b03259401080d002c6040c005014030707000c0050380c1c01c0001901c21070345800500d59400d01d004596000500e6661250b401064404500c94148040035040032580010710220150381070705900d10304040c1107c412400c0c0003920304841103082c02055544001240b90907501c0c1046200840c25a81e24032094000800c01d2010480703045041c042c6000700f03800101810030744001200483e00500080070b8100c28142e072034400100e400400d0041c0f2035200c0c0b010400050342d01d4400c040c015960001d00680848100100050ac00100c0504001161440c00710614445030b40b5840800402d02c500110258144000b1440044418000410200b07035004000240201c0e41c1c1c801d040c9081e55204000c420468001b80001410210107001070070003680014044400400464400e80900410554103000207841d83c10320f5440103820000766403c0303403031a03451700007424010701603401c0c078042c0041461417a43c41d1801c0c402c00c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 958521987 1250 958520737 958520753
    0x5040b0d06020d020702210d0806012304050a0f090c0206040807081809040b0a0b0a050109030605060a12050d030621110d0c0602030c06090c010e060f07060204090e060a09031b 77
    0x1950346c2c0a03120300c4003070805203042c591687e0311503000c4a00d8400d05228a003014410399042d03018003030603100d803c8008940f0040760304c100c40014a84c1c00340001404001550350fa090392038001031100c03003040301d1070700c3c14490200159104a00a0015580400240300004144030201c400d15504003c04a40703810841008541510007400150390060400080c001480070614070303103000c0c50014004020b607002000500c10b850955110b024042940103404101041c0140c0001303a111700000d03c1c0384003160300c0d011281020307503070020192030503170041440e040403139054030808000c0e10700e2039404078074484140312400b0003c240a200501b03c28034050a440030751143d0101c111103640c03114a603091aa10b030000295a030300003800141c05845070741c000c100c0703e090215202c0201c2e0b0043e510080d210a0300c40a00500b1b031f0089201100300207040201001160b601c1c4040c0000e0080340303502242a0140b1a54540f80030070103804500707810f01c0c111450000a0300030612341d01940d0b41d68022080f40c1e4060400800b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 958523237 1250 958521987 958521997
    0x603050a080a032016150f1506080c030a0216050607120b06030f0f0603240601030b01110c041806060e01030b1e1b090d060f0605040b0d06020d02 64
    0x8103100c0e05001908010960300a4010141d850742d08200c4203500c84c028240e020041050515110703410442c04542c000f104041211060081400e440401c0501c171250044803e9000c081c0d4045940360042d0300d4504148010f0030003040240380856031814540311210b442d200141c0180c000540c005a143c000d4100358465510250b0440140c900c903151007000a0b02486000500141652800c215007000d89005001e4a0050903d244940d05555070501021041240a003441d42e05108801007041280116000340e0411408490301c0c07081c84c20f10300005000d90f61404a0a0f0600036446d092907401c01d0b0004600d21150406c40e03003c1014102900c000c00c1c0b1902c1690086c040609000340494101700c996031444c100c1c0d00c034a991015a940d0b9044444603244100d49018034400b1160104500c12200c0000c02d00c3c070b04400e00418500041c0c600041d00d44046800c04840c06911000c85161070400e40c81800700400c0292018014808800d0005030885007070b0400a1a00d0b9000c01c0c49403d00c5460360541d1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 958524487 1250 958523237 958523243
    0xa0b09091b25150626030d090309171c0c020310240905090f01020a0503040b0910050115110c0a09050c070212150c0909040b060301150621020c07050607060603 70
    0xe450500c01c0303001c0002804d900d001d959103018200140080d80d0150b000c0c00c4401903c9840558203049401501e20090a84035605800300200c0c0c42000c290b400610b410307003c000403910300901c0c2c0d00c11451661210510245a010300344800d11403c400541c60100d103021144512000001d08086840b038003224000440c215901544007900b800310b07004605a00040c01040f0a00440d4942c4600220050130f03441940300d0840083c0082c00410001806025440e8000c1d0000c0151100e40341407802e01130071034209030300180c19000314006400b0059048100f01c0c01840340c441c05000207500d00340c040744501c1ea135481100f01c0c80da40da500081800710240152090542e0091240100c80040654656548111501c03250200311503c04101c601000000321820003070040e0a80380b60b0b030b0fa6611800103481d0010807003900365484141004404240400e0030001d803045480d00c0002c441e120140d203c80041d0700506403680d42c03042000b2000d15100241501c21107804880042d40c0782c996281207800340c0850b82c801 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 958525737 1250 958524487 958524503
    0x180f030d0e06010b0f0403020603090a05120d0c111b0d020619020d0804050606010c030c0b010f1401031e0b010216030501060e28020a0e0a0b09091b25 66
    0x35114040c040e0010454042000c045075580d90301d8000c00812840740c10411014800c0c01c101c1000182040340182d544038010006458840d50700d61140d03402e00f6030101900340d4290b00003812001442641c840e0707401e41007041c600035081500300da04a5680716503c009a1a10000000c0e13442800d075a4458620380f45075020b09056160310500024000130048150b002003d8000d015061500038811800e0904c1290094000c0c420340d21280c00640d41c2d170b601000b096040207012080b10001c0351240282c02d00030304800c0344400545213010221454a80c00c1c1030b180c0e0406041c541c200d0400700343c24090003194003014a00041040c1940c005070320301002c103045041c3c90304011078008240305065000740111600c40c4203035145952405881400c034442d202101d0b20204090845401540d0b45038058400b4560b20308000400305032542c002941034986503c59110075000040c044000d0400b101c800707800540c0460190804c2d04070307a00d40c810a0003036540350040e104c0c11100b04641c2041681511014640040d08 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 958526987 1250 958525737 958525747
    0x40308150f0303042402030f070f03030b18060111010b18070509130b0a05042706240816060206040308070207180b040606141b0c06041d070201090803180f03 69
    0x504004039007010405170388201c109a81c0030301c5001004545404941e1a0014602201507881d00048610218181c007055512a107950382174070380d2141801e12100d0b0641c01980e40c900040010300013584002c115585904228090a07540c8504502d54102d030020300703d40c0204d60f1080d40c11039850264140702c41d400448103210034004825a0322004101d45d05440c481003c640ba80140030642e5204480c610b0060f64000da03078403a24800d80b000840a80c03050201050ba4500c00f2001c000405042921038040304660340200207241d01002499065440000710021207864841c3c06074840100810140c18000d10b1000100302901c02c0c44040050328184504186900c0b00c180c5680081164000741c82c09545452400b054490040641030844001da100d418a00400d420400c00035403400300200c41b00380308200035009a030f9112806040600511103d4000100c91911110503c80000e88284107591600c200e000105030780c141100d6205034140d2040c05014070f0300380740c10300d03050341c400c4400d0683c000855 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 958528237 1250 958526987 958526999
    0x161701020c1609050f06060403200a0b0405030106170c0d0f0c030609050c120d03020d02040909030302120a0b100f02031204030906122708040f0b040f0608040308150f030304 76
    0x881a0503100b8140b401c211a03507170f4010b44220f0040a0350300350b40c00102804100700050a0504d03211200100352184442d04190901045802e08503030031500c6041130224040c45607013024800c94004004110021035001c1000079802d40341c40182115034002d000c0240035905109000300e103200125844a811205155a418071030300800c14940200c034680a80c40341041d0503e0401e05124a181416016000380b60315407905400075402520340c22001c0d0b03028800040d48038580e11803007801c18029100036a40e120240e0001041c014002c02c00c664252801001049079261426494810782982c24a01d42110010000341c1c69405451220174451441008100805034000f400d41c0c2154403a8590210010080c00840240d9018002c0c00c100c0d4106051842d1105107030020b100030560040d60505c1c5065112011000038221f0f40e0005000f42c600020108400c00c200004280185210310f01500f49007402d5900505000c00504102092119408180e009070b940342d428222008008044039511980c0364 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 958529487 1250 958528237 958528273
    0x702030a0803091f0b100e0d15020a03050105010c050303010303140403050a0f050c03032701031e0c17160809030903030d050402040e061627060509040e161701020c 72
    0x4100080d0581c03801139814042c1420f4081e5213001c180c0100000d100380300b072071030459842480c040f8660340110f010600c42d01184508030fa9400e20703118014051b036600ca04490150660f403041c0e05c5181081803007405070300441d0001c800d83c1d0540e0385c189400b11400f10a111241018001e6820161150003140000030800ca0300c500400e841c50b00c20300c10b80d01c168200d8406c240d200c0c00364203440500c0ca07045c00300e584070028595040a00035001410000b4902c00031040303840034a22001c018403581c1d590389032007401441c0c00c0746803103200462504500c0340d18940340c2d003142803012040c00000107009010300440d2800c0c806000740c0b80320f800e01804590703c4801280320540a0101a03405074002c610309080310f401c001012649500c651031044107100c154a1902e02140c919040b41d4440c1d001e01c0c0110350000a82652920b4400140340d04c1c3e44954407440f81c030082201b00e515003c2d41100d1580000b05080340248034481b04400c03107d503000003500b5015000d001c280a44101580ca803041e004022500352000464 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 958530737 1250 958529487 958529503
    0x1506031202010b0a05040605061803010906020a08011e060e010e0102070302060a05221406070303020405040510380a14070f1407051818060c04060f0e13020702030a080309 75
    0x1302c40341000507948a041c002115924012a40c2020040051206000c8482e0141080c68400380000402c0201ca0719014120f81240705450001404000100403941030300341e16000440c41005240107042c070300a00913040d84107200796107050103004019a08107038002e101740c00c02160042c009540c1c8201d8641c0041081e4007401405030680500b01703032101b45030700b00111303682035904400341072042c0c082000c104103281d004144110105502003101041d1621a801064000c146030f0030b40009043c1001048801d040300c0001342c10302c100d01d01c0507003040004c003c1c2c40c0c3c10721502d1801d03844c1d58a43c0006011108461010480b06460340f002a00a0800050518902407540182c81144400052114154403480c49210712584010a411120480000c0700c035425081074030700f00d00c0c1e800301d17001411443c20400c0407214181d038102e021a0401c4026005501c0030390924807403520301252041000054405540203180d200d485234049005402c6440810403158056000055541c8900e00481200d540d5088 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 958531987 1250 958530737 958530739
    0x180e06030d170406021e0705060103140307021018031a0a0e1f1d0118030f03060303090902030901021303080705010f291f03060f0807121506031202010b 67
    0x956108140c0c01031081c041c0d401c04100b0640c0000d07030b58070307a900e49001039001500c03008400064030041d025131001020061103064800e101420080d80355041c818074076603c0080024030f64004000c24070040c2e4500400440700031860034840186030481e02d415404c0041034000414400200c0c42f0340303940396005140c0e0b03032046180030780900c001620102c60b076894082180a0040b13100180c2c01030310804003107400c07104400c0031111020545940d40d01c00c4600313603090252803022450200704030b901070591140304035040e1b044509007442601e10b1950000e200b0066481201c8107554013102113800c0703c60039012034100e0480d0002c1e040c011030b1039042c0303a641c940c84240704940d15840d042100409004901590011007048004061800300400c9242403aa001003451580b10f4051440c40740c40c5c4001b000c0502540d080c640d00001c20605150050505403000e4014598541c001c04040000400a080b0440c20702e5000341c0e0724070042003c86244002c1c0a40c0e405c0100007030000c0000f240d4107030341588002c1000c00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 958533237 1250 958531987 958531993
    0x3150114010908030414040f0501150314010b070209040203010207140709143309070e0901050406050904031821061b1209020102030915040501020f0609031801180e0603 74
    0x210000054a0a0b40244103c1842d40c0040c0010040d5003e6030034041c0142030047e101103a103900043c3c00e0760171204240c00800d4905044160f07242c0d12549840760602400021260745003650508841d94035a02070140000c2c0316040700c100203011500c0c02c0d01500c103a254800c08102c107140c54049450744030171150240c2840e181c0317808490010800e00719010b60040d03824a00c004500c09602c030521b42503d00f031650807107640a9214540d180e03038441c01d0140340708000c1a640e1043d9070201d5000c00040402c180d015502c10740c1041c0c8180a1581c66240013500541d0600b4080400510b080e600000980700c2d502c180c4820450101c1c520f03004a5800b4507681d01441000100041000d0310302240c1003120001e0b4180010b0b0a04414941030010741c1e0004203068014012682042000f01c000340a48410b0340e0148140b0300301203820042c03541c0400580e0107164245000d44010f00d4584103180c1e030703801991040c5405151014004000f6400ba809503401d2034200410308600c43d0b111805010b0071141500c020380284 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 958534487 1250 958533237 958533269
    0x3030f03050402090708060301090c0902040f050607053c100609200c12070f110d080904020a030902190f1409010e1b0403050a02010e120d030e0c031501 67
    0x94428481d042c8500c2d4002d02d0b80005403035080d07040ba03041c28020541c0d5059982c44040b407020440305107040004044642c1c001d640da600f803804003030a000d50380e4080b5000340014001d5800040b00864034409d4070361100822500b200904a003121080d40590000f82d41c08071004103400303050000300b0740303035181c1007070380c0c0c0501c0748d40d0b42d841c1100101c8940c00f40015000129190768080000c0c0c40f0010014031400720100c030030602c5001042d244544c0010000c854041000881d44100032a0341c00810000b202200c00104820712601d03400c40c507200706200b50f0b01c610b0380080c084c4a158000e90100c484c0b540c0160841640c04020304480700094800e019104480c251503600180d108040100302d413104c0c3d000350625400383d280040c80890a10042c2c480340105d00d0300b1782d40300c080c1c42c074a40c007820003140600c00410141d0720302d0001400c4a800040c3c8180180d90b01002e19040500000310f6101180903032500003040c8031051001410310314150b0350907515000302e19523000400c5060004505035450000c03940824 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 958535737 1250 958534487 958534517
    0x90c0b0f0f03131e1110030b030106123003090201020a0c09090209060a0620190f0c0801050103391401120c0c0b09031e0a02160308040504110f040b040303 68
    0x20741c01c1e4003c001c00b6451145548036403401c6c07014040c81c4c140224140851086803000010742994195040b07088520b5280c1904400d000d504061404841103c660280c61006107143c08480d418203078201c10107054036031414200f1a44200444005545c21080c504021500c070b191300c502034058148142d114000d4503001c5900380c40c05500f6001100c5880d02c4040e0f1400d40b10043c1f002113001c1c1c1981807802c1c05608900c040f50360f421780032800b01c03030312400b034201d04210f00b483d210b251110b1541003000141c0c500f1005000003031044102820f80c412089180c0707171002d82c1740c100c40c8035040c110001c0703541c440c00c5440c00609000345c000040100341c400d8892410282c01b1a1818088400c21002000016482507120001c02c81032803400c0e400601103401c0c1e030700d4008000303803001d000750120030300f0300c03001000040300701c6455418442c1006504000350a80c82651442c2c586a05030300887c0030380c40c480d0f40e40f02c00502007604000103d0300104000c0f001e407621256200c540d801caa400910042e40894000c40880c100 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 958536987 1250 958535737 958535783
    0x9030f01060806061e0a0e06090a0b0d060207080921071a0717070b090303010501030b0d052e0608100501051206071b0212010b100201090c0b0f0f0313 66
    0x142c541c640020042507940f8000c00001c1049522031034503503901c400b0f8414143c0c0318484034001a02d115003540c03202d0708106c4103100003194014101d101e01d510b8096820399903a80c010801400726003010015032102041d0a107110305100d021001d690103852120340100c030049044104044a180b48140c44040e079443c41096034500e182c100d89109100104075140000382c80301c0b9429843d45410000034204285a40c80c040031860644400c881c560000c00104550342e8140a504910041500d003440035030329998400d961200200c84000d501030030a01103d00400d4041d00d00303070003030403507010034801145d80e580901c2e1240c01a0030201e00306420100041540e040c0340c0e42ca1440444420024005c564070414201c807040064400b9a54011401e02c4101c0544d5800040c1c2c40e4800d846400050f40035200c03400c110329802d07482c0c0310000350790404038414042208072032020300b22600350134910380d210101e10960301c051041c00d81c1c2d81550b41001c0140f10078240075225a5520302d2140c2d403c5006410035482807a0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 958538237 1250 958536987 958536989
    0xf020f0d0b06030d39050a030c020f100507060c110706080a05070903020d0b0901020409061e0e150f030c06040e1f050a0b0a03090b0a0f14040c151e0509030f0106 71
    0x10842c4d64207006500007a2103a17440318800c0c042810304000280740d03900d0a0403c404103005038001011005100c0135407600c0c00c491480303504102c034100300333000710b0910207009030141540250901d65a51a00320340c940c0507400003a9030b00a41d00aa420007034546902070f0442e42c06903405481c291400c400a610340c3d010f007206c5420ba0781c00400c2007450f5039080c3d0354180c901d1030003005510595001e12000900a100d8025240588080300303100c280c0103c1200019136030103c652241541c85400030a0040e00801e1406112440c10169070b0004101d01c1680401e1070000d2205070340340c0051002800181d1415a10303030703c5000741c101d2b84648a210014600804d400d401c140206a802203502d24100500c141181c0206114991801d000c1242941c90b1905004280b045456411040d140e4003856400c000c81c0c0715900e00d541c01c004240c82c0904040c0c4520544041501a0041410800d60b05070041c501a039440e004051701402a0798040c00036140c014442c1e0001380081d402441064001814900d040c01800 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 958539487 1250 958538237 958538267
    0x90507050313060e01050406020a080f04021e0616050a0215040305060f090109060f021e1c090302030f0c01140903070b0c031801110702190308070f020f0d0b06030d 72
    0x5815510ba81001c2040c14050030011a0550b90b5580c2264643c03e0a004052080c0d005220040e00c1d0040c5600142c42800000c008e024001c01c05000c01c401030b0f80d41e4160100240c030000c140442084040080f4516218007a07240c1401160801e5490402000040f55442944241d071400d468808250b0700b03951301c0c000c07070000412641109000501d10440c1e510300507405100b842c00800d400946489030022100c84e00d055045054000a500c80c0020031400d0820404025044040c900030030343d514001d102d040428400d840d161940404818580b08000b513071321f5401081e070100e6407803407020701c164000d020b0309090003880100500040c40758034020042d1110340e60040d0388002d8541e584500700540b0340c801022560564a200801c0c44c44120904c03907030b43c0b915112105240c2d20301403030041084040d012030903110300e00d448003c2800002c00200035542559846440c400001c0c089100041d24000070300c0d030603600104104404001d2001c00c00c5614000c40341601512481304030070408540c0300d001d00d1004 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 958540737 1250 958539487 958539497
    0x506040c0206091c090b030f1807050102120a0905060c1615080403270602070f151706011e0305040201030c18060c08121315061d0a15080d09090507 65
    0x2038091030640704c1d800c40f00b42d80d0520b0f20548503619541800302e140c1040e15007203800e80343c0004000700d41540c0e201c40e0b01840c1c1e00c100148041d52406000079a2401110307680110004007241081c022406021404094080204100d84912901210300c0d9a8110209900464801080c0000b48503101360b0014203e1401c50b03451600e513544645003074400708003126540ca00c42040c06050031243c5022000d10014140e2503010b0300a03d13191110790110340b42143c001d44e00c07500c2074110303511442e9084802c1a9402e002c00015900e15500e9400603102480360940d0403e202e664030132000c0026502da44042e100354400d232420402d00d41c1c0203000710391880030581c201c5c5001c00e070800103000d128090421581303c18800d40c48645081815001882c12090035941003002c645520303000c00800001ea8110845800b42160800000e403814510a03c0d10020000c070110b44454140414065900b03a0042a203006050212090880d911051035640f481048034800002d003030202c010480701c0700780c02000e0142c2c4003a511 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 958541987 1250 958540737 958540753
    0x2604020f041a120109050f1207140313060c03180806070c081306020705031c090b0304031707090603110301030215030618251704150e100506040c020609 67
    0x144002040410001102038140300b0141200c1d03034843e240d140c181410b110000c40c02da207035894411705d02800510114040d400408030724003000ca9180980d2285038024034030303040b144c0000b03038068250710410500f0010050180350200700075401c06440000280700740d440d1501035a0401016142c0032135800b0b51002e582202001c50000707031040040f511214060b014841c0340c02003511a0003c2c84071107900c81409608040f100f017040b45818802050009035031408000d806184a00c000c004000074007520041c040044003140505220f07250500ca060000019880780d41003600d0041c003504801c3c429480080d051078040c1c9070000c510710581c0e040307980c0502302181c1c140c005120079046070002090150015841100e519000e07031100300b018054041c0c026650000b85000003124450007010b0070603024407907090304092003414030b4801a81e1254009a240100341154580c80c40500041c15080905100d103050f0080e9805184d030109000d6181100c04001d4995003031070503a2500012209400d06400080c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 958543237 1250 958541987 958541989
    0x1a03010506031f02120405010e0105011e15170708010504050105030d1223041a060a120b071101020c060105040b0307030201050a0804050703080703080f01060206090a0807050c0409032604020f 84
    0x59901e01d110f208882c00b50502c282c2e6618400030140844068443d41c0d110050050310302da0030b220703e40c0988054000c001840492020f600344645c0248560304034006e006c1d20021760948900301c032032420210004080d06c28104000c00400406083c000c240c420380c0780c41d0000480e0b03e400600700b08420120340318081c4280d00742030030100900c03050060900010072901e00c0d03110798201e00d00c0b043c4920b00c2505585461028040b155401c40c5004182c580902c540020601c502c84d803042a058405522680c0d40c0c040b95901181140c2840d07015411001c15070006c81e448844036000304003e8180c52041da0100910780744c050030150340b0400c80c40041c0c08210100105050030f407140140035030050240088643c1c01d0755aa41e090030a900c62081580018008030600c42040d8011080900400091000b881541003400c00351b510781d902100014800c0c00300203508800c00c0706c20300440040c0040180b08010300c1e1400d040c09080c000d180e0b14148038003c0c030380b840d91802c0215500c9140c0070381d4001d0301403c11500e00ca0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 958544487 1250 958543237 958543273
    0x109060912080f09031204080118170c10021902100203041a040c0b0316170105102f0f10020f04090902310c020c090423101a0301050603 60
    0x350f9041c203052001c00c1098101c0c1c504004018440d0411004540d560f03150042c0c0c2070031151114a001441c59050101f5404a580642103071f02030081440c90540c3d50a007881c0291401a20640d1850202d0011401558150400c092000491b140b034090ba11540c0c4041300caa402c03440704450041099103516446100400c8603034005910600c919081d01083d074840d20102a65041240d45071401c0684003150070311030340d20280220b20f000003000c5000c900e504000000310b0315122000c207001041181030380b01c0d500d660040b10b07040c070340104a81040006214a002d0315195200f510041749940300c0d0050f40508406a44220b80c00205080750f00303400d00f03050284038409802ca80e2411307640b0803400071140015071020840450311040706004c9820700f40d0078921150541e03003940c40c0c52055400500c1503000795114250f1a99105900480c194203842d80900b60040300341001800400c3c510074504080d540202c1075000001c5000a80400525402c1d036008042c242c500440c2c48035015005803503216802c00e480 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 958545737 1250 958544487 958544497
    0xf01050304120e0111070b03150d030212030c09040e2b0c0b180139020c0d0515010612050604050601020a15020409360b040b131a06010906091208 64
    0x14580240c0411014005da460172206821031070a00750004103200070100c0245e04003691810030b03549011041441d8a010351140e040d01c41c1220240700c00400a80b001d51001c6c115214200e00420400c1268046d240b41660b0300005885c0c04030710452114810310b9100b0082c81c80e0450710041e61252043c417043c0c0d0b00c2601d1041c0c0030305403c040040f5180c442083c0d100a00400007600320011101034403002d410794078a0300910080e0030000c910390481e010051540c1c041075003443e051055800c04c041005920f892854140e411248110380000f120000c40c0d039560003082601380c0410749030244080c0d114401004201c0e042a0390306400b6071701100c240703000640440440c81c00e1881c0a400182002d035a07000980560341e1450221005401c802003049241e0802e10f509510b0354a14034110301d5002c241e6588e00c0e1040340151015200c81c80d071200150031503001c00042400c0315802802c01c500340c00c2520703c003413400d1400d42d52140818007815001c200e440c417a80c8a03008032440c14115420200c10341e1550401a409 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 958546987 1250 958545737 958545739
    0xb120a031e0e0a03470f070203040b0f04120507230d03030507020106082409060903090112061e050414090c060a0e09040b0f0a020f070303020c01150f050f01050304120e 74
    0x9290404029002990401600002d664560381d82641001c5c2c19615110082c440305040341400c0900c0000b80e400819078054031000c89c50140c0e0398004648226050149a101c42d040d041c00400080800801061400448030090f211090b10540703151800010f00d42d5031451504565030701201c0d00824440d402054102c6828000010a00d858010180c2440903c0514103c0383c1e81e010302c0100c1300041400c65a6009401e48042d20583c14064449600c80c82140b91103410400742103c00300000341c0c41d0741300f4802001800401c5041050610107005107503403910415210f2032070b001d11540425002004030f4800d141d050003400000c0c69803020400140c02c590018000c000055441c0c00c0360b92244252180901c0c040d003c0800603103000c0d8100e404940000b010560658014401030226040c1d0f502030320328607a2b1506015031500103c0e2015401001c40d43c2c010056184015030001e4040407540c134400964800361000c0409648950056845100a03078005100d0b143d440014640c0d18070a80c440d0300c003908 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 958548237 1250 958546987 958547033
    0x18010c051e06010902091e220b1e0f2404060309060f02120f090c0301020c10050105101b081611010905030c0105042108030f100501090e0a0b120a031e0e0a03 69
    0x3248419017100541c01401c0e40d90230741e07940e90160300f4501e80112210780d14000400503903c005070600c00b2a0220380c05a1841e80614100c1601e031513904281c00808000030401c2c004076885695a9000a010b4085984140c91261a0034002d0a200050780201c0b44840e02c250031149403500c07220b0b2044c1540c24002c00419960140d414104005c1d17400707000402c4242c071004010070603098000d840404039041a804070b80305140b050140b40310541c0141031050144051070b003110890100b810940c0750380c0700d0144003180100f1040740c80b81c01c00000030441031800c0400c2c0e071862401501d07042410ba4031140c1181c1c00c0d0110318203000401c0703000d20205000407106946032659024220941e20091650030588041400300036000030003080905480314440142401d103050341035180741070011a45848061301c50320240352680038084540c1c031440340c04821031896108481020201c1d04006007502c2803c070f1b4890700810b002c03000c0000c4a00c41c106004903000c00900c2d89460514560340d0302d008808040107402821 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 958549487 1250 958548237 958548259
    0xf0403030e07080102070c05090f070f0903020d05030a030c05340b010f030618031d1f1d030703170c0a0213020706180818010c051e06010902091e 64
    0x104052182c407004024060000d03071560058a0010f03414815034000600800b5800b04125900d602541c0264010a9034104840c0466941000300c4148019400c080d4005030011264010410008002c160f00c07009503904000350000440201d0f001d105100b44901140d0000c0304405c1c54550345e040c000580455042095040096641c910301100001d902441e21001c085000700706100c43d80c042d2511186201c2007a46144600c0e035805000168001c501c26120006c0104406031038958643c100f991403080c041d012045544603030020401030910042ca000c0b070301c56040061407400c0000d01001520792008910034203c1000404244540054016070594414a1041800b40e1141c10b081524480500c2015a5542c85030920b0811f642007008030f0001c503c08980c0600201d907080040e1800c945100c041d00d140600d044004940c078840d04203016000d40501c184029a081e425900c01d15440005002d440c0303160390710f03d0090102e0144c8181a60800c101045103000c03140840302d552804040145150705078 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 958550737 1250 958549487 958549511
    0xc032d01180905330606040b0715240806090a080c0316230615191802041d040c1a04090e070509100f05150708161b0b030f040303 57
    0x800490481550303280d101211410034410003941161360142c122944007020b0400c42c5c003042d000c3c415032084042c1281c010500d034080000c1c620b80c0c880801142601888110b00c5c0c2220140e16101a0b407400050545107100090100000304060303104005032809080181501e4480810b1a030001101b00f60a000c1006840e20003034280c142c0032000e42c00b40c0305405228287e041c00b20124a40d1070243c000c40d13480b034010047d902d0340010000710880c01c141d40250640101c810b0000c00402d05400c0b121800c8a402811030500c1d8880e03018000300d0724410740c14640000b5405650307001da041034402900c17001c3c24030024051030702007402d01d000b890b942482040c50705503614250000c84241c0d4419407240d0b0000c26041045240004215030443d00030910400c03103915018500d4550305251090500618031081c0020003020010159060640c2008805503a144522a049980304c001e180454940868180943c003842070340903000103407201500b40900d1515003018400807030900a00440c10552101000082 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 958551987 1250 958550737 958550743
    0xa030e1204080d05120403120609060311030106050105070515060d12020a050f030f220e160809031606051b041d0a02070804061b05060c032d01180905 66
    0xd0042065a503038581e41401c6040d401c0014620b483c0d01044400d110032039442c280c1c183c3c01c9400550509140500c8403030302c00120054440c592160340c0e141c6c68803100000388104605084941d01c0124020130405407140015034090040b050013620320307031008002d540503819040140e500040010480d00d207200e50b0b951202c030281090840e000044c0c0143c28a81c0422404000c9405001c055001542c2485036843d1a01030500400445458100000031010383c45001042c1010103405030b5443c0078014900071119038040c0101c1c44002001441e1900041d00520010041d01ea29200a1450000b100c0385501c0341c5000c1c00d0301400342800d010002d140b0b1961410b07180e00810080c070407141160a411040c10b08820a001c00070f024007040f5004001a10003d050f4800700e41c10796030581814244c0c940c1101e0750b0001c2c8224144020f0040c440e4806200c0403452090145100341c00520580c02c50741d0003003c024070402e14142000106024100050042a00500d440070ba6119488000100e5440c01e440e1103203 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 958553237 1250 958551987 958552003
    0x1603060f120b092802130b1f1103040b07120302040f090b120a050708011a150c030f0403060b0a120b07030b15120403091a09010e060d0903031e0b010e04020a030e 71
    0x1004806202c81002c6050031800c1207100316046d5010800401d01c0001302d0344a0702d2030721921010002ea024900000c50052205102640d01042242d031580d0300c52980c48040d900910341920382206800c1d80004441c42402143d0a0b907102c0c09495000c940b03031540c0e0402405c1c00c07142a40c5d0045108910048500f0104070240303031907008600501c3c1c113700d4040c902c0e0031902c045086048034040406100c1668840144001c1004d10410165507074010402101d411406030302390b560700c3e00000141c008280901c90700001203188003210010a0655111f080d04545400d00400400b240b9035407000640345030081d44107022051000e803030b8080c40100b4a0b0000100c1d03019084002e60b54042a0601041c036907c0801c1303c0180c902900321541d00041507001e48070758000c10789000c0c1045013164030300101e5211001a0b500d2020100014001e180c40b9103000790150084000891103400f02440024500d10b19020340c0c40d1500301030b1508035442812506000295100c0f0ba40e1400b4191540000d10354440200504a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 958554487 1250 958553237 958553293
    0xf0f030a14070207060203031302040615030f1524020c0d080d0b03010b0321040b03040506090c0616020d060608060c0a02010b010e0f0f01171603060f120b09 69
    0x54112041e18501d00c9060300944103030215032011409028403900082165000150201c1c021090910b502c0020042d160310b401110b0004a410802c0c40a160582c2151a80e01d07020b030801e10601a50b4150031014030030302d100329018040300e10074402564a040c24690074040c210720507502d0322101d900220b03940c612441e100303c581c81d1300001c08102c404a07a00c00e01142e603804500a1082c500e2000000b030b511034041d8413468542c40701d482c4081101500d4421100100303005c442041c1c85e0718250900b07984541c0708a0f485a91070054001040b01031030039201f1100018141d202d4904c03039800507001c0c011a01900801100c0c680c2c0d440d0380c041500c0320200070f40c03885680003041142d0f94020600000382520207414019041c132011015000342986d4003500076000440940e01d01e8085403c1c0d4004072050b02644441c80c90250126060001c0c42c3c4111414440e020129201801003550380c1c003c05a00000b248103081d400852100301a0001c0c60200300d164000d0400c608407851001c41015500c81d110003c0851 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 958555737 1250 958554487 958554491
    0x3090509090c13060308091002030d1a0301050f010b0417010f090b04031b08070b130c030c080705060c030a0809160b030a0b03030a0c03030509010204030f0b100f0b07080f0f030a 78
    0x1500e1403074400c043c05401e500107a001e00c02c1e586141d0f541241401103901040c840d628200061700854420000d03508551034000c01403044250496400c0c4444212000c454040d500b0240010405010031601504131060224030502d400d01c2c0181e0341006101a01d144021035403551410038401e030341d0703000e8001c2041c00b501c0ca241c85814a031030058845a00c0d0b6880c4d00c402c5055001000100d4040c1c1c007130340c24880d04480300c0301040e40c0381a410110345242d03020007441c0100d062808818080340b40a18003d85000008032940030b0389410811005d030040403401c6407907a20411228130070611a60f0709680101520b0115001280301b24281641d40d0000d801c0f03868684000300401402405901507980081c0c001d4000e1843c15505010003080f01d510102d01900789030329031011400d060707002d40c1258025034120b0500b05012400303103003a0821a100b92468840105e5203a004900c0512005120302281c10b052080c518140c2c03140e5400ca100d4200c1508051550b006000c0d89007640c0d485001035108145503200 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 958556987 1250 958555737 958555753
    0x1f0e070801051e090a2901120b0a050f19030303050912040e0f060604080109060204050301050903130621020c01090203010e0c030d050306040e0a03020a0b1e0406090309050909 77
    0x60203404160300c980d2192802c9210205080722200b41030406070819130301d1840a9030303940c1200d0b02511803201e14000064980350001c0a11100414202c410f1001340e0b034000c1950102c20318101552001082d056108400001c100880e14000c18200c030242000750074411011440640000c031400594400d50200361584100908000c0034096421800d1654603040c0c06c0c9400c0c582c0400003100d00500c5030308640b0300301c0c003c250302d5a944419607000303101d45d000030300c07811045140c900040d401512840c0d01a40c2054003180d080070b00403041d550150102810b12001600e01042140e940c1d09507594007250307400380fa8500e4083c41d914002020b10080900012961030214810326003116840d81c0450380c1e90f006402910019034022451091034900fa241c0030340c41780c807101c000600a02c480007803440103210310141c5070100754020440b551620f0240c81962000c4c1e40362148034102071005d5062100280d40007001500241c0d103a803040c458a400ba203014940c0d1a21440404c21040e001d442c161055400921 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 958558237 1250 958556987 958557001
    0x301030303140c190c1704030515011409070309020d0f1104050f060d06060807260303130602030903070b0708181506060a0c061a1c1104051f0e 63
    0x12200368540c8500b80b4442803914052982280c00b608001d00200c002c68104041054810269001c03030130b42218030310204c03c0c84448070040d1544640320440c4d0a00407201048400e01104218034101c8000100401c0c08aa480c410440001c0d0001d00750310074141c0d541d1904003d6184c4010100300c0078071450352a50302e005c03a410310341a92010080302c2845503040500304490500304c41d240326041078080c1c40080c1c010600d460702c04007605654020112612548000040c200756214a40031f080c203112003088445100119078a4691204861007503580f0525181000060a164002c43d402a1941d0649003420019511485030500a490800000340c0501c01c0c0070460f00c0503107a01742d003138076540c008100800003002608030201004021074422340c0046198000035020b0209040f1066100d2020007985203031290581409000002c028011500d0854210100440e000c01030550f941166003a0385804815080001504005010070200014042d86a0452800100c04005803070382d00ca402490380344c115 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 958559487 1250 958558237 958558241
    0x3040308090a02280308030a0b10050f030606070606051905090c0a090311040e030a052203030203030f2d06040c030b06031305070b0c0c120607141c09080301030303 72
    0x1030420a559004002c406006a40700c1c81c0d100140c20f0f07103001c0c1c2221465124620100e01c48590700207094050700008110403100b0703540c40810f0450b8200c5264480184004d400c4030749001d00c0707244090078182080420001e10304000902482441017001280d41c035140e86c041206000b214810001e0a06046000e002916040140c1c540c40f52550200e54200204140018441d07001844042c140e80c861100024040e242d5400c0144461904400c5a69920b1260b07401010350340500e42003131140040074031205001c0200302000c002c40e60107034000c50458030381420b5100742e940041e12a45105200719055034100e90440007150403802540c0400c1c02c0c600e80700c005d0006581c1c0e24103c4404042c60901c00b880203542d0300041d260000d450034041541c1d0096440d02c40d290086540007044041b1020811000b001c50001c0e1190344e44a0a54402c41c2c0c0c440c0241040703035600000c1c1c1e150000b1881c201100501c84800700e010f0404407244041c0d0110075401d0120500450304003840a4890850000041c0103144e058 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 958560737 1250 958559487 958559491
    0xf0d060510030f060b03060d020904140a03260f01150e040c02160506120c0f040f0f15020105071209020f0d1406161b0204150e011e030213020a09180203040308 70
    0x5c004180f4620300000001c581c05000340e0020710411050700460144940d401c000c05819091108a4441e2251410042c00c80c46c11602200704900a10b40400c492915130300601d0b00800805540139010f0b400c10110301c111001111031641006811850540d107542c9a00030b8142c81c02c01c0b17401901100300c00d544851351031a5130b60002d6002e0300c410040680307292010418aa80403501d2850181c1350340801c1c0c0303c010345200d25401002605c803603581c0450a0391205071311000700c0b1995841450f5040c201201039090b00c00844c2c0c4000410341c0d00881d0910307440320350410a20540b000304003656164070000000c280c071490f860103440c401d10b641d50000188008101c21608013001ca017207410180391000008042888111031b0010a0503220080411500c942d006955801e03071090540f48010345860420300b0032142440b90807641c0d4044541c1c40c8200b40c0c0e04a0b0b21082e81e330050601c00307141904c1c0c590640a94000340d040300c1007101d001c04c0000c0c108004030b403024005034400400760f928207160400510721440 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 958561987 1250 958560737 958560749
    0x130605031803040b0910090905100e07020115030312140115020c0a080304060e0414040f05010606091d04031103030408120c1611010504231c080f0d060510030f06 71
    0x1c00060180e050000191144000300301c54011040420500c1180d007c4450750002910604000600102e110300348441c0c2c041c1c5504554031041c680c0e880e8801c80c2620020f100c420288410b5800510109118000e003c4070914880404920454070303800d030049001e000da00c443d40210148901a0b4519414405d070803a104040f106c6c0070350903040ca20752a480c1e00c150710034001808110600030407141c94503080304032165214004003e580c83c00e0305025100902c0100c04440a520707200d000300e070703460240d9801020340708080f043c4038400e01c0140045200300e001034000d0342070141e20700e0a680315690800056125904ca0b00b015515250001c2c289088050003802168080343d09228070008825000244020b582d00015075001e41d40202005940e0740c4100d8210448483d0503201c2106800d652006506a296058405184410f055408012812411a0014a52101001800742030040036015000311b1001040000312560f8900004543c40841020030001c00d4503080c240400e40c403144602c0c8002d180c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 958563237 1250 958561987 958561993
    0xb150f060a0305090c310906020c0d1e09030303090501021b03041e050f010309030908031b1006080606013c021c1416020402040f031e05211306050318 66
    0x220040b07010091804441c40c6d06100c540110328442c4070b8003207400c81200d650308100708541c0d50b55040a4641c0b1281d00c0d11010001c02c2c414612007640848508030403603d91403c0e92441e0026003140e908a001d80804130b800da8066400b848140c0d00284914000d80d49200d0800c000c56865260042c600d200c0a20500d03070b01c00240c12040c081245803030b541b240507010402480c0000c2c074407220b4502505c81d52410340001c2500c0c400441d02c9100503001011001101e803100b0121561942040400c4007074444901410207150855800b00360203500600001d1000300340107801048032000e404100e00c11421004070b216840050320b000c0141c1c141c05015038140302d02e803060b0341d4000c0024000050002114500000c111000024040100c801c01c42c0114010940c01130066648075600c0546c864011410b000a8170039510b0f082c2c41224051f9589a440b0700140d0000141114003001e03403d6508905000f0048481c62800300008005c0c1e68000c40008007820250312000d40701d050100b0018000c03020300c200e60900354 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 958564487 1250 958563237 958563259
    0x3051501154407080603071703090d0804090f1a030d0207050105030714070f0c0e10031502160b0109060f030317090a0c090f050a05040b150f060a0305090c 68
    0x8211107608011034000540c5242a4800d0349511800c0708802e045105828240402840400c60780036180b680500e00031012140c0481d2070302ea030841c91100e0481c42d404280c0c410000380980d0304040c106040014060029541040e55070010041a1641c44000c1280c26507282011005e001a0100f40d9048480c190000e050300c000032980a941d904241c015036060220100000c0e40740ca200c0c0601c1c11011040d00f050b0781e00c40600e4a091000b0365280402101d000f0075100700400c400100003600d610604515480103d91071540d00e40e42c69004110744d212400c2a020400411114500d010303284000d8402c0d4a940700e1980f61415903401c960094010603164a40142c08001195101d5012224080c1c54643c005040d21100d01e02403404203c004000e100b14600c0100099a0505521120141a82203424003042d075503003d0041c01c49004840040203c80304002080c0342a001c135125451080000e002907107050140c00000f0b00035040001c00030b00180d1200c0800611034400c1c4421190140240e03101c5143e5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 958565737 1250 958564487 958564517
    0x61309150528080d050c060c120a0b15041e050a080a030516050d020a03020c1c060b030717070303020f0c060415021f0c110c010212130305150115 64
    0xc0c0854124221407042015115602d0581c03200d0360040190100b21400f44890060141550308030780320020060140400040305410b1003021681003c0c1414010301550342d81e09400e0005083c8842155080030710707408900c0d030300c8100d600200050800914112850744501d4080c0ca030040043e0071003401018081c6042044000004040c0540d0b0303814101f050711030308900305805c1d83d4400d900c00940188200d400c03c44486030046003448800313001e0742c292040f400c3d0500901010902c440c001d07075041a05441064081a0a0390014009210060907100d40aa5400800c644042101d81122841e009580d04008142e0100711900c04501600081c000340c01040001882034003039403140700040d004403403241d0103480c802d2140300400240341902c00f1903080c0780301000d00140581140c40e40030480200e061000d144000076082a05d98050b401003105488012004483c0d410401d00501141070121b00400090824030080340c45e0100000d0f5510603600d84100500701101118500c000e1158852421405c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 958566987 1250 958565737 958565749
    0xf05120c0a051e060a0e1912170c0607020c030c0a0e060609061902010b270406020a0207090912080f100b07030e100c14030c1b0f0613091505 62
    0x8450040703601c1000207802d80114201c4030700504095500040c001170070045e4542198103040c15140c2074401059400340c8031009191803000703020745059900e01011000c000385100040341c0c41500ea41d221242401c03070701c00c099450321b1410381d1a14096008048030b410f080c00c0c00c011128071101c0c01c541e252030aa1801070204180344001d801140a07130000600c510982c0c8405044589020091807050b0750101a500028000c151205400744100301c1e101c4103400c8000d45542c03c0b000cbc4a00e01c1c0300507185486543d1050001d40c0b0800024041d030045400014012002e03101c2d040406000d0044c00340410785070710004040110040003281200d000405000400c0482ca54400035500140f0310547d41c2c180318141a1400030054860341d81c01144641303446000b1f58820707074039001c00d0b224030b12610180452200d0b160b1030f4000c0f003001082540c0806100f0174880da0140340c894286c0710103031801c0d40241515020034440c2d40400b0f003281c80104924410007032111940b080f501100040d10200b07084609007000141 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 958568237 1250 958566987 958566989
    0x10050916020309031506030106060c030f03150f090222031502030403051e120c18010305040f0b1e1506180a05061b0610120f0f05070f05120c0a 63
    0x3800140016200d0514020411107250a000500b22040f0804030310060fa00d441c01280e8140c000d508050000503c0780c080c907943c10829605031030701c1410789101ea00c12801040780c0722916541c2c40100c60300244480c0104251005481d4414015a592012081144030016400da2201c0b201203000c0081010402803943d102d0381d80000b210141e40ca440d14201101c01d4042c100322042c544000c0c020700d611028188000b01a11107030f904040c05e80e680c996481d42c409004858114035515a508400440c5610a90019520a1140154000c0d00c0402e0f211070514410445113402c1d0400c010682441c0007035152038050340f00a081018000112108000c038429018074444d01c42141c0201d440c90105948a09505d40603110241c4030b6a180c103114844124410051403d1000c4c0d4050000462070300c2810f034500c0c0e4199480840107d001c40318681d42c141c85440c01d19410b0f21142e0240e03102000150040c48460010a40c405048076054245820840301e80041011281d00e030b4000c0049001c1500c5400c030240c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 958569487 1250 958568237 958568251
    0x10509060f040b0a0605041506120605010813031709030406080c07081c020c0a0507050a06030203040f020d0221061518012724082107020f1c0b100509 66
    0x815030f48505109001412032a01b0103503200b07080c55056150481075010071421610a580c400c44022001d04c59641126194054a03001070121400126840d06101a008140740700e890f042048211643e001d4040c203400b03a61041c025040001d0070404181d0000e90142c21140c1c000c0401c3c41d211069580403224420500c03040c01504035203c00c80e0f4007495590560300c41030301080a451441c00c0c586001600c4800a001c1c0751711908402d9404184c0703500c01d20a40b03114580c0711820000100b03080d020804110101c0c4012a4001680040d02c0303502c08541e0111241020035030000c0810b4240080380d4003c041d0341840603406002d01c072440c041101500000f090440c0c0210307030000340b81819018000032400800c0806100641410b030100326480f0038030b11034844c0c0f8403040c1410481c40d4540b600c007a1101d0405a406125024500b685420400c41800a24a0501c000d04805914203203501242600b100d8440811100741240c0c105001d110690040b650b02c0b1801c1e030001480381c1d06150001704841b9010b800340b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 958570737 1250 958569487 958569503
    0x90b0303040b12040c0e100312090503070b0c0a14070503010c0e09040215040b04032109060c080f040512060411010e0102070b0c3c0105010b0f0310050a1502010509060f04 75
    0x804c041c002c0c0e80c00d040c070207003c54251403c06440e281c0c4800300680e0540c40210790f034001034060b000c01036224250441c29150020080e1088a240c00310131142030304112296030030f0f070094060841c0028142d81c2e00300180c1850001801c4c516143c90205801c442245050340184503481c8800000395903000c00c0f060b0701590403628000e0200f01d910031402140200c1c1c01c140c43c0840f0015000c414410304d80385202c203101aa2030300156568040004884c994028402c02001c40c2a9041180c002550900a007074030761582d40350281815556000214401900041858203070400341c14041070100c2c0c055052180d4800b8280f0804500f10040004e59a4180740304d081121b04000c01c01803000c2c441031108c07031030080791400000002c1209841910444024200103038003a8441035440c0c1c2e0405060041038100c408071101c103400c02e80fa07502900c0048d48014414007600310362007808a103e07520031101001404100c99080e0310090341c50b2000e800c4a601412010481c0d00400030004030902c0c800d030081d8042d0f804810 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 958571987 1250 958570737 958570741
    0x1e0c0d11072c150402031305160f0326040f1809051b01121d0609011b030518060106030531170724050f0709031e050a0804090b0303040b12 61
    0x2a200320080c3c401c011551003030001080c8404500c0c58017950b103245020318240c902c541c00341c1e240d101c1e0401d45131040204610001400b000411040140200c0d200039100f2801c4003500c2c0700000c1e00150344103400c10941491101070601403408401d0084000441c0600100318501450326581d9039038888000d125007407118100c0040690348512100200b503018400f0600001c003d105440c5618001017071111614400d05000464940d030500500c051040040030121038403c840358214050f103c014050030000c14a1010801c1d0604100000d6000302003e81e030000750741c240040705001880395805491450140da09192064090145541c04029800100c1c0d480c92103106c3e03102008e9001c0d4801c094000d601d03c0c04012040c2503030b640d0f2040341d040074080c108480e5980c0807214003400c0003a18007800180e035543c0c3c00d2001607001c00040c0c0c6248046100c4080c01039181d03807036601e8080100710403542c0c108081030400412070720740104649948220302031428203040c8500d0000354022820380301d400b4001800 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 958573237 1250 958571987 958572001
    0x60b0a0c0b0a29040b01170a0908040e040b071d010206012d0e0613050106021b010320180901080604081c0c020102030f0114061e0c0d11072c 62
    0x10020300c507245182c00728010800500c3c010982d106410580da800743d424059060f601358410501250144104020031106440c0d40140e007005000c01d800c01c44150a0411020070100e0282850a22880c480c003404845c40c03030300400007000421070034404070354a0b041c400c2030748050703801003011815139004607110b040043c00312041c0c1d5515070601c2820081004070100200395003a549081903c44c207400d88910340e60900000658044038402d11950b40103070003030084c204841c00701d51000880250149004141c11200c1c010301e4520719411a26440701c0303a00080c69682c2d80058070344d81014998106c4100301c2e25032400c6203035a241c02005200030050341e0005101c2c2c0b0b201d808880303050300d843d600c05410030001d840c4041c064000c2d0300c02e883d91a004411580001000a1548002c03590f41102401017810b1548440c0f00749900c804000034041003080510081c240313814100140030000310780d9a1025052a101d110181c00c040c846d0f00841040c03005660081598083d00b0039040940105054812090345d07030380 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 958574487 1250 958573237 958573241
    0xc1810051c0b2a0a020601050a0b09010e19120213051006050705100204060e040506030a0201050d0f091209060809121801020321090721082d03010603060b0a0c0b0a 72
    0x140e0007421620340c50070300700200810181650104da0317000c450280e6200c208006004c80d1510620a000c6000c01541c291940310b83c01040b1a2040540481c0700c0c203045404002251099400c40c00903061030544090561825162108010344c0c28101086503040042c401404071141c0e02030b54040c0100002d04104204040011440420340440b045484136210100140440d9055040510442c20a4040780c0b040c54003003101c09000d54140c45035481c00a44a0040016084401b100e948095842c805400400c01483d0748106001003955032803045818000e000d0306e4030101600e2458140d00c4805250040480081160b074600305d0f0602c040d0804103d000101d24620a0711540c90601c0c0c0c41d0201903d0407050003001c0c9006085440c00c9c0d4103281d4540e0040405180e01d1024cd100952101c0541c4003c03403240e0b4001c01e4804500004280c0307400c00c00f043c1000b0341848148003008180000010050350307a040c404c80d0060729001c4030a5260000c0071000078030103c2900009030100301081d020801c0e42d00c6d25 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 958575737 1250 958574487 958574521
    0x3081902070b0a0c031b0806040b150d0e0313181b3603060b04090b04081207080601120c030f06061205060109030218090c1810051c0b 59
    0x1010035581d550440c9806801810292407603503c19040c40f851203071981c005d0040040100d1194800d4004900200d4210b58208000c0c0a4a420654910034080030740c03070b81d902c43d6000c000d0f030303042d11170396098118a49070440741c44c0c0c0c0041981d81c10031301000362070051013841d00d000c843d8031601e0000c62344004107044000b0f00e55407000700e40c40c030029081c0030101d03900500c4d6140500b0010044100380e441d81c440da4801070b9045540c0003040f00c16002300b8000100241d000c66070466010308009400c43cbc4580d5400d180040584064130000c4011a010800600d00305026a00c05141d14282c80241003000c00640703000c41d5800d1100d034954541c8001024144240d05c80340c1c2c0c02c600200180030055444001074510044412410a09402d040c00220a54090440c40b01100e5000c0c02510340c900034003140000100380a080d8250902440315178140d181c0e94481d03400c4400009600180041c106551050320b60149507210300d014000c01c902c180004c1e214044c49060071a049030221850b0341e6280800454880c607 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 958576987 1250 958575737 958575781
    0x23070305100314030f0a1809020f09060d060302030a0b190209012a0b0115090e0601090b07030c060911090906190b1c050307031d030318041509020a1d09040308 70
    0x170101d0300c03c401c25031044070307103500250040d00c8549040c0c4820844050b4071800e034824900c01010800000391382081d00040c0b040003c01000010b0a9071a035000034102016040f040e40d16a249805201c1200b14a1852140c2c40030402c3c4110b2501101d0400a00401c44000c0e803100c119051041080309000c0c80b62400c907000d68400400f030402c0d80c440045480011303d001c000c000103408650041001480c0e5282d0034050071050711168032851502c40407011075480950120104040d801283c800140113000f0703003030002d00c10012032904104030028040e0030070005050700440d5110105111a0140100d5071400b181e15500b404200e01040303802083d0303400101e030b80070303d0002c04508807503050040c044064044a4032a0b50b540c0030620146120065102d149074034183d060300100508c1001034100c101411510300050f1000c502284c80d50781000542d44513500c40c81881e0b400164078201103501c40c4202030321149006c444c40c0d41c2341d41e14010a0041d400104010284000388000c01c1c407e009099000c0e400c140 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 958578237 1250 958576987 958577017
    0x191208091f0f030f09110d080c010c020304030210030207030e0405061818010b10080105090a1b020106080105090d05030604020901090305030304050d17060102032a012307030510031403 81
    0x105044002c141100c002c0d118000a854503c007142004454000c00d040c0d96000b8400412205507141001103040154030f081750b204504000d4040008801c3c0111201008a40c01558449146005002c1d001c0b5464001c801010b00c104502c2c2c00094001f020014400801e03640002d0507990000407d03082d180031384080090380d24139810040c4000c3d00304440072030101000001e01402c09004180481e40240841880120340804014000390074006241035000030b0b105400b140d4a150030405544275a641c0201100503511502d0510000409001d6280c00074020340c0181000600060000c0c840c0c0000f030700291080e80c00142022140c1c1c420000b480103103801100741d07035803800e251801035a40e0501040400210b11201c1c0035501c201400054948100c0040e00603603c0c0c00c0c2200d27014150105402941c614658032001034401540302403040002128a0750b002c3c3c4034201d0f90500480d0000e1006000b50101414501041145c7d5403800420085a6004040000e000d480102c03841c1180104465800010 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 958579487 1250 958578237 958578289
    0x140f01020d0f09030c061104090903050a080c0414040f0b061b0111030f130311030c011a040506030703030f03240312180501230c070519120809 63
    0x10406500800841086240422400c0d000c00700d007400707441c003a03100500403030141404100400d0094100942c10341c3d000c010a41382c03075110340d8440c0c12503040c00402d800140000c03482c6001c81750008512783e006144410128189403420100e01c0010380030f0380c0703458010382c0c81e00070003052101990030000901c2d0f001084180c83e80603420b48118072055801c940c0c10a5800d00c18100c491a9249048a0240e4141e55405001e56610f03c000c14040784454821810002d42c03550042a4582c00d101810158100500100c2d41003600300c14030820001585603a4410f601d0712041c404a40c0d400505142240e0303040c00c1407018102100e1080c3c00402d020300c036200f0118200c41805580e142c41c11a1481074030301c0345214620144010204440c044400015555050300e12403040c0540d6004240b00e440c40c0e000303841c0c0b4000d14a800413000750b00760428088851030340e014100500c0f00740f405060403100e49100c0070810300714a160506501311406d280710040d001c540d001402d2403060b116a4203a2410310407440b8919540 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 958580737 1250 958579487 958579513
    0xf3807050a0c061806080417070f150b030d0206010b0307080415060303170f070801140f030f0705030c120d0807030207080a0c020a06030209060d050c131d0c0c031614 73
    0x41c000042140c1c04840d24004049201400344051b113015540003040c00703800a0314401e5400481e88040415144001c600d80c04400141c0907255695034441115070206045103060b061510706080d8003040e600359000301c030050048014520980b94468420310b0101302c240c27200d0615110301c00c2100d484c8035401b414110040181900b11180030b401300d0301d8020800d015900d8107075480c1d083d00f00391440380008590000400880c1c5c0e0b4641c00d40300d9010000c10384001800e01c580047e203080b0f10b0207482d520300d40180c0c0c1e08100c0da1809010312840341200b07407500510300100c90089911900e01900d00310a2220a0000c00d813020310030360584038265444510079603510310819020705007018480c822071042031410004a80c1c0391081c000e0356105c40e0085c1005043c10000d2480101811008280302c00071501804003001c042d1001c0c00340350040c60518105511400b035440101c1400000614041d001107040002da100168004121103900382c9400030900351104030700e007215151102850800341449010003c43c45 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 958581987 1250 958580737 958580747
    0x6180709031716110301020d230a02070305160c0510020609061b0d0e10090803070f020c0d020d170f04061d0904032105010f3807050a0c06 61
    0x1600d00940800740d0303248946040d1280b511809500b0520b5118600580d0009501d8a2204000020080026040284502c100c4045544007050140d404080268420910b09404c3c24030b1f80210b60b41038251308e0100d598802500c01d1046488140c2940c142401050a114450a820018040c000e002958000740d00304020361700c0209685130002c034090701d00032503010714a081c42c1c660f0100c02144c155080049402c0181c0c005c1103e400003000c140281900c0000e00151403254401d400d100d0782102d42c0341e0421440003400d00442c641000c0656004480030700d0345588542e0381d1a45c090741260038000204641c60944494922200c01e020b0000011a0264180c41150090300642d10300d0756070200071001e14501c0441800c0f845d1102d0345c111a0000101c2d000c2803150100c200301280b031403c449450041582c150003210026440420018070810061100d80c14850354401845202101c6d80d0040201d8408010880080807455182c8140019208200001800169051600540130039903259946034041c0c5 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 958583237 1250 958581987 958581989
    0x51302120307080d051e063d180603050415090807060c08071b020a0e100b040b0406080703020c120c0c030f0706020f1b04090f061e1503050c060306180709 68
    0x1207440301c80c840070302c1c1b030411030b0445100b000000c1602014010903a14500e2440c1000d81074104264005042d08400c00d00b80800900c0f10300c96541c400e0840c84c1380d1003902011485800000400d801d02c0180030220f80102060a12a202d5440004800b4142c0ca040400c0348a0321070010074290800580b4000750346c10a02c0540724101d0794030b03038401e02221b400503c244030900c1480254001d0320400300380910010710041580c864003c40d0b190740d540d6202c2c1d07040348171504903a00004009400180c18020350340c3c00342c00e280e00315229003012741c14034030001d017800d40300e102c0382200c82c10310280803813041250342040080381450b0030050162803085000180144d103d2780b20340a01d2015124030700c0348071307208000003038001b41040111200c01c03440301c0340d5001c01c006041d0300317081a1045c555004215010405502c10710003041042c6000c1c3d140035460200f08020782e4091800e19135001c2d100301d01000402c3d4081507a07038000b40c1c01c460551741c0341d586000140741c41141e41441200d0030204002c021a582d04504105c0c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 958584487 1250 958583237 958583251
    0xc07300f0b16050708071a01080604210c0609020301060906180507110d08040201090e151207180b060d09080309010b04060f05121e030a030b0301051302120307080d05 73
    0x2003141c0d542d2080c01241d9041c80e00c1e025002590401c10a03000c41c0888003d494a80d00c01c0260360408092a40030009100003a0441c50702ea0300320005000802c20444c0e4055900c10b0081c4100e0f030b450002c40b2014095032546140a0306a45d2034a4158003103650a5000c1c070302400c080b40c0100034080c1c44041040040c0c1a6400740c00c840362a143c0802c1c4d0050260a802c10300107000801407004868101d41160b0001c0040e00490500c0a03515001c034214030162a039038802d60034981e0b48180c04c6071050400440030400b190071001c03a005800e041c8800f80440c2c0d02c28910300315692010070082c41050201e0158403509806401441c54107070b980e0304100c02c4000940c000d00c000c2c1c2c0248985101d074130401084801c00c0c89849640302d002c079020842e5052180c20340800700300030341c15075200100070842010641003a40142c44942c000240084201341c05214400948009600810161038140440c4da010800904007074402d01d2042100c980441d010412240703503ea00c103e01c26201e00740100d03044041c00081c1c4e014 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 958585737 1250 958584487 958584503
    0x90e070e030c0307121b05040504030c110f03071401020309030d0f092103120e0f0105010f0605340c180b100c0b060a03060905060f07050c07300f 64
    0x140300f40303400a0880306a80ca20619034010b056565560300f210740700301d800802c20005180d000600d59071603209651050f030203500c90f405099118604030001101c06040d5074400c41d400040e1b100c02e80c0380020a04103590201c886411100c421038010303490b42c0906c8500d1a850300ca941e00c83d001d0140d110602c010300c90129141c86080741c0e1968040b81e82503085e0441d9082c54100010712002203403013003103e1102c00041d00300000b02c160440d1041410701c04c031801106031903915040100404084100c80d1002840e15180c5a420040540084140100054405c11080042c00980402078207414840b40159074441c045d82100b950303c16212102c07403060140f03042c02a241811f00011400d20199008840340560b42d44080403240e0307a2040c0d9145805014690080382d40c18001c40014003e1156484a42c002c000a0940f443d102c01c00551032080103205404003c004d100010b06040700292510507606c14000b04101203144100c107406030b009001e5241110000008507105000b005085a18013a01903a03003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 958586987 1250 958585737 958585753
    0x1803040f080d050307050a0305070c1b051201020708032a1908180d120b120c040b0414180307080a03091a090a08031806071805190302060307090e070e03 67
    0xf900c06010490f005e05c0400c0c1c00b002519583c6120364001ca9000b00103041180310b0f40e140f91500c40240820701d011101c5035000d41c000784100c0c907014010001e040000d0707000b580350286a41c4c80c0b0069010240038154280000c6446642a40982e0031214800d4414415191600268404000c101000c41c2e001c002145d2204081003039074510074500b404060050300105410f03030340f140f01103c108402482c80300500c4c1d0390b42c450903107070754890512195641c1d616008001020316042007204680c620305c05a80310f9031402201090340201000900d078006e1812050f0844060f004a0b0503096118943e0010001c0b103000611071021078050b4406041e0f14001d041c111480c410580081c898070005440307010321075003e02d192800160079000150761048182c90f8a510b80c1d036a02c402d01e4170382241500c00b0004125400c2802c0c0d22840e0030080d06009060440705030218101507001001160340a00019002d40000000079000720b006041c0140201061401c1006506d080240100341d041e18a07000d900c40d00031680 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 958588237 1250 958586987 958587013
    0xf090d030210061d01181506020313170606060a0e10081911090d03050405181f03020a1205160e07180e16090803040e1006030c0806091803040f08 64
    0x1034007a0810303d8132406042c2603421300074003444594078110f003c2c88054546803010802c00700e045000b4001c10041c3c000f141c54003000b0b1914101c40d03615800080241c1c803c5041003442400000d07010303030429405c1d08e00f240c0e0b0f41601c82c011a0084500700000d03801c00345130503c801d581035010300360030312890381d003618801840b040c054130000f550301e402100030302010140b0412040b898048008220326120381000c81c0b9203507031640440d0070204490000c2d5000f6100c0d60801c884c40c102642c842c3e9248400c010113903103a6041d94000f420306003160252040400400c00340700704008042104810804545043d046120740c0e030005c0a404103811580040000d86600783e588207100340404107025901070a8040d540caa40d0b2107803041d0b00281b68095001007204078030000407840300900050015010201a00604e85042c5024000b5000c140d40814105841c00c0401e55160350303c0514036070407040880310421103485030200c041d11400010380030512400001400103082e80c00340c44200480c2c15180980c3d012040e02c030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 958589487 1250 958588237 958588259
    0x91d0f070c030207050f0a09062607080307030302030628030314070506060d06020f1902070b03060112200d021c0e06040807030203120103060e0606061c020f090d03021006 75
    0x80d40c002d025a20001091015280041140b8152070000c3d1080d503440b582c03222001d017034070100ea010002d0b40c206500c803040161404030000b20754004800041412031324154004d996841019005400c1603404804104140cbd5903240b5034041030481d18041c1f21f00c0003400d01c0304404188901c4114086440d0028410740311501071b0644520070341000c054000d41d500e41c0180401d0400405c000c4400343c5d8200405010342e01c0b4080a080d80c04510034005503001d4803240c005c5d150444a8001160744a000d004000c20781e83e200d08950702c00701280d02d01040f102d21200f18880c0346052103154103210100400c1d40400d240e0180d0107070032001d044001b401801c80740c075054030381156510610040c143c0c010b0320014000c0f03003024008001032882803040320302e0800b14030000d02c0c0c2d000007a041120803035110070301c141e12008208141a001030303041b18098644048828162420f85801c81c2c0c1c641c07402d4021401d80080000383c07060307850468010f04040025501e5240007500c800004811503078070b6140c9036020541d051a1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 958590737 1250 958589487 958589507
    0x2100b01180620060117060708040809010f030b0a140901050a051f052802060a06080c0d020105090d06021c09020d0b0a090c090e010f02030c0706090201091d0f07 71
    0x40a000c01142c02c2000840744034504080c490300050b100c0e81031418640007000100d000f4241005400d000760255680c0500340603001e810341d02045441d02c2030001040b80c0001316800c8141c01d007802e000b041d0365075009402908545d8141c5034018568400001d5a4162921400382d190044415a000741e0300c2c0c1003001030701110360140300d0b0410380e600804041d85a500c0c51a40a00c0d660f4103142e42003441521041e4002d1610042e043c41c10b480040030600751540400840ba003150b2a00e4080c00a6420034403000c0d50f900307202d89030350720814450407074600f5a4001c204031140307044041c01480c0c0400c0b49082100c080d5200449044a6160300001440c542406202e40861183c1c0108090240c1c006a100c80c84540c0029082d2307021745039504200310018a203183c0701c000520700c00c58007080b0141c4004265084642e982c0b601804103004000b000351410645044440032984003000291a03000c83c00121a10030441c0c010f07160810743c1e090503902c10440c07074a10b2880fa502e54040c55030f055542403030480e46a005 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 958591987 1250 958590737 958590767
    0x90c020115051c0b040501060e0901090b040b0703060801020f071b0810020d0b0306150910120f17030702010e0d0c031b021201020a030f0e0c060403110409020a0602100b01 75
    0x1094005221500c1c00b1082140c111201e01c0c00c455160100340c950321108907080e102286c55039540d4404000003100702a815a0140451008004486d0151030305944140010070007804034504400180e0403500a902c88000390410728001c546130392030f44910000d1a4020182602c0044da800c2c82c2ea8010604180f414041c0c1301c0300006490815403424030100603401a0481341c0b502902d446040d451078800700040c500c54403249520500c0f4500403c14006594800352084a41289070381c010b00254519030f00c0c0c038018652000969110300042e050003903e43c1004502c02c41480300000500280d5641508090042e018050589207450700e030320829103407044d0900000b000b05200700c0c800d803003d8981180c0301c8840c0b4001303001c60f2081c00350520102e00b241e0156841c400401d0360343d0400c0d00d003154a403080d913018081003c0144001004000001c07118011840010001c407070385808681c564503103421500c10140d010301081403158949102035280c00c5002d01400201b441c100b644c1c896584a050010700e0054 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 958593237 1250 958591987 958592021
    0x71d010609060e0f100201091a06010905120304030f0f12020c011d040e0321060306061804060b062106030d050a030b0109031a0624090d050f0a0606090c0201 69
    0x314082c81501c2a40f15910701d181e2103600f482101c420785c0c5440200da080d10000307500008100300c1602e0484503070705411220029156a1004002c00c2d0790700654541c00f034590480e1308048036804a89a0b503d944030302c1e00002c224500680c0c074002080040ca403100040b600c03c0c0b12449500d00300e1101266150080b100290015801c600444440c0080220980d4045009480803e18089250f507a030726550181600d068039a12602e404425a03862500041d04020210090500d0741020000520400b5904402910b501c10712004a0100030181c2e00c1914a9080505215100d13045080312034040d0210f032000c3c0168203074030b00018190f0301e0007042c0c05003050020b4580e1030502802c0c4c4012001041d460040d1814446c1105011003c41c4802d6a105554103045c20b541000780b9080083c4402c44082c0020b003141d40414036002204a10220103031003c00c2411f580c2407181010341d0034494901102c1c0381395000140600c2e00707a5401c7c45156002102607612101c1c041c060038285400490887d0340b58040d55941e54 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 958594487 1250 958593237 958593239
    0x203060a0e0a0207060c110c0a080d0311070b16030624050a03180501060314030a0c021e09071707090b0301090b010207260d0e0d0f02130e071d010609 66
    0x1029869241d4102000400050812100e07684400c119483c2003041404900048074111084604101d08100d50b07600b81c4241d98481e00d4149041c0d603d82d01c42f449a420301d500c3c1c1c42c68205441902c4180d8512582184051442d8201800154001e040060351040040d0401a0104400300c2145d641c01e0a000c10039407185019042810464003074006049190400d0b49690b00e8071502015540c82c034200f1400781c00002021451490803809400e0003112650903a0018003000030000e0b0084031116107142c0556100c100000f0030791045101010300c80e20a984294070780180004194812459980c000c803042c001c1c9000d84a0780020b40d5103000b28407070b050b4106420401449007000703c0c0c000300310318141030040780c80a503140d890b004030700c6410090040180054081b403113400001007181c228003201c1400e006000d00720250204a585500ba00d000d8540da8084800c0e03802c545590350301c409080c0301c10100b041000e004001c201e48800c9130744039890210302c4000a5515180010030b09074125100d03a12294012 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 958595737 1250 958594487 958594499
    0x60e0f040b04080417030c10060b041a070b070302130504060b07060216080c03070c050103180803270c03010b060a0801150e030105070504090c02340b0406030507020607030203060a 79
    0x501c2103d18003400c0c400021070030700c0f80014030800700307512010f0760b190a03c0007802e9107401e204062035030b0808c0c2443e90801826215108450644218401c031585020000210a44a128078000104041c28103401c01a0721981540502349030208140081d80b100d03582d0781004140d824a000b120499041000314000040e071950040c0500c00982058084007555900c0320009a0440807141d061a04005604010046014001e5010f401c013420108072000e156001e100090080310001810450300101095007284031060300205203c01c24484403036002c1000d1401e0b16070048030380a81c029070800340ca07400d49181400030ba03440280f02d603a500841ea0310301014048100c0d44528680103008007000c5402a0b81c0b028025580300d12002e0300c400399514540380400c0222a012020369003190002d07102e42d00803542c500300d032107502086c20303e04540c0000d4621001e5011f00e03c80e480310920a20001e0300142c1c0c550036800c294410441c94080c3c1d001941c40d450282d0681c4001c0b1070700b0f5440070f440f000600c01 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 958596987 1250 958595737 958595753
    0x30080108070b22060519080f0a05150a062c1302030613050a0218030309150f0417010905120c070b1c0c091403010908090f060f120a060e0f04 62
    0x2203001d0124182829411035030b40ca201201c0d40b03070031080018100044d1443c6d03002403403641c9020000b09107480070303e901e001201d0310800100640340b0003070f194448010443d032034449000e1010707980005003145e9105a440b000602003d505004d0700c00c50403880061016001c00300c41c14019410800341c40e0340c448a04850060000350310050046a20440d55461041107110620031581300365400c0f000140e582241c10126030304081000c1103240700e41d004015540498a03222070b403100041d45035490544400d102c200c101400d0086403c5011030f00c504444001c0b440318150001040c81d030240c41a181c2e0765420184802c000d2045485103001d69200040801018510303200070081c11740c056a5003890380000010880c1900c542d90f41840008203a03480911124902d24a5100809000c400800c81c800c4141e40310701550081490051184244415480464456600304d4451404201d03081d079859400c000d0780020381205880350030200303103014004100d110f80060824003480c00d040034189940d946a07140c4003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 958598237 1250 958596987 958596997
    0x1020316020315150a0b070f020d061805101103011d0a02090604030b040302060f090a17070206040b27090103060b1f020d0e060a0801031b0330080108070b 68
    0x2e01032054507003111841100780341a5026020307001d00061480e80040801c42c094907185c00c4032850800c200059070014000c40389584240380c0c10307907903000000043c5c10004018083e0020710400c401030350207100c0400c075004c41c1c10f07214200c15480821003600e0407540c0c501140400d000d040c514142115440807035502d2280c820764040c0101e0310143c0f40090080100341d0380c2c0c00981c41190000082403cac0300c2050713010f108050b840040c002e420002882c00144695695030746600143c1449840340707081d05600024000c070b90364680c01511041c0d4036503444c011900c09a12519122240b49003421340030300410800f6401102140c00102075548a0b421511494010f203d06101250f1214000f20110307052070004d081c58a42d58801c0c0c000c2c2c0f19010414001400c0d550540c182c04d8451542080056003954000803a80d0540ba001380f4a521200c49030404460090520703000504006001004250240f00200d10030200c0600c044c100c035880e078004002a11803000030300078000b05411402d814484143e142c00549 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 958599487 1250 958598237 958598239
    0x100308120408091c031b0809151b0705100801080a060e0c0415140a030c09050712093f050c07120503041e03080403061a04051005010216050102031602 66
    0xc0d1034001004001420000c10145022030030303650400820502d504411000b455405082d20051207442c140c2d1030000500c2500b20141c440e89481c1e8009030420805826554041d42048880c04009035117007804be9074400503c15507100e000d101080c1c00354076225031005412103000d40020f050f0380070140d58400140c130b0b523504130200c079105000101202e582e0b5030190b9a014044036003442a0300c0d050180c517140d4401514850340c02040f04100800020f603003008860100c8081810004054940c1c3c0c0046401c04581d040403445181400c46490512840841c44001c40d240c50729504001c00c240d403040b002d03d00081080c03903079408070400c601c040c05010301c0081402040305000d40f41c2c03664449a001d19910310b2480d080d900f0f588089018007001001e04041144039580c5007190700744a10310381d1211140c1c41180402800161903503640080ca1902c2020003c86000c020310500103458140c4110b0ba81c910a0f1065a0041c890042d207010144c514030416000d691041c0d01a5182440b0182d1750804100c1401c0e0403 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 958600737 1250 958599487 958599503
    0xc08121c09021908070602071805060a0522140c0307181503050f0a140c09010e0a061d063c0408250e01030f1407080102070b1003081204 60
    0x5040140da078200c1c043d1110f080d450402c0340c035500300014540b501c0c0d560b800c01c50030f41d030046c2000d00c0454541201015071a0b540384012499585240c089080ba015581c800c0d50000384a54520440085400c0b011010440b003500c20814061403440c01400c881c4265079290003140d00708041110140b0400e0000c40d05070204a020703180e0340da241442202c4114000b0500f001030781c3c2e0000d0010010403081056046481010107000458060790380522040e00940740784448800052032160b681d000d80350702401010014401c028085e641c030000f0f81110300c0207050348442c40041c00b26203080d00d0520b094482e200c40344d54002c152051010701d81901c43c052180080452118001940c0600d102440100040e0034820060124400300c640029581c1b44403000d240c85c800c000e01014071141000e00c00c03180c1140d800c0340c42c1e43d2201000e4140603203c016648605082c500550030049081c100540060081e02d02c40c200741407032036072400160903242c1e0701400b005107041030401003599046d2540000c960400d01410341 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 958601987 1250 958600737 958600751
    0x1609050d0c0806091005090309100513080a0b0402090a050103051c0309150e07080a031b03030e070e0105010e060408060f2d070807050910030c0207030813030c08121c 73
    0x540b41c50030038110b03500615540103240010140c8841c2c01800d0300302c1d1414009504010702603000868401d18070804104009010802000004180411900602555043e1950300f156030402010f101000c8070309a00030b05040340801e004a01c50304c19541201d400070060b0a40410040c658901d030514600301d4002c160b2a0001400840c0722808421a0300c9441b280c000f688001c522040d81c05c1240a5100008a03084011072501082c1c00112480d60b440c09285d00041d10303003507898154000c042c080c00e44481480341140c0407445400e000c80c030700d060b642c2c00d803078071188004544100910340c4140d0040507059048040412455001d04504a0f04003d040f00c4458911390140004460340101882d58000b1194010901c18410b40010980b50810350514000d4682140c50000c96405a000c5266400709039640c1c1c521142035100b400701901841d03102c440580e41d44409100e14900f200680410350307255203100e4000a240c100020300520358102c9100b064104a0f200001c12240740c21400c02c11005c0e03480740030b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 958603237 1250 958601987 958601999
    0xa03020906010c0b130c121a130807050c010306090221070509030a0b0a1a031504051608010218031f02090a180e06090d1b080d02070f0b1609050d0c 65
    0x469201e1102890b00780c208503840d0a06100c0030883d640701100d1407181f10f20f00c3c8003040c440102d10403280703680e400c01d220a03100c0c002409544c425400024041000100300c1400b0040b000c5031310400544266001e0040c8c1e5283c500d42030491084800c12040c03030342c3d840b80700039504000644495000086007401801d00641e0070200b8104450010101d61070030425040260f42d038594441c08024071030303c00070354100c8010000441c2d5241401440050340c00800c1c00060700f000300070040c028181d040b0024007125161f0729246076020303421210550310b40c14284408440c1c43d0034006500e044915050304a007020054602d4444020b40c0407009203a0000c0109401068001719103090a000c0e80b030701d1400140c0d20017107404190409102900d1001990000615040b50340e034056120010f41c60320f1103071110386c41c0300e51034138510920440b290511800d0000c00c0a009214460a1444000740240c104260b280d480c040441310031003060249c100800c0142c0f0080c4042d0510111607141c1c1403042400b100b6481e2130304 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 958604487 1250 958603237 958603253
    0x230709060e130612260403031b140d14030f18010e0a08070b0901050601050a2f06040308160f03020919030c050f03070510050307090e041511090a03020906010c 70
    0x140080c0c000c0c40d142c62001c002c106460441a05c1141c6a0710712844c03003031941e400c881240c8a10720000d4104410400400301481d001d00d0700d0164a40d0100c40c2d0440807184509080e240d00850040601088205000c0300c07040c00008112841400381c076001400c00d54036820500310745401040e241c16259a5150b21100e1807408110038542240505c00607034842d9490715041c0042d14000300180e401da4104014031101da41c1100503104903881504121307060b0340d1848200510b00d6030703c1c010340c0c10340e0040c080314480e507500104401740107a01982d10403040f95600062114402c020100c6d100015403003181c02c0e80c010b442a80a00094480181031104440c0b822110b06d5031606582c0050303881b0b08a0391810012494202c501c00148017056024005182c1b40c20001100902200018401c4c0039000000605661103248280044c00300710888984a0805060050034800403285000c090b038509078420001d4040310050b500000401803c1030516402d503030900115032006841c0c030341400501181c000c0011140 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 958605737 1250 958604487 958604489
    0x3050702120a170723030601030e10020307081006140d06091a1002070e010302130908160302010f0902030c010c0312180512031b0901090b0d230709060e1306 69
    0x90341e80e800000981400c0034a40c2c0c2c800341a04017480200982204481003640da9815400c880042031a160b5075020700680140144590140041c000c804880d100e240c3d0b40d90207135020b05003e5171462821350703031900ca00700006220b000d60f0300802c55005440e441c1481d940001d150045d100a40400c8940e5a400d1100c1943d03030300a125240780d40c40302d85406041c01c2c085100c2000400e40c0c801444801d00e003c040d044110010b00010f0702400340c0351040703501d001664002120482c0e001c0180c0e40d0301e800c00312030401c00d41d002000c102d005500740400303030307295035120301440d0708045d001405040c0600f07020005450602d20900c0c1141070289909000305c1d84079551040c40d048050b14005140c80342d0452801506007040c81c0c29840c0c04000038414003000f03180c0e00c0720840e641d6401942503645d0340640f10041c1c0760713024a41d000310070176040000d5004010a02d84c01410a4000c907c0048540040805150201d90003c03100c03080010308100d020400184100c00c5810010400762040044003454100701060340d2a03 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 958606987 1250 958605737 958605757
    0x20f09040e011a0907120902030c09040f0b0c03010f0509070c050d090812160f14060c0415231602090108060f010f080307241d07090e0d0305070212 65
    0x14442050249220340f80c01c900c02000111130351815841c02c6030014050303c1c0c0310a0403148240d5101174140454408109030445840000d0a10070185001c0c40e00040c00000c01408917500c100300313400f0a801c10415000d40707040c2c1d0340c00c4103464034050802c8117008159900804131003c2200301035030000882c1040c043c1c02090801540c175000c5403030500300c00074a0b000840c51601d146800800800003181c243d600078448aa6100050745100301c19400e10700184e200040008607140160003e03c280011200001c1040310355600c00220044504101520403041510b035007045080030440500c40305e08000001c10035030a01758590440c0c0c031000d40100b070140318240c0200a5650102c401e0100500041441500602180010120007420189540d0320303030040b041f0007404000c20503100c81552042c10720540b80c80311900010400c00c031400d4040c82c2d9003800d10102c4011400382c0e19001c107008e01c0700e0060710380404004004054100c00300030100c2c01000001c02450840c01444a26400301e10980000c1c10700b290 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 958608237 1250 958606987 958606991
    0x3030206130f023f06010b0705030f04060f030e030909011a0417060612070b0901120e010e070f050f0117040203030714100612151a0402040605190e13020f09040e01 72
    0x4c0b8145081c400c294081c00c004100030080d01c56801101c10004603141034403000c0b80250b0311021309147c480d140d130140703551000d110350010a001c00c07411391205541d04c070061a40d40622441100000341500da201d4040125002001e09006114080861118000d0000342070515490300782d54004142820a80c0501d400c4a500448240655031429103024528026102c2c040d10b082c606c0c20039002c0007441b400b50080c1c140102c11100e401c510701241d005211000c0e104000b805080c030b010010310f84030041c80c0903003070b0039030900344011940d401d2035030340c5014215040c0c5803505520f2523820078003d00301d03000340220707410f10080100d240043e88500d00c040300c1850311402030584a0325241030a065078115008a04174003c96000640030400c01480c94290821078800012525000780000040c40441c03030441c0e40003800028005a140d030310400410320b840040100c1402c80044420442c0c0e9115a4a903d03980b01d045840c0e601d24400e0a0790050101c0000030640624182c6000c3c04034098070b8014403c19a036035 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 958609487 1250 958608237 958608289
    0xc0c040e0f100227130507090f030b060a090209011409150a1e0e0d030c0317070c03080c070201021c0507020a170c2b03020c090f0603100603030206130f02 68
    0x540d00c0116210541d40d03c02e0b940200c03403141320202e0200081800c101c40c40d03588540104050380d00401031440500440e540c2c00003903030744030f080070418003209031136a6005411007940062141940e2081da0030540c07059448440294032040c0c0703400383d0b400180701194044420501d0031041e009070350040100081985441080c0401800301c0400c0d001c0511020342030000c107039020ba1a5640741d03003810b900c0c0c5134142000440c14116050841e076064003125088001c1040e1401d010b4441d4004604207010361181d40c1d5007145a0b50010541c004e8060590000d001d603010030442c00c12007011240c015003441c920301d00241041d41c0c90b000074181d114158401c10391131540c08ac0344203861806200b80042000c040e0b60340401c0056034a0300d903248260040e54001181d00160807542058802d003c074000c444c0008201412500741122030030b4105038251580c501ca4811200c2420002549006440489803d0740241109603201c084102d46a81c1c00350003281e040020302d000d01c00591301e484942d40c09010401e82c0038500 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 958610737 1250 958609487 958609507
    0x3130e010f080d0507020402070809030708030d180b0103140f060118140f0f130f050f06070207030b04030f05220504050a020412141501090516050c0c040e0f1002 71
    0x280ca0701d81000d81150840b40b1a5040c19070000122420036a040d5401a0340e030f4210b0400c078429001e48002c00754940212840015611800009454400e08440040106010f81d99010304c2c00d0211080003001d00c94124010030205513a0115052001903d40648c3d2207916007441c80c60400070b00740c210600c0c80c0416819008d88520030700c100f104c0b04541003d440c0e201c0c01c2040c1810040d200081150340f043e22610001200c4065109807000d00b0341e4049800c0c21500e2a925000b61a052020b101c0180c2d032203010001610785100141401c100c0e070308a00034540c01d07140da03103085400c0d4412540181c1441010840004804d55413400d5099010220720004402400c141c04c10080e2403020f030802500c40c1c0144130030320602601050b40843c00764000300390007080d07400f1590303282040e90003081900b000071030034000100400644c00035885881100e200c080b9000d9040010f450500480e054a5415400780c0744030b0255090a0f130002d81d04480380812103c0060306148228502010041d5004406402181900c07403 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 958611987 1250 958610737 958610759
    0x60408131a030412050409060902070b0a050103021f090b0f03070f030218192105060601140403230111040e0a141f030803040609030206070c020a140303130e01 70
    0x94480c81a008520840741060020180406003003e8a01d0120401c032503080c41c052000c079001011103507410310406680751100c1d07009402c80002a074003c60480c000801022079886003d040c1d0307600070800d44d550100c0101054004050322440ca05001c0c0c0640089080154580034090140700108041d60340e1810107401018805015045001d160060180d080520b45103000c1100c01c1c041524803804c414840d4840ca00546802d81c00f040305101580e0400c1443d00c000c00c1040c80803401181211942d440300001103802c030000d040030140c3c08109101c28400512100d0220301d400b0902c44d0039070744500c10798121702d0844001c44002d20400790700040400c0005d940106e41c0b0750101451400304000d0b0884042c3d08407003400204041120740c1406030360001894036403001c00185400c0f660483c1c0f40c0c0340038a0108010145508181d000d8840c135800944664411448501302c4d95002d000001c450307150030b480c8007881140c00c044541c0744c0006e1060190740b40401c3c00090051544071004086540f50a1140d18 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 958613237 1250 958611987 958611989
    0x406050405161a341a07140c0a12080907120f1101090305010e07050a12020a0e06132a110303150a0312031a030d1e050c06040813 57
    0xc03001d500c01d00800c01c008100650240c004001c050182e901c103003042c64a40b1544400e0740c8403d010400100c1011300202e16841034010324442e000c801e245c20629400900c0c10b640c110780c0304001441c1d44146a81492204000d0142d5460f408210703501180e1940d01c4e40a00d21120026100003001d000401400c8501006408020404000800324014142d22707a111a00f004d018041d200894051240d03041d6403103099001d0045030040002c018200e500c8580d151286c00070301ca1644102e4184402064807025041c0d1030b01d02a50040c1403070041440d10300b100c030b4110002050b850784908000391f000700810060040348526440d5030f04000000c20458240c480c21403803440028100b103004071061801c0130340041283c1d040317140b150010840340c1c0b00310006261000c103604001c1c00d5108524854081641540001007010080c220b40301004040000307240d83c2d0350301001d441d000156070010404101c108840c01d504151500e21388145020141c0800f1898032600360f44c00c5130440000940e50040804c40c5107480 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 958614487 1250 958613237 958613263
    0x30b0f100506090d0807020d080a0c060606030605010e040b031f05010312020321041529030309060a030f0f021308010b01080708040b060d0b090a1e02060f030c120406050405 76
    0xb403c3c2964400441e142c0e5280c11401000c600c00001c0c59029540c803c03080d039220580c4410001e60b0b500d4003034070041844024880480700305050000c08035020340240108001e480040e91486001d240c00070400c00a8030042c0b4119405000341d00b415201d198062a0710041800842c40105140d40b5600e032104400b00b01180a02c215003013408096650010321800d84042c4500e414518662380ba03e0034045031840390410031000c65494000c0d007c2143c40d0703000c0380300404195860031003480385420b018582c6074441e849a069000e40c040000320075a034043d92200b0811440c22100280c410002810081281d10400d0b0702c07040800b10308410071001c1403d005290010707200f0b20785159a8245814091320350702c009000148610111070010300d158030b4141c160100c4603004100c210300760a01018007921000c8803c415101c0014140d61100b030819202d40c0340b07501a0303002e03181c03916003900040a4400380d00040c1520700c0003202003005000801e40700006500035801450f0001389400c0c20702d01286410320501c014 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 958615737 1250 958614487 958614499
    0x1104091509060321030f050411011b0213020c010b0a030f0c09021303330501060f02030f12100806070906120b10030c020c1e01180b03040f0804030b0f1005 68
    0x43c000914040090603a0940081991814801c840001d5025002c241440c3c0707080d070324280820041c40719001c40d501d1204020f0301d64401041800e0401c1a280c5481d860103904000240742c04018200c80703600900a0121403000051030440c07103030009221041603407050303607103240541e4280f0620401102c00001000201d0007145410201031842c0409195848041d1400403218a0007211156034038050500e210f55103144100120343c0101c00005090a000f00c000007060340000240c01c82c00041254002e01e02d00110030f0900030159000612181c00400985010400030b0000078140e80401049008858a0325403040e03007810014002d0802c4d038a0111824014106000c40e540c90300c450189139040001d600d4042a0b001b0751060036031400c6449a045500504152450313480007109015080c80f2043c2641c58140345020340f2115684203d143c09141800502080880d001604000120000a06c144c0c01c050411740e903038840300c500d01422100007005520440c2000001e010288104024240403521 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 958616987 1250 958615737 958615739
    0x150c12060d030c11060f03040506040b06030f0303040215070c060305090c1c020904030e060f0705010506060a17040302072d080d0c151107031205060319080d110409150906 75
    0x4000c1c3d280b0000c003902c002c91040b08001c0c40d0300d600003141d0781c079043c1c90800c0f6a00d0616190840d6145000c4806907119036003680850024a00803c030801501c0b2090021411a02d898081190985d41c4209c241c440040400c0202d0009024003c032000030115030720002103518003504040d0038040c5c00c4004900c99060344005440800c020780e50345642e20340656007841070b940c8524080e02d0700140034800a03802840442c1c3c00c07004891000090050070701c540000c3c8980e4482d00e00303000c03860003010046800704205a182c0c1207480f034541c003034650050180c4122000d046d5200305403500300502e2048030085088030004045c9001c4480c0c124401089654024003910140070001415012550310081c0062084141081100c6a47c0c010229010032424110742e00e4586250181140d16400035034814581085e000072901d14002c036010180d100519a18002d0024542e107140d0541d00c070381c1c0c0c1c20003000d503034100c10080c800b5040c0107400503240d50366000072415020013100d07a000603503a100b1a00d070703810054 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 958618237 1250 958616987 958616993
    0xc02160503150c0c120c01060303020106120c1224090b06091506130b03091e031c020c1501080d18120f050319031a010f0f050c150c12060d 61
    0x9806a000640c14060fa46982d40032048900b41071440404003120000030500c1d090302c070419803000c0203c80c4250000c115581e40e401d04001c08105506000e080b00300c4042e82005205001e590800c40607203d41c840072242d100305c52031001084510300c180d024032640e400a4030100301400504c603402040807184076003d450019118400d120101c540c1c1e40c00303201e004c56041c0c000c90003103108601616502c0400c0c3e86038540360791190340ea10b85a840014100c004803040007100c420110441c3c00c0b1244014800c0e00a1060135003070390103503001c2000390343c0c1c51003244c203c000000410317560503001e0040c01c40030744024410080001d03c402f080c003030b4242403154840402c101248003505464030051b48240307107025043c40e6050141c21070041005101c115003109201082d11941030b48121081e11130b9082c0440680b4000c4011580c80c111a0b42440210b002c802c040420203029001520400d1098021140f0328130081e07103400d040510940e04486a0701004c1000b065403254031042031792000c000d4459081c0707075210b81c07 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 958619487 1250 958618237 958618273
    0x1e0a061d060a110c0703050615010c0309050418051b01020d0219020d0203030c060115030c03090506040314090a081c030b0105041701020f0f0d141513020702040c02160503 75
    0x14140340065543c4000c3c031600002e10300c2c1515820510340c01a0381e41e56540c0c0c03c0990301c0b628100d07244464861510380414040d8050318070400303582d4040d40c03202c110382e06280520005082c0640c5651010072580c1241000a030100003c0004034141140d2503207019805001a01c0c00c91200c881c03006540002d40d6541d0b44001000202c04280e804a8030710070702c0031090022a0075071107083c1c01d4000324000c44002080e41c00e030703100408408860a82c0c0c1003051901c11320040741200d01004004007150031601c04140441d10601c9540b24100400c2041072420b45540000340c0c0d03c02d820b80c4080455001510b00340c000f904511004002038410f0b04080c00816404000280b1038400c9005a9000d0308031300304442004031003541a1001c03840921103240d5110020264943c050b0061a0490016800c013101e08440c48821f0072454020400034030801e6003401e0500801c42d031f2a542402c4c05281c140c5c28010f241c0581d440b8040c4a1040d00150046c1c440c10141c41c00c03081000485070401c6000780e00c030031041c03900d00c22a1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 958620737 1250 958619487 958619491
    0xc180501091a1c06240203070c050409050c0406060f031802030303180a1205030f101503020702011106132612041e05032d070305030601021e0a061d06 66
    0x200740b50a60b281c00006004207400030107032800780320740d1400c0400308003003c1040454200c0400110b50300f0104080743d504994a1050490042a00e06a0502008181400e400003104c0328804c509a425180401d0003240450303202d90b004500003409042000900c0d90103100f5411001420034501c11520884c1d00400d990b448080d0841890780c0d10a049041070b4582800320b40c6001d54041d40101c00d8584640e8018002c0d0000d41d0079140142d0800089140d041c010740032501150b60f00303804071700b901022000a034000d40003004142e042c0700c07407119410761010080c030419208041c200210f0380c45070420f00746000918141c0d010703447e00d900c000340303003212441c82001501c148080c025004a0f25903076514112003d012805040d08802101d98901010002c022010300080150400c0018503a000d0145400241e07468030a40e2040780c1c410800240400d104400a640c40b510600459a008090304071722512029003420556a94006000000c1000020f0140021038034481c1c0c1e185c2240c1081920044c3c443c800 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 958621987 1250 958620737 958620779
    0x1506050103110c150606040909050705100302030601090b0c01060b0c1e03030408040e060a0504020a0f0e0a060519031103011203030b01080f160e060c2401030f0303050c07060c18050109 81
    0x1c81d1380000c1c100e940c0e01048a02505501d4801c0c420703403125103042c559500041c05800d1040b13688a1201447e58424402d517031186e00c05a5885503942d207455051a015031050080d60829503d442c000f003040b1700aa401080350300d0a0b6801440d503803200400d03200212048904c42e00040d0400c005200125522000b6503007501c52084501c00070381c0320741c0001130381c03821503034051070b0002e001248502580b41c00540c014507020003900e4136016805150100040d900030340c040c000c045003091003c21a0024121000045101c01d13050001e4121b0000101554540003680100b40c3c2c1490440e084003003540c035014003094403d003802c0612040c100031b2160b00c881540107120034a80b00641112605441c1b00f00a00301d070080b800741c4a9565002201100303603d070b0a94100c4041c8120303103c08418444104852018100da400400f12003503500180ea044020300000303080072402807420320480c00419203510651200405586800720f8030011075510700c0b261340b02075000506105015a0401c940c4489552002c01484 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 958623237 1250 958621987 958622023
    0x903021f090830071805060c0304031118091c030510091e1505120f03120a0b0303040f150903080406140d05090307030813020d1e1506050103110c 64
    0xc00d2581405200c1c0103100c039070148030303410b01348107a0310740100f451401690b003010980e0380780b43c0b9002407050900c00e00a10102503481084100045400c0785400000c3e400c000301010300d68003021030000303000c90003526005055045010290303241c0340f40f504014140c0c1603d042c20700840c42c03e03c62203100d03c0242d210301e002c0070f9100d003014000341d07001d5802c0780040842c3c0c500400040243d2008460841241d00440d030081c0307500c07081b9503c80d520009a400700850940000c1d46080320071928184c142d8000350007102119240c42da018036a940c1400908050311900c100600780d01d150128000e0501c413240c2681c028811345a20074000708105804443c15540700c2d060803070040503181c0038104248074004140c0015032915007400100000030004014882c00b07540c40c8400c035168059060342140c48501d000f5800412104a44002500303144e400c4a04580c6100d038070070000450320b6640480c608044603e1000390341d184140020340e0184603004035146010340403030030902c00319000d90b581c00342c00c640006540 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 958624487 1250 958623237 958623277
    0x8162301120f0507030c0903120e240d0b040903020604140304050a090c02061b030f0709080a060606020601270b060919090b010311031503010f0903021f0908 69
    0x19000d240740d540740c0600c582042004042041e0303464000d05090300d403e000207003450742101542d40b20308110700c1580d400501c03082825150280a4800500c00314080ea00070100c0501c0a40e08142c00c1c011b44a00300c200d40025640794030a5280104540e5000001e44c407461400e181ea01c0440d034005000d5a00030341c0206080000200e81e042c071461070186034005a84202842e0001c1194500713600070807010b0005800302c0f84030342c88070710780e02d07000e89a03500003039180c401c0500c0010040c82c41410440e41210050611405040e2540240c604103a400c103c1510070740c2d120300041000d00c0d41001841d00414107110045440070695410b0072900c14000300622100e82c49083d40c0000d82c1d40c0f00f041720103003000200796031002d080d4040070f8202c10310030f4800e640a19107444400e18455001c4c1c0500e5516051560304145583c1d291025407900b0340c401c8000d203415641c3c81401c411703c0c0c0003034814032200364060b40050000c107400c401c00080520303040c1c2c00c42016604100b16400000c044100303903940e102303815000000070 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 958625737 1250 958624487 958624489
    0x1151707020c1c290c252906100e040b09010e0106030608030306010f180911040e0c0a090e0405120f09011803050705061602040c09081623 61
    0x402802c64241c1d201c00000040036400d154046500310451050700100e404215a440d071602d1059059140300e94118001d0024a010340020020a0340c542d850711041514110f20252903031360115400102d61880e1345e4480d050b102c00e190741000c005040d01c5029181c0d146880008038408600560510b41131005800c80c182c40e99940d604284983d10015101d000107694844201c01e21400030710034000420f1030801c0202e41460040100c0748501c2040e120308980540a150480d0f00d4031801c3c500000342a80c01c4404141c240060080e04004198149456200d50a0092142401384041e1803d810001c04009840005403c640641700300e80030304040d00c0c00d03556103060050401007003d550118a04000500308118010300e805050580d81c00e03070b43c000c0c40c0000001440c1c00d0241900010300141c4c0007540401840c54044000d21220001d180034840042141e03001c1000d45011246450105280c0c0005000009003000750001c00c2c450000d0500f2418548900510302080d03c91031144072a10104107603000d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 958626987 1250 958625737 958625743
    0x20705010309260a08090115060f020f01050c0a030b090112020405072703060e0a05061b0408030f0a1812020105030411130b0f0d1e030e060d0906050115170702 70
    0xa83c0900100d2088040303410341d07801005903c41402e80300402c0449010400e03c0c141481280e0241800d603940184039400c05106940780c4410384007600c00c52044281120945000f801510700407410741c160300362181c84581002e0140c40050f60800d003d40202c0d001000550140322a1040c050703015500001c2e075844a2904841c1c803102042d603814009a55180d00030000700c887e1b06074080f203004220030400500c003000071503143e00030118064025402400411104184421320350b07208551010000d02d0581e0f115201c40c290313001100c9061401202165141205420501c20102f2a82e4000ca50f842c060a181d810704524100c4080030b03042040200c0040c0401410302d2540c008143d0042c8aa110408403009039406050f0103e4564007a405081c04c908890601100b64a0b60719030044110a0180d09200c040900d074a46080a40400c50035900705001511810b0040207500c0c440704010800040d681400f13020b4440c103a1020654060501518070401d40c458440c2410301212041e941e03242d00d5400d01246 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 958628237 1250 958626987 958627013
    0xc060a0911030d0815060a08150406120804090c05030405070308030c071e03110c06091905091006020706180e1e0a090b06040b10050c0102070b0a091e0201020705010309 74
    0x9050f200c1e801c0d031200250703000251548110604402080c0d444480010710149020300320ba5440880d2050340481d440342c0d40e40d800b0740c101c0302c0e015200080300d55a540219541ca241c548050b140301d000010180040307180742c0501000d11290382042803641c14141e442907581c88562201410005020021801c51507584080302c10300d6420044003404d0fa00c2000c82c002c150000c0c00700841c041500d0000030300d00450080b03040440308900400c8681002d0800c41400300109620844000b0540000c0000c00e003503a502108074040c2c00d0840c1c020303a81e00e0501e00043d1404c10303144c01a20034400304100c0304130411025480c41007550b00a401c103620688038201180710a030b4a050b4810b0b032a220384410816681c84a1b80122000ca01680f0304a95948071401444202c0b0031414216400403007242c00404a1030080b401402ea8514400c0010b141c05250344412484c5101500c0c42c086450b140d1120109111040d6105401142850075144000506038001303940e610440c490981810f4884c0e405405210454031045 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 958629487 1250 958628237 958628239
    0xb04050f0c0a030e24160e1009050402030c0c121e0a030b0409050c0301110c070306110c03040e040309060f120b01050c030f091801080c01031104081c080c0c060a0911 73
    0x2102c44200081021980e00b4000c0548410b0845c400060136040615a24074611402e50700c82c8400030139028180310070018056401307001d21042c4000014903481d240700551060000400441d250008442580e00b041020f01c0286101d800034820580c03407010903c0c40060b14400200c1407aa200c1044800f90040d04000c40b02941c0145005040400d001000c50b641c5c1e404003086000f080304040701e03000c90045020300c058091003540200820700c002140780d40a2580c1410400a1354107201002d060986560b219420224031740b017452061001b09034001c0098000b4242c1c6040418039844082d40080c41c0040c56110300c0543c80d21101c072030b49507901074003c98503405940d030282c0b60344401c100c03000c2d12164848040c031801812502400c0d0340944440000606031100c10000c0c1c19210b045000440c06440218040d007081041080300150603082004034801c0783c3c4841940c1400080140f0018108100c0140038800011003080010041e60700445c2480d8881030340c210000d8182101d042840c03d14042c96803036 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 958630737 1250 958629487 958629493
    0x70e012403110705070e10060504180204051906021b030a0b10180e0c010c02010503041101090902030411030f01200c0a0c08060109150b0a03201c0b04050f0c0a030e 72
    0xc0c801d015001c00c0010030390303006d280440e01644488200903c035410b64820000001c000348814401c8074568014481e640400100c00340c281a203500c00601e4a841c0a208041ca03030810381e00800c03200d81c040c400d0302d2107042103030b24034001020420042501c0313240c0c000004142010075000200c80814061280c00a08140300b19218ae4075a8198444000d000e4401000401d00c1003100c8a800ca41c0320f00d6130301d44041d0341a544c2e00d045440e240c2d10102110b06124056051014011001c80c2030038040c405588654010425010007044d00b509242c03d003441c2d640c030b046407641042804801e2a00d4a55444003001c9002244d0b540e0b041c003030b103045041c00a00a00100040200d560001c2c0284002400d24140c3d210458200842440c1d4484ca00001c8070600c12550428010701c440313600507001e51310650b541c104e0a5264a246031402124448075480005505e10b456020b07444400c07402503070f10400b1240792050f20f081106007031481c0405009240103003040e102ca4000144007104511941011103120f11310310031 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 958631987 1250 958630737 958630747
    0x150b030f1207051905123105130605060306060705010e10151502120901020a0f0b220b010b070f060c08071218020123130503070e01240311 61
    0x140e1141640440d07010f03500c0e4450a00e4600800401a0f8400c07941c540c00300c01000400c00442084415411020f810485d2013025040140c03144000000620362020300020700302c11074142000c02101701640d003110714070b00f807400500344403036110b16040f240c20940c06c95245845d505246000c6024168000d5015614000e0050b802005030f5250054116101c10311100030a294813800f0b010b400311848111580140d00456031011a460410000c0040c8030041c81500c54000301500c0c0c110817a4a039800c00c503011000c0c0401c1100d03541041c030303c60900701d00140c0906c3d0740304815150a40007180600070880c1c49800003890000b0441d80c2403803000c00d15801403091001003042c40000d090b0304001c5070f050b03002c219075400f91806004507100c1c0703030010304920101140c6803140e5001112000489243c5a0b500310359240042e4080c0c411001800f601011748441500413400d00091500f006140c1d40b081038a02d201c00010f00031402507190740382080c07030440c4a240c4d203045c03584d0085000d000c0300c01400c0804400060 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 958633093 1106 958631987 958632013
    0xa05010f0903021c06140a050a02040303020a02040c030e0d0c0201031104051c0203070810020912060603071712030a05040210080601050a031a0907050d0506090103150b030f 76
    0x41000c00403503d075550200b260a0f200146c08507680d81c07010040502418003030035502c0300c8102c4c4190b040c00d14695019640d1a2550301c020b02c0345840305500018a4440ea01101c001140c6a049403e542c1b43c04101414050b100d110076070000382440d4032090102007103c00c59048a90240622045c026800c4000003840820030040f81c0c10700800000054a5100304035030207c1d401641d400581e03d600040800103504204040480a60819030401481d50f4020600e001110b1040180003104000c1d80d03480c609016408050307070401c20021091209801e1554816440380707100392014608030780d41031800c0da495501200c405001450400c9000803c5100e50401e12400310b00c000c1b28100c003818600025100c00c3c04494090024002042119400c40179004507a001181074072203007010350640c1c0f030350301c2e000c1c11034a118001c01f074841c0c100244a48081002c1814840000140ca4110300703060 = true := by decide +kernel

theorem cover : BRFrame.Cov 958453237 958633093 := by
  have h0 := BRFrame.cov_init 958453237
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958453237 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 958453237 ≤ n) (h2 : n < 958633093) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
