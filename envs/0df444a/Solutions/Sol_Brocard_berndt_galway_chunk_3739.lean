-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3739
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:32:11.139511+00:00
-- url     : https://prove2.me/submissions/e3d1a6ea-96f9-46ff-8e67-dc42719b4100

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 672302158 ≤ n < 672482014 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 672303408 1250 672302158 672302203
    0x604060f211a090f160e0303191e0311180a03020301050403110c0f150c07180903020c030c210a06050406020403050d03112a031803061614030411030106030b0108 71
    0x217083c1c00c0764003090404a2800d0807025a0030000a445c2d40900303010041803010110040b09401e800c461100c14902e103140e086896078400e050194203c50b4401c1d410081030303404204609011040d40d4200b02a1007000309859102c0740c4a0700460308480d8100e40c2200071640300703c40310403440c50402070b03c0704c1c0300d0341100c2c1c1511082c0000c01050b1002c901401c906101c510204039030380c00d0340d401e102d40b20262071210004101200042e03c528050302011006a0260103003a80b610014100031604d0180390101810500707840c25044031b56001007a6011480503e0700441e80c0c00c0c0002212406403500560003003201503107541c20b40c00c1603810648260b07001c100b03042c5002c400202c2203078514240c803400d058407010b50900c981e0841010b0300381e0001c581c240440e030200084100c41c0400403c6000c281c2a0240c04840440e0f65113a0380403403840010030b4480103d41d410381c0c01d04150701180021a03005102d20031441027481c080d400b29007564800d030811103401d110140148150f980c200040e00203052070500701d1501 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 672304658 1250 672303408 672303421
    0x303020a1709030f1e0109020a062d0f0e0102010b01120f180c14220b010306180b030105060d0206190e0a030302010603030e0604060f211a090f 63
    0x350140000d000303040022103840729001100c51000c1d2458490040c0c2600e0b041640419102c0d00c4071000e90130701c0c400003401c015003017046105100380050268081c04041002d03003046001e4884d050800016040c1c400b03802822225129046000481090180c54001141229490103460300031501c6401d4116854078141c800f02e60390204100039402c914040000d0f09091200076440504503000c1c08180051b5035140010401c1081100b40045580c05101202e5100d0700d041007040e800201d1840b0020041c200030310a400311001c0d4070864983c0414100010100e9560111440700c0d002c0c40503208500340c0d030b030541c03403240e00f0b080c010554040d0f81152801d0300040b06a0015245000e40d4070480d210b100301140f148159802100705000d0810300509800c1050344e43c0c58000e02811840c0000c500203101070307007228924100700c82a5000c0e03400c0f0343c64504144114401c129424040101001c040054856400c12615840e01c10012820b10f00540803821072207070b00034445008805801c0301c0380d01c000700040020 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 672305908 1250 672304658 672304663
    0x1a0a0b031c120606080a150e0414070510170c0f040308070215130303020f0102031608070e0a15020105161413081504030e040c20070b0c0706020f0601030302 69
    0x2001920020000c03603041c030044500e80c0504010100840c50510081039054101200911902003c0828003140d80541e504a1040045e445080c0e945008500803900190380d2030081212034030600201c0721a1583c5a0008500c1004006010041840200d480c020600032064150744161031710741d850725004040c1540c40051140e03100c00b0f0124000840c440003155a0000707104000d80c800135801d83c4a060740c48120403116120722040300940301d00d1900e0343d0400d0040c000d580c40b0744903010100004004401d41a541c3d410001d0000041066003610300b0440c0c0e913204005800b40050881d19031000c41c00c5280640ac50300081c002400e4401103410501300c041e400140310200c01004000030340c84034080f007840c2501c0714058208204600a08200d98a0700313040c122500d00c290700076510800001021418401111344a45141000600b411807401d0148155030055010184040072a002c0300d46d40c02035440305d90007c3c0c0c40c0f503034181c024000130070010b81c0c100120003243c0f410300b01800b280c2d459a9000b07075 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 672307158 1250 672305908 672305923
    0x307180e0c0f0618040f0c020708060c07080307030207050a0303320a0c121a011403090a0201030e0a0602160c230f04020c010f140108070305070b030606161a0a0b03 72
    0x503c2190002001c007031005080c40b040f06641006001805070240640324940500110308100d00188114040011010f500040d031900400150301c50030300c1c00d035068681c00009da200030f0921080c99000c002260000364208010b40700940240e40000344d000351001d280c410b03c2d1008500140e240710950729480a0a400c9100d01d0b0000c8000e040000c1100e081041540c06050030b984610140d80761040c410040300780551601041102617032a1500040c401c0c00b0608103000c1600c84103040d0344a00c0030a00103500a80c004d120f4044004d045401100150b03417840b061340e00c1482d01c07807010940c0410032010442d20b000c1441c050300d1440c0d81141c6180300100080150a061a901032003481402d80074070041e219035048444149480f802441070450206408000c0c114012800c110b0302c002400000306100c01140807010743c0d44c4030028150482c5407958043c50742c1c201810513580203008220b0541c01c8405195251911445414404003641000f1285036091100a040740501030070b0683e15429a81c010603100d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 672308408 1250 672307158 672307189
    0x50405060327060c040617040807030f030b2d0108040f0605060f04050108370b040804210b0f16050d090606060302040f080a030c0305030a0b0307180e0c 67
    0x90807064030703542180355400c511903142e09050154070140401121301d580100141d49042e10340350600d15030f0559036900c2c007074100c0b005030070344105206010000c0c2c815601c041002c04145004203405800a00150403401c0007011150391294400031480c8001409103000010402400c1c40c248515260301e0310004200b02500c0102000e031390b400082c4072540e802010b0027a507040604104410741e1150011a69503a038420101c00341c4200404250080c0081e0701d0020407070003c0100c60240d83d081d60b48071000070304080c00c22200407000384008a1514000031392510500012548d000240405042002c1420000b51440d200072000030204000c030b0514405000f00760340186011503840a49182c094003d01420030010659400c2400c0010440c3e810380280040d60380c90703202424203550b1030203d00d50741c00d024880200480d02c110300b90300120340144099688810803080210f805000400028202010754124803108440c44002c0e55040070b0a10803261003032203040c014501d224007840002d08181100111 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 672309658 1250 672308408 672308431
    0x6091401140109330c0209060d030f0302090d051002040e010e01080a0818040501081b010c150c170c13083004080f0309090c03010b090112020715060302100504050603 73
    0x9410501d0741c1e9001c08004131000c1c5840407118189800c0c001d00d13528114034180d10444400000c1207481ca000101c000e1032940c15156505414922070003900a500300392a4140c0c001c1c0d05500203404220203000d1500444100c5800590312801c08407004041742c410380080c015101c0010051001c0040020042142034020740300c941c4890141a8002c08101c02141e000e41040c200341c0001802100020031004000c020441e55039001200e50046418a040c05400740c91020078408615a0540f1a4419001c0031070500d0311080030f0302c40341039104450f00140c4401e1801400000e58648245c090f2070810041c2c1b41000249c40c0070130b0b0306410110b89100d9103d02c00c580b01c80c04507030209075501d52000c6a00070044541900c0c1407000840c1c4040d221b801c8024020302600140d800030b1440e81d1013208590590f034180042c0c0e404c0c5211074004440c0441e454052442650b82007144001050740614640009240442d020403038508620600000901082d004814402d0500080c4026a550020f0383c1d440b40d040c820 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 672310908 1250 672309658 672309689
    0xa020d0e042903010c0e0f040914060403051c060e072a0305032d0f06132c010b010905090a111b061b0301062106091401140109 56
    0x14001e2402d2200020100040c0035101501080074100c0d00c00050300310020002e14003c81070030358841c46400d40b400e6214483c014582840d1a00b58098071042d0b02034001808001e80f04111a4a484800d803001c1d004548041a021007111401c1425001c0040690042c0003d915012445103500005040007051000f541d00500c03008800c03140d800c0e0007800f1a0301051001c42d1a06003d0f01e00c0e4025132700c900741c1c01000050b04400041c1400b03e605500204980006140c0c0d91a01902e2102c0001e8055a881070303015880c41032011050090411100b1401c11108104180c8060340b05401d608051701c05041e4101418001c8507a080448001203940640f20301405913200a8680010054052114541000814807000d85464500801006c140755421034405440700914113400d02c41070b0303180b944400c0c02000180101445142c1d01c0c00007920f0030303003100780303081c0f080d540d072404d40c1c0345038018000143d9560040500c0d032003032a207001e00420071101020300340e20400f80000c01d03211042c080d44030f050300d8060307 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 672312158 1250 672310908 672310937
    0x30403050a0c0c1401091205060106050c0a020402040f080c0405010312030c05040b0d0506011404030b040f050a020301050421081b09190906090c0f0206150103061802071202030a020d 80
    0x240ca0044a070f03000c0f0040c0d100c80c0d100e010074480c0441000d0324500146980340081081c1c002692400500ca070030000170b01c8140e1074890101d64030780c0408d01070050303400b64004800c0181c841340007400161101c5c42081a605082904c07080c41d2903002d40c5014425070409004002040c002d0740300c580c46442610300400c100c520408141e44610540c1c0c083c60300c1c0396000551801000c440d500481c00360500342d0392003888803443c607004403060140b0b000244c504480d590119001580718030346c0c80d022601c00d030207031031800600303030002070031200100d505841a820306540d10321583c2c81c44640c5000e541403802c10012904103085544034001e400400b5101003c0300148d2084203685144041c5004011104400552901c031040103001d03080c02d10690403c2030501c0f13441c6c1c104601818240c403500312070f603000381180e0380c0e03004d500e69010b240e00e419941451b960745008203001400e4049040d01032850400945c0c4c2e00810301d4002c940318000704d01442150010700000b01c1e03140e800300d040c079800343303527803804100b1070b2501c8 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 672313408 1250 672312158 672312167
    0xf04060f0f171e0a06240905040b010e0306040506091207031d0402070b071115060d0b061c0308060907170f100e070201091b060e041d340506030403050a 67
    0x10320a200b01c0c00152420800d11400c580c000e40309032250250001444020103008140c01180600c0e50b46c003080c82a034062100d4101a40840c80d1030304149030000e52804180d000c6801d1140995080d140c503041b00d4100016400d04002c00c400440304040d10625080054134000d0222400111640040d0741201001c41c0d00da6950301900d5182d60480c985a0390750624034800303001600b41d6a103c150601429003c03d50720791300340019505c60701024280ca8509440d40c0d071112480c51009085035445192080212020248014a128101c1c440c0d1250040f41c10030004004c2803401c014501010402035240003602d000741403e8143d000010151002442d450710032140d0001c80440d00008503058064082112641d0b054011002e02030240c0700d00c14241c0035003890369020311024010300000c10b665843c0702c451400c00e680303c004104000c0080c000c0c8103000304600d608101d002d6608051540c8990440c0c04036880b0465100c400280300d44110281a03d0800400c01c54000180080d042c4403004c41c0c51034516028 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 672314658 1250 672313408 672313441
    0x3020105070212061e0a02130504020c010e010e0a0c081908030c09031f1a09061003090204061202030f0706200c09090f0f12040504020c03040b0f04060f0f17 69
    0xf0094600c00e2925400241410740c4155000007428904070104032800c005100b16001d40e4401505000803074201010f10000e94000303120a070301d6659130000f80c00f04400030311502100a00e4030001e0070800e010f03810151540060768000038016000038039440681c6410103031204405034031142d16512543c1e649040381440c09001d000981501600f070a0408405101d03410f00000d100391a800c0219155420b20400780380681040309030025500b0300860b1740303850030740e00c01280d1000c0e525000c51403083c0c41c0c1c04a0292400303a40303c06403513486060400700f1480c040c003080046000e808010302401c0c7c41c0440044c4507140c44449510250503620b28040c80b2134042c0002c250b0707103030040c06800030b0341011803101d07555504000354031915005140c031250f0603650100f520040001c9a0345054289410141080020742c0850b11041043c03100308000509582d034240507082d40740509a4842d01c982c5800d0300a81203080000280c0200305981c03a1551400e80c011265803204400301c1d5008131141d81750340440c641c0380c81 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 672315908 1250 672314658 672314689
    0x111090f100903080f0a0314130b0a02070c0803090a0e0c07030c0f06021209010b01020706020c210a0606031e150507020c060d0615020c060301060f21050601021b0a030201050702 78
    0x1075190383ca902810000c00c11b08025650801900b021845031460b8500141c032255050f111608108020501602030145c101024103401440d0248c0c0e6a50039841401590107941550000b00300e000340e0b4a05a022200106031100d50013000d8a008014604188a5510000c041c0103910340f44130700307000038003010501040c1e000d04210b68409140d52894038a4004482a1031298213005011601d0b5102003645000c03980607400600075507210604004402c0825400c8020260005402c00d40b00c2608104c19058280030740c0c0001110360950402c4128601650f0340c14402c8500380a003035000030f040d90120a071150010b0000152612402c10481c20050380c1030300c1c213a002c074010842500c414040e81c000c1e0704940c0f14903141c00d04001010030036601d502903409695408001480104100c60083d00d00640074a814549441c0000b804103001c240208e00c00c2000228030380c5e8500700301c1c40d5601045581621001d194440810050000005241e4502408001e042040200e0350b1821034a46403144a1030030fa = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 672317158 1250 672315908 672315923
    0x7030204062015191119111c0c030f020d05180d20031b010804150e060a27021021230f0601080f04082107020111090f100903 55
    0x20400904a11080960000d2070000c1c41c00100e801c0540540d0200c030381104039400100e504103c482002c7d501c2d0300d0202540c90490045181c1210092005284042d80c032000e074071400210100350400414404494255500703641c00b540740d000c410358002d0169041c212420b10a41d198130741070300101e03810780409503004001502c18110250400905e0050000c2d4440940450b8042440c0e040108002c1c5800c0c00c1c00c50100345036001043c0403661020303220032260401900401d40411980703280b8a00034040f1198503400d030350b65074005a0f00300620103900c507081c2100c0b650f0380d40e80915000144403a070004600403d018a0110080900e00d80301c0c14548030405c0312004110040c0c4001070041001c001ca00c0c03c20f01c145010b80020750005401140d14002d0301c060303441031220741d141080d101a48070041c00c261007901c000c0c85104201804102e00644c5504918540000390600039000383c02e6850012401800103420310803000c40352103110401001010450701e0054070400860280e50a42c00c94001401e6076 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 672318408 1250 672317158 672317161
    0x9050706080712020702090103080c070b0d020d050a0506030706050c0f030310170a030c0b040206270411070b150114040b03040506010909050a030c0219030c030b07030204062015 78
    0x250300944418030454040c2c681140c030410056240f0221701c610b420003940600040014000306000740007074554481700030226400340b81c950300361a4164225030304000d9555000520151031003414000c0940050a2100920041c10b1180019072103c80c14014131b000c0100119080703409e07440401400e28540b07200025281d513070a0038090429820210301409d400210350184001900e080001c0540146801d503550b00a0f034195540d8404002c1d50180080e42d10020500901c076003c502e0081c00a00502c0d6501c00301c100040341000d002c20303101008003081c0941d005001280c041040710002580c440d98050100070002c90507001650040100b012190f00e803180031501280031058400114022400f2304119519aa41ca1078100c0607030f014600b0040068101d0a080000240250310306010548010200c03104440b06250304074400e0026030040d01e1082004104205001c00150300540060017031405601d01401c1c200060f12214010501044e600000701c1c115041d60001d1140081010100c81701c41e40a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 672319658 1250 672318408 672318419
    0x1090533040b01052208251206110f0c100c0c2a030c03200a15140c03040e010b0a0915020a02030d05190e030c04090c1203021f0203091b04090507 64
    0x1d00160301542d62030344104004c103000d47d1080d42e034000c003003c0e010415922950800700d071000841c10700002101c403e501c500590184501403009800a1440507401340d4582c081c5111a9191010449415009a00d41600840d03180d9000c100d60f51000d422903c12518030010000300a02c42802e42c81610311a0101e104c04010820020644c4044030301803c040c2c0d0f2804502c1c008081e0aa011840d00c95003c0c070300f032074200080380d040c5a0810281e045800d01130b07000c0c020700740051425440f68280002c0c030b4000060a206015111003040c0c00340c250002c2190504911000103041c0c0481c6020b40a01d401c00f40e40145001882000b6082c0f4250703000d02036484401484201400a0700306205000340d52140b0300e01d001405100d2001603505100050003401d1300c020a005010003044042020340780591300010101f00354491454440c1468401da00034240036949520116401c080c020709142c02c10700400500140c401c002681a00c0313000b03a164030b000450700740d20001d002000c420074010486e000303440e400580c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 672320908 1250 672319658 672319717
    0x4141819030201020a021501140d050309150c07060318080c0708010e070e010806070f030b01020f010e15130c030303020a0e030f0c01020f0321040c0e01090533040b0105 74
    0x401c03803919022501c00c2c415607d510451b18100740600d0300703007180c140f41c61040c91400e601023003002d501400982c1d2801004002080b020b400741203c142d140400010405080b031400c2018100403c40c03403400300010701c4041140382100c40c2e01000580544004510174035002c00600c0030700000d01920f0000c0045180c07042030251504418490380841c3c2c400d400000664420100c0c442d80324003469070f01c243c8046031b0440f050340182040d14006046210b50422944800001d1040107607181c1480006d00c24180c0301240c0302d440c1d1078002e002245001e2002000d1002421000303406060f02d5041c00c0c0503032118020001100c5038a040750704281d2511402501412070700005c01c3c5228196800c0e4250b68426500d4400e85950f8410309204d60041844049200c810401807030391183c120b4402d41044103084c2d0b1b60f07045001000800c2e00b02011013640c940500c440c400022103880c0e1030940c0d01520850540b542c22041c0070012903809641c0c0640c1c2c8421150025a124508a440c04a004409104072129403101c040 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 672322158 1250 672320908 672320917
    0x9040b0d03031a0906090403030c020c180108010f0b1302070305130b09091b0414130204060914030a0308010501050306010311030114010311070b0412050706110c0c0414181903020102 80
    0x4003e2800fa41c0d420420341000308081e4410758010b04500b10b02d0f16a694110028205070290300700f1401941d40b00d00c1e141d42d540d20801a04003001c9811901ea5051074900303401c40c4e03540020381031541e203810b12216080e01ca14215014001201200503202d44c858101030780c0706c5c030a904025660540c4118017040a60010780a0280700500742e800803a1030340c07a20701d040f248960141042124041c144000c00802d82c01884548140b08003a01c0450505500007441050b82c00c40e400010201c3d0744074130140120b58800c4070405c1024022401019011100d803000b419003001809107a04200000002600740d902a40089151551004400740d4940e0b449064250211104a00500203818040600c1c88010140261641280c114091090603205d075902c80f1480060b5040400078402e00780b102c400400d68510400c404254884c001c281d0361049000301d541408140070030113118914110024049804803a0072690200f1240c400050140444104620b8000761030110903c1c0d080e2201c0fa08105075040d000380 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 672323408 1250 672322158 672322181
    0x607080712050a1a0d081e040905270c01050a1103070c410405130501060e070f0f02070b0928030303050f0c16020a030b0403020a020307060207180209040b0d0303 71
    0x2200c4810300c1c0c4c800c10a07280c2019102502c840000e05c050381900c0005031081071904007560256181c6540c41000d0015110304032400d03501c030703403016010300d0140c01645c00c601c50480c181000303004004401c80c0042d1550040b008507104100e00c80e0800d061a04c070070011900c15642140c06062207640d601d1492100407042219000030301102d0398003103400444030321740703600201d40d0700c062900a1030200148401002d00615080300501e01800d00c0001c10000c2c0303e4440540b0030440100d4403403a241138040c045a6095034900204410035100400701c07540031401c0b40a5408920340079035510910000920101e150221105002900403040d00006040031801e404480c031035141481190384402e6442c540540440d130ba20440c500400004464000341042c140c4550b1005250507101070316515030100c0080e00b2141100542d002207040c80561408220000062006100511010f4204024371045802c0f0040c0b480807542c010460308191b03640c540001c5410300024261040011050400030060041c180b000c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 672324658 1250 672323408 672323441
    0x18051801060b09040207050313090b04140402010206040b04230c090c040302090412090b040806090c2407050f030f190906140306150406020f01060e090607080712050a 73
    0x4420044040c0181c1e0102c4424508503420480803d0612000e5848034004541c01d0200300580c48046440201080182034018800640c2c0c00d03115090008880d41e03401c00f45201540c00c020000143c1e070004081d580503901950400040c1c82d907160403000320f21030100c0c4991202c8159040c1220007400a410303907826600703e070000c2098903884081c3c2da91384210300000c1e400124400004000ca011481046840c4c10146032461070320380d95400c05540d40d0803503008038010303401c00d200384416110200000c2d030100604407551001400c40c210004080c450307000601e5441c4001280d0502445400c0c04601608c801d0042a81d95840d002c00400c11a5400101039111541030303a100c04500360302c00d0001405842c010303190042c4030608402c00944c16000180065400000010146014525070380640002c1556400510400d10360f20007443c00c0d51440d0b04605034461413001000226080069581c1d00440c890400e15581d071124041220602c0c1400d50700c4d24103c0c2003c045c800307288107a43c000000e841e5140107 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 672325908 1250 672324658 672324691
    0x2061605120304210507020301020a05041404290102010b09100302010912030e061606060b030714090d0227270d09140d060906020912061b0d061805 65
    0x30158881c0010740c1c0c041c01c0d2011890b4403080c2180c0d01c002c21300701c03e0042e0074158103190107540002d007668408102ca034001180460200903402c411003401c01000c000301d03814000480810342d10300d025110710140f02564016940e41d8226039000307500018030508003800710f031401e142031080310403c1040c51004900044204c4c000050680401e20b82c88100365040d525840107140c1c00d02001942c1c3c002c0e001c40c60b07084030307003400d44e000041840c0b04030001403201920142d149d1030400c00140c44460280c030364000d08001040700003d1980c6007000340000980c115500508595150114031015410701000690b114180c0c0034411092548500178035810b407202901c64440f88116070003511001852400d101043c10181c040c84a0f105112079003442c0310303014120002c080e0f0940c83d800103440c070415090321002c1d0300060301c103c0c40c2010b0400d20820020400140400d0030034031451250800c2e011100c0e00e2004d00416400084807064200c031005100c001507034050a210a90003030001d100940304400107102c1e950 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 672327158 1250 672325908 672325933
    0x40306091a0c0c060103020d030e0d05060f010f05010806040c090509010b280206161e120b01030209030a06200f0d0b04060b091e101d090609061c02061605 68
    0x2c0c00c461214003e100039010301d9107581d003030029141030501c04605021007011030105e280c485c00b480190440c05500288180d0070722040301910582c06821050030340c0034070340d0140040d9030845440d642148080e09d00185041546400300c540d030205800c21540122001c000160121040016010700032030304107102040b082e02602c10031100642d9151401682180001400d80208140d200d611441203042c0308205150000c265001010350005c00401f08030021014107603a1000c1c407c2c48404a801c4c2002c51902020100003a902c04c0e42e010000c10441c0c0b039032840041ca0185c1c8517040148003c0c010300d02c6c2c460801e4404e48000340c04c0000d0090344249050150460fa16082c0540b0381212410009145051065400c0c0080381070203405600c0d03810721043d80c1c12819111240c19070081401561070154041a50401134003200f804500c1e588115200028080c2c076075101c441160b0003100841d20003582440e01c0c25201742a20003503002035889080400c0c1c00c1c03400e01d5140002250b540c462410303a40d01c2540e54 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 672328408 1250 672327158 672327181
    0x10603030c03090f15030e010902190e0f0f241503041103150109020c071509081606080c1c091b050a030b0402060306011403072109050a06050606040306091a 69
    0x1340f00d1131644d0417069402c920058004d034028a4146003040c00421250301c3da401250301419540c80e100108920720008110101c401160181c00070400c6020f9156420b040c00c0c1d51821080142007000d040740010807001000007880041c000b1810301400c3c3c0121100e6000a000e002d400440f000d681c4428010803a444c0e83c0780100c1c05d0040504a40c4c62070301d0507400c00b4080c1d002500404541c00041c8208040031607950f80c104c1c0d441144601e140c0d6031030300c003e09001c521400d100390114907124511351054103024144d040350001d540b00800138401503c0e809a130880005d64030210b008001011b1400c5462001c1c01482c8421050f011080052624031a555070700303110f802400c80c07201502d803040640c081401890042c0c02507030811814036099507401c07098102c0c00039541c41074450301c01245283c0380303030300b005401e01701d0740408564010360070440316501e519003680315001420004c1c072081d0b0347d80009441c2d5a403030003900c000d95000f00303007044406d20500e805454424024513007003000162100040668908 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 672329658 1250 672328408 672328439
    0x1606120609140a0b06090301050a0219080906040f1703090a05011d1f09021c030305071d120304080a08071109041a0a020f0703050702010e01020616110a05010603030c0309 75
    0xd0252100c1ca0366910f240c01d002481c04401c25a8884000c00c00031005a50034025540107016821005a481c203c07220a01203032941d2180c200103020584040140c2400301107001544030b600314072048031590b042e16244c9183c1318035400e82c10364242e0100501c0780c0c21400107850a89240314100130001c1c034040c0c144280c03414030003c40c90300c80f0740c0c08950524548c400103800700e56401c0b2040342c0421507c4e42076000070f545078240c1000400c03101312101144103255141c06280c0d0015607600340b503130400120075100b401d0420b4504034240150303d454031440c03041000300211001000c604003580c225941510380300d20507a010040a488004d0440010b118510740b11100f1030145a000e510301c451006130484200b0604801007241541030340c20701800d0827128000c401456200c0c400d954090381e400045c4000340179903650710001030442d80440200102c0f9401443c45044092203420214200462207010303030f240660200c4020215400d001c000000c158000050b40741c0c89100c0c2c3c4810100320f446072602110b02c1038 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 672330908 1250 672329658 672329681
    0x40e150c13050618180714030f06060a0e0306090c0301060b0414150d06121202060105090a09060b06070507061b1205070201030213141203190f021606120609 69
    0x100072104100c01e10700307003004154070344001c994402c24203810000034202d450361036812030401c4040b2040142c5181e01c07507403000c101c03280540c1031401d60130807480c2e01c074500300014002380c000e0100017502c3e5a014002d0700c0200f0000002404c58181b40381204140b5101d03609046424000c1d0f080200101d441c0b40f001c01540c00356038480440041c0360f89640e0410084202121100540300c0080020a0000c2d0303d6008181c040c100005080041d00c05601d01840a50000c031561000c41d08103100500c0183d40318070070240c000b000000007058101c56400c0c018020401001d1141d4002d0000413444108480480e1000407241140c403410a4000510034484259104400c01400ca03c0240b10484486004101910250f40103140c0113040118001216403002c08503045a002d00c402d1150342d00951800d517207502074149a1001850078104c4c1303000807140c00017680520000b440340415607010b00c0d40c4204031000c070300991094440c03140340d9108000f41c087c010414001034198108040800e4420b4030380180d400840 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 672332158 1250 672330908 672330937
    0xf030902180c04060f11121615270b1801150905060a0e01030f0818041811060a1704060b100302040812040b07060c050f1813050c0403080c0c040e150c 66
    0x1045850481d5440c0e009401d405050700fa40c40202000c04d0460b0f03031604034441d90b0274001581c0700350701244503402640503520014002c5078840101c0041c411224841d00030700c500c40448901c9415041d090f001d000058420750134640780c60b4002a02d461a03030083c9000e20029640c170401ca90312403030401c0a5100900018201e055100d5035500000d90031002842002c040b4000c10089045841c000b4041c0c8101c2e00c9047c00d180400d40041e014080f4201e03070540a034170121350040c504000700c41b0140000041e0080c01c000100f10780002820f00c512608000540d000080101d07290821401c1c010b8001c0d00b01c0d0140c45468401ca075100d50f401c005a00031201038604104010b0b0422070280d590300007824009034080304104040c01400c9541c1115800f40c04c02210441c180c0280e48003c4043c08142200040c54888440c01c200901000001c0c845c2164242c90700901402d0f038a20a0543d13540c0707400f40380d001c00d5400510342049425080c1c404241c1034100c048510100d0720580b200ea45c5084980645882c221120 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 672333408 1250 672332158 672332173
    0x110904060e0403143f010605090f01030b060c030f0301030c08070e0a05040219091409010c1403040305130f03030206152107080715020610060f030902180c04060f11 72
    0x921081d40076000d1003a0358001451040092017401c09400f616075042d440310b40b94240004511700f07460380582d0140030185811400c0800b001c002510380007610030311368149aa121803007503444d2031b40ca04681800d4602011260b40d8003c2d940b148480794424030003034030191780021020403180404074081c812070304140fa0003802910303004031180042901500481c0d003c41c04020358551000c01e40059402450140f50000380031403409402122403a0007030441401d07924043c4200030142d0002e000c4440a00203805654a075640d40c50140c0303451007444032580542d405c99400041c01f00307842200c10103907842642680d6181d11651200306400e00c041c0395540e0b0040e8018641d400b2807411b03001840301503040300101c407d081d83c0c0b244001d08015032904108132208a19100300d0b500354041190b01d410035006406440c120f46410b40c010310550303400c07070107404040d100c107000300540d502c8411200080309210107180340760808084640b0607034001c0c45082c0c0414200c2e50f50740b510318015010b0343c21022007500540000c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 672334658 1250 672333408 672333437
    0x105030a0308090109020904050309030d090e13051203010b0a0311030f010b0a09030f0809040b190e0a0f1805010b0d1e05030f04060c03090e27010f110904060e0403 72
    0x200a00070083c609942d680c43c0507001680d940d0241c0790040f4011406142c2d0b6942d1031042c5400c00303180600e03410502c0388c0c021042000044c407035201503001d101311a901410345810310b805420191101500a6040c0300071001207282d86910000f000d1280d11034504103c121007400060507140012074009080082010041024840b00c10007401c0c07150240c030b454418941c40365200124060f402d201502c00c510003054110243c1460b20031400c105038101c0300d445602001c2c12100340140c1c000d000e00d5841d142403401046500d041c581100010f08070355042404030302c03030000030b40b44032132045071040d5110343c2820682006402c000d40c1104403250031074050840359103600070764040c07111149000c585ca44000c00c0410300044e14100600081c1c807855440c00d0701c0261350b0a00400c400b000b5049a00c10482c49010f01826042c4480018041e90380d80001900c65403459813030078010002e070107110116606101fa02071242c9441070044c02c403020125400c01440e51100d0405602020840d40100440c0903031604852 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 672335908 1250 672334658 672334667
    0xd1a15030309150915040305070f260a0c060f020705240306060f040b0705010506010f050703031a09090f0118020102152a03011401110c01050c0a120f11060105030a03 73
    0x2902c90f9582c480c1e07440c100400c0041030010413040d801d11746507030b0b01040905c1001780c2800010010500c03950301c0e00000341464a0740f90040c04800319100c885454104148800c80240140740da107030b0b00400200d405580c0c521001e003030120010304140c01400788240200b481d10f8100440c1070b0301514000171a240300c0c5403220000a41d80040c0110b58400414030030311444881c01c1005102600d40052119107455061408a080d150040d002c141841010031040303004581c002c1c15540402d07003501c1c0104801d000d0048480b90b2408078110300d500048100304002000e80c1c001860558030304d801000300158040360681c048039020201000340141c0241c000b55014544450706542c100c3c3c00f05040113231000407003004a8140c0c0722070045000f82840840100400305501510001d01c12003070a20b0002c079007020f410320b610342d527a0361035007810f00c80d0100e844ad490860410003410159072188440010101c0401c01401062280a21400007880c00b0782c0069065400705440d4101d49018005080007005554180d8 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 672337158 1250 672335908 672335929
    0x8070b061c050607051803030c01020417070506030a1e0c03051005150a1107080d022404020a0e0a15031a0106021204092d060302040608010c090e090c0d1a15030309 72
    0x3d4141c0702c40e8410880e80c2d90140010003c5109e080c00051303507240340c1707501c0880000079601000441e0700b05010411590711900c0440c0d9024220a8001440d084601030f100c0802544048200003645444030100b00c140e0194030660182d00500c89800450340c0d607004100010814408035101360b00700740410007a00d8041c065403101c3c500070509581c5040d490328141c2c2d15201e44a142e040050748240e0701c04d80303490049200019103880c0806001103515240e00422059055407007541042c4640708009400d04507558000040d12600301c00b4851615500e0900001000e4810340c0d021804518000000d180d41c000604030080402419155050a181c40107403001420b20b59091090300c841c031104c0c000000c045215900c4024030050b40018654114011311046900941003c841685028012100142c0000c140022200c1d1008180110358032280c80c241001e005541842e00404040b803a401003001c800004400b9000000c1003500a07a2003140c4155840e880c4400c058141d0010003403010a401c2011090 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 672338408 1250 672337158 672337177
    0x5010f0302030c0f0109031202030304030806092701060b180f09090d030504031e080a050a0612110f04020406050d0f06141908060112150c020c061608070b061c05060705 74
    0x6c0030250307900c1d00d600445985030314103900180c000104100803d42c01c00e81e20b581001041e5152092072904048031810110b14a80142000000741d106807409202500400301400003000070b50f440e444003a070200728490741c014550780b040d00c60011075007640c104814114401c11100c001052110140c1406070002c0901070426810091042660400807085c02c82030028a54196502d4105103445041d80080300c6005d0703d81107159040200400601203445c106010301600820008441441140001c08444040e11110707009030011500080c41901b03d0042c0008081141082c0203c0d024842d0340000c990043c00749100382d12443c0040c0345039040400400c100700380c1c1420100c50040c2ca812607075107406000d0b40010986641d0030041c0341007003447c00d01404911a184800e101040b001000a5220344c1c2c1d00341c03010300600c00418241032104074074060056042d00310400ca966945142013035011020105c035054001c2e804200c009800550b905542c1d40c0c2d07150030001a0509448459040704c1070760002851 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 672339658 1250 672338408 672338417
    0x140f060f0d180c030506360106170703020315010302130f0f06080601050f0d08030a0b0118030501140117100507120608070617090619180b040605010f0302030c0f01 72
    0x44480b0090106800a4051003a0416251942c40e125290034402001d250b581e08100840001c60300d6000180010700c000110300514100219141d03a004084a9100c20004400400f4000d1148400b0915006a0b4000c0d425170b10507130f00c2400745035803508080c4002504510010f5560042c56456481101c0d1111040740229004001210600545610b90012149500700c0c0300100140d00d400e024800029805030350001c1142800e48807218140001414143e9041d21100342e9410303030f84190a486a03040c090b100440d085604c1c5e040c00350080c10009403651071440c181001146801428055800c1f8150602c010200c0b0b140c0000306074090080548603c080c00040d0a1a00318580f0b280284806070403100010000e681c9484001009083d0320b81d0403142c0c9109203c18442c2255000c04c201e64001b850000359543c1300c02c180c1c0f40c10f00600d400651811151165102c0404100204840d58055030080b94103100d070b41d8071561840d031340343e01e07174440294542e000c49680c031102d0502c010354100035581410b0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 672340908 1250 672339658 672339671
    0x30c060507032610231c050f0105101703160206090604090e0c060310030f1a190c1115040606050603010b0c060a0b0a1211060a0207140f060f0d 63
    0x3000c18078848100c0703500c8030f44000801c005a550b40c0080c50080c62242d0740a207404144100e40c80310a000c0e800342601900c100d0403010320f00e09131030100c0801c1e990f1000454a10001411907280242415181c2e2800e01d4200c944c002915441400400149565000a145403925070100d290b60300700ac00100320307008441445062099500e000250004042240010801c05003402055003051012203603148034010a0091242e0b54aa44c004030042d654800b207045088511400c0c00c0c8407900241c038000d4002e01442040121007901c1480391030303110524400c20f0040029044040e070303500907500000d90385170740921a00c04414440e021100e421900a074000240240c940011640e03581c02600301c000b10f10800100d92400e88000c2003c1548a40000010040500030351b000030450304441c403c0200000c80b00f640308090003500000264003000041445644013804036019440700e60f40e2003503c01e2030722401c00c1058181020640d540c1d10719002440c1514222071000e8414035900640c3c0c11200f030655602 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 672342158 1250 672340908 672340937
    0x303120209220e060109090b0c0313050d030c0210060b0f07080408030304081e030c0d0b130905160611030405270c030a0e0f1b040b060310080c0a030c06050703 70
    0x450440740d0340c100a004540003460840307503403070490181c2c446c503401440e215081002c10074035001c0580049403192060341d652141d420b40301a11483c2203025240e0700420051051031601907011450b4030401d6020b64070300c03d0100d801c40d003c841980c800e0070500d550411881140c4000c0e1801080c0551040341c0a5041903103941c05140b5541041b1000c4a840c840000c0306000c60386100c416420941c0a210594590300e4075104003141401800344d8440110388030b000c0c407030060303881148480c5107030300c0c0c40780c100420082402e040e03690b44c844c0864601d18511809020519030320880d43c1021144a05009501c0c0514000038400e407040c40c4004604e103000e041c000701300c110760342501043c0941d684440c426100c0c1040349a9000711441d075000c500c0694400f06100b0700c10340000c40c0e10500c0707100c0062840303010420903002c10003514040071400c0d40007800000b0042c607007400000c000c0946645600b1100140e40c0134082c0402c4480e1800301408040943c2e008001c854413034030052071900c4c03191078890f40000c90003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 672343408 1250 672342158 672342199
    0x50c071a070b090f060c0a0212090109031208180102180f03210d0b0d12120f0e161e03080703021f09030e0105030c090415081c08060306010303120209 66
    0xe4842c0403c5810061a200001d0401c020382a08a00e2040c0d01510b800d01c0b402c1c010355074025020401e0780802c0041204080b44e802021640c0040d43c000e0800d904100703403540c0090080204a51003900f00450b00f0494940040510903219a034075a02c8246510a8040080005403202e561001c3c0d4940b2802e0201d94022141408414403800c5c1131640c541c6590301080303014280e03204452158040c06162a007040420038010104440000d2030900d03080d00b807050062280942403403049401030309d003820700401a100f00061001c00410f41300030008007107078070391380c0b40d100c0103464080d642c0008500a4040c00400c45020003405034500c2401281c40c075079060390103c000c2c0002c01e40130040c0c0303c0d510901c08050580200306444690000d181c011310f58684000500c110780542d4205070700841d920310082e86003900d411188c00142001c1d004a86500c0c5a084020558146400118000801e001c0100b0741c00e040025456059950544400c0d410004100c1c9160081d0403013044564070818031140e444442d03400 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 672344658 1250 672343408 672343411
    0x50f1201020a0c1e08220302030f0a0b06030607050703110102210f072313180204150905060d0b03150703020a110703120c020109090e03090f01050c071a070b 69
    0x10b40d21861240c03c0541040fa0380040040c4244c40712080c800050701c00520582d085803080e0780d0b28030b015490a034001c0c200103408141900000d4051250241c0b4095140c0e00040c00ca4000d071103020300c14030315540c00c070905850b244140c40c2d00c00807036018802240000d004101c4030469503440c100060400b89100851210345a03032591000302d007200b50b0140810400a2044160b1142d80360404442c0c1604803409a240300000b42441b44608001042c40329042e01201cac0100000c007803128000041100d40d2a940000398014400c0104458045440300c240c68083c90245040fa80001e003071500b003609141000b0040c229102102d0b40c5809155080c403030846c0d031031030a81d02501d0b25590041e1102500040a49040c042c06203485d070740da001020810004075450030504411005180040e1045114401a030780e200c01c9800684400b420080d000241590000c0034103140a402c03260040311041200054405c1d00c202c2040610f01d82084200f03002d0300c0303000c2c807900025910300000589040230b02d849400c041740c0c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 672345908 1250 672344658 672344677
    0xc0d0b040807140a151b171902040b09031606050315040204080a1a090a081606020912010902150406051206030c06070c0924140324040b100f050f120102 67
    0x4900d0b10420150701544201c40144926034061b070030380c0300c426202416a15022440c2204801c1200000c1c00d0000f000031014000c0c004030101355101c0c0d444001e0030019400840c4998007d01c04e02d480502c50700203244620b02210f140c0d4035540d24584800d61241568150040c1c0740e03800070f03000c00002440007800c010024969000f81030b8800005101c40c6000e20482c4050030390000e540c02540c4071008141004100c81c070a010b4134200380b0701c000341440d01702d001c1d02a8800c00c941c440c140001440c030102040d01325400040c07080b02d100c00b807000c0d214240791903400b40b03000d8000094018800304920070344458005800c100000e04840070061250005503269002c01022500c41044000030041c18086000e440000445407441020001d0310a201d4403480c80c092144651101e078004144c145618140601d0001107500a000c04600100c51400c420346207017510203c0311540700c0d1001805d1003000d2900641510411452006807500d44401c02000e0a1404070b8194403950b006550507404900b440101206c00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 672347158 1250 672345908 672345923
    0xc030603080315040b0f010f031a030a030f08070f0f050c0a02060a1805060903030a0807030b15030103110d03140702040216050708070e040c09110c0d08090c0d0b040807140a 76
    0xe0307100705110030340c2c40b1101d5440c083c01c1e006e0921162030780c20070791000356003410b8500007405400c2000182c0010300b0004955425006007500032042c1940b01c0f40e034540d1880c2e00d40f0f42c03980d40d48980b4011140320105810040004006140f10241175100e08010201142441e088030a002003a030001181603200092080210743c000c102c0c1d102029880e10781400406048071140c0c106038134100841c0d1030b4031502141e41e00b004154400610b185003c0e0344440c80000010300060207a449140d03003003205500a000a4501c1c83d00f0a0f00fa0340b030b9140c451244054280c0c9940c5040310181d038440800340c00d42140320100e0344176409101c518040550b6034504410180540002d10030b0500c2c11a00a0900d0084d4210030583c000420410010800080d01c03030084800800f00050300f0700d400130907903040d405003500700d10b0240140a00284155030019a190007426020191200c0600304003c104a03e405014024880103410300001c0215071080c02910840e800780340003076800d0445914180c28040c08840844904 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 672348408 1250 672347158 672347191
    0x121e0309040c02060415090206070507090c0e030c010f08090102041205030711031513030c0503120f0108070602100b0301020f0a0903033e100e0601080607050f04090c0306030803 78
    0x1454140182c1c10086001d002a100b00d0030300781c44401030684042042500b60303803901502000c41d08e43e001118082038229050b6054240c40f8040c0102401c94207018600090306850810114a80410143d544200584501c0400700e001c04040c3d440d40001002d81307001d03540c2403000041c800c1c42c481e031b40030550f4882c0300035650712807041c6071814115a41c014034900035440f4035402c801c840e0214000c280c014088001a00c1d41198520742143d00b24100302004000b1300010507403503103241c481c00466000e440c041e9280032190b0780700c80c3c115540e04013600c241c0005134052907404000307400b00c3c0e0050050346400340c0003510348840b0503640c24050340100a080c00080040000f0020b16a01507460a03841d002104018020004000341da2000f0840c039004a10380200345200c00c00c0040c0c10001d51185918880c410f00c1040040c1e01d12940b20202449104040d001d5003001810030fa11031000c0b01d600c400c041403030b103040c0b90511015800500d00000803500340f40d940d14010021a0700b86010b9442200e1008040c0c806 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 672349658 1250 672348408 672348427
    0x901152c270a050115030b0f18090f0c0102121303140616030c0f121e0b031e030a0c145506060302060409021905041202121e03 56
    0x1180700061050303a802d4540320040c01090f001d1010203034205540c1ca00401c4d40d0350180d00080b1100c92041881e43d00c08601f000349000010400d4016104440900550348058201d45059890b0300074074900e103005030004081e81d4103c2c1c08100c00341200d04c2091710000b0286480b591740408190b0009000c0350680e000004005801c031000c40c698100000e03500c4e05101c894012040039010a0260071030f1710603c142c034541a10741d94080d500803007080d40d07000c0e0304410b129102840325004005507200c0ca40a800b1743c550904d00c000c030341c900c1c00542c0c000c40d90056282205410040741c00001c1c16500712402c140d20410a804844c0800203002032a85043c01d9034401380650155441010039410566649a617a42c8038070707016501e40442a596100f11260318410180910704a0010002500000e611280202d000710b400d283e9640a4549000b078285240c803020544241940d46020300d100310303a64400b0248004006003840b00c40344002403c448110741001d022041d80c120192000f14450380316a0010549001 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 672350908 1250 672349658 672349729
    0x70c0c05030d0512070c020604060c05030d0f0f0606180e07091e06080f0601090303080627040204050c0301030c03060b040b03030a110d0f0914030a05030708090901152c 74
    0x7001142c2e07080108111100c0e44c04108c481c0120f100d8003040c4006402103205011007031084410703145040c0400c0106181c060040c81c018a4196050360703480d40303003000110b1814062944100e0200d0404080000e080c500700c800c100600c0010a00c50400060920004850b101e802d2003001500764a0010304109050131401004c0b04401440b24440380d410b0014021030340d03049002070096075098580a0825500e420224605483c00c5441c00f00d404504041c8030244050103e000b40aa40708440603c21030301c40000304e420740c1c002800007a05151004000300000f400580c020a01d103d000b5002103080c4010a00080c110340046101e40c0100e84062507034040713882e01388407690610111313060040320400280002469440c0301d014a0460700040b1100c25155502017150078441035011f0222940c0f03100d0703480e2046094208c03000a0b802140b510b4004618521195952400840d21b5554041e002c8903442c2c02051908201c820600064901d100d0015182c0318810500c00703034903034800c100d4001c41e1408481c56 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 672352158 1250 672350908 672350911
    0x230c061519062c06040902030a0501050607021509210a02030c01080c27060417121611010c0209101703071101050a0504090213210308070c0c05030d0512 67
    0x41d00c1c1c05100c0300c140206508150140c407480f0b000144001880403412071a1001e0200c030b80322542c020310120380000d01c042e0540056200e880031110920a50b6030350024040c26014401000b0f61103110700541c22a032300a0706000e80100e04009166404440c42d4200103140703181307541e60641140d08070351294030a40c01c1c00c001c2410803040a01e004055803a10360303003021340c602078a0007050445520700211900c010180000e11400b0800400042d81c840d030b0313003200c0c007615030008444084500600da8000d8240100b0304c1a60303080da003145a80030041d480d035591071143c2c1007400c0740700e07045c03000e421070103400b41e11491141807084245019074882141401004243c2511800c2102d069520404c000750004044c0701041182075402e08100d901c3d00d86410050350301c2c0c05260490341c000c5202041c5820001841000f03c4100d13001010400340e44603c000c240c000141c00c0c00305c040c2c0441c0044000c9503519201c0c40321100494001c4040c40856920341c80080e00340b03100a1301e080005040800ca11142442045d00725 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 672353408 1250 672352158 672352189
    0xf031006080906070e06090a05040c030603030f080c03040b1f0b0414040213121e030f0906030c0801050f0102010608060901020307090e151519020715030c230c0615 72
    0x24503a618013420300421070074140a01c24050b1001040f4581e1580300c100c0c40e040501401003090281c05103140c40203005100703900c400e03400a00d200f0b015500190242c18040c0c0242e00510429145550f1f0740c032100034110014150080d4100003a100041071900600d544015000300f41040e40d8503481c1064110b00b2114121040d4402d0380304005c0149002c03074450404044510b20148000c04d00c1e1141082d0700f828a140100e1041c00c0003000c0305504042d40045c00c1803002009456612040f87c03268421001c5901885415002c182030b080140060b2070078a980015140051002188164944500c40c0c24a601070300c441c05603a4010062006c9190080c105e1800340c000707001c50001c603181c2090001a40c407084c03100c107801004a0b01c0700314000d103446800c94001c5031311109541d00141d26400020750320a40d03031003900e10700042343e881c0c60740507442409054501d0080c0d9807112441c14030042c00954040b1800c0e25950b10748810041c680a00105208081c41021040300d8803680d508500b05000680081a802 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 672354658 1250 672353408 672353413
    0xd06080714130c0207050d06021306031103041103160308090301200319020f040303020f06060402090307030311070914090106060201021c022a01091a0f04030c03050f0310060809 78
    0x8001c07464032000c0c200c10904400c80004100340f060400140d0a0103034903044503030004c030761409a50a00590350010580c1c020020921800c0c240e45403021030495643d980140c0d4580000c0000c20f01041d1021030804416600a06441d550541400c40d0b0100c1c8816038000c0b64210780c00b16040b165480c00307102d410b2001d074206903000c030480326070036100034544001401c0d81e40c2c681480c9000541c0411030360545402e03103041c6104c030b039459451f810041d43c4c1d0040062841d00302c0c4038000014410342000e009071a0100b8019004000c911700310755013900d00a2591900a602e44680c0d074001501100e07e000d417403813042c24090021140d090801809094682c00e812a400f560300401c54424044500700381e07030b14907030500f800050321403010080d20040d85541d040998980c00c0081c4800c1e00d01101940310940321445581c4a140700d0003061080720111000b12209503c8050030320001e4086805805551001442403411510b815011354440d0043c1d0015118440502c2e0b07010402c1c4003482c0c11203800e58105444800 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 672355908 1250 672354658 672354689
    0xc0d140a0f061d0403050d0b042313020f060706140103030e0306090102070b16030e0105070203211611030c06090601060f210e030d05011e050a06020d0e010e060d060807 74
    0x10000341c103c1c000c0e0009040010014400448031400d0740402249000200240244010b840c100384000c4014800c1c4074030702074500040789000030410541e207405036000c0c20400d13042042504114181d00401800d6402c0342d110103400156182e080e400b039000c0c41c443c0e21038201c019040028185407050081c208821680b04000480200b02460381c501c2d400039103248032840490589400300c01524014011104960900c070030710200076000303c041c0480714858405c00c405030007143c05c00d04004500b915030000030345002480d01c81d014441c3c084502600b8601007120726144400382d44924001003121680115003150780148480d80c0c0c864885071694401b0300d0010341d900e00c0c850071030075208039503c208041e039a074615084012250910030f1314150303640c0304010003c541e510400c01c10907203229412880710000115010640340340c0b441c0301c10140c4041364020003c1900c01b40c1c043c1c4000a04500300d6051100100c172901080d5030b800010b0901490040700843d0180c9485c0d116850b211290700010f0000b6003040c1e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 672357158 1250 672355908 672355949
    0x5070305091506043804050c09010905060a0309020d060c02011b08070c140106060507051603260702120f0c311104081608150c0d140a0f06 61
    0xd1a5504203408882c005422503a070412500d5811000403102141d07003110103042022060b0403000c0c1401710b030070b94042c1b20a58030f03403111418a20a5021480c0440c03019542440385003084e4018007440e12480c24001400d018a4000a4040242107001c0b14241c1c1c8903c1c1101e007413a4203004d00d031f403140304000d04120701892035240513108240003013049003003008140341c09081c80f000030000c0610404c0d510080220907120311004010307500c400c0007550300b0b01c100034000d0001301400e031111040b60703001142c9118291045078000003195588140260240085c000c41d00965114403802c004011108010520104000c01960924000141240c8a90100801000302e100f441615a0b0b01039032082c48182c140a0b00c214a030010140359001c0c107460725004c03601092900c00068500c512020b808620151581c0d100703091507640e21075418002000c00d40a000c51100803c50000e425009140640400c2c1080b19460b541c040010864040400c0c82d1100c0c2c1582c6986814032602001c3c0010548140f05c1c001110b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 672358408 1250 672357158 672357193
    0x30e03100924180807030c060510030506010e01030b270115170105040b01050f0a09050c070c1a071106071a1801050421090b040b040e0c07020a060315050604090507030509 75
    0x8640184c040c007000104801010310032400c100c02c0e560322500070015807c100903610b1000e40c3e80d00003203c092098000100e0880c6034244c10034122a4400858140755640c81e05071030980c0342c03c007032441c1c150b80b115400d541050401c0c09900340c400d5441d400c102c2c07810b20740034004146545500308a1441c2c0d240000b0f01c00460489074255054481c19500384140c420840c010540720b9582d50b0240002501e050244606989450005c00b026406440080107194035414010004c0c40d10710b4002c40740e854200320690010b0000c55002810340d0b00180114100180c3d0740310403032020300f0401d100780014401c004010380001c0c010100340c0c5400d41d16008128900c0c280c0e440348000710941015043c605501201880301604c20712204028140b4040c180e030326582d40380c06066864119000328411011800c001a1541200006030348006800500811900c1e1610341e0075801030a0102c03003501c3c00009404045020b894042c01000100307524180041d0318070345500e0090407580041d0010340305410400650310200c03030341c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 672359658 1250 672358408 672358451
    0x708060f01140a05070602040b030a052518090e010b042004210819080a1802041d0106080a1a0f0a020a09050d14010e030901020307030e03100924 64
    0x120039030380f41d403040200801c2e1503a00811000170405400000e01040e51101e490155000f0082e03060103116645852072606000710302c0d2115028210046c05807070444910459030608007518602801801d540c850b600d140c00c0d6407814801c0c41c0e2a039101c2c0e80384002070078a4404c15080449007401e410440c0390017450070070503201d2031181030300545100e8140a44260f001c1009010180d008100700e030740d09060015600c1c00c2840000840100d81061300103414000c0e14010b070150030f440d6000c03000041d6016400c00000300501c0c200c103081d00300e90140c002c000780b100b449a840500307aa10002e0003031076064500243c500840c07081c2c90140e81415000c1c40180400f1101c1c0036000300c54084050f84440e120f110490b0341a2541e80659400b62215200c0c0d41800030403140a9a8052954000e204000c2000041a40c92080f52a03e5005a004001c000080303446035050032303941c041c003e0548086a040d400c0103010f440c50340300280c4000f0341c1c01c000035903041d00b07603e0301148001e000c01040c020000510308082c20001c1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 672360908 1250 672359658 672359687
    0xc02090124020304140607390b070b0a020a0e10020f060a14041401150b0c0c010908101d1002031f030c0e041e1103010c0507080315060f03010603050708060f01 70
    0x4040703030180070032807184e103c41c09030508e25010711400b422554806104071040540024a8400d9800101c0d940d8071450440344415045101d021440d101c0b0032503c002075001e0820001000b2008c486c02c040c0ba91404806640d16019500a10302e030454406010709103180580712442d084d103001e4010700c406608500d443d51180d008900c20100b11120403085003d00040b080d0749603d4102c060021400000c0d02d0301400d803403142e40044410315100c40c1c0064070031005a004080c40c0ba4003842100c120071401d07405c0341090249000b50450000500d081892520082505a00d250354001c420032041c4010107e5040325481c000c6c0150b03514520b151940c100081e20b0b4055400b220342900c000500703004040b10114a0f0491640b0b03107450203911801c0c4507600002c0700c0021840f950904002c2c100d480e1041003500e0785290051442440c6446401c0c40b00001400001c1660b0000d500780410180d507400c0b81d02950091200d5100861a441c21050051100c000140543e03c60404850040f600e80da2100e80018401c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 672362158 1250 672360908 672360919
    0x510050c0a023d030b01050313060209030f1c030b0901030308070c03090b0304050d14040513090311100605030c1206190204230a0918080702010c0209012402030414 72
    0x2001103042a500084500306070743c030040e0b080189510706440c000da4114200059504222071200d00004507180d02c82a0b620801501c003505421010842c0e40d802071024000090403140c024a64820302820980d803e01e0b001d44895000b0300201e05c1c2905802088403614007210b9a6001d50704541d0094015440585810708003ea040c51030f50416000307035013500250518110181e00c0749001d00c0d08546c0d600d59802d15a0010b00803c0d540c2c4860f0544206076030984d10010700841840201d440d15600601003014154108900e0b41d8091290240500c0002c003c100440008140300b070401062514010041c1c0ad0f540c06854010b141111034140420031a402850100358058081c2100e0788510107401b494200b10920342104990015003070145041c400b604078161601030400d13581d03582003030403a8080c0032050041c0b00c00581c0000029640001048940d1050500301984001038004c20303403482d8240c20490030100007041d0f41140030b003007030381e000701600042c4010b43c9058100300c2007076580341c007103850360b030160 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 672363408 1250 672362158 672362179
    0x120901020406200a0c080307020a090b030705120309100908120f16020409051606080c03060105040e130807061a2d0f0301020d02040f0f08150414060f010510050c0a02 73
    0x3003013800020440394006121a0410f13468180f200d440f07620038007040344102c20820000481c101d0600442c660500024042e0110501e04410b003c0c54900c4081c1ca41c243d8041045440b134213030b03141c2d03a11420407402076503841c8800341426811407800c08516518400b6034002d111140400e803050048624024044019190108003032010502412800074010a140103141c0c031000004001c01405003192204c0e0385068140d100d4072540041c501c400d54031540085c000700014064808201c10580d00080b02d094220950815902d42402c540c0102404443e007588420b104008890b02c0d9200700c04039001150719031500c40081d803c401c500300c42070101060b400d80c2d2100651559540f004140d0500d10098000d42d0788404403c3c1c82c500940c000d00520071014030300c10003c0381134000181000281e0381250010204140c40381035060285100900454880c1c0d008001c004440f0310901507180584400c1c00608219410901008140b411b4071701c071001007010030302c040d68091000051807605e441c1c0559a15102 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 672364658 1250 672363408 672363467
    0x61101090b0106050316030905070b0318030a09050117190c020c301504080d090210020d141c0908220e0f072003041208120901020406 59
    0x9040c125501070058000c0400004000d07030028000c43c0302c0e145818146d5915000300805508403119003e024200b584000c41c18001031246c10b006680003050009420328004607011501e245600003e00354000490100b000c2025503041401c2c2c40c005001c8006244040c03800c1168486107030b0b00382c40380c0310719640c485d02c0c1400240c0c001d10100601e82c80c00b900c58008280b000303210729625051841d00120840c070032002d4000d41a4089021010151341440c807144039203840e161100b058000d44100041141d0b030355130a00040e80d5103e1000034001c100d0b000b0340500ea0100c0c00c05811101408102401a0000c0000c0c0d00302d00a00c28030a040007400b12800207071401c06080c40c0241d0b000d61092517480d9041e909408025130502d4410038200c5450558107016a61004c5c081890940140d400e2004243ca580c266101d0800c902d101d8070030a038805003240d090640d2000382d414840010141079507801000114240b0782f001d44001c456001e080ea40080d8a01860b202c40208100b017a407001296810110140c00f06 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 672365908 1250 672364658 672364661
    0x14070e130204081b091501050a030c17040b0f061005071b090501170706140a08060f0306191505030a031b0c0914090106150c0302031216020712020901061101 69
    0x7610b50320742194921211310f00015029620105840e04c6924514002140390190fa05180580003040e92414280401c0d0740041d0b000d40500d05110003031083d18070f4044040f880c00918144030311b010b58440c540c20300345a000c10300c0c840b034050700040c00383c0601807100350640c1d0040c3c02c82e080c640d4086c0940803101203192102d1011801c681140145a0a140000580758000f00e2810320b58a80a81512031741650785006403409420b03038510f60000e0000740b0402030721500841280c1c0d40404043c0c030f81c806d400000000242003041c212903212407170301000c119449107500c0e48a0540107180d0403c110307488034144400a552031003070460007400c01c24a040031200b04100b44480014041d488030101045035200c07800900a0301180f5100e0618603407050002d44030382d40501910045031200c0d083e101e2010383e00c001c03c40e00d004600d40103070150b1004000050200b1541030030345204503070101c0c4068a002035200020f091181f154410074000850000311009a13541e030395481c3c1102c4180c1404070080480324200e60 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 672367158 1250 672365908 672365917
    0xb03010501030314340201120b011707030f0c05030106090602070b0318031e071713090209010e0637091e080a030c06050a0903050405060a2d020114070e1302 69
    0x1900481d2043c05e0030610007400c01c00301002d10076280e46a64001d2000b541044401d54a110303800500080f621784180044500c9207908085240742c007050401103016200c09541c21081d0100001e407000004002d4254080140d4001c0d101910141c50740f545418014442804003070501d45a181e186450180c0305007041044400d907603014814039605c0d039049240c02c5110f1308a4102502d1051201c180328000307400150460f184812420164a003950a200201c0c000750418a1080c0c140310b2142d84850182d41d4941c00380c810b03103c051400701c2c440380300010304080141d00e40b200c00098882200f070003000305030440b40c11010b5a102c1404a00d0034000103402111013a1150b001e01c9150082c030420f54103040e480040420418014441440341c0c3c2c0350b4401010454006070b00160000d80217003c00c1c8010718080b07005122001c10f600c0c0c400003440041091400108100d0035864421781c446018521143d028002c07103071804921110007001d8078004401400d2070051450321445204c610201c3d82c4000c05560503107 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 672368408 1250 672367158 672367207
    0xf0f0c07180603060c030b0d0f020103020f070615080a03051b1e0303060103061403070b0313050607020d020115051c0f080a020106170d05091e130b040b03010501030314 74
    0x5541041c00e00d098002080d00d03000594a460a2500d48881c0e103009019510320f10002402006e580c6140780c0ba4142803d000030401c0b41019001c00080d16032041d0100940102d9015510000b4000144068010790300b2290b0302c17a10564000808410200c0e411106403692010140c0c3c0c0d00d03410f11030280315507042c10505405040c0c102c40c204041c03140140c000018621a0b84283c8082103529282c0c45080003003541d008003140d0541c0412018010241404040c41e001903070a03010403119901550317600e0618008071a40e100607403007500e021806681c2402200700e18a4819020901c4604000c081a24421014440074500c1174050b848001c0061400050000b583c020340c00c140c4030a04108000d0103403649106218102d91008160710910b02d010850f00c00c0c3c50402d4603141c0c81c02c00c0e03400c103200c060000d0488400711003001c100c003501307240c40b0140c0804040040080014001003502c04210440d42c0c000286802030b0715110041c40001e820250402c881c100754102e031501ca800c540c0302d14840c1d41c545042e1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 672369658 1250 672368408 672368429
    0x90f070504050d0b2212030c1107080f060c09030d0c08090909060709080114070c05160f170a03080a0e0a05010905060f0702060c0304020105130e041407060201020f0f0c07 75
    0xd54091058500314540502c5c0e40c1541d00c025114205101324603c0d41e5418050244056168074492280c0250f005519412240c1000d0101c128100d401e28203200840d40508010342280040e03400c0510240308071944035412050752811310041c2e80200350f0301c080455465050016218180307052041440039586d11810040031b40009d072401c580c1c0c184c1c485106484110103e5441c8102080c92807060213420b06c0061302c0c092414082d13545200880344940804000e58983c081c0101c001450107081c840c0d1805040040c1d03507400701d1442c0c15a100c0ca0449120030b02005908503000013030000344d2066105401550900e80443c840403502c2c2445d08100070810010a958a00030014040010209105101d0200000300d0f0000703a40c0d0890a0b03840b103008031804175154104000040042d0301600181c5400c101c03203400d41940581702c41c9010b8440c0810384060321081c8194070620b003610410403480d400340c81944020b42c100380ca880210140c034003031500314541c40b00300880c60081c5c03114100040700041008009 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 672370908 1250 672369658 672369679
    0x20c040c051213140a1e0c030b010905060a1508040320010e1c0801050d0308091507050310090b060915130e10060c022229090a0506090f07050405 64
    0x101d288000f80c1940111400fa420401c00c80d145800031034030319400350f0880c4901c0c14282803100180d025485022080b0b80b941103156012001c04c0c29001c0e098043d062403403002030035041440401050941e150700c4680c100c540180e80701060781e44041d00313540103035160a02d00c5090380144202042c2800e03901c103880c0503600e40f0802204021000034034190310400d109000003c001d500c9001c0f99081d03824091590440040450340300040e10844034141d0040f482016580340c684c5294186c1003116098907040d0000e8401f2050003128000101d9010041913004001c02c48110500c0109600713005500c01c2c02d104002c00303540e014490b075940d001c580d2070315000216a40c1a9440310809403001070f0566881561001c10400401c031107000711211060300b0f0b00201619400d00b8412002c6024100d10604088510b40703980001d982e040180128040360085a03086a45961012050180c1c4e03690042c900707080c0320f040c14141311040c5c56500c603682e0000644100010581c0d00d0400980c0c80748659482503820442810 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 672372158 1250 672370908 672370921
    0x91011040f0902040b120703090c120209070315050d0f08120f0a0e191109010305030d0e160b0a020316030302040e06040911120703080c0d170403020c040c0512 70
    0x400c16036600440600c845078035001504100d000301c1c010301d00304000030000d6038495030f021403070503611002500d000316440d00e07680e071401303010040c55002d04e251000e420014011440d2414074994003a005250400c0b4260503011590034040311840703010700500403001c801c0700b80030039404803d10603a001706585a45a80704011020130070421904140407910500120fa100c400c64011003002d00c4d0300c68020082140913002100e03040e125504101d60000c0310703c80c00540d5444103c545402540184d0203141c88452080c201e00c1928141074110000390014519039000d42644545182911003c0881e46d84400d103501090740b45100e005141409258091000001c041e07250f00100700b61240d242185905494903000c0c03009171082c4c55002002c0001103028262241000c0b0503118540300d08500300c5000b2a03994a4488042e400307500400040d0f00411040000c80d034000500091104c104001d450082ca1300c1e071030003074403104509800c502c5130b03440360251030070f80e88a1029500d482d00710342031583c00781c101035 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 672373408 1250 672372158 672372191
    0x60402010e031024050607050a080d06050306040b010810090209012c01170709091227031506050109050105031906050901080312060301150e041505040510050c090d0b0910 75
    0x107407801c15a95901c1d9000b0613176081410139200d4040c8d001c0300038446036100e0390b944145600282c032a00b80c1240c0d500c800264070361b01000850b000c0c5014141142c101e5062140e51424200e1461118211a0500c14801c005840d082707140c50440d4100c2100800b40d404001058010000701d60f84002408500400400c1306c404e188420728a000201e401c6412720f81d959002c420546c0c01c841030142205941081d540c0b001400380004401502648812481911001c081c1c81841c1d82581c1003076400e5032050350440e9004696102c1c440c050708090a05505451819000078958800108408803490202c204004200c415030011409404d00800034000da6844003013844d42c1c1c6d08000075071618001d0030008103c8604042c0f144070f242000e40d01e00328401c03d082007203544924901800454003900c043c2d00c42400355619114090003244500c01800c030106213804074609a440180004030409020000f220883da180403284008982c016909040382d510000554205441000e130000c80c1400c0031010303410240302 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 672374658 1250 672373408 672373451
    0x405030919080708060705040b032a0a08061801030f06021207050705100c0509040c0504080a23060f0a2d0e070b09030a0605040c031b1d040302060402010e0310 70
    0x32141142c02c400d584002c1030b45d4540301515541c010030001c0200740f248070780d1680250b50000741050100f40100e803001e400044280c0c0703060031044803000410001244e070380c0210595080f0780708a400300603c002c0b40c00581450103040c4401450341049042e60b5040001c07030340548002e0420350000d04c5040c40c03d0b1002400f607a1100408864500440010b6124140103100792051008569940c500f01240f6400348001041440404801d004060200244401c010403001e00d00c00d20580c00c040c00150341c50b1200761414000c03498080c003900700b0350401c208041c1d0a01c280358022100c402c003041515484251152606e402071071442015244860040c06040381d03000680c1e52040b01c4c08490805903610460340380e038000c0346e6000343c0c507070402400e08000c50059000145c110f40100e0003000307141e940e961828901381809041164084207004100400304030045400300038152102c008015140540e4000c0d220840100000c0c1071003440d5201c1d2049480030820b83c140e104845000304a00494008181030110a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 672375908 1250 672374658 672374669
    0xf03070c0c0e0420030105091b0103020f2701090e0c0f04050d0b0402011b1e03030b100e0f0a050d0b1504020a03200412140c060a03020304050105010b1903050405030919 74
    0x40401395a019040c144500e40c030800c0d000020341840c5002d00340d1045e400c015140310a041580912032a01d44926200040035507114880b4900c0b41c0c195194211500520803200240c148600b0450030008500b0b0b40c84002d0b405048847c0b4580d991038450710b440001c1c0981e800c8a07800c801e80c0103075401005032010043d80124002d8031a00071407854841c29210008900000400e01c00d003503c00d80305605010010300c288c0d01d100703040100f0303200c02d010007090309414059109000110384c0d1810040c01d041100000c500e0000c192001d441c00e40c1060080f50003243c074503600900c1039561000150f12000078810760030701ca00000b03000755951100302d400140600042000d0f00e003500094960201c100c410742c1c08480403268007030324002842c8402c1d1507400328000020b440c041c1501901649a445989100081c00e0f980b02c00c0c0c40040c0c4908040c00c040b404c540d0142c200c10b0510504000a0a001200d0108452100c6192801245503540c92401500303602440e0341e991741100b15111611201d402c15501041600c1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 672377158 1250 672375908 672375953
    0x11a1306080708090f0c061b0f0d030f0218060a0c020405071206050306041106030901090b040b0103030f110c13090803010305011b030207020a03021c050d030606030e030f03070c0c0e04 81
    0x441340181c45844a8040070800516070041604098504089016100a01e241885200e0b52010700211505194442842d4200ca4000300010204150540300b181c0101480c08421401d00d1010000041c2e4a150307840701d07030700c1201c02244e41e144551080d000301c02c259502800500080c1007412002d081c012042c400154200e041c0311010842c0d0400080e024451500000018170031030030401488519440034080004954071414840c0c0030440002e0124090303441084291880d601d90704004100c1000b428060080012880840c0050207000403041070341d4008850810205030902c111000800c2012402040e0f47c0003c0000018420f040d80162050f09803e02c5040c4a01c5400408038100d116040e0001d40c80000c03c0f1042c809030030204501000c2003031000754540409000d450b0315250014034040781c00007945500c030a00010f0b502d03008100d0134420013402141444a050982074190000801000801220045c14001e20040015050003421940c00c920843d040a042000100d0b00300240e0781480b4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 672378408 1250 672377158 672377161
    0x50f03090a05090f0402330d051e1f090e030c0d181206020d0f0e12040f09020309031b07081b060d0c020c100332011a1306080708 57
    0xf414480001440303811100104038895846a0801202c1042810114007a8650889002d0525030300380240001e4804968203030345400c0c426101074165803005082c0383c0001006192035a50f641d910071140d0304810031002d180d039030301c04002c242c0c201e01c246944159200b9040c4048009903c0003c8010312480d102113081e00d00e0140e504605645045500c110041c851090074403c0091a1806601c1ca03085449491b001d488d10140d140745006580d00b0b100c2042c07001355588810107801e1010043c440168040c0040300d41040d26003202c540d0701428078850807a460f03030004002610058280125002c0143c6028211000c0704182e441641c1c50038280128000344c4615000340598903000490031403ca00000c2a240c0340c00784a402030720207003220410394400c0d88180008036550b584c504a0344207038400c141da00064442c2d0250b55000c0c6448241d10304403039a010007440400005044010b087c159654080c802c00300e503003010141d80d114410b2281c00701d0324403400d10012031110350068415006040580d01c141c0503 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 672379658 1250 672378408 672378419
    0x2280e070908030a03090c0b1206102303042d1b0f0303050a03060e09010e100902100810030210090e090f030405040902060c3c060c0d09050f03090a 65
    0xd51410b401848020350050001c5070325140700b5040740c14058800e12400c040e00b86c0d606607034419074002100c0c000b18011003208201560502031110610519a841d001c83d41800d1568416404100c0c1c1003450941c0c0000000a81030041c3c42e01d6421080150042201e00310204004c04004c01c02958000c0755680e0841007900750005951a112003590f103165181e9040c030385556403c0d5810f6220110381c000703068850f103001420350351201c01a4444d658240c0042036010580421609085071236070b0300755155203860114000350321140303c0c0001e000d03820304000d0281c0e2220184900c02c1c2e89075500081d80070701c552269041c002ea019104600300ca103940161070003600c9011115880f0507a0b2031b4082ca65900502c8100042d29107500129051800030b0891803501c503840ba00942041c61103800d0300400c107410309a442b01c89590600841401e00c03001c5074580e600211004071529110080d003040200c000204da8962000143c0d0300405c1d08030340c0300b8200c414820040e280540c60b07070070060843d8851100000005030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 672380908 1250 672379658 672379667
    0x30f08070506153a0305130806011a03071205160e010f120519020c010606020c120c010c061b020a0c05151c090203030706050103110607080a030902280e07 68
    0x83c1182c008007514003801520301100da680048020200c94070008a480c2c00300d03841460030040056010340d4a9a075510007041869400b4545035000c002280c0c024001044042041d00071070501218600c5503d58035203d0520864841c40003031541d0300054584820320035003801c0020204103040c190713250007400d0701000005407480350380c0d20401c40c007080d41419000d00300f840c02d40c0b20702d5002c4019580380d00b0519034500784508036084400001d5441e0340d220801d00c0301c250104076045001c0401c4860704104411342c034a4a40312800da0b00800c3c10b00c41d4143c156020800030b900401e06d001e08105642c800007241220082d6500070050040c0da100c8914a000308a6041c21240d5050901d0440040751a140a0695441400384646544810306030b075100010016503041c4000c2c05018003515001c106c0f9415410000401c414403121588184c0d005c202e242c00256404e405d64071081d5050030002846141400841c0d6510340c0107141026242051046040c48010090304034113450b010100d02001e035903004070035103 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 672382158 1250 672380908 672380941
    0x71a01080c0405071e03050906010e010f0909030c15090c05030607050a140705070806070305151e0f0901150809031e032503020415080606040915030f08070506 70
    0x40e450700450345595250a00d0f4201c0b540002031881c1c20340403141c04441c082c1d850b108040f0100300181e2603030144007004000700300a0740902400035403135140d545091084000b00703e0340c9c0b00d69000c06407115415010b050040900c86501070700040016440e110340c001c002d0081c11001d034210303151409500089424200015564814070042d106d192500300c0908e402c1d2650710103070351040b00820b0100711841c002401400f04400514149004080604000d50b014043d41c400070000b09580340d0340bc45d0402d2a5803103c6584a00c81e4101d51403007020304400c2c0c04118070500c0541c0075a0444030801c00080c0b4424002c0b00c001e0103245c15500c81949403160407500307803240f05008145140c40a0707448119503100e000c2c002181c01010102038201e504000c8054907e030a5020894240441d0b8049003c02400480c4038008403030801c14904a00d462a0450000d070701c0e4003d82c000c246000d80e84180320480410074000d41000b075600003040040d03502c4189008400d40e0320041c800c4905010728004541600301c8001502e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 672383408 1250 672382158 672382169
    0x70209090604170c030927070203070206120c0931180201032a030c090501170115022a04060b180f040609140a060f080c100201020f030c071a01 63
    0x111800e4003120f2081c2c0b01a00000a5940c9600040001ca1310903503846581d2914250b10403c2036501c00c0c4241c00307001d0400e0f03006240308255001003250304010f03903030002211005c2e445000c1402d20741e1900c40383d082c1c1d0703030241124264020141101000c0c115894140c814011842071103640802006440640c0035514082c010f186103410342c220110043d8000e4104864044560300391002c0440180005404110040c5880e40441e60383d601e41440d40d42c0c41341c01040606000c0c2010200c0300b0701d4580b03403514050140306102186040050400589100307100300c81080703d07085d058100150740034206001254007030500c6413241386000000180c4446d060240c544505504042100c0e40d40e82e207081c0200035071400700d000e5100765a207902007818469482120103e0207646a100700c40d00e412425503045a0080c0c004119a0404885c01c0100b0f0200140e500ca2052050f62080c0843d004400140d0180c011200c8a0300d0f040030110030404007401e800090100c01d4050140024a014046042c11310002c0a00a2 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 672384658 1250 672383408 672383423
    0x80609162102090603011e0203010f150e041d070b0909070306050108150d06020403030c020111071a070f050609060a0c030203040215130b04060e03071706071404120602070209090604 80
    0x210341c0586401d4554541c0420040d00105414403944102025980f5145c070049002c1c0d40400103021140000e103044000d84054010464a250001c00242c960081d84030490b216545600c4842d51040c05144101400c041c14011601c00607100c841034010f54000100450103110917400280840c1d101c0c0c051002184d006849200c070648605134a4140031001054203a04074401210080000d1035a00c02040198029640c45602c0c02144c4001401454034480103803043d844600c007445039008220507803407480c94030308000b0ba0340c0955140c5900d0380000054050402d002d504100108040701203480d44c441c18110b90b04010a04034000240c0c101e0000340c030042e4101c8001030b038602c02141c0c1040100007000040039120441a07840340f20958030f03440f680002e40059920458070041d81410800c6a0107050700c90480410303903580c106003039038442006160707600b000b1041c50789550f840784400c120340c00390400d03814981200d01c441c207160010b9405228102e001d04124000101e142c0d5002c1440350055521000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 672385908 1250 672384658 672384719
    0xa1b0c0b0309010b0a0611011d0d051b060907170105010303090501030902061b101409060714040306090c03020126010515040909060f06080703080a051308060916 71
    0x349011a40000b80040302565a80d003815000341e8420b9284002407100740d4400c070345428003a0480d030940c0d070004107440e034060480081941041012480c407140b1072061410380e03112081504071301d054512500e60b0030183d00400c001d100710601c0105054042c0c0303a2424448404200c0c844800f0b0803550300b40f001500003542000c0038880b0f58800d8010602240c00184603a050880600880140104680000386070358006125032009520758041c5c4d42c02c0b05014074900242c1d00d4204103131743e12030500904402c10807840070303c00401030302d41e042030350059500b1100411510280b0310300390708090407901050780030695801c104007040082132000021520600c089070600d9207004180903d650482e4050303400090140b102150044483c81100c203141d0045030082480c502aa5080040740d00c1034000c4041c1d030304640d100707202207410041103542c200c034186840c50380c0306507074110540003801c0c50304280094090041481000c59000502070441c0300442c1e036080c4079580c1d4406000750001209440c0c08048180305 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 672387158 1250 672385908 672385919
    0x160b15091e070917010b1905030a0821010902180a081f061806050f0a0b040b09030a08070807020f040b010c030302070c0e090d02010c03020304030903020d14010f020a1b0c 75
    0x200820340081660038004040d9440e04140d505400300004c0141c4c60307079520000700c1ca1900d0104048201c2010194144c80301a0400700401d03140c4c803030981c000c1e0510000040320135a401c0308281092803c958400c0100455071684078543c0a9840068002041d01043c3c1d01d4409501d072005a9804841c0c80400070b00131600802c080d80300910704540f440007201c3ea2940009440e0307180032105200e4280c000b0000640c58201001c1180010040c101c45002c0c100c04281845081e4002c0c1c1190251520fa5814546038460308000a00d003411103400101b203500d0100e103010030804824040e0665501c04c440f07040c0c0703010005050008840011b007116000580324521040401c0c040c4e4020103030b03e070041200c01d00d61038543c601401c046c02c095035507500c95030046030f9101e0000c1d820f2017800d94440040c913007545076003000c0d10004c0481c1c2083c0006889511022480ba0030460419aa003c11148800090240c0d8140391000802500000104000700d0100d0003124001040907450840d10303503209980003130207414003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 672388408 1250 672387158 672387211
    0xe0604050625140106181406010c0f02151c090c120602040305060f0106080906060d1103150109050a180b161b150606021b06030c160b1509 61
    0x10000303a03002d540c090029408a502030021081c40d1a4000c00428810301e0110008620800c0c041040c0450f80750030155661035551000f801d81020342442d01a8000e050350030900300c0180c0100c0002e502404000c28414010650409000d050000c0c408242014807030015480558806403c020100e0511207000c0c00a11003c040c501c0c00302d0300601006040c2074407940c48610b015000e03500f40080201c128010030095600904503035120041b10040e0103241050700105090090004000b400c03c0002d10494407261010000c005061882628803010b6503034078070760180100000d40b0400e2455040030400d40180d00020711074010341c1c0e40401e00d0501a928000094207882e25945048108072040040c120520034042001c207546000d841002c611003500580c1c5012104154040341c10743d00444400c0d038841d0a180c6490380c0c500c0e010f45420342e0f030395101841c8184500c225030910511300d40401d01e1006004503441d51900c0b0740d00021010b5503d01c28541000300c245811240510175000070040c004003440c20 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 672389658 1250 672388408 672388447
    0x31005070e060409060e06030a050a0f33060501050c1207060207170a081302060d0f0f15030203060717150f0411030405250e0619030f030e06040506 65
    0x1685003401104480d000059400c0d84030303601c030b0035a041c1c5170407081c0030704040401400c1e00f058089009100c0c8030700c2030340c8050f16a05041c0c400343c20803076002004403c1c8034180180d910b031808c200e003030105441d900c090064000d06c9000c40b00905d40c1e242c00b00c0032985500513800c5030410000140106502001000c480c100c5a206402c2110a540c090100f82c0026400d01420f404040441400c942c0762041c403440105002c1005200909140140750380c1000f40c1c451404a42c0040300045012402c200010420006080e01092100c01c07107142002c1140755202823124801039038400c0381640c0d59611b070340c40103c60f4002d0b440c00304000079141d4000706072421343d0f045280c20700309000340843e142400d00710006022541c8440f5000d1072080c0000401080200501003c4d0003040c2d1074405e10102700c41d4540031051520213004c0d0301440c00b184070100e5080e5840e102940d40c3d000352005443e4806480346001c422040f2030b55812001300c0c03d08100400a4a8110107503030603500701614150030b001000340d145240004 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 672390908 1250 672389658 672389671
    0x10203040b25060204030b04060b06071505070225050a090b1c030c0203031c0b101b031e020708060108010618090809120d11030c07062a030e120c031005 67
    0x104070322100000e245130000d00021801154650042c1c5807908108003034682c4880141c0c86503000300309080002d0390582c00780121020052000807030b5601d0700d000f64030700008688109000306200340b4003414020240e0800f029180b060f9080d5140e01e50394182074081c0c8002e84811640403031040d44810b2807800b422203d0503110b01905e02031000044179000302c1c0c11a0702120007058202210300203415041c1141c054403198200a8421a82d14010f514005140e1f414a0a41e541103801c004007100c113048c440c44084600e10440428100d040000e000041e640e139400740705c0c140c002c1c010500002b0b0f02100c1842080100c07500c0403090030011035a60380840c0201401c00d401ca45012060022840d16290f0210425038840124014131680202000180c5001c0d0140d860b03c503107070b008100c7d1110500000c20011700b180c1c050b0a203400e0309000c2c0e103c000070b480c56103541d80751641ea50340000c03c140355120303004451000d02a25902140140841d280b91180301e20f504103034050340410541c84000420380d101951090 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 672392158 1250 672390908 672390967
    0x6140711010c02061b03180d020d0303050a022701021e12030414061503160302130c051611190e1906170606130203060307090c120903110c010203040b 66
    0x690080e100f9110b142c1003845210b1716071001c2108501d86081103125980c030300c0221081c40d44840640d000802c51101103c00030201501c41c00442d2181c070050b01138440060414031149003901c00726010195040040b0601d40c0140300d84003090716034480c001c82e000019032024002e484400101e001060040e44050421200c519451020615400b81401480c1c000d55041d00041007030b1010408252810411131f80381c10590b9400768040006941d91108580340d5128240d01042c0d00b101c0740815031300c6016401c46c0d1240300784102452810020000f10421030001c04450b00d0054200c032680e0042c5420590080c0c1209040c000c001c01d081d94043ea50759810301c0c80d85103003c01c400c0e81360030000c1019880850581c110340d00070400c4c083c585c500080100300c0540440d00843c154602100040d81d10b8109204580000c5d43e01d2100d03180c0c4902c95140c10920385c0b0329590520054095180090040321a10590043d034018842d09240940c4003008075402c892407a180f090400c52030100100103e8000c2902c6800d28 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 672393408 1250 672392158 672392167
    0x3030e030c0a03030c020909010c0f030b04140c03010e090304060e060714030f120105060c211213140114150303190201060f08010204080a030c080904051006140711010c0206 76
    0x41e50742542c500c0c003843c841c0d41d4001c0300103000d2051003000e03440035094a5003a41404d01d44100d20358031908442d16003009240c086a80c0722000042001080c1c446007860704828103004010803250302500440c120794013011115407d648155100c2d8a13070280780510300000e1810084410113240800162042c0c0c4c1c0100b00f54403903a40541400780ca503501c4001211072485020860181d10341c0a1a0140e0051605503805881e1001900720280c07030b07002041c1c4c80c1001d00d801c100006000d00b6040c059454003520988000401d050200e04810300303080442e801c8892401c10a05401044010702800c00500c421804c0300d4202d4035120344003135140c0382132865141c0521061142005006a602c0e085004486035000042c0031401c150000302200900d42142402e6070040004010401002070804c43d01c0f905840c1c02600c01407185001103003485100d029546c0181807400388680130403250221411140c0a441e6205504440c68041c0201d01689101410b02011541c120000394024100c0d00d070754510042c050b6141 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 672394658 1250 672393408 672393433
    0x13020d0e0105011502070e010e06040203100e19051303141606110702010906050a230f0c1b0a030f0f050a020d0c0501021501031e0c0b0403080d06050901080703030e03 73
    0x2c40c1c1090f800400f00d0388100c00400b00c440d8051210f20f0180c8840c0100720704540c18108024030b20305000e003605004e5503001001906034070b40a546200a40104030980d00181402c0102d03081a44e4182251044d085c50714001c01d84003010341c3c03070008032203078562920240c24024000c083c450381c004000f1465400c03080001a4000b503198460111b09203403482d94580c03606814000180b8484098110009104080041d0300c1110707009118000040243c1520180d000c07140704901c4420302400884c1e404464011500d4103a9000210f8500305070351075000d44529004811301040701e5030f8450310026044165a0400c440801e00c030849480200f40901c0440d1001c02460340440d03004240c0c0c54058941d03030300d00310003800300390313414400d1107410140940300c0300d96035046480700b0745d8108105040051089100444104200c4420300040042010503442038603581d4a0905040300d03848640030741c514529040012034280350192060313050300d81c4080182559429a5000e84107001c00b1000181d042c41211000e60700f = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 672395908 1250 672394658 672394661
    0x3020309150301030b06010908060f060a240315120b0c070f0f0b070804080301120507030503031806010b130b22151106090607050a0309051c17040213020d0e01 70
    0x40031403032401a01d0b81c1c1c1d851401c001c000e054010745001d041000d404000c1284140001e40130b0380100c040c1c2e82c020900c0d1034020000d403100f24181d1240140d003240c00c0090950040f0000d60094045843d1014006150a11001c586000580c003d103a081407030542c40d07101092501074069030040a01000c20700d0600e590b1101802421444011100c02d80d900350a602040f401800d000c0e040030311400e0403102410595035004c038502050050154481c1005104010f100040141750f00441d004070699650742085003078103084a0780c0c031110140501c0391b0400003c1c090041400c84001c58104584c12010b9400c040305441958441e800c200500e031611040d920103180c0c11040d640003003121004c21400420700d00405000307090300c98018043c1e41c000e441089880d08000c40c90310341c0040c03d4a011940c1d60303c000002c0e0002d20182c070740030b001b42c81405148907003001503030303202c0942e141a51212160f44107401c036103c640d81c408440080d00980d901000a2440c00d29801a1a440690307101c0482c504580f454101d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 672397158 1250 672395908 672395929
    0xc070306020a2304120204090f1211030f0307050f070510090204060e040c091e091101020c090709090f1407031a030328030b0319030f0306120f03020309 67
    0xd444540c00246411100d80101505524074100d10301d8010a00300c1000c1d016003402144940c041c280c0301c003031441c0119a601e82c0031030500c0d54407805140c905405421300d0231a150304845c055002c600c099440400074000001034540c03051500c5200e502d5a0f40b070b10401ca03095000907641c40081d400502c01040022070511614552100b01d0b0030010310312800d030040001b9500c03075900c0701c06003103e00c405100218001100d4041a903612250200e024208800e82c0480c05c01581c0d030941d00c05280c01d0f03c00d4100000c1009040c5080026070071078030400c0c60b00381005001d104c00d9840402143c480b2008001c14459500304c602c10049030300d000a0303120b5018840d01c200380340c201c4218001030f0751071040010b032550390705408282035001d030000c1d81425002142c0b8175250700b007104081d0450f1503c00740031f0841c0340710741c000c41c11110303010702580d10310a4940b49030741d2b02501c3c4805c1180403500c0314070320b0003a46201c1d21034030040720300041441c01110038a449898201c245800281e0440c041004a0040f90721020800ea = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 672398408 1250 672397158 672397163
    0x70510020a05060106030509100506060412050609010605040e07090905030d1109191503090204060302041107031214041101120216060e0c0109180b040c080603101e110c0703 76
    0x144101011450030604001058102005147c038000c20311640442c0000c200a4003c1080800501d64407080001a400c1c0100da108541c0700700b01a011004104010079400e01a500c0c0f00d0003130201c40e8444003000b0555100c3d40c040d02482d80907910400816003103401080456010b0010340c1d141c01e9030031091005a50310300c02d1120100a000800400a050020070022202202040d900c00745050049800c002590280c20a0406480d404d41d40e0541d601d81e0f011100443c0c0c010700c10002007506052030f0856400109054000c18006010041030072014010100002160040180c507035450703644140710404083d0299042080c001e0900e0981c50151005000302640350100f0b00900c00140f410303406075400f00c14031344250703000300c80040110b903082440d03030040d03d100c581c0114080c81d084030098018501405000d030f0040c07e00e1228146079400030046405440705600ba20701c10810080c3c400140d8002148070490340d42d1400c81a41d07805000c0d07101c008203003000701440340f5040560f45114034192464106 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 672399658 1250 672398408 672398413
    0x6070b04150f0506100903390e1f2625050f0d0507060e01110304060c140109030909150e010e0115080106050a140c06270102090f1207051002 62
    0x10303c130091070b2440b03004090280903c0e10004850541c1d446039490f96201602c41607980e54000c901660100d060042c6c56807041c2080e402403025626404120801c10075920317003d4a4206d2014103000c2640c81c80ca440c00d46001040c420b090302240c0c130301481104201080b280880c050740f40740224800c69410f00002c0c132480d103d40f28407614203001c00c009140200340a014130480316101d100d80056808100407040352080e04041110482160040c0d5030040c0e410303d000041d000024000c21104c0c1c005401c50b04060241e454003440c42c40d04000c8038221076840c2d4014000c5080450204640503080d0445a40c1034403011140c08111743d100c04200050500781c004814444c1c03c0c80c0184071050384a10031180f110f00320b00d411002540340203000381c091b2003000981000c000229900ea520003c0e1001201c80c810f40d8441181c910741b40000c407903854094206070034002034003461440503a0010500036502d00c2c0c0c400500c1180200c851804010b0009003c42c801c021034098500001080e81d40c1e0801048242001e401 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 672400908 1250 672399658 672399661
    0x402130302030c04022107020715030212062d011404060e1f2109120f0905030309102102040602030a0e011805060a0e030f0c0109080c06070b04150f05 66
    0x402d410302c100841d58a02452040c010352500c02060004111910f20b44044c2c40e0043d219178030101d01b080301c00e400100d640e0041c3e11284d0703045070340750340141041e5441c100542002e407100001c0000110b619141180c0c1504c1e841d1014046507880400700d400300f0014104029244169881301001c1d410550050002c60a041260881d0341804510034aa180f81013201d02801c481083c1c0140a0001c0e014082c0030a0050045819004d1880d40c80f4540705038000115008107121020b0060801c0d100d03225240004149c0c44000540f803c0000685100c0e04000382810165000b015045070764a441c07100c007200b40782c0910440205c3c0c0b002c910040000d04840d038003856a505080001819060070040d001c1d0400c805d039001110590345c8001d4400a482c5c0803140c4550392002c104c1d0444040c419100d020b90300d80034010241c8110080020083d15481c000e2301e0b07414480da07035201069190b001410308280c20960410100300010496003895034060701c81c80301081c1e003280c08441301080f82c155003c0d18640a941d0720 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 672402158 1250 672400908 672400913
    0x1403090103110405031c0c15050717090c04020a05160803042003100e0a0606060807020f210a090807090b12030702031b010c08432004021303 62
    0x2802c0c0700103502c11580303140c54503040129540303401c40c40b5052a030800070720501482501c0b40344141020303a00309030880070000171402c039132004290a4941d400854042d0140f41403018100f14000d11440c00b0354050802c449203001840040d5201440450030000b0400c4207040c0f80144d02007032000c40f401814035a4403031926203800d01c10031010030040b2608820280581c0c40780d41e00000e0946403800581e0b008035030f10092452441ca411349600004082c0e07420000086a12584200803500c035842c1a400c480110f0004141140c4030b08190824000c1511100b042c07a900c00b503035030010103485030b13079203041030314030f59580c000030b0800c2c1258014003041078542d000304c0281e2419040c40d1302142c180c84080d5280a0740fa40c000390780d80d610b09005820110300d0001c0c0500740e0780180c2a1513007142d0010245030781c406030150b00780494501e1044900100389a00300c3d6401e01301601541300004000d004080210085640351018080b45c620f0488081031505042c041a90325140080e1848081403001c50f5001400c62 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 672403408 1250 672402158 672402161
    0x240f0607081803070f03030507030e0409030201140a18022e030f0f02040605070308040206160302060907060f0906050c03130902180906130b03120a05070c06180308161403090103 78
    0x100b90b028400d074400c2000307020781c411010003e01126450704006542d02000d141c1594035011001d8481d520916060710001490780640042c0d1425070783d98070011103503071190f26880c222501c20070081101c4505229850041c1420b519280c42d161b500c034240000004101c1030b109012241511080000384c071090039548501c2c59018030300d403249000d20107500b058100100144130780a81040a0200501391001c14150f4903035200b11904126510a124924400f0b810040c1d604c80054035200e241b40706195000801510400d0580a82030869503000b54151410038103c0e640d404c4000d550038039010410020f5828048a40c1c000d0041c004002c02603110b0420f284020f00050380305500714040c498090401500741c0d030310b014155080c00707821800140744070240d012914142c40154203410b014000900c0e01303a003982040c0640300d02440788903142c207215111441181c42c040e188000d1550320340c101d042440098000c00103030130310700c000d5281942c2c00070300c031340303600071090205204011960000620000c555905 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 672404658 1250 672403408 672403447
    0x90d0801050109140108040c03060507031d03070503040b0708040e191d1c0c0203061e0c070f0210020c090403110706050415080702030d0614010f08240f060708 70
    0x900f0300b1020280f900240d10b90410f50348098a0400114500080c1000785190410000e07540280703080003a490701d0100036000380f021900410214844458a00f1100000400c9031100d5900201840c241031500041030200d8000540440e1500000c1c48003144892072a0b024a00c44d00311122448100010305040c04101c40c1a4420b011030740c1517403106409c80c032900041601d032402c5084400004103d050004440c644082040258075003d0502440702c0007400074444801e6031800300300c0c0d0040e9164120100c0f043d1081e140e0090001c01019800400f52410441c00d0311002c2003401a2441c4090100c00142041e504841c100d02180070301255815414080010b18041d010504085141c5420044054202e0036140e00c02000c2088400c00104aa032092003560004001030000f0f02880342c44212404c808806046040d001071540c240f80c2d5480c920440b2003c0c0240d044841c10305c1540034032100040100590b60140d500b0040a03c2c441306503807940001454018080ca40583d125401100c40c036160041 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 672405908 1250 672404658 672404669
    0x609050703050906070f02010608011103060111030c06151f0c05190305030105040f1803050706110f12040602210105190605220b0d0207020f190603110d05090d0801 72
    0xc1d12042100310320f00040d1803500a000e81c2002450441c100c04101c0c0074103d42d27082200c855013000000404035114a000d0745c000d8809032038034540c036122050343c242c1d80d01428070741034000d0380103102040c5c00d1051010807074a8034102500901c090f8205240c00c501d04445003020a001983c400da62005100342400b103040074078002c9007404032092282d03c4c0101140010701800d44115610f1241f00900e01d03569228844001d03940041034403607203450401070690f8201c01015640f8074203001507101d8003034030355003210b6106007840001e60a0500030381500112a40080081710855420006c00000c0a2030700984070421003207541c6940b0035810402804000100302a42c445903512407401409843e400c1026645680d1805c076010241107110007031402d07a11200d42c010118002c0015040100b140140c00501203203000b5101d01074040340400078052403000e00d0305000c0780100d60b2001801841d110b5044040d0000140c011030781442c941740c0c03250003101c2c41500ca101142d070212280c11a01c680007001c0500608 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 672407158 1250 672405908 672405911
    0x3306080a0c0803160209060d02030a05071d0705030403050c0a0c0902041d0c030606131509031208012111061206280504181b080c0f130b120f010609050703 68
    0x40031541e20000c1130790090000c0c403400d401e00009a10340c40712101c0f07120302500101156251340c82c0b801c0140c1c49a020380a8032940c800c0f400416090352218040490140c0c5c80d50ba11645103030f0300d54130103c403160030000481099000e003004803c003080642c5400c60291810380b8005946500e001200001d00c82d491032101c441424507c108011420101e0603243d11100a40340325039100e09549500b2125500c981254411412002c480d11410b507002d545c400649105956450903400c0111013514007600900c6514000c02500941408050002030318000c090700c00c1c00480110440580020103035003065030424968840b2104100d41f51400030b1140811881000d00d140850203158a81403d0f5100360081a000e5501d446048070710a84050028582c2034000c000903002e074031a070b100001180c58500c40c00e8010f210b079000000d90b51800442025000c08000c0500c0000380b00301c0050000382c400d140483c1c0d840044000d09810b2810705028056208000d2400081c0e03480c1001042c03000c441c2c000d0928000c15 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 672408408 1250 672407158 672407167
    0x714012d110912100507120b2236060b1c0f081909050f0105120a0e0106081f0501060c02060d0902040b040606080402100c3306080a0c0803 61
    0xc0e481404966600c81d09441d002c501140c43d03190245084254a5007081d040d103880d04004401c0d52000b203000c020b1541c103006204001c2000108403401c1201110381350940300f1100c0d04400140c003030340300807603206400c210081c2c25000c0c11800450b13201f8000c14440d642c0c1d1480004010403c9034419030302c200100b290349180f0010b505101183e24040c02000400709810780c0c19070310501c00104240c844c4000d000c0e003c0b0300d01404c0c8a50040811300c00e0f1042e0b50107544210905d2590b076006406840c0b0351a04500024a581d846890300805402c1c01c00d01034045550b51000071861040920a00b00707001703990b60a241c5082c8100d92098100e941c140d0101c0208800c860991005a40f82c104403421110801d0713000c1080e0b03640740000b42c0204501c0001650040c0341c035500140b03c41d0004811845180202c0d111030400c410814281d51110103800001e090007500307500c0421454031100c05001480c0200d401803101d854422042080380c001d50005071088c2d0100541c101088401180040684a401c0165080 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 672409658 1250 672408408 672408431
    0x9060f030f250905070f0c02030a0602040b0d0f0b030a0303022a06010e0705030c042d1508090a030923060f18030c0f041119050a1101021602060714012d 67
    0xc59006500c101e08005444c3d1004003927660401c1220300080d0800c3c0e045540d00d0351030aa45a540c0e02240306201c609051940c0e5111500d4148607a07000c460019000c1c000c0d03660b680d50124006d40c0130050403501d0074105c50b101d4000c05580c03d40701404a8401c0f00078002541400c06130300071100d008082c4010414100102302010400e582920101c85102c14511203d6004152034120110161949420b0850b544400219403001aa0717001002c081381d1039514450315481945038980c1206080a030128000c0a41040041001c0d41030b008200030004c203010180136042c00240d0298020300e00071100c0306000c5040c810103080803800e1606c440040b0000e010552900700807680444c0c5500140f4840c5a030381004410a22294003121045081c8261011031442c0600c00500786c0d4202880e18000240950132070441c440b0140b08070780300c0d00c6800c06100507403510f60b420002690b02690b400c45d400c804100070300803408024020041407560004075620360075140001e4401000000842890450030440c0d995507 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 672410908 1250 672409658 672409667
    0x91b0b0901080c09090403021605030703020f090c1216030b0613030b0a0b04020f0a022515110109050d2303010b09060f0f1305040b09060f030f25090507 67
    0x34180d10a09100da41c0359646081180709024035030315a13801c00e100a0401c010542d002c174840c00c82500000103813071155100d00606a03140464080250003510b42c06100105192444003954000d941116007860a0500c04000c0d240010603100a019901e00c00c4103128210340501400100038000e0344c0150034840d405030307080b10040c01480064011400c0d180030271890080383d084000c00640180041d07584d4071b1250707602441783d03100c0c0504400601032000031203000c6108420014000013191003042c0d0090078031942c810100703900428038040c45814214220084002e0007a00b0445020b00082c0c41e5002c0c03c028003410310000c00f000088c4440352801000c40c14070480c0192819109000809601c920108020030001d1040c1d0304444058100890f1140c6a040308100a0001038014a6081c0c11180d03110706110940d8400c0c00751950181903600011054100000000404000101129110b81c400c100c1207003003100264000c6009a204880450f005040c0d00300600100540ea50400c44d40c68111030050 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 672412158 1250 672410908 672410917
    0x1a01060f0e131104120c0b13180213090c09090e03040608090f1c0306060e0619030f0f0c0305060619051e0301060306090b0d2a0801050703091b0b 64
    0x5101c0c080c0d40102d80140c10705035000b690341910003904155900c0d104c2a600c51204080c400840e0010030602001c1604421202510000310800c200d500403542041a200140a090000040884d07400e02512500018248140008112240000500020501c0c0080c02c6200c0c5070001c1211501b88a04481180c1001084404807900780c600a49292130701b00070141480110800e500142c455014424842a1120b00340e07104500540c6081160544c0c80c1001c0e030f40d24010034201d40c3e00c558288101d80780e130800c1072a8000412001d2400155942049941c1b008a40300031072032900595a510101d411030f5098441c840d008031084411a003004000307901c1e800035002085c0c1c810200080440c0f41640180a0313084040c206038160203403a107968680c030005008021a2207011007050400b00805203d0405201500b2010382000740f90070014402d03804070350380b603403044000008184007c0c000500c440c000c0c45007a000b40e8250f034010400761254100103180242c40341000c0309401560714208180000c0c001140c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 672413408 1250 672412158 672412187
    0x18120301090606021b011d0a0803181f0c0b06040e011406040f020301080c0f01110708160b1306111009050a03091d0a050406090b15101701051903020d1a01060f 70
    0x400c41e0751040700c08123030ba26031940d010380712501c4041840700d0040c1070041e05036400441078a00c1c00c0039070090fa506000c00c031007500f141c41c003161141c0c1d1240c4c00b29071301915541d80b00c0b40c0508045072840c03013200034508640c20204001c4034644440c042c00039501d0a40502003510345e20907000c2d805c2d03505040401d600c405114600340d01c00d8a6214180e010799006a080403803000000c01541c011507940c1641d542c846140010a0910045860010901172640400c3d5266607440c440a591103a007481300c280d80d100030480c1c01c4c0100307125610306841500c1590280c030440381e01c24800f800300c3d0482490302410603950764022601980710720655420300440d142d80c0d01c1d0700134500741d404901c0e03417510306007100108001200603054814220400a004400086000c0070140584000d245039842c60030443d160820064480055040c0e000108002d2802c3c642c0400621001c10042002a649a0020b00004031408080300c0f189540700c08803405014a0141900400c1d82d800c081000f01d4180e1801090380314056101d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 672414658 1250 672413408 672413447
    0x230a1a060103140408090117090316020a08010e0102281202210c0a0810050a030b091e1608010603030c0305071407120203010509010b0918120301090606021b01 70
    0x1400d5a1003500014805420154241860709060602500075400140c07114041441d001c1040020614080c81c01d00c1507481d080690b0806e02440e294405080881074240c4c1e1000400301e002c20300307134028400d651491008030001339855542098910000b0b205032607480c1c0e140844020740342c0c4580c201c81d280000003068800140d0b21110b0018172801e20300500022040051181c4c10400800c07140402000380e26040d4680c1c0030a0356426030309645008090140c0703038224012101c01c0001035203125a040e0800c00f00c5094411085800607124074070140903000000b258025250110141107901c45c01005d000da100003400021f0940c1c4000d04001c0807080001d0400900040709002c0c40341044649039040030741819a60740d25a0399034810842d4400320010b038820b520348030124160420512070080300c40406460014603036141902100c0d200c2c9180c400120034056110021407030000e9000443c041d101c00341001070900c0c00c01074000d140c6003170700c0002045080100c140e58110382e0401015000003001d11031 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 672415908 1250 672414658 672414661
    0x90127020f0405010e0f2101230702060a0e21070206030a0b01091a0a0f030b0a0806010603061715060307150203070c060302270102070e01090608121905090d080304230a1a 75
    0x31f0301801400e20701b10401242501e02c410302403680c882c0781d10900600044d422070b009511000f050300101c40c0c4452245802c3d901004585054420203241038100c42c071402099810b004071900400d03a00d034130413906000341950320f0704146425030300f00b59600302806000c642c03812550300b05001185c46202d050802c009100010a09207440e9204e60401e00c2400d00150124002d03682d280d40c08bc0d40c0b10002c0c02000e000c02e0030040c002c1405a07081d46024021042d402c01004610b1081122110628024000580500404801143d4404000005070800085900030350740c40c0498180b41c0400d1202c0e030440c00805004012041440040b114034101d284240c164460080203090300603840c000c49a80098101d0200360000035981041754082000c60f0490819550b0203603040083c2e041922075280151044001034420150700792050024001c601c00c040d1800d0100555501c9006050304100c07030444000308038200004c4011951303504642c62000c0c01d0010030150103503941e00d11038090700048042d12105c4040 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 672417158 1250 672415908 672415969
    0x9060804080415020d0f0e03030403080904140c0903100903021c020304090e01090203150709090b0a09020c0d1205100b0c100914070b0405090127020f0405010e0f 71
    0x1801c4a00800c0c010f890705070483c0404101944039407844140001198403c00707031090701c90184c007050242d020300401179881e01d421640d607507116410080409401030340c2c400c1041010169045514060065030031090740f203100407010949080314048145815504041c05400003d40009203402c07082c0d07540c3c8041c0081e8043c040224514000d0b50f21051103036040590642200c00103500482c2ca02c0d0080d4140c2c1d070a44070903c00c01d00315180c25030300f050010711702e0709007044000d0716a03009290303000004010100550303407400104c09903000303a0180d540542044003441038039608020b440d00762620300385003440145410b103400c1928899a1150825081d00001d513004d0411061100300c11000440e641044410b00303504107400444847d002038036852083c15004500995007500b5a8111040100060050383c01c042981c090b441c0040c6030250381c00b91013500e50b942180140046c1118040904240b602c440c5000001130400100c013603214029210b42e0f0400d2030540328020342150ba80e08000600c6201040d0343c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 672418408 1250 672417158 672417173
    0x213031103011e06030b0a050c09010c0f05030301180f0902030c040c03020408070f230904060b01020a02030d180b0301051513080a06050406060e07020705040c260a11030709060804 79
    0x2c00a44141d484400c9825000d192664440c105890240304008000d41d516004501200c0c02070300c0d2720415440510007100c8640c4070f203802406180c0300302c06c407140f0361500395a038600e582c000b80c0000810742d14515010b8034803585c520501c4801280d40f00e00340300720003454010070344442501003541e010b0750f1075048900c1068001d8045500074a0308008030b5220994805000216840714040e211000c000342c2014000741d03c030100c0d101c00440380140071004070b850320b5840c45c0c000c0401d140740c04c1c19800f4400c1d2490240e5018002c001c0700c0031464850b0304080c04a0307001c1100740c05058100080318802400148103648580c0304105d0174407003000e021a9101c910f18110241c0c5600d40d0302582d0507104140a002c00c02840350441401540324013418012192540ca030148800001c80c1c100b40140d02094041080e0300e0700c0e0b00485003098103800c0440f20a00c11075002d0f846104800b82c80194002e9810a100284000f4800c20300e101c4d03901d9001c1800c50030007410007402ea050b075114910030003590201180500008 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 672419658 1250 672418408 672418421
    0x906040302120c04141621050907060e0d111207030803010308070c0509090c1003061503060312020102095b0e060a05030a0b04090c1503021303110301 66
    0x100194000c0900202c0e95680b42a9040a10f00031820516215081c200065000d4003c0300104075081040840d200c4c11100b900040240540c40b40100c0c000d610144002d1040900030760450024120f902c0c24540c01038011f544024405010f106500038910114124201040c40f4000445030004940c410301006464914140c00160a1800c008000410403c1c0340004118040c0314081c0244002da482c01081907482d030071036440c0425003003107894002e60300c2c1503208500a5070003030800081f81c9442da02c0400c11200100010340119684141c18000d021b080080e07800ca507800ca100039441d254802c0c0c0800c01d4135215200c044202c11a5000c0c1200e050380e000308219072041200f1884042456080c001610010380340b2803980780903594075084488034490360f0b00300c410081c0540010307d4403070031040c125000d0b44010008801a691001c0e000c480760303124040c2c1e108490040d02d9a1052604007220030000b4140b03c25990300b81071041003061100c0f804e41e110401100e4000ca21013810162000109015184 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 672420908 1250 672419658 672419663
    0xc1204080403051207030e0a1406340209090c0f100c12080412030509030f0d090219082505092701050a140402030a1b0b04060509100c11040209060403 66
    0x64034101304036810f628020b0021503000b5517441c2c0700c02500c44107219072408039004010001c401d5000c04403050070300c44020450810454601d1850025400c0c0c00041c003e24044403200940700c070300c81941580303040e04040d80c118001c02c024084136000d91000500480b603240d03101740070304106050004494003d00d00880b4150300000032298020200c1c10050000d01c0889003100e01c0c111000313044100740d104c1d204440c81241035074021b5150018441e1003a00390341000001c602e415803141740031401612074001070740c66000a00d68554001f1b0a00440740e0810449d15202c10b007d9982d82158401010690149003c07140d06403144e203041e480b180c00039005042f04840100644a804d070580b0084001540000d01c502090f903410421100303481004151102d040e0b4004e941907200c40b43c500b02003440c1507210b041441010440d0b00c2c0d40d80d5242640c142c035401c15070045010031b00204e6060340c2814600b07039010648243d4600203e180e081c594442e880403039607030071140c00b855004c620440300383c603040304507002381d238 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 672422158 1250 672420908 672420913
    0x16110f06090304031203051905060607050709050f16140a05040b070c030605010906050619050c060403020106240f0e1314150402120403030902011b0b06090c030c120408040305 77
    0x41c2140e44a5603aa11030301c0111840c44800c1707601c180c030034800c3c0700d06405010300c0b40b05140011711050300900a818058200342d40140300704401c9001a204000c50310080600c6500820240303000f00d041110360380d00802c079082d0001c00303024000d6220741c8005000c01080e19800c080c0d85940307101300d046545006941020401a44c000f030f2480620448004440c100c1e44154000d0003030340c0c1c07607200078015141c09206464100c00103209004140c18050f00d2140b0490a9241903420004007100c4141f5280c41541c4c280d000d0703552488244a110404004c03401109443c500003901807101004c020030b4071a0000214080040880d00345140c0e685004015021100441d003e02c0510030300c0074000b0312020300342d403207446481d41d500180460f03085c14001e48090b0000c1d4a140c030702c16602e94609070040c00d0000400c1381044124a007a0f916022040c0c0300607120382c0079070b805040b039150038014002407600c09010001011400d00c10040b07280d103a00110f40116071041e4892201c0e40300c07481d01044c1401503030801003550 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 672423408 1250 672422158 672422161
    0xf0106020a0f030c0c0b0c010507180b0d0905300403030e100c020303132402151321080708040519080417030307021c020a03081e04210816110f06 64
    0x1d4140000740016000a47c020001034542c01d109a074066281e41c0100c101d4141c624082002820000180c49600e00030140481d50450340d42d80c080c1098041d050900c0807160030b030074042003496816001e14404040711121491f0500f5600c000e44240107401c40544104040800c44001500c59541900c00d20b90280440c0d031a18500c103081035100683c1c1c001d46104042c0c0b602c0007500c3c6002180c5540d810401c0d500500040c01410302c4060079108001c056644103103410903ca4001b50944032420307100715409050640e4080300840040440b14007800718001c0003e80c0041c800414000715004280003150103030211070b08807503d82000fa500030b9910000c50340103941d8448949003800300046200344119400d440e0125040d48403002c0d01c107495080800140c1c08110008006801401030642060140700340751520401244c4002010701d040750111415100020400150740708042d000f400b404203400c00e00c000d40f0b091807968a01103103980001d0104075100e400841c410005110720400180340b0340a070307075a6 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 672424658 1250 672423408 672423419
    0xe06180a0b03151804030c030207080610050f030102090f060d0b041b0201050705121b0f130e100302090c03180a03020a0203070e090607030e0f010c0201050109050f0106020a0f030c0c 80
    0x85400850707032055680024922007025281618695001300508400881252070b9500d0403940c2e50000e8200300e040d4841d85c0404260800c1c1001003e11408440c00e03601c01c490708203001d0044200031584828001c1c1e0040c81041d01d20703900d00c845144601000d50f00b580d2621b41b401e00300009090780302000c0c0d405c07034a0800d103a03403d140e01f02d070718107025843c6400038012341c2c0350058110303014441d86402055915400c0040750312508001c11001100308516451401c010f046508031030f15a1103e07801e0781440c840343c4010040c1581d003a01d415032160321000c01c0f03120b15103140c011401d00760008121607541c803000400a0f0015858000701d101c1c3c42c8904c000c0f02e00c0c00c401440c002e51780e0b44241030164480c0c030440200184150300b01292030b2181c0c00e84070160030191a0210250068040702c80c41d80d20324098004081c0b0012024450030131202c0c055800469254548441c03441150000b03003009424610039801842820740004c2d9200350305078446489504080b040c10212020003013084d0090150b0b4145200103807 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 672425908 1250 672424658 672424679
    0x41106190e0901080c0315070e10110705060307050706091a0f04060b091003021e190501030f09021f031404080304141c110a0501020c030a120c0e06180a 67
    0x20300110030380b0030205590702e9072100c80e030350070f6030030140382c0e02d68000d134540d211004420b4030f00c5400444a040c14071041880c64000307400e200545000c180042c0c000070a451680c041004088021300c41541c10a04c0d50411510003840c038030403518040c00854950320103008020802a01110f8410114440821030404800d8400b403200160f40584101e814400150342e0351520805072800f130758150300c100440c589142e0a100d5142c00401c402d250702038010f500b190f615211039845511022400b2102800b882c18080003404903200480c080140c40d10b0100800010303101c1060011100860455010700210303600000c901070420080c000301c031000c1c031030b02340010030103610080d41c0224822a900c641c07000688100c59aa00301205143c0100b4201c9104081101d0051045840d103c21800135154031819644039a42607034010101c1d018298800a0607004280d80201340d4441e00180810610a85140100003481e044200343c03801d116000009034112300c4c51400c011000004809022924656a00c0e40740c000f = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 672427158 1250 672425908 672425927
    0xd080d06030602120108010204230102100f0b18010302030322080d0507032c060a020a0602042d0602100f0b0d05062202240c07180f0e030304110619 65
    0x311300090300008182c621044c0295416602d05100c14210059500a000000440f43c10901d06601a16500c10048010786c0500c1418981442d8003080d080001024882201108865055103801c89c0d030040c00141e401104035845c0d140c3e203549840c01071021500c00000e6220640c00781c83d01d4030422140c04081c3e0340003c003a0002e1f80c000d4403017140e4103294505042490401149000c2c80c085c0356881030304546048009041c0054481c030441d8441c00c66039944400302c1e03000b50050408406003180c42c00000025400c0b1803129420380903161405464510701a5841d00000b0003480783c20f4032169500500011540240d000450040200a00b60a9814460344030101907408400310004040b0a08144100281070f90010358080c18031928000c5544041d00b02d100103a9101101c4801000080c0d241e01c820131026015100906412480101c2c2c884100101d460092110b01c2042c104002c42000c81da0100035241d00c2a0800e0245c0100c2c90300d400040c0c594810250720070031140003448d4042d141c69102c1c1c000d1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 672428408 1250 672427158 672427177
    0x50f070905100902090d060e030f0c03131a030a05060105070209160f020102091804110a0602030a0305150a0b03130c060e0307050904050d1214011404050a090506060d080d06030602 79
    0x2000303c1e01c55042400381c1c4035142d02d46401c110f440c1c1001b80014000e41c031001c0b08640c1c0c00e094a00717202c03141d6003400003540f0180d20201d8580c004a00a100640c044030343c000208030750b06050a103c0300c00a0344640500000f050b61087e16520f000098241e4021021102840c0c0e000700602d99616100303850000c4c80868a00450014a48019802101c1d005100f00d4100031402415146565003140d01c4c1181c003240200704907090b010b0143d0106080d100c00544001030446a005540c4541071450004d0449100403c07145210700c0540c1087d10030744460000301c05480c000400035580b43c1e90001241e000b481c240c00d005000e202038910000b001c1c0da1007000090303a040105e065650707181d600c00c1000441181520b0160840d045541c10703500701e600035002902620032400d404140000424100f0311000740c00d80c841021030382810103a60043c0b07000d02c81d0580c004c420000070805070707882d40c94032903443c00000d101600074611440807009109803101a62001007210000b0b01c1110b03260314000d0046c1d0804508e5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 672429658 1250 672428408 672428431
    0x40c0305010303020d18090e07030203010906231b0906270f1206150d201c051c0309050a0c05030d090812132c09031c0207050f070905 59
    0x400c3c5c0c283d1003011851140c0074122003000c2168140455907004001c0c0c13100c20b01c000e1150107000030068800b801504002401003030000780f00010a00c0e61600180f00140010b0482499410400640d014080d1540088181606035403510380800c0401c145200310188403060140c5022a901d00c2d074058401c0c40e0f0701c21402e60f43c0c402000c040d482400340303015001450200a40003c0c00282402611100001444070001c1c10308400070126220700010b050989641c5102144890800c402d40c24070241c41c01c003000d00401c0c0700100b620540c45854494411000d0401144000c2d054200141e00c240c2103c2c00305600181503501c0082d6030300d4803005044a520585000e40110541d00d56100e004079500000c40c0c43c001d024129154811400100300d07440050707102718814a074840410030318400078514510f01e02c3c00c007101c3c002c400c104143e01e55041001b8296046644208013002e00008006c86246011010f5580581c80b12418a001420f0590b40101b4500c3c0c7c0c41018400a032910301c90b0005030103525021203 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 672430908 1250 672429658 672429673
    0xc1b0c052b0f08040302092e0e040209040221060916050901030b060a0306140402010201060e0910050903210703060f0302013006080312010504021303080a0e040c030501030302 77
    0x2455050000c00300c0c80410320003007071516440462108034203046200d00c91150540707829140d50000b0240f482c142c850010040c466401080003035000032458041d10040d03903c586507185040482581a500204000c2c0a0382d00711000c1003c54454400c40c4541301e84001c1c019080e1403561a9145d03480108664110403485020f01c11820004402c43c20b05c280c503005450380720181c1c25901c0b02c1c614420040d20356900101190b80c0000420340f0f910401e204440d0418505502d420640002429a002c2c1c2c0c021300b04070f0054106100e481d420002d1556280c1c04256000309569841500040c118020080307002201c00425290110f01020001e1007032241d08651801c04c0b8040c1c4410700d00c0404030f001c0c000280071491540841d120302c140c1c07003c0050042d510b207a10304100030003000344d60180da103181c1c0000040da01c0894803424a01c603554001c0c2c090442502d04505041103a034050305030013000e200142941d0300000328000f600e4480d02c0204030040001d0b00c1400040140f480041c0140380c00d10069005003d140c1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 672432158 1250 672430908 672430939
    0xc0307020a350c130902010e032d0a0f0501090215120a021b0d020309120f0c0d0c0306020a120635010e0a1b060903080d0c1b0c05 57
    0x2181e6504680700311098146104101c0300010901c5465265a101e11840203c8001d0750303030300c41654070203441040d00401c15003070b10320002d040c0030200144103102780c01588458021a1443c0401801907030840d400305001c40390112514100084800d000d44940c080100038400d0000540012407440d20036540407000c812069901c04d2980180760032065404241404200f113150a500604080c04e100308607003c990300728403030071460a02c0b10341ca02d50240c0c002107205416458802c185440100544d806010b180d860703110000d80f2010b00000b502c0c401c04074034080000f03000d80e90b04032a01031944001c0443d9107000100f0040d01b50042100942c214905121003c205030740400001d49a0b008990a440b0f4100e100b0070310203103c2092408072a81c41e42d41e0b2a004010902c04010550b4024001d024080c5444c00b4000c0618001485130440300501403945001c000040c82c0104950018941c034000068601d44104222440c204003e05840035500909c02c010501c03880e00b2000e411140129440540301c038408 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 672433408 1250 672432158 672432179
    0x218060c0304060309060608030c010905010507020a020d0b10080d03050402040f0603081b032a010c0e06030703050a060f1d15060d020c100504080a020601081c0e030705060c0307020a 80
    0x36801002650001d0004214041c0a9001207164501c242004980301d03071a00f00207861034200d0310100420b03a448036004001d002d800c1c4101504807030309102400102d9203035004641d507410441e100400d0005081f0005400c41042160b0708041c03d20b4406481412540e00001400703040150f80613442907103001358165a940c441e1080c24212640a1019030401002d0490013407082d01d0070042c801c5a0104004010306c2544c080c1000e001c0795440292540030107c4401c0f4035007107800c454092800e00211518001c0c050f9500781c190b81d03001d800f43c03030040317900da0319001c840002d030186501c0460b6840c500a8080785140c0380c13a22400041e042c2101c4114a9650007503041c108030340681903a500030a04101d00e040c40761581d0018040781d0510021101a190300c03e20042c00c540040301e0603262248041861070341d00754140603903030041c09030300020800c681c004858000607814210102c810711450004d681156203050003400c00a0400414107a111a0040320082e113961180500b01d20503542e1138000724912400 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 672434658 1250 672433408 672433417
    0x2307030c031e120902010e0909010f2324030610090f0b0906010c02030708031209240c161718061305040507090b03130c06020309010f031d0709021806 66
    0x31540e444a25283c03102e00d0400424100c02d0a07410410251900c0180b5254000900c0c0101c081000004440c0a001d0280088549410480f61301b200b842242646c414001101c50f90841e0202da140780c0300341c04042d0001ca0300134902002d184c2502400080004200740710a41c2c200b1114102000d006200800c140d4a0031600030130221a0302299402c08a902540315543c0b400070140b0240417102810b0303d889501e4515040f9044050800b03058008001c002075040c030000700d16044940c150700c0c0e14035a03500216446d280040c4110b04190000c2214040e8000385418080820b42051000072459140e298080c807a5000300600c05027480e4a255180740c0b410804101d80c0002c403484006000ca50903c01084068100a0180c2c2e0800c114034001190070120480258014030104016900101c03940c900301603008010383c07010095400c14001e911203039801c00000c02e082c100d1450001103100e40f92400c0072080d03140d40d500301c0f600e00c40c0c0c0e0380100703d4a600d1b600501840781c040b011500e125a80ca0204800d074460b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 672435908 1250 672434658 672434717
    0x1203212a0a121814070e0a090c0602150a0207020f1804020415030b06280f0501030f0c0e09040330050606130b030c04030f0308070e011805012307030c03 67
    0x2000d4014401051481c40c1d040050190b0f0025100d90701d69508484c0a05071b8141d43c51040b007035590707a41204015000352644c004001c4c5002504c3c100c059500482d090304001041d0500e51900018500215511400440e40791034004011420354900e130070003e00102e104850481c0114178001c9800c400713103d4803886c1c9040320342c44900500b50f640d8000501811100200c030710815280f2000c42c2066a55040b41e181002c2c101c01c0d1b1048071020701c0c11000400391042c03480300d41243e51405049201203039004424030f400d208203076031002e195100c51401700d894a0301c1c4000d89802800525101419406500034441c894030700c0e1200340107039107411040000b140304a0311280c038945041002000355050200244d070344644010415414142c1e20384070800310088420f011070005060f0b0701044030304c54110191110f80b500c00c0c0380c0a200c1d20200e80e540194140e00d401402d0500c04500c100d502a503c42504049110188100f07280e1681e5092a002c0c0c62200981c100300d02140101c03042c045a2100345111126010b03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 672437158 1250 672435908 672435941
    0xd020720090603120f130e0a060608240a0801110403050c0307080c09070201140403050307020d0201050624070206040803070308090c03030a08150d111203212a0a12 72
    0x2800244009555400000a0408180d0034001b8450200b4a096298001c00c0c86000c0200140f920319074500843c2c0300781d0444410300210005211600034000b11842c0403000302100483c03086d049c0c100040c2c1c191000c0d440999191308003618880150039400280c0101c80c42401145d0340040100d0805448458500444680f503002c206d03810784602e001c415407604001107000025a414a540483ca0f00103c122001d40c0030038000014401c4540d410400a555107580348000c20240c00c11000141c82004410803002402c43c547c142600051596021600c65960040c152540d41d96110201a00c94011000c194049031030400050100f00b070101d002d901d0b40320000c018500d00445c5880580e6001d03005040802d40702d07006d0701e02240f180c4030b52198140c41801224050b00764a000020007003039034074400e1032200b01c1e001881944003560603502c1c00f54004045030040380c03148e640c0c0c05d85003c4000c1030103800b9065103180e11001080786c0f021b000611a4400e96541c4910800c142c01c503200680318034103002030211 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 672438408 1250 672437158 672437173
    0xc0207050303072d030309020a09150504050a020d051806061e040f09060207030207150f0804140a02130c0206010603060302090a050402010e0a2c100b0f0d020720090603 74
    0x81e6a400c00c80020003413400148903100614040980b100a03c25030807000700c0d035182010b1055140c515869801005404000d01c904d0022840c03041031101a407040c01c1c040c54849000c113510076415010b6844206c1000d000304441d141c0081b86141090311560303010030a014640100d20030f030600f03444142c95591860450805000344c0801d002c0101481071803660b10303644d00c6e0411000240140001d120150103980100342c41824204400503840124007031400340450701c000b4000854002c2c0c0c01c1e07a4841d4011004103440213000d0702c240e0070315080d500020740c8280c1c03508d4207055000040d440702d1240d618640c2200c22aa80352503068045422602020354082a007100141d02c0b172110390811070b8814410301d000580b02c003002003ca01100116040408810101d40d61509180e0344c0310340d0000e0b0344014400030460340c140316142014038803840c01108103d04001032007812801c48071003140c0310303124090700455403400d05082104000144840302000c1d04203032000c00c01689013401d480d2707008541c000c01800e5032 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 672439658 1250 672438408 672438413
    0x4051506041a040918050609011a0103021809010806010602010b010c1e030c0803010f030203010b040203130b13080403030e19180207150c0519020307030c0f052b030c020705030307 79
    0x1038440030740458580102000040341300c4440d40110110540b440102d405120028900b0a0030060020701c003001d0b907031500203a80580300c00c00d54040031006003802d0050341c070403040380c0e400754401c0c6102520382c000d52440d0001800c800002141c6c0d040750030766402000742c80c11810046501c080e0070103001e00b004d0400310341c101024100c0055400524842d041c401d280c03800310358804406030800d81c00528084038040341003082d42000c0c001c0745c5c0800400c603021451480e1448000c07194854100001d404d90310130000045001c0382001c484220344d50010007954455a0f41c0c030313000345001e1040e4a03181c014202c0c040490720880380c41c070211003682e8114001c0c5504805c40c0f0308000c02504903400649110b611001c0a811154151144800c80340e91680e51682e501002880980e80302c03d02100c510866108020a00100b0341c00710250078240d82c0041441c000c040c0340c1c1401841c21101c10264404171100115040d410002411401c0307004015850038800c1cbc0c803407200d00342d840392194818541c041e0030400c02c1000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 672440908 1250 672439658 672439679
    0x90203070e0d051006270207050304090f02030a110910030f09140106150914091b0d0c200c1c0804080a1b0b0a030504060204230405150604 61
    0x1803012680c41c04524425041002030071201c0022025280c03900446240050000240207101c09080006e044241e450100e620f5080004103a500115416034041182000c0000900448008102d000d100f40b017940c0521210340001c0d80291071100303405140003c0249000f0300031094034540c650040110900203031700c01c0c0c140c0182c9006075030703041400d81d01c0b00c84c200083d40a100c10001d640b491400040d607207003030403142c4440900b04408042130125580c0d0801029074106001002480150f410a00a0701c40752038818443d0a141c1500d041c901d00414040030061325030348030113990205550346032a851100e10980800020040c80d4004642200125100d5403e1201c054941011005018101c414164a9180c0c03260020b4000b0700464100c06800820302840d440c1d200404100c6201200c3da45290800c000c5161060004110038151a200007606200043c2d041d14024a508504100d82600494110400814603100903109500d80f8003c80c0e404500140d134000001c4016108d0b0b841c2500302040d852 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 672442158 1250 672440908 672440911
    0x90510080121020411070804090b121015120605310f08040306060f0e16080412090503030301080d0201050c03010602070b0c1614040b010e1311120103230105090601090203 75
    0xe801c65201c085d40c01c50440b1281c001c107100d5000b0088252102c0c1032040d00b100790380d0195003092207100d40d10320b02074102c000412600070200181d1800a04460714400c0c0700510708003580605945040070051034144940c0ea00b00c68450401000000c05196041140242081001e0a09c682902d100e4400741d0004210748404403a060203000d500c1d0401e41d50b50b488100740d0b8413030f4000550703001241000f008100300c1d07510710b9600302441d030b1044003802289001c011f000110003000508071500a0b41d001550a010395841030190501a064903980d40e1140c1c1c00954600b800343e0000700640c0381c440004e03034800f64801502e0583c0c00f281c2c00b610041d460301008640386c2d00150005d0405001e01e07086e00341e1403004a03550900800e6212074504c0340264050400c41111008010981030004640030982990350301e00d80c00d0b0018038000c00026688402800c190b0007070281030f1000318840524000031040c042401e05411b01d0741281e4140e454030024540314642078038000d40361852598002e03401441014182c0d0044c5 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 672443408 1250 672442158 672442163
    0x806190b090f0c18060c0a05060108030708070b0705091503010f0603050c0703050c12070f11010203031510050904092a120204020306010507320304140d020f030a03090510080121 78
    0x100361a1a44d240020341c0b903800400a120180c0c0b1000075001008018040d4034010909480a18204411a00c5d0000b0ba40f080000050004288030001400c0500a00a840f4621000380a81c00b41c075004d21078103140ea61080c010102441c03181140028254030034040c0a06c0380741007804090510225036800d9441d0f8224601648880c0160070400718a0b1803d18050000c1901649880c11081003604010420b8142c1d0340c4014110f400030810044c140b001c902d9804040b500544285980c0300c40d20000b21202d0294203d0941d006061034108000d0000c1000640074540c6109400324061540003040000b081c2d1602c80e40102d1b44172000780c80702515140d40510361003001810f20030724000c29682c1c0c00c1e20007542200341d40c0881000c0461418182210702c01c800500890b08010342c0361070304229120b085003410040180c03042090640700c904540714240078642a0602408545402c5031520b0701601300e20315806043e005260640b5020400c2c2c2c8540390546c102c807000010b4918010034080e414003103a1400f1401d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 672444658 1250 672443408 672443437
    0x12031b0207092c010207031b03050a23070305090f01260411150a0806010201020a020721060203071d01140912010e0f0102090901050a14010503100806190b090f0c 71
    0x30307031843d4081200508802c002c1c0005968211500d0050202e803214001101d40d038032802c9401c400a40c11a04440400059050561043d9000740c0002e101411080e92800c217808082020410141c0000c060580c80e2011208641030031061300044492074910100300542d4a07503180c86055000e10720030000d80040c00781400955113100c03a80070907020708085608190715400080c041c92541e6000c0f0640b9002502440203500e4102600d02c02580d45015020b4009004203562131f160180c101607200030011030307011400390740302c0c13809940260103120b40a0b4090018881d03140c900c81c4030362003000401e51480801442c282000e18140500001005105100c1500c0d9650105103502080811072800e075540000005a96580c0c03c90503c840310380183e000a010b001c0c0750009121101e003a010303495600400380b82c001d44079038a0180340c10340b480495003d01c645e030040405000c0d005000c190b4080100501d040c080c03003143d207024180401000c00719848800320080502180c607204009004000c1500c91000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 672445908 1250 672444658 672444701
    0x12003041e15080601120608060a02090607020a0e101d0708180f010501050112060e0402010c15050f0105090117120901031112010515030106020303070c17030412031b020709 76
    0x1031124080c610b90900c000454860b104106007580d00c103203035048a00740c0d003005201c05132034609403954800c4043c02c0326620580100301c0403010b07140c800a85440540051006900c146c1d201a24041300c801901d003140d042d8413801e8081240012214071003d000058080e4140c0780d500c00c4800c44c2c010718041c081c6120780f02c080b01c5c104e404a20810031141d003a0308110001620303516081c005021f401f50032420729599418401c04215003114036503030551080e02070030042000d2040b80f5244141c41c0c03041c4c4100070b81d00d14110070700021443e8042c809050b2501660a0781950340ca815504802c0002074040000a901880c20720406003542d4002e01442401030501150201040112162a41203121040b44000f8034000400c49481e140c8414240e84444100741d51a550400200944a1000401d15000d0002c0303c58414204045c200316500403852400302161242070514002d080300191050b03400019050000068517001e0542c0b103004040c2c044c3d0020501d8520740040000500f6450044001c0400d8209 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 672447158 1250 672445908 672445919
    0x7020301090317090705011d0a150905040f052e150809011b0c1b15020309010306060936051602120301030c14131802012003041e 57
    0x30540340342d00ca41c50b15204200041003190641c0002882e0301307004d41c080f2800304120303600300303c405601c02d040c1601c00707400428600108240491b01d0b8420514034545070f0780c41170034a521214800543c1c038110303818400f1035402070b280400d9030300a941401981101003180c541030204d0520300c3c2c000301241110945c24030365401d1404411201d0030042c1e40030030021320070020b426030284150030140c03074040c0d00c10001194909000301051305583c00203041d024a42e048880c030301240c1206000078540c8050a04451041a900075160b8001e0b0002502003030810801250450184d540181998906041e02a0106844110315480c2a0351040d0a5100241d20301c0e9003030f20480340c015540320f14116501410010032000000340391407003a2645000600d0144014000214012507040855401039285000030900e02c0000f0040c6010110169459141561011002409194030000d1034000d0b00c0f000c504400c60b290a121928807040c100c04140c00c00c11040c0b0a403114a0001a12401026405400b480e100d1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 672448408 1250 672447158 672447161
    0x9010f05060a1203210b01200303062202041404140c090d060b090903041a030108060a090303022116050c060a020a0215070503040605280c02010b0415060206010b07050303061507020301 81
    0x41c0d0039105c80d0f0b030f162120360043d5600160b01c080a500000460f91400109903102ea40702d010180c100c51003002120f2308100b02c20501a50404c00042400c011517a455456440d0f904154a4030800c0703014908048100143d000201103080c0311f03071606007020340340c0070f030303040c00c100810309480b10446150383c6d00c02904c500e6403201c45015200d1600c102c0199515400c1039401a28801e0000e1008034001c0108014003440c540858006e400884030100400e00745a9440d040e006802840c01982d006102001d481e0481140094041d00901800000105003e803109049805d40f2900280c000180d00c60000718050740303110382c024001d8110354030643c0d180500c943d0795100e0301c880540b1070358001000407051100f4480c0302d1040c07680000202c0c0b081005803d50251401054130503e20510300c0c65030340d40142c01414003c0d0018415424020420019603551042116001c3c80c80d0141c040103100b0b05001003040d140c3d00e0111240c180d0000020760455a5180402620b0f00562002c841051014480c403001a2000d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 672449658 1250 672448408 672448457
    0x105070602130602011805150c0c060f0a1107081e1603171501020a021027150212180102030f2d09100305181509010f05060a1203 57
    0x821802c4a1520000909440c0c40180c1004445590018040040c134000380b60b0075900700b05041c54020b640d8400e261a010300072005081440d0103010204081400c0840041c0e20407031210300208950600c100c0d802c00140545180102115000c02c20801072542032824400c12401c003450b25880c08601c807010400d007400590044011035071007420098900ca0b150b2040360f22a44045000c8590300465000079030306c01d0024800b0707000d8164082c0c2540041c2c4100b0400302e4070750241d1f40060f28a00070850003074105c0c0880c0f01d0100900d08840040340464804039201418810000b80380b41040040e03a2001d0b02c0a08002582d810361104121441c1c02000e00000360071380c0c07416100c3e400a82242403c01c44007400c07142e0400f90030004100120300d0540c1e81d584160300e40c61503034540040e071039599a4010b240c5501407081181d2900c1080e030403d1055807a050081d11442d05900203011080c030309281901030f13600a031403840c1d0181e110300703080c41103c6105040c61540c03806450460a407040061150741c20556 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 672450908 1250 672449658 672449677
    0xc10050a2a0e090c12060a0302091006080906010503060403050f120112060e010b130207050a022809020403170d0f0e100608030705060114060c07080309042901030b0105070602 77
    0x11050050403140d00402c0100d101102540d0088241c5409909a1110302c295440c51440e85509000b103600d540f15100118091a4050700c000c0d250b040503440304613403200034855000015900f000094040b0700109116040716005001048161202e17034080d10300303400102005000c80300901c002d0020000200a0364020302c03040e40e94100000703c5003401006d9940205054078560704212903104161203440640a584e908400c00507102c54542c5443c600340140a40701030752100e04614922515070203404101c806045030904c6103005030f5940d07100401c0c0d00403031001601001003403441c2000b204140707004140707c0c180c1d00400140f550000c00910207c4004800c000b91030b6005608041040b0180e10542c005003407108000d40c28400f640d038986691303060502600014079010f61084580e5200c02e401d503107100b81604180c2c2c2d001358440d083c042e90394000300c80152089041810140e142d04507043d070810b5500c2414036080880480c4c10041d00600080d2840504001042102c20080f030110320103020442c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 672452158 1250 672450908 672450971
    0x13020a120e0303060a031e050f1506030a0515040c0b1803070605090a090e01060305060712231803090d080403060609021612140c1e030c10050a 63
    0x10000031202084500e1446458069441082808445d603a50311010003104c0e808100800160941c10f50a0f045681e00c5200914511a42994030940c1c40e001c200c4e410058684108a962680e400701010364030700c00a0b902505580000c0041e402e60075064407000d6000c1c1c01035940c0d030003183d074801c4008803d61191207011841140300e5155103031071405000100090565251036030400c4c03026800550048480e03c5a4410380303941d0340b00748000100c2074001c02e00031130b0807805036080e603d01380c800980034040442c1d1304810113281003404140070f100003188114540402c00e406082c0e60700c031a49102c00308010052000d0030700c0b0500c5240c0305943d4501c840c0395000d11031004a0f13102c500d1441c0c60406e40c0e1075600580891401400701240000c00064407104054100e02415008030304154181e491001c088480444800001081c066020340016081c00007a9a04002081c00603041c0c0c0841c1c503401110b00c84051034000218a401c1811584c11264000a8103000044c000c014000b181c80c061179030700aa04e5900 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 672453408 1250 672452158 672452177
    0x80a0203062e0311030105060a270b0309060c071a04020d15020703080c0703050f03150405100501020c010201111b0708010518070f031101080c1308011a010309020904020f13020a 78
    0x25540340c000d080745501d034003000385c0c10740d41080c2c00118180211041d02081040b1078156810194450716410f00402690302c5454401d51240b00603401a401190102c400340714040c0071403402154101115400303508501500700c04601c2e091030201216000e0001d0b64004801c00d01200881e2540703403c0c202c200005200103a580d0394500d0090003101004048180101061008101013034004c42240c11031441d210605c3c0d501c0e540e9100c182da148024015058001c0d15181c104050340302542810015544260200c3e807102d02403100490030f0300c841641c0d44c40f541005206010003404a00c11603900da81c4141c0c242c1d900c1d01d4036400280d00310f130f404564800642114025180e1300d44418010503025104520f2001034641c19034444070107601400400741d04100081001901102c0c299059034100c0d038141164041943e43e400c59140a0b0040c1ca486410124450001c070321290700a01c10040c903250b000e030040c04c0da036442c2d03020081e0083d441050385401c40403c5000d45041c810707030310080980d032150761030b0f000b240d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 672454658 1250 672453408 672453499
    0x203130b0c0c03010f0e1b100f14220b1c0f09150b0f01090602060c031312020a02270609060402070203070f0e0a06031e05070504020a090302120d080a020306 69
    0x103041f44060241c040d80301307100003040c29454401c0200282d220b00d00b01344a00408000c1c0c1169496400d00554020280c042407103420307040d87c1461201096121b29203070101c1c2ea1a80c80c0d40103c2e20404038100000707900880d045a1070f203803540140c00103900d050400104194981c44032070660810024440c4810703918465007025140005469a150703c2c00c0c601141010b09150010399105405004100d00020101c0020b40310114544450182ca0348840c0807001520807007000f0f5684c4913a140201d2250010340c450700500103d0b0032068140355030034000c01c132003619001e00b1301103146005805181c01a800304070300005600c00f00040e030024450902a40d211510300480c28055103009009032a140f0b080800400100c0d02c0c0c3c00c0040541780810a9002d004070062601529064a41c0d11181d0401e00200d01481c580780c005840c601224000e4035000401c0e031405c141b15807211450b20206000c42e090030089100a1341e00e0313025661081010300140d82011400214609580d09040b02401040042640003030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 672455908 1250 672454658 672454663
    0x9170d0605041b2a0807080a030f0b0a120203010b09010b12011a120601121e110a1403040606080102070c03050f010515120a08280203130b0c0c03010f0e 67
    0x1841c508244a24021400900d0b00074601441c031001c804e4000d14001d8803103102003a14809060669112400d29941c400300d1500c1d070074079045100c2a401092505603410780450440c020500f05010080600c15110701300380c001e4000a02c0300d40141d805650300c03c040f010984980703600a01074010100c0060300c4622800c0361030002ca4058120380c81009020a81704500d060000a6402c402d46106819260750b03038500040300e40d1340e060580d0304000c3d4100084410707088205880e080d1060035411051001d940ea60140c04154421310849030000b6451604a100c0360740ba1201958005203c0c0c4008600c981c4d49030101800da802040058400c3d001100d410010004100000084080090021f100e2032a02c080c115400c03424485516004030403100c50405043c0c41072240c500310b65030200f0f002d0b842d01042c81007000c181c09020b260488a07040b89801c40d01b17081c000802d842403442c4103811000d001d420070040d000c4682000711189158854001c4a00c2180c0d000c1c05000c0c0c9003a80c2000002d0410251a807417031 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 672457158 1250 672455908 672455921
    0x6090a090320100509150705130506030a14070e040e0303040c140105040f0305060106093f0b0103230307080a03410a060f0521060114031e0307020409170d060504 71
    0x1403c0c0b203000c09c14044807020768288003003110000c440c65922995149515000380003422210009131141100304982c264002107041410401610108580c8450311401944ca22042d6000740210381c000740c08110421607460b201540007010f143c1141045c1e6103030500c0b810340b03207140c104950641040c1c00502850b0b5000c64a0002025003c00c086c103048003419140b80108150b1101762035140c1200340344031440b0050100c4076a03040d4002c24404066940c3d041100027111540300b210b42400840c00100b0b040240002038400c0c10b50411001c41c509044880d0070740042202e40d510b10071001652031900580c8200c80450321a61407919603032200c0c192083d80ba410f803508001c0c2000007091038900c007400f00a00d61b071480419520180c032154076074060700300004030038002128043c000784901c000201d00020440c0880d030301c4e00002d804a60000c0d0320104406071408001148241c903030310034080710015141c030b504100c15103409155510304d51071451400394459171040034030070111503c800c0c0c100f044d81054801e00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 672458408 1250 672457158 672457171
    0xd0807020307080601123c05071a0301031205070c17100912030c020111180d05030c0d080a02250615061812121815030506090a09032010050915 63
    0x104414204041a40441e85001c43c0c10b5a04160002c7c00388100310042180c0406801080c4401d50314407003c012024156000740001c44180840721400c440c0c4602401c2590b0080341c2c07100b201010b00d400d014914075503200903654028503115066140b1000c110500ca84907556005004001c0712054844001d015100c0d403000c8082168903060740e603c42222190150b40700202042055001b0480007400a41454034000d00035005000020301004a0f100002d00c007649080310741c84110380390303850303c01d0003040f40030b2110045d1240308295004040c2e010b4a0442e101164400e080000e01c038429012994902e0703100e6080340300403e041e0010003410030001820107008101104006803015500d0741c03084020f042d900b403403a041c4861002c1c2c00c1ca0780c1118240d5003026007088000c0d4442d035400080018068081035800c0c50250317903400f01050101d8030038018000301c560036803140206041c600303001030010341040010030014002c2808402d600041801210f0141129400414214030082e0410000c0740c000b9000d03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 672459658 1250 672458408 672458453
    0x1e07020f01080412050a0509150c0706030e060c090607150b13110405011b0b04030806120d0c080a1101050907060201230a181e12020c0d080702030708060112 69
    0x204400540483e001c0484c0f40241c1c0350051311100d40d08015582401000c0e10b85500c400011629240081c229020b404490740107012105000e55440c402c0c0c08542a00b0300440c1c2542108000030124411000282041000a020549044150703203500c143c290810301a400380c1600c64001d20030b0707440c109130318441d548034000e01002202d1034000c030403026100f1352041d1418030072001e8001e903c0c0b0f030101c00d0420310340f5089007181c201882c2507e00203003800000c40d10580304421150900d07030502000107a581096605072984005070403640c90700d0171181c0103000e0650400101c00b03c0500700345420b0043c24001d103000b0008014040c00c004000c0d003903400c4038040c42e6a04640c80d84150701c5c010880802c5421015075080010b00045500a1084079802c1e00c07409881501c41012034804a0580e026050b982ca01800ca1160311022a40d8201e0311010602505a4403612010300310300401d1024006040c0c1d24401021140c0080e80c0301c01a50810509900c005060b151a20b0f03281e06001405100b00050340032600c5 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 672460908 1250 672459658 672459661
    0x1c0212010b130b210f01050c0903151807090e0f03031012020a090e0d020705030313230301051626010303030f0f050c180303040308040302060f1e07020f0108 69
    0x1042440d246040b0212000b0349400540005403502002c06090426021050a1040c05000455524003009520030320b558608000100c8001082040e20f240382c800a028081410031480d4080c80f110014052242811071030040700c19400c001c2090078000e011450380402d0300c8131210b2040d404c11141e00000391260b0001c008104150f14080b1030301040d41d0342c81d4948115601e8034004569211b26a0b0410305186103411a41030700c461001864200f81e0607168222100540c941c020f0649a0045401e4160045d603800004d121214090117007211080c0500324058480c4c0c000c000013030a42e941a520000c0390341c01c001401c1105540a0305490340f10400c40d80d0250208a001800c603400c0e841403102404165840a41c09060400c1d5002007800d40e0072a9414003281c18801110000e580c4400ba00d6500e006120510001500307010058408030307900711000e181010300d96001d009841c0e200c40d5034400800000c0124a10140500c841c401026182c0340240361103080c20b1050001c2e54900042c4203050012410 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 672462158 1250 672460908 672460931
    0x602060c070f02060d111809060d0302060a09060e01022b090308010909020102010b03162310031d010603110a0e090604120207081c14070503041509051c021201 70
    0x429501a5507815596070b035562170202000402010003404130f940794100003442c800751003001401014000301c100c8200116485040411440113a00000203016802200000b00c0c3c00000350702c01620640200e401017400c0300c500c0f004900b245d1004c00f04400c1d05949200c1030021752110520b0724291204070b202000441c00645020b08400d50510400741d00549603054041164401c4d0000070210801030100c41b01080354020980e82c40c801c07801010141106003040c3c0415128901c030702500058050129440584091000c402a01e0a48107120307203803400480c0416541c10902c100802103000b1002c0c09250b4541200300403d40f810355002c007011400d58401d11003c0d4502141c15034025501c038105c000c40103811070043e42094225440800c0a010382c000c0440c0c1c0c902003075a19205000c1d20f507124043d80c0344501e007802c071700e019920020f41145d100b40801c0c010302c1c040800780405000c80b81024100a030381e410000d096030004980c598206d0b00c05c2c42d5000e003141401c1e0182ea4481c0c6c2490003c0c0809183c90 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 672463408 1250 672462158 672462173
    0x10501080a0b0f0a1b0e190e010506091504080c03100207080904051801060323010501030c12060b0904060c090609121e0803040311070f0f06031a1002070602060c07 72
    0x9011902d00310100f10109112415030b41c0100c41328800440d840350803002c04c44000d0400710101c000744e0300070284070140030034500304440c041050754510030300c40d01c00c9e90910040c0324646d0003408400e50000110350342100e6201c2c1b440060070040c0000b5009140c8000e000c0300b0705041c0041480c402d40200d0051100c0d900003455401035070207a141c203075030000c0c4603981c041403128403d9680710419029403030070a000c010f00000681c0b52140589d122040c15024640c184c0c07150032030b0024172020307180c100100c2080c00a4103803880b845440d07034007414000c110007000030001590203100f40c5044503410307564440c0d44141e540142c0084003c00c150f0509c80240d525241c00402e0200d00c4580c0100404021100f44a0461203c0c800b803481030f80115195480c0c2c60203290151290303040b009030220b144240d02000030302c4502000f0300390036145410b98025100d0300d4030700181c01070140702d20150b1101102480c07803c01d94a07508403c4010500590084c06003e19112020b41801c0c4054400c0f04240303000c02c50b15010030303e06c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 672464658 1250 672463408 672463411
    0x3280207150504060f18060e03040506040302011d1009031b05030601090207060e030a0302040807120f060b04090f060c03111809070203070c0b030106030513050c010e0a0b1b010501080a0b 82
    0x4150081034990f01e500c3d02e0340041850042035080c2c28504081000340601101411340000d200f100c00b0409007485407807842d6240214452950311003420081400154421200c0340c09040d060700403850440201400507001c6036a03c031b41b40f40041c0c0b550b4000c2040c49001802c0861020102404090303560401000c01e407584414000c280b542900050300b14100139003640a0100382000400707482e294801804010040c0d4403503c50a21140701d0181c0c013240d1a40d900104002d03039035020780440c951200f9603945401a00c007400e4001e80c003075918144940030400003411405441d00c580703000600e4156040bc05000c64803040041300316201e06010051440c4422010300340f42e4039044920003101e64803410105c0c50751080346401040340d48107035400144921782c100514180c85180d2000d00c000c0d40c850702001c03140c2040602c06041c0360f01000900409501905143d04002005021072510356242c22655000b40e000d8030000620310a1138029800443d000e01c94603015140f0580900a44803c0d61200da060707030700 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 672465908 1250 672464658 672464693
    0x12080d0c21140f090709060e0106020d1706041a0d0f030909150b280504140607030e0d03092309090f101a0a031103071e0b03150603280207 61
    0x407150200d07100b80c13400c01a141c02040720240c180000d0f615002d034154101401c0c4034142c054410f00e00070910003405625040555603004590704d05c40e6540c230081102903c0540d041042c1050354602d0004291520025100c01c6802000c02c5000c045240c0f038020090241e0b5030080496074070741204005124400200081180c482442a946030010b065000204010441ca1020713003806400100140070b0f0031001400441e0340c6950300701c0403030300d0080c00d021513803007403040090009880708600142c51030101b02c2d60001034024500a000f0030b440d0344442c1840400313000b100c5900f1121070014412803030000c0a0030b5100c0510805070110350902024141d03160101e60401c81643d0b215a40001941e507502c14403000c000008013040e1145540341011001942c0c100c4100b40a4083e0f89404507044500700307550142c50316840600c0c800103152516440c402c0d04040c0c03a00254000033b085881c00360b561100034502034499400c0c441d0b042c0003035a11806c031100a10070990786460050050764045a0601800b442592 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 672467158 1250 672465908 672465931
    0x506060706051302130c02071419060804120504060f03020c0106210b090703051903030b09180610140105090406090f0507091707211401020c0705010c0203030412080d0c2114 76
    0x1280c081c0020b140ac46114110107001c801500c0c002051644503540c43d004601407940c5200038201040100c4880c412030040c1004030f1500d825800341c1318820742c02010110141d0000140d482e4a0309480001048407030712a81d500b0b40c1d4480c0d20014030003a0b41141d5040718180009002c03c0d0700e9030352060340b141752291007a0b0000003003684450505000360825558002d004081031003605d44060800b42d4444408405e012512808000841c10b41c50980b84100351003c5d4601524140c80c0c410045541da408000f6258201b500c0b0200040d010095005000e1741c0c4002860100d100c1c039044a00a188940f990b004610a10784800f100340d0081003c111003040c1d410502c1040c4c1c0c111903459441e0100e100701e8000801c280888481a512090f041d0701a00d1100fa01209540d0016540c01c01141c8022140c0d4004c0c0d030603042040100710b540300d80704800204500c03c903038060600c290884600112186859040013143e07100103002410b10f4600c03014030114801680c100170940740152040c00d4290010305404510 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 672468408 1250 672467158 672467189
    0x40510030506060c030d090b010501030b01270902160302060f0103150504060b090f0f010605040608010e4b010b03041101030219020c09060102011e0506060706051302130c0207 77
    0x50f20f40c0822a03070340d9030482c0102d80d03a0f41c0d07041600d640280001082950000540d90020480d58844d006461300a58165100f40c503c070041c00c00d4000c03951000164003d1110b421900160900540c00a41000d40c02d5405129510165050190420200801f030b0b140000c091401440019941c107108070b101e240f5004002015580c526054000b040c041d10380b558400b20503020414556200718090384903003c404440b0401381d0361918281c500e40540d0161102244001d00180908269001d2203580b210104141e9030100c030b0b2113400250b8039641c01c0f0b80911110b2882806121000c103a4845100c030120600344100707590b1400c0511807240c00040c3c401007184401c0301209445a1098050b00c13001d140445090020b41c0040d01d0181d507403461346070305902540c0c46800290b095801031042100405007141d80c00c3c1c0c1048142480d40082a000304942da0001c424080b900c0070500320306c00d982c0300d40c0e036812200c0c881d03000e40c3c01005040c00c648010341c880c640c1050740d1480042d40c0407c0c1e0100702c2d0f0309100f869491 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 672469658 1250 672468408 672468421
    0x606040608010b092a0301121a0105061621090614094b18070f1b060c050a080a0605060405010e0621040b1e27010c02010218060405100305 61
    0x1c05d0a540d60030001401000100c0c0c002c800d0304209420510440000040b05840c2c0e0741058444401d218540d404a030900c881445c00e82c10304240c9c000340f4400d01c030b01c0045070007010139505030389402600a070010b01c3c100b10078015075030041c19201e04041905070841c01c10031403800142c0170b406140d030128007903c1c00040700d0b43d52100070300072200d01d44059840364402c104100da10345080f201e5114240d1140d200d400c801c2c0749000c20078170664028803455480760751040c0001c405a450040e00310300f0440c4400c240f4141000710341a4803c6984200b000da4800d50782c0d030720b002001085900003801c540e4489141040070019560390004880c110f900a00b4904030a070b0041000400c07901449007c407442c04407101d0005c4101654070101c1e403013070784246d000003496107541c0c1c2071002c030301d40140300d901d104000c600201301c140005042405107128008065698900300941701400d60b900089600b025031740228141d4143c0f41c90100300e2403100c1090f40c10301d091078502400164101181c004c90014591389402091a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 672470908 1250 672469658 672469711
    0x10e10090510020a17070e18060904080702031e0105040308180d0806030a08040902041d0903030708130203010f0902090c0c060a0f0e12120a02180906010207090e0606040608010b09 79
    0x280400800f01141c92410345006000c076007c10381a50303c03500102c1c26429120409446250181001401d10809030742c0300d07651022681d0021000380d9161242d800012041046008181c0d12508441300200c0d07241410315000c2c0803900040c114500480151a1000e01800001b81040c410765862805026a44840700400c0c24040200c0c006020305000090210f03800e02241c00030011035140c1124190704426040c15150448003d5403d900d02d03420410208400911940e041e03a08116403540914803410954006030840702d413011907041c22a00d03170501e402941b030700c445419071200404110314680942c2e0210300d611003000801840b40aa910106c16980d081c140e449029290691070459800303910200048180c1c1c1c111492014145072002d000400146950082e1085858102c84203542844c6030002c0110b4604024080e0341144a46080003035195164025031082400030f501401c22800c0c901c042c0000d03035155411110650f070411910324801d44a0050740c81e400440d140312204403040e101500700 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 672472158 1250 672470908 672470927
    0xc08070b0f032e3c0306091a0f06040c0e01020c1203090307030c15020c0604052106010f051c0b0f19050705031f0b04060507051e010e10090510020a 65
    0x10030b91803025000c0382d04c40c0e6854186444c20511034001c1d071003650780c4500b01400c203e42c1c0c00402400b041e400007000080c0043d0071249245d0b100c0d030b510000c48658041d11040307554048804541c0783c0c00910601c18203081a02c1801c08a211030f00d0000b4054000c03c0010b5628500b0281c001c0c05000d220001401c0c040050080c0e400d4640c00900380e070391890b44c900b0084e4803140e1a000c0d5019000f0b520300207041490001619000000d0080d1003e42003500d4402007088a881e00d1b548110040c7c8982400140b042d428010140a841ca14401e480110f04003c184481c000400340c043c802408a4443c2030041050740383c00b01d40c0b2100503101d0306030650350f900000181081009500d01c900d8240401d01007429080f00103144108041540481145100201001c0c0d80c2c1071442040c860b090200800d00c00f6600c2203000f80300541c02901100d940035281c1d18014103140401c81e050131030f650744210181c01100180264620852103110900907100703035464582e11490701e41801810039a0005211400b6400307080b028 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 672473408 1250 672472158 672472231
    0x23030a02030105040803040317090604110111070b0c07061419180e070f051e0d06050603090109020405011203081303110f1c030c0801090c020c0d0c08070b0f03 70
    0x9002c1130610f4075240015400540f0110041010780c48842c5100e0640e001e0544180241402800c1a4999440b24441d00c1c4640f44094100b010314003408003000d10404c1040010208640040d41d2240841f06507402c02e10141c01c28010050070b1204140f445007408143e69160160849074689205184410780d01192544040c9004c0b504242c40040c0e240440c41d1114800c61181c0c42c1c02e80f8010010303c08541c544958144402525424a2501440303140d140160480c00100440010700b50744441c00110550411514201e5982d1607540e100c046041a005181c0140b0109441c00304c101d0450b0f80c00340901d0401400d411880466810b02e03000d040c4548486110440c0000948202c400912001621100c3e07211050030b0420103802c031745918174407030320402e85400036503a03941c040b917400c0802080141400080c00002c510030300740e05030340c999108400c01084a2081c1040302005250050f180c0c01c00781c032035100960b110020301c4902c016001e0042242d511611100c00c5a0403010304070740807024600381c1c40f00d1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 672474658 1250 672473408 672473411
    0x4050f030c12070608061f0e03030d0e030306030c1203070f0c030206031303031a0d15020705030309030403030f03200c07090f020c0606100c03120e01020307090510020723030a020301 80
    0x1000c1458004158001591103c3e03075020f03040c0c1d84d00b001f072120141914503a500c98248900b120a41e0034455a85000d0581004040da40340100e038102e0074055803103545031040c441d0400000d02c072151504201c1007000150948024074a150485039998032402101e074090903800410202e8020004207243d01405554002c04130358036400d01022801c440c80c0409021000700e45002652107500341111114003e00728024200b41160035651350340440043c050b044d04040719028040b071000107800f80040c0d88246841c2000303644692460a00401c48031440e402c684c01d05142a6101900c440f00020005404022605c0c5907a500740142d451450506641e110360bd11b140780081103000441700f07400034098610302008450850312494200084101c0c20064600491000c28850740000d010b09091040400c44032800556011803c503140c1c01ea9000300c0e6403034002401958107225a103491300c400c101c0c144d0948000d003141820600d000118907000484a50150b009a5a9401079a0104005101d09078041e00 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 672475908 1250 672474658 672474679
    0x5060702010e07120317072c0f04060311010f1e030b360606190e0a0503011103060907090e0c0a082a090301060807090209042703080711030a1706030a0804050f030c 72
    0xa100c15440d5041c1c0c2041c0c0f144070272400c9400d20745820301600d41a6600300c0030300001c4034800001036500441c40308003c03043c00480b055014003980541d80c28008214561004200c0d030249008100c0341c108400b803000340b0711203e0b90f03030080200f40c529408008031080900f40c1400b6151600000c2c058081c00005900c203188203081501801c1c1d02140c0c150000c00d007075a001020b03513210703801c1609a03441120703181000c81c000d0001035481d14000d10b510760025034a0800c0c10156031981b400820381d41048500c0c14500c000010714101e272075408490b040e400000c002c0400800749601c02c0c5241c2d040d0240c0e0034076100800c041080340ea02c0c0d5080d8000001042500f0488550903950040840a034105050b8035104600e060b412030482516201c628582d1129a406d1501000b00740d9000d440c40ca4000c1c1107034081014240600e107800104000800c2051010789130341d00508115409004180300007440326005e5048102c60500203000358080c1c2c0e050f43e900301c1c0c8a9400c222010003284c03400d0b6a020b40310303900059110 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 672477158 1250 672475908 672475967
    0xf0201140a03060f061119110603090102190305130b06060d0e010b0f040908031305031218060a0b060a03091b2409060c0809040905060702010e0712031707 68
    0xa110304202c580c042d0103031400350390314082540c2d011b140014040d80c03034110700c0007031860022400300d1030b114511602100c0c4810000101065a41d0806c44414075a69400034000121241007101485401494503051050349000340c00020214030051009000180d09008a0300d150b4450003a2038018041d000208031603589003010034042c0584494490041c0c403400c100758080c0c201405103089081d04642c4052554868401201c100118108256903601050001400d0704210441d1035004c0d0404401d03407400c500c5600001030600c42c01401036040741d450304d00e0155a646441086d50074500d107504000404540c24209440070302000c40c58003c00da43e070350b000401c10045292400da600035502030030b000c920107a040295000d12060040d440480d820f00c0501c00002e45410060140c0c00f00070f000400c9071103003581c58628044044d107464000d40d4440148074810117081164400030108000750000d801000d4401618400003140700b0010b0724403800c00100c1c107074040c0721588180208072403840901c17501d00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 672478408 1250 672477158 672477161
    0x114130b0411030d0c0c1a030c0a11030f090910060207060c020d050f0f060c03060303040b07060b130209030d020718050601211406040b1e270604060b07030503040f0201140a03 77
    0xc40048070041d0290b0070100748240c0700d95907c8407060300c2018582c03450b1140c0ca821451a000b0080e50000c0120515030900881030a0000d041224414000103488500290030010314900c014a40c904040303039600100442d030750000b6800c007100d0b503600704405001e07a01d0000c40c0c1e503940f0504002e040c0c0e20605101d4005900d000850700140c0802e0f0042d00c0d55500c0d80c121000d81d80c4002d44071036626501c284010f000c002c41c80401401110300c82c1c0c0340000d2600c0c070384e00031841d00d50003c5050403245a002c2005c0040c0c1c00d040c000e5040ea0782051002c0d081d2700742401815038601c00c0910119258660b02d100045c00c80e40107441c10440000c5180f1106442d00c8091588000741615401d4020003521130305c0401c03410b04260250000211005002c0d80b501ea44141c0220341941020a0440d40000e03840c0030302000418403450070030034844404035146980751000a210554600f41e10020046100b0008080031035841000d503070f0001d5001e07000300a6040e40e800102c0c1c42c42501521542e50242c0012010101c0703826 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 672479658 1250 672478408 672478427
    0x171006020c0a080a030e04060801181b0b1204050109020909010b0f09070813230120070305070b090102121501020f06010f06080c1308070303020114130b0411030d 71
    0x1550071150340c58885401d1011006180c81602c110354003842c8003000080c09209082140d805c05000090f456039254101da00b0348800801c900b1140310064520824010349003c040003403200c409102c04400e00c0c000d1a105940700d5080d10302c9111204001050410600b0f401c030b0f6250316001000403016003000507003180201407000130f00d4428404080180814240707440c0440c8181426201c000701d681d9004900c48004c0c498a01c200d4437802032092881400c0a081c002c1c500655080c1e0001030b210100031140703880004020002e02e40c0c080107101520010750f001e0110341072280d00c580200c0749615205010b9001e40100b10301030701403140d1101000503003568140010105c010036800c0303c0009011450090302d960080c080c40d001e01e01c12207001c0c00014012200c80741c00006003803840b0f29181c642d1400e40070039000f50b001180f00f600551000c02c04d0590902403c03100c4010500e10390404d05010414409800c00d0381001002603500c8400203003441140707003501d00e00160190035070341180045100100801d84 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 672480908 1250 672479658 672479669
    0x60a0509042406050609060d0617071802040506090105070f0507090209030105162f070e010305070f080d030509101a01140909060108040807050a08120a090c0302010f1710 75
    0x2c80003445120041d40b400b550b012608060300852914880d9000d000381503000600d040c04083e100c0d4000039410503244d2076441000190000b50104a040c001c01d56254090382d400090036500611060003180d65031001c43d14628001d0038140d540b007400f0701c1d2074148030211100c05000342c06100400140c1c228142c0042c1015802100200f000340e90305007541c4c1524207121003e0001075602603083c0c1074980c000c0a9030440c0c000710401140310004407102245804000d41000096840401c01041008400c01c0114054403640b030100852500b4280d0030303136560204038015420140c0720f0002c964441c009110003048521640024080a40f0b544501048108420300060004070404000c0800c07000d07120039207030800c400601c2500140c942000465000358003600c1520380740420405032001030000c015103090103208500c01610303250403151040380c03410000d250000341402e10b0400320000e0254014141078a43c2402c0101c1c981c45440000c45854000300d01d03401c03103c10300f001400010b5501e828402c04482 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 672482014 1106 672480908 672480953
    0x30a0f02071406010515070210050409021308070602010212060402030603030c19030e0108090a03030e100603060e10060302030d11030d0606031a0306100e060a050904 73
    0x24031416084038004480c86031042e2004003801150300400c01110141640040c00f4490301407845a5a40284601d50818001003e103001c5c1042e28042c0a03a04411511003280700380781c0c09080c817103002e598114030610600055070391050007105c0d80d003580c0250442c50b6840382000d2101a400c09001c03030b0f0340b41c0014440d40003e00010040042c00e00c98203803202c9450002d606020385038141c554560350401000344100031660f00d002070b071612000e0341480c0c00201064040300319400e040c1c50b140c4080c00141440c500100380503d54000d002c0b000c880205451700402440e007134030200c420b80c0c400290503800003a6001c1501e0f000d2901ca11240d041c42095a26204131021033a045803920380088010030760310781c540c1c86404c050003d14141100f0a41c0285814201003005040715283d0344184140c40c0b92810000d01c5540b031300f120500040c8000b40041c513450078240b41600aa91441c5503951284c0c = true := by decide +kernel

theorem cover : BRFrame.Cov 672302158 672482014 := by
  have h0 := BRFrame.cov_init 672302158
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672302158 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 672302158 ≤ n) (h2 : n < 672482014) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
