-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1037
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:56:57.764278+00:00
-- url     : https://prove2.me/submissions/591e30cd-8271-401b-968e-607622e4ad9a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 186330935 ≤ n < 186510791 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 186332185 1250 186330935 186330941
    0xc0f11040608060f130201080c0a1206090b0406080c010f080c0c07062609031605030903010e012711040218040c0f02150f040605280507031a1e0f0310 66
    0x88110b15001046502d50140503450b9281172000207000c12200c0001500006280c1c024205240c9903080243e190702d20360001b2411a900b40c1c202d0103c0e1545d404c5503210a00b8248100300103010007400910500e201100083d02d1081c031507904030100500c402c0082c480b441e00105880621889004483d502e685030380e800340c4200360082c24540142100e0741c000d80942500c2e00920301560744d030800745141120103a000d00325030010801c1a102444208086402d0352000d2080c030b8100580200000303114040700445180c0448080c070446420f4041e90b0481001c20680d402e801c404120881300140c1c0c1704065001c003a81180d26a204a038054070f05020350500c6904141c032004030710581d40c00d07100c0034582c03038081206000c1c0568889034900c00d07001c00180054042d6208940050009800c0294000900010511800b100581c1c4146544410900400642500810400640d41c900e10103185031440046030006020341007000840407440c1010401c0d031074030307112a05904c001030305850807149ca440060001d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 186333435 1250 186332185 186332191
    0x40507030510020d0e0d0e120304030f0b0610050a020c0105090d02100815030f0a020405060301061701091505070512070306120602070c0e04080406030902031c08090d020d0c0f1104060806 82
    0x501d05102008241174400706001c1e0055089031504c911098a4000348140c0060045411071b69100800010000c603860342d051242d654030800d00d0b045145014002d1000c2c40340b00c00303110002d110303085c0503907942c2d181c020820b601c401c8000e20340035840300ca4450000d0810096000007940000c591003500070450303400950244141d612451a0406c2c103c0c41040c190345044006c00c500070745d01f00551076801444d00d81c000542100d001000490b01e5601c810742003440c03100703990418486a650b920032000304038581c1020204050070368400c00851400c500302034141e1242e20600100210b554002508443c007036440039019189513040350f41c145c0480e1a003440250711641c0c080d194104505000a00b5005070b140003441386a00c10030030350402e460003406601925000b04c007240e241c0200c1c490002c240d12444e01d000121002966414414184503400b10b04241c0100303074240c11500000d024003c0c030f0f0b80040440c0801a817110202901c410b0b0b41c20022144541c061001d0b03407080c2031160000c0ca100c0002040c40c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 186334685 1250 186333435 186333457
    0x20109020f09240a0b0406050703090f0e011716060f0305060303030c12040c05030a0308070806240a03020c0102040b0403050607110a0204050702030d0501301a04050703051002 77
    0x20581070008004036114103c5072091007168900400d6400008200030000f6454007405081e03081c0d448684041c515046a040440014004658202410380c411100c80003403817000310a02041c0e040c80c1c1c010b88071501c14003500300c0007224442e52588050042040f240c40d5807450424204180e1520340040100039002140b10001c0d0510f40172451510f804802c481c01041420f000b603180c800d81e122071721090280200700755455a0380c0280020192000e2002d00102882540c80029070710308024080c19101028060500a44120f5800d0355000e0700030882e200801008103440d5154414440100e01030300c00c1c075a04410650001c64001014003244001e4810303244140300781d800990324000e04440180c140b00d4100e006900c00c1054074094142940010340000307580c81540d182200421101040c0c41081c0c2c4188045ca00804a520300b04c0c035031007101c500d500c4403484040f080581b00c0d02c1c0d0440c1d0318648080d18101c84001c802240c10032404001800007190320071b0954140419a898040013500801d003034030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 186335935 1250 186334685 186334699
    0xc150c010c0908030304120210051302130b090631021b2103040c0914100b070201020615180405100506010302090603150f04110c010b0406120b07021c02010902 70
    0x240114002c00110081d6803a10b8000e5080d42c0e9075450740c116000b0030440f40c6040d8000d5007034185501c3c80c00e0180f140f18049256124900f4001c42c810311020404c480e4011102a140410030a03044e034070b03a441260050804c44884540301d035812104c00b852464085220104442014002d802c00c0e801d4014001c1754910300742c6050003121041a950310b460841c2c1c12649079181101c0e01a108407884005103401c030303000f1400b484955403119440c00c01c40e03155840707030249031400404200d0f400c041c00324440090030041e40908d0a002007940044d58801c00039103412aa1030f064080d5000c00d440b0709080e100405001e4000700607904080c1070268560052141550415061030006141c0354003d00843c0c50b0150042c12883c031310381e240b0003100300c120f2070340000a5011012600b140c0c00c0d50b659000780c440c3c803800c010040f940d606076000d20a00b1204403101890050b42481402c00070b048000010502d241c1d00010303041c955a0f2046030482c140030384a50840880c40c402190303d141950305600400040e80300703640746 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 186337185 1250 186335935 186335951
    0x6080c042319110403030c17040b0409020304110d03120b06030c0a030b150f04210507031401020c070609030201080906040b01140406050607030302090a090506150703020c150c01 78
    0x920091841081c14510351425501140040800c6005810754035000c140005140c0e861195086183e4001c0c1d02c141c0000d5025040d40f01481041640c0040d000e821020301c2e842d0a20700202c070404c82c052032040890310f560101c002418810401108040701c0c200070000346002041c0c0c1b401801014040480c0314103180303041c49030355641c1426400c0368090b01c1e8aa01450404032030031402c8000e0404541034541000071a440b0f50010441d5501a02d4807404160803907450f2400e291030390551781c1e44003400d055540445440e20703001c69004103183c42a02e03006503a4600210071b24408601912903410400c2c81d600c9000c0c8001143e9a01c04001c0050324400d136581d004907103a160360141d8a18080e6000341c194040d11b80100120301d0740d204007402444016001080940e07940b0006039607500542000d0740032a0300003030414800c0c6016049903000d04a04a0100038a041c5940818840030105218a0344100005002014180201703c8800c420800a1840d00408281400c1418541042d55201e21541c00c00c242 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 186338435 1250 186337185 186337211
    0x3020306130504050a0210050301140f18131b060305250305090a08040e06030c01110c090402040f0510030210030204061b170d09021807020a03030e01020d06080c04 72
    0x2200d0091a00415a007491191000360100405028004940d9481030210181c010f0301c030701c68500140c070342030344845459603d888403607604d4034101326005200f82c403a2070f143e0300c403503654803c609021240c2c4103d0103182da0701c035103165901c0740d4980d8014085c060130040417040001e00c00c2116080c0c90083d64107000342e44895840720142660400e003a0249080303041d8445046119600084d8050b49a000b2140c400f4019201d1280d540e00c540c10a5061704114000c01105040802a4200c400c00031320b04881e02401d6194010385401034051644e05c220030b8080403900b036585a82004c0030810102c1c1d0108070506000d09007005900091008901444103100f10140b0035009209682c1251240e860310306480d1140120940e240300d0f4000220707051001000c50400d40c1c031028000d85401502c982e0006181e010b103004028059443e5606e681c07062040c8020407090030380c0072803800c2d071450b818100490b5000211809a0190190ba001c2030b4945142480c0014000d00001c0c290500d4882a41c3c10051410051a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 186339685 1250 186338435 186338437
    0x50402030708130314070c152d030f0e060901060902042114030c061008070311010305070306030b15090c0f0a08100801060e06100e0108190b03030f07120302 69
    0x2000303808100910000f82c04522244100b410061080c03a01e525115a04403040300039810aa40c19250928041418440c032100fa11a00006421a04055002c6500d102c0140c0d03024180c1320002d03040c0303040c110040c803406000c3c0c0c011403140e80750359000740981c42030801490b541d48002c8505641d00c1d0309185002510220728400c0b01c042e10781158040140c2d40e03651480c1102000c01d090101c0340300003000400d2000b82001d0020f08205954080074088500300815142d502800390340103c880c60708a42c43c2040000d842561400100b002030a012a16640b01b22003900244290b60001c2c0815040c1c004101c43e83c0c010320701002d0b40c0c0100b201c491b0709a0b216011880c4075800b40030069040100304128101c8814080c208041d8859a8201800010b0741c4910000d401c0d20915808030084e103420600340b102510f0248510440d4943c240f51500400c804a030000702042000360031040701c20301c00001c02000700081d070441c60500c1d0001d82101d54813036001d90b092009a0059406444401021283c8400c0c0c80c4a40 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 186340935 1250 186339685 186339691
    0x20d090305071418010906030213110409050402030c1f140f09090c041203051e070203060c0904020d020c0c01030b01050c070605161a040507061107090c050f0708070c05040203 77
    0x34005120141c03c0481c0c00002000b031089040c1c2c06003d040078184c2441003a41603602070085c100c07001c01c159103076105104007200d444d485002c01c14102651841c0000301101038604455001d000031a2030b845600200e03040c511a1130300d01e030300304d40e45510800480000100c090300c4a682075985418085c60076584030b1407070003854018040c0820402079080c2c030b4688080c5582d008244030f84e140d4549550380307064902c0c1e0585034100324003242000c180048030344441313090b40300c0d5000c3c101800c1e460200164002a01d0ba8001030241140702c0000c251465640c480d5810390320030034040e1008540e00c9203020883c659801d540c0101e80c0c002414501d1180a40d4411000c0d01d2001d000440284245410a1001d030341c00d400a121107141c0d840d5101c2031201044e8650901001d28100c110303288400e041c00d0902608003091608000140f101c515603140203407a0014240040343c03071000c00005c1c1c500440e44201c3c0d151064056000d202c00010072200184100c0000401031244aa03441d09030b099500d10511060f40012 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 186342185 1250 186340935 186340943
    0x1050105070f060e01110c0a0303050615030601030f1d01050609100b0d23010311041d0d08040f0b010303080f070e012a0b070908010b0303160212070b0a03020307020d0903 75
    0x38400660001c2c1184d00803460000220002062801034820140c180350049144c1e00c100d98060301d42c210038180c06200c0c0641006064800c001c0200c1406220840c610015140d00d04241c4d6a8084102c580391a90091000038101c2c00d50044840551111501030003080d1036003440b65500c107000c620680c0702d410050007200d0070407601c5030401c1205a04400240354160420880300c2040c02c01444084040c441940a984075201000c041f41f0380009000071510140340140d80406003c450b041c441d4400070360110a00d03010324000403039a64a151400b851244180300402c0c60100c00700120401d9080803000340300d01d440380b400101581d00d060303003101c0c81801c2184007400b04d02c0102c410a928180b2480700020504c3c15850303146540c0f801e5882d510940001c43e042000611038140510260800b0301070440b01203c22401181081e80c074410842d401d1492180c001e218904010188105940031b100510040611001c0241c403403055090140c06588119070b4031005010f0004020090b80c00340382101c09890300 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 186343435 1250 186342185 186342203
    0x807053d0908010903050c0d0309050c0607020a2315040312052a03030907060207030b0105040203040c09050702030304110904050c010810080304080d02010c0804030c0f06110c150105010507 83
    0x86039489641011203419080308001540001044642090081e03229842c4607070380322a41c4130752403c042400c00a00b01000700415003408200c0c0049040080d0051034014222201c0d50340da03000c0d100240c0d10002a90010410045040c1518800c10000d0f501d0f550380d40302505d080c484020413940c1007200744100c1c00010020140d0090412403107200d8005010a5886103c00c180110b010710f148492a003a0301d0200361080e44000104201c0030320034030980008068500042c210319003581d90b48004000140601c600496001c00081c0610980b05d01a40040500d03000030440b60908180080d00c2e540201c5058800ca0a1b800360000c55040880c0d51501c1143c200740584401c0c11800011240c80d003000c2c2215004180d0f030440800d0040c0184000c09c000c1110000625181c0d24503100a030949090800340024402488c04010100c0e401142c151145a030140d607100903025103107049030040c41c034401402100725001c41c0c039180010001542c54a084120703403800c446680d0720401103070b42e88079000d001805001 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 186344685 1250 186343435 186343519
    0x18170313080a0e030604060911012105090a0f05070509010e07050d0b0f100509120d1b1a0106050909061203073504030b0a150303050a140301080705 65
    0x1074050301401a0070810f1400c2000c41114400003440c01505480c2610002ea4424922080204050034070350b0320102030070410040d00008103800e0402900d045220b08031511a00043c00807603050001841150340428410800303041c500f009565181c030ba0203403502621605002043d160200c198642c810002c990700d96180c124440c0310071010f0301d603020060340c01040b49080820281e5504191603008100c40d641c854440340303003004210154402d01015070306504031103682e00d00140e0062400364480e42c0b00c0c4148060462030714001601000e41800b0400c0d00f406c9d00008116158403000400e40e0380001c6811403440e4451000b00030068111400d281500d5000304210b0f0006548007120400701072040050801001c1180380580800e00390741184412031400182c00d1007088054010950007141c030300b10801881540801c103c480c80410f00001d41840800300e09040c203d8840c4001004801c1c52a29031512540c0d504291903032410180104d502c20300c541c1445840c229891070f040803018900030a80d025080f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 186345935 1250 186344685 186344693
    0x2100507020111030c0c040506100f1b240b0108010f14040209030102070819020f03090103020f090d11010e03060c040e0601090b0a170106020313030b071218170313 72
    0x26204600c2241803240c90442d41000803800c2c4042c01e50a501070300540507005000c0b040104039000248280e10890300c0307220b40c5101030b41c01100c204605107181040d00c00d11200010420044401070340c0181103400001d0400480c0e41c00a80b4015168070681702030290f255043c2c0150391a1809000e05076010b422882304211801e0640a05090004050001444d03d02d901c000300b400d80c1d00030201030780e074400000342031141c1d10400543c04c2c00170195072019000480c0c100c0c0e2060307141c2c4a0840a581003603004100c90366aa40024103c07001c404d4004c0c400b81c5040c0b80c51401d0320114646240b024041000c6a900c003a00e81030106417680326221101c0c09924003800c0104120307644a016043c43d042041012010030311f000b104e001400100416240c3c9141204100020741c00498140c0084085420900c0403c0c05100280300c45825694003030030002290b40c46d05e2040300d544c2c4041c2000b004581c104040446a01c1c1011040c0c0900c1f4010310130504050b85564a84040348070a44400d51150f25405140c0041 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 186347185 1250 186345935 186345937
    0x61d060307110f010504030810080d050a030e0f060405010c03060e01031704030507090b09070e010e01080411030304090e010b060a17151f111617070803030108060a060503030403021005 81
    0x78000341803806000c1d4030034010510300525004585440e81d580d038140030034035402401865120048512040600d4202079010341c84240103480720301840008950101c1c540d00940003108070300c80758400c440c04c106444800e00d581d1041690306a4055181c40b0654010602c00e001e600159007990b079202510f6440c0d40d66190415030410804a492582400003000040052040f0b400400385000081400300d10901000882c62010b481c1d9428048a100c0303881940e41c129110f5503402d402400e20198540e9241001e007440ca155045141d0305010011f00440d42005c642d1003c1e600c0003003079000704196403501c0306110307203031090504541c00301e0350401009007180501145a43e005440c008032b082c006418038046442030f5450b00c119000050044070310055180c0c00140149c03034400000c010030040001d10704182c142c21141c09141807101c81d0703104005401c41c04001c0c0c04000d01884040340c1e035940c5d550700300320b49840040d2004202c01d0b0500f50000740f140781c00016101038a40003040191480c4000406981e2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 186348435 1250 186347185 186347191
    0x1005090406020f0a1107050303040f0504150f1d090a030912031101020d0c02010b04200c031605030901020f03070503040b0a021009260304150506060706020d0b0a061d0603 75
    0x503400300001c00029040da0040d1403d032519468010f90405c1d103024043c1400401e0700828001e5000340810091862341c000b503882180d4007a42c0010383c03000c5206030009034031030b07903001140c540c04031280029645022106680c842d161000c28003905864140440d621480b00c1000500082e140000600414003510081079180b1b20a04240300580b080d407090b01d0076a00000c0b904079580d99900c5841821640a02440108903400c80d410880c0382038208803d110b80d0300444004900d8400481d070744942d110108200c506030b01d20600500b10002040c1303000340d529888410304a0060050350f00086078480000156000c80741d0020141d814603060040809039508440c10400440c414000d080c0b0610080c2c0c4101e40600707004210306101590540c050410300000300304e050391010b0041040002107085411414100116000081145e8581d00002201030240500c090925480060211076410b2554420390368840155061034500303544890039224000440b01100341d84241d081400c103039152400003194 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 186349685 1250 186348435 186348443
    0x5180f160507060c0903121b030e030c0d08040302041506020c0402160206030f070813030203071b1703190c0f060506150a02010b031b010c03180b0d050601031410050904 74
    0x8200000b41c1c595500b9140700c1c078900008510b000c00305006009400c480840d50010509040ea0705107468010351400c800d8022001d420010031941014150354180f00e00403034035200600038208400d842c201260994090b2100324480da01e0b04024460b2007032014a4034040ba001d54014003800d182c0c02042c00040d43c05400e45085015401c0a80001a91000059030040c5a0a04540668900b07003001429120307000e0800b04040103403281e28000240c0c000121a06181e102c542c80407000c4094224241070880c94020324001000701144003201c070350000c040c00603036881600641d03819103541411b4a14804100010700300c000c289081f5008182140c22040c3c1006004c0c1100c582c0384141c04202c0c0064011051000041c1d440c1d801d090810f2908100304044600081844103004100c02d0010b4500b042e04007006051040c0f190740c81c1c0c0d9031110740e0b011100500c10807a03c5540c5019880741c00000b020115981404249001180300e00d428102c0311701031084401045412416003000c00304501c01c60000d100316 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 186350935 1250 186349685 186349687
    0x5030c0403061b0306090627060819030f03140a09020f040e01140606030709060809010b03010207080d140411060d110a08060a08010e0303060f0d050708030405180f1605 74
    0x10001c0c072140714524504100d5040c910010f010201c1c014107584195009443d85420035109201c0251803068948140b249880700c1107006000c90442c0b0702038400c80d803104882d401258020a4401800c4202c07000451103030340e035680a10140c18082e012122042c44c00410600300200060054040340d00802480d0300080c0100826078003c0b00040039601000c012200316519103c0030341022114841d581e802c0001103601c1411071138a000700a00421003880390908100110003c510360f11400c0d8400811400058000d56030b80000d410304000c640e03c00e8508070603042c540300f204030204d04d1851040340125441041080860740e41010410160403c42c181d0751300b903568505641c0c3e060761100041c62074184039150000c40789000f8040040000c003907405140d01e0707410101107817070070203001c012290f000c1c0c13040350350910032828074022405000080800500512031200045144080000903108581c03084444c0c4100746422007510311148029108034403214403140114101040b0700c0c103514101d00d11841e020b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 186352185 1250 186350935 186350939
    0x10020703030e100609060506120708060d0515070f080402150a05040905090106030606050306090601031217040320010b0906090403030b10120c080124020f070f050f030a1205030c04 79
    0xca42032004160035128030310b076240c10800003402035006d8900100b03011111107080141d0711740d40298010000340f490b002c21020700c00203142c56a0740c811070001c050700704080b5112115840c4c800c081048060380da40c00800c920006001450703200c0c60500340b00313a03030141825074005109030040b06c41da0040508030301403210a11020501d01e1552241d01e118200050000c260503146007481811511030350000c41c001c0c0c10003001c00c280d405001407030a04582e440781039884003855515049400c40d4406800100844400d01404180350707018200503519403181c0414007829050040382822240110151500032402c0b0740002d270b09141c41c407012079000b03000c0e0038007090000070000055210712800300300401143e0200201d1506030050302c02c2550003c07a504000c0300c0d80d4106400b142c0140c09107101113680b0380c8481424620144244111401221660b007294041502d981100b0115080740c002c8a024180e0b12558245902e00001c11820403038000200007201181d101049480d0f0380b0007440102c22110070000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 186353435 1250 186352185 186352211
    0x601090522031e020304050f0901062c101d01020c2805030a0f11090606040320090703230f0f0901110f04030b060f06030a02071a010b04170105091002070303 69
    0x40c81000710440e13406150f580c0d00b02010401c040b0880c1c0d191038020413030140180312450704108600d00400d02209190709903824249441d02e0030449031845034024901009400840340c101100c601d036402030104104010b4441001242e642104654550344101c4d40000691200124082c2c011080810100c0c61081a141c10200e80b030507034003210481305408944496018412030b03080c503030342042044904440e40d04100002811600482c0805001d28281e0344085000100903414000c9115014000007190300e4204030150040540c03140314800207815240b456450320011001505c551010105042d0b6903d45000c1d01c41082001040d05406650300e001340000700d00e07050040c01080c2c0020782025a22415071038007080410000c0c0640d405840c481c91582d000b0703541d078400d9a600104554006132160b006090900a8440c2030300000d482c92041c03000410111104c9004006030b5004044c40c25105c504030051a080f0f5000311500540c40e0040d0b00c0b14800c0020355002044928000e10b8045000004101 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 186354685 1250 186353435 186353477
    0xe030607020f16050109031104090c0b0901020c060906070308090a08070602030105011e091802160b040627020603060a0e090606120a17160b011205060109052203 71
    0xc0010150744a2241c1124010040000000020110800d555018686070018003156810302006003a215401d1040d905a2603075480300c01560381011002186603074035058130035140e103c00304641c0140260552003035503007064811103160440c05010507203091fa8944040b80c812001074030816160007141590000300c1da521000d0700003280074040c01607036549000c0001d0250074a1410b40c6103d0021840c08403441900040e910048440c103030880c5c2480c802034500d80b402440340c05e0404842c01001c417500401d02c0100703203a01d8825803199038100b0a840c40741c0b03070310700509150144005034605508030074001400e00b1009590403c03000782c1760446850f1100100085154112280000b0364401420403585141141034100c0c468506005808604503d4881d041c13050a955141c2e42c400306c00148040414031640c015079080d0340c00c0b445100071075844048100d030180c00d900b000d86062280e40004252030340b607882484e0142d00a0b5030b804658484000c0071403400c1c000c80409506000411444c2d6440c40c03102d030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 186355935 1250 186354685 186354691
    0x30f060e0114100509010e0f07140f07030e030c04020306090711100603060c0801050103050c0a0503060f0402070503070c14100f021005010b0c0f0705010522031208090d022107030e0306 81
    0xc080c3c03100c0c0c142800d0502074413100503806000ca4200034030500a04444100d9000e401101c1c0707140000d280008441c414107a44110b900710024100c0000c2e4079001c0c1079100d5541825004101c0c01d89144c55400300030801030b03010980d2566402540180440c0c90310340100500100c1040e00c1d000c0d240d442c0340c0b41c0d080904460b25540181c1d8126129010101020345c00401310b40540001d0804105034100400302562034050b1f603c0ca4001d10070000f0200b13043d41c1c2c540107001d2024400410640d6200f405250003522900f00381c1040b50360980f54900416042c0006036441446280641020845041ca0b007089801c150121400300c1507001d61607044100c00c129000701c0c0d0180c001a03042c15074030343d81c95544a2801d101c0282c451842c2d0408142481103a034468100c1319820850f02100303185012882d82c4080c0012242d00c01402c1400f080548841d0a801403826841449004182e440e00c002d21282a81c44036500100000940324199440303c0d0701c403c0078081d100f201e002e0300d0611180894400400d103021019 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 186357185 1250 186355935 186355951
    0x207090e0d05270d0b070e090708130c030f082206050a03020703170103030e0315061e030709020c1605010309050607050d0f020c03030f090a050c040903030e0d030614030304030f060e0114 82
    0x2400400c00e0311b0340c0124483d10b0b54401511443d1640c501074000901110001d0480040c0500c1c90038003205000d44907400d0406160080e2107509648c0c45441d10310703020b500c0001d05c3c54140090300c0c07805c001d03060b030541e4010466020f03480385ea1820303840c0f00088000354040d00b0120144042d503480c1107506d511100c4c4140c0a580b0030384940344402c843d40c0805d840c011824000c9440500c4045c104001034645900c94681034aa00010581f1002c01c83c1c0040e040c070134503410102c90107201160b1580e2004002a0302c11131544d400c45194403d503262801102a26410750b405446a488030f130100c1c000034070800040c22241d0040d4400613004046103000c1c01a030741300b1903151165034004414481c601d10114001c5400c20b0940c1c1c010070221119903034140d1900001e00416224a584840c0c02d400d25010341c100d0380b51801c0f03060a4a594014486010b0000c100c0f901403d2290080510300c18024100042102c058036080310040107c80d600b5a1441c01820100c01c80507242e54aa0305034410340084e00d0411802050700b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 186358435 1250 186357185 186357203
    0x607150b010e060c1009020607020d03030b100302030103110d05010b150715090f14030d0e0a050f0f120c010207080301060908010b01050a0e01230a0207090e0d05270d 73
    0x35400145140c1ca4807402c0392088008204852003003c000a210110704080f240c042103146950000889070b024944000e0741150745400c0c05e904065155110701640d00c07007200e00307404030a8821070440c200d00007400000c15801042507181010b18160034007420300c40c8154000704413801c0384804210381e40c859445504038060b010452000700505010400c440b00282d4104010103101900c40d05400441028041c0400a00345004518004184100d03219101340820074001007200d250069510149040141c5070b078010b983e0509800030010410300c45440103d40103102505034101a1816903001c55510240713503500300200c02c009000f0402443c000c04041c0c03100302c0010314191480b0f09481c00420801d040103c00c0244811164002072002e403614000c0c80d051411060751811020501821081109114002705981c1c510603400078842046c2d0780c9000003400000030b404411035070762082006070b00c00b1810500c0341082c469000314080540780c0800300603454807000030011078109202a90b0940d00104 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 186359685 1250 186358435 186358451
    0x20a0905090112080403170d02030c040302010807031401060e0406030b090601080d0305190506060705060a0b01020c010c0c0902030c19020d0e0910140d0203160617011a09060715 78
    0x10702000c605004005000e5142c0d003852071552001c04600c9103002c02400540e426030035010f003100030810303600d0072500b8080866890900364003072000da41040c032040b0f0010344584005005c0920a0041451003a0540003580d8241d080140035500761071500b07900c2c1d80095036180c00101143c03000c41e0050056016202404255061030015810540c0032039028081c14100000d009840004990303500140d40392160001d61a19400e00003145445040809030081c8140400d001402c10168084244140c00341c00b2140028481001910441d501a801410040c0340c1c9008001280300d03a002954040c0a0b03c4071240b0b0016074094003062040e90f0a45080146e01c8000f120b06240c0d08250300442ca80c1048404104619011300607040315031150040640f48207100094140e00c0d203606001c0000c00e503008054a501702d0428501503603181c503d11447d000954a0a18040704451600540307061350141c1c50030681c50480c10040380090b80c0034865981c0c200703408000b94404076044810300d41e4064500b88010410007 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 186360935 1250 186359685 186359689
    0x912090b03010305120702010309020301020d0c091d04080d0b311a10030204080d1e0507020102031603021e0d03050604061203140f13170a0317090c0301020a0905 71
    0x41159046003400020400040c00032800c00a04142c01c1c07100d034000207680d00010b1004030090109a40005c0d003560001c21482c440002c40d401001d118056540c1d842c56590b540c461f140040340804224501552000f8040740c00708024000404024040c10702c0402d9640701c96001c0340c4200b030f040c000c0360600038008003000051500c0d4040b140000030301ca51f090240c0040302d10760028460581003102e10900444508031906070180d01910001d02c601c0043d035803200305081c005403d440400ca02220805030710110a00c02078081d20030780d030700c150f01a030007103044c8035542d0315620b82c400c104d900980640c0700d0109041c80480c9081c1141c40000b401e100a0002c0d245060380103010382e003014040c0c61003035050000510000c0840b8180001d43c64161070080c51500c00030000100714800c0e00b001d0180a1400a14440b07120740404022084603501e00900d6614240b00e8220381e01c0d0440844000c00040101065115400c0012030f0660004001000d40b50f0070080b40000034226884000500c02240c0b01c0c0c44200424 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 186362185 1250 186360935 186360947
    0x150e1c0c1814060108090f030c030c0114010e04080318071401030c021f09080d06060507030206010602072301110f0c0a0e2e030501060608060f01031407030e030c010912 74
    0x400c0c0c40c02e01c45100c90000225944500500e418104680e040000e01b8130300c82000200850000c5c1000d41e07a07200c00341003003284c0b00d038000c419051456007841c0d441000c061000000904a40e541518814161100c0d41c4144c071940c0301412144041d210380285031584a0140486402031a4000e03510a604030350b10005004c0c0c2c0d000c10040130540d00a146d51500c00d04d40d5046920100b14440d50008510f0550701d04000280140146d888140b85486804500c1d950004010000d240c065000c55559a0740c49000302d03a0741c2150b002c2e000101020401d0604000310806d4a6440e0354130504000034034540c6054014602914400c13405069445120409079504140084c40c0151402074584143d601c2d01040c0446100c902015601012a8004004c40300001d84861032000c1d507440760003400100d60b078500c020600d00064030642d04c24941c0e164012084c1d170091080f07455a2036815000c26880d620290281c0c01002c11441c0408140020410fa00f00a4000e21541c92858420341c01d0f007151001c005002403103 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 186363435 1250 186362185 186362219
    0x90513060b03010c020a060507051b06060114040f0501140f0d0902090108010c0219060612030807020106090207110d0507050d2108040503040306090c1206020c010e07150e1c0c 77
    0x7030b07403528010103584c03940800e01040c21034104c1404290343e125460121028450822050120500c1070307000b03011901c021400c0d40c0507160036070381d5508400c5d001c21110064490f40c80380d0902c1042401e810851940100d000c01d4180948802c100d0502c1044081d085169003c2405c500072607544003404411031520302611800f408092008101000020070042d517100003400d14000314031401d0341c1007820051290061009042c3c0c5402c1c20351044c103503250261024005480800140d4203100011070f9072142407090307030b580c1e981100c4030513418180c017810f00050090304101a94031b40203003800401d103074032420344400301b1030b12070f107800e22500081c0100102c2089002e03040b20704000c1c0510500001ca50000162015a60020000a07107894140752007100d145441d441215211100c5000300180125a8050304044598030000d204007940da07080140c4a407a6402100d240b0a80c0035500071609110740326005039444040c00205ca5102d0741c0741c4004842407502c0080701d004020b0202400707a0501c1240c1c4410b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 186364685 1250 186363435 186363439
    0x60c05070515091207020f04021b060a050f0402010c0c08030a05250201080c0313021509040b0f15130803040b270d03050a050702191e1802070c090513060b 68
    0x10043c10702104403a100e60241c072070100401008078460045d91745807000307848807000041085507038038240c80d0182002c00e4441e03411009401200005503242c00240a258420480d400e103c41440d641c0b64010f482440ea4404183c0700603410040109910100f00000d11141c8c500c1e0f1260341d1100010100c00c1140e005034080000419404032100c0300603608049016000300395001e2950b20f0ba80d841805070300385450703c20043d42c044501043e000c603c05040c0f00420004c0d100752414040c0405036001e0045600142c1d5200c4d81044101008408641d2448094540f60b000f1300c4d41041c200303075034050b8140b55410030342011070025800211014030760b80c03105545580c1002c0c0d01220840d41701c03020004082d80c40c4480c000d4140000003c028030058407039000c5944440e0700400c1003002240d588059100446280100c100921b802c018007581c6d606000d18010071101c0d40b102c1400007402c03200026010350420b10f8101c0340b08162803404202c404080c014503108400002400c50604004d0410340151030064251034 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 186365935 1250 186364685 186364723
    0x1b061f080c01030c0c150609060e07141e0403050102030106020601060f0905010e18041401050a0b0a17120c010e10090206030a0c110a06060e1e0117010207060c050705 73
    0x40c20100340c1c8450050242000162043c001200745d99500032410014a07041503c1404400841c407540184203541000c0801c01106844103101c0c503100307005130b510070086190621658051244503005044110107003031050300d104451501c041d140e40094204990b00e940100043c0000c3d036040050b1030051040d403818509a140c800d0303014266100c0c90051785e04100141c54001f6164131084007003000610b00d111001650f180606014000702e19102d06003d0720350a0001140a0f091540651101e50000070240180310345881503880c041d00c54102c0700130041c010403403801200c1003508090164103401000120310b1000e400303c003034207100384180e81e02c0c0340307610304494031000d40c17038075000d8030b070b00c109066400078080700194010399828034506500503440c443d1010346800c110154002804548200c0303200e90340c90f2a03144000090003e00000d2503480507030100100051615180004009950000010300d030000940b602020340d005e60200d800030410001d108020043e08104330f11042d00807441d28 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 186367185 1250 186365935 186365939
    0x3070b041532060d06230c1e1c090609020913030305010503160b03150406061805040209030303070503040624212003010b0402030a050f1305100504081b061f 69
    0x6561111352000203072070190b54280050200540c021041c880340380d4122002c0300b9250107104116284e01035a8880f503500742c000c266501d0b201034141a111410303210252012407041240d55100104084041a600301c0c1d2240758440242e1902c020b014001e4000b500f1017400d181e01030602400f541c5060740011f000b68048280948111084031440003620ba901000f9580e988490300e920076081d04100d0708a500a140020000d651500140300050b91035103140940d261960301c200b08400c80c020702140c030350150003c1000034009440f500045034000e1044a00040710522402107500d005164075868120440d940014041c0e40d001822400944904140d15076100d000781c2c1e66119680c01d010900c5c07502030004644810980d03002c0d0000e0032408400341045459161020b13808000d8101640c0307071013139a00100040703041402c6002c24803170300c55080f00c02800241d0a4228203001001c1c014002d1b286c2131001c0c4041540c2200b414100349200109400903e0741e414200c1401300c100345a600307448001d40202d002 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 186368435 1250 186367185 186367189
    0x6070c080304020d020102010e120c010b06070c0509060607062408060403020d21050408092b0b0c040905090d031d0c0d06060b040e0403170903070b04153206 69
    0x44a0b405641500c0c2d084500602d807005034050544042da0102d00d02035000c00c000c2004181c0060b00c3c000000b000244400c0700d559090040341d1083c0007001d42400c00700c07607060180c1e0400202003500440043d020a05e03101c95034683d04219845100345d1284ae11964100862017688d11842c14003428100c8040c124030300f040e607070180d910361416440c1d806010340d0216802c1200b0848603608411406d0b0318061141c1e00d071504e0b15006940c4520122441140146205066211141d50000601c24094080d01e22108144c0f200719050310b0090820074881c00800010403005080d002e01c9008526400044c002780d110000080c01780c0320015071b1200705441310704151039003801c0043c0c14440254161201c40702d0394090b04004014141540003180102e100040001e680c80c0318035549071040c1c0c0a030f9204102d0401101041011040544403000c45034130030700090010804001ca15030700725200341074241840404103100015101520109440d0304080000122415050842c0c4804a0041002d5500501d41000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 186369685 1250 186368435 186368437
    0x106050901051c050316050a0512040305070e090a02040e011a0616140102090301020c06090609010204030b01060e03070503060901061e06020303042015030106031a1e0d0f03030e06070c08 82
    0x1010107243c4116901841442020310456203041405040c10618075014203010383e8400328018121840e12650050094050540003500c0680b030781f010142000900e408601002c0071005426450703a400350110382401039507103100303924401a00d1000410b40c02c980040062842e08244069070250404001d2424400d0700040c8000c1c1b00e40c1c1c80f001440d140403030045224020700650026a415620004841ca10140000b4689104000440899039a031b81c1c0c0c0031441d400c0c4d008620008004014600c01070082d81c0c044d985021100300041c048034ac0706680c59000a151480988500b8502d0755501c2003403103441c07010111501411030354130b06840c176a8a003840003907603803200520107030801a2855008846031b007040140011083d000300702e43c1c117001c1003407200c0c21147e10a116842c0803900e46002208118000351219909080060012407a0940c2802d600180d00410b000c603036102040384600c400280010b084202c03654003035035001541420141c1605d140c41801742401c4240314240900b8400245480 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 186370935 1250 186369685 186369709
    0x7051003090804051302121e13021201060608010f140d06110423100e0a210c1203091703030403030f02070203030a0809010f0e120a05120109060305010605090105 71
    0xc940000e0a03182030404a80c24060344c0c001e01e5102c1c01d181c00a2100300384940141c110207082002101c0e2646410701c00065443c15141c0038400101014000303044508040035030845940082c08049008586503c10f608440b0f407500a42c1c00b1504100051028420030018607005c2d0102c1c0da40d008000343c4003c0000c4c8440344002c0001c00c0c03aa120b60002e00108125005e65000f00107038143e01c0620152070401e000001a0034440a00518080e403c174880c20748120000818883e0181201003924101200c030380c1c4100003014a1481c0d40c1540c0c120b030303000034015080c8074020101164031800903961071800a00c003280c26441440081c0000c404400700440201c120380d01710390702d0700f40043d00110040402010f4002e004010303505000100703030440c107a6084018548510013201c02040200c401c01028030403500c0303620303244041d41d00004050540340030f070388000e100f00ca4040c00c050381400603002e2213082010007600007514107916002c0c2041040024020f00c0c0240000701ca055000350304000c08259105403203 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 186372185 1250 186370935 186370937
    0x3020d140a230408030a051c06030b0601110c181501050403050601140a030c06050307030e1209060c07050a06050705010509030a05090409020409020301060f030c0807050102030921031c0b03070510 86
    0x2218002d00060103640c02c0f200104060015a900e40c8483e031005070032a00550b403012102820060400c918031110320503082681d0340003690142c66100c038401100d20100f00d0410000314461030110012b940d8520074220301444011071003070310501d84800d00180b260000350b045410300005010034000a100410b44605545449108800c0760b00c0b110002000071146600250140e411010003040c4585d00c103008510400c00d513281841929101c9070380380d43d181c03613030805044540c40c240501c1d985441e1420050042d00c41020803980069114170004210072a0b83c1d01a8003c1a000540341c0100802030007a0fa0303010f0407a1b400ba6003010703128400541288038401c0960702c559504e07440c4d10f04548e40c9901ca4a509038000e0000c010b040e0301ca50740b0080f02503803804161002c8203191700000c1c0080c4009100e81c150341c03040e40558201111038040c000c1a1a03018101c0c1c55034100c09800d0900c01c41c1c10805000c0c101003900d1a420081c0105590004850502c10320600035000810140102c0e110301e101e00401ca20b413 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 186373435 1250 186372185 186372227
    0x507170702071a030609090c01120209040204080d090303020f0f070302060304020607060c110c0d0f020d08070f24051b0a0905030105090309040b011b020409020d0b0403020d140a 78
    0xd414000c90802c4000d41008403196a00403410b000f035505100070b1031040c0003d4603c040f0355100c0c4d40c0704036a2000c03688060f50002e03154205c000503080f10768016000c0000054009814075840383c44803070400580303102140005801103800c105142e410000000070421036806018000d172088103a5442e0361041c00048c1c040c00000000c0303011074a484003201c41d86504500c0820008100800080101d40312070b950403024032031000e03124524a0300d4801000899800309202100b10803a9092084007a04101e0903200440144031000100f00d803055030f180e50350702c22001030140905c81900e80b8411040d0703440e400c8481340741008000e1141c50a0302e4034000001425030040c0c80d02c403a41c904440092040d009603401d9400c0906001c1000000009880207034012503003405548040c5004449a220040489207203034110140c0303a0240c1050303840100440e0024118462003070407070b1220000f03040c0c1503038100c0c01031703019100c1d002c0100ea006d90041c00595030030380300c0ea1502e000810020001c80048501c0c1c070000007 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 186374685 1250 186373435 186373441
    0x1e0b010501051e030906010614040605030a0e0109051603060510081b130c18090e1c030b0d110406080106050f120f0d0207090b03011e0209010e090a060810050717 71
    0x50722160104090781206642d0f1389040000340391240703820710074800400e50021030700c0401c0c1080c5081d4ad080d104165201811540e40b03003140d50182c9440c02512001e0755880c0000c40c04604207100803c900b5038030b1200200305a103186407080480d107004011000d0103010500500400030003091010f1720141001146c0440204070001480603650000075421191402d022740c0710b0240c109080031003164221038000380180c0c0e1060040c4c00e860303400c01c05403070b60b801481f00e10480940459400c1225601ca260001c0c3d50040400810f030321a41108098441e0000c6a901d920703180307440d00a11020340001c10081c425185000301140300481d210510b2442400b40e0b00c044202c0407010400f03240d0290400c0200e81e1601c81c8000041d403180610300a88102c282041022011400c0502800041c10140055100480441e241d400c000750031088241e8100000c440c5c900845694150200d40208201e20300040c07518540143c05180581d0300301000890740c10141000f8110380c11011190325440000032070111071b5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 186375935 1250 186374685 186374707
    0xe0606130504051f0609091b021e0a0b150f040b0a05040b04020c030d0b030d0804030504050904110901030606061d0904080c1e0307020901141f0509040e03071e0b01050105 75
    0x20011441104d800d0030344d52400a1241c0d84568590b00300c420f9140304206908040303c0000882e4480c401c204050f81c092080f40340c05411010b01c44c9200b81e10301d016114100010782d00c01038000c0042c0d9800c060700d50100c00301c060a160080d0703510038078081150100040007042c0040784561036684110f0740b24541d10200e01105844940403240d90fa2002419265118144c030b4800c0d00400c01c21190034001d10032051010445400340103a01d0040350591a00c500713052610301004803909000700200d6070000700d03c04001705500c5120f5058040c1d8803030b00b008a01c66041100003405010b140410091140c1201d901c85501d40701c0c1218660070642042c4103a698418010081d40340035442440a8840c2e03590100000c01e004c8084042d1582c41c0c42245c01d410181d81c0e415206c0c25030b40000300250340c001c024030503401030344c440c1280980030044142000c074288041400040c044864201d6680403680000501804010181d281c0400c2840c0284040000c00304a451b000da960b8814000e01c0e06106001a6085801d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 186377185 1250 186375935 186375961
    0x70501021314091e1b0d09061404030801030f11040516030c1416051204120218070f120b0d031205010f0f06051c020705030a03051602250f0f0e060613050405 69
    0x1200e45924040d41d94186c1250b00c4014010740d81c06941aa150070900c1443c0c1e02c0c1011450300070750300742c1e64801d2030b0703401c5032290741100580c40403c880762804482c007083e85031103500a16110310603002c0e0050300300e6010715000c3c0a841600b0422004c0280074246080e0308401c1c0707000d41c0c0c2a0300c4268a10784624485140062403c250026030341e110b03200114000540c801c405096201039842681e00d6200d103001c0e0030411603900c40c01d560f240003003a088201e0455041c81807403201c01c4000c0c1448040390814040b00403403103040b40c0060a80026074020792507043e54219000c0c0c54010002d88152200080ca0045586400c01369030145408000c1e002803035190703001d45542d080c0070303c00f24903404540e00e440c5450a00d03134a512805d07202021900700400940003100d01c0c2c1d00903450b500e40d600648000d104030b03c0f07240e000f0210429615000e51980304d0104408030211152030103050000861301e405424407a8078900d0010003400c00c1d1089030304006201d82c0c0015000c4117000c48001307581c0403510341c4400609001e0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 186378435 1250 186377185 186377221
    0xb040c0803190e0f01050d1e06060c0309080a05030304080309030f030a0b1c0206030105040f0603050f030a020f07050d0b2a1c0207080a14070501021314091e 69
    0xd00d1101141e82000310866114081d400c00070ba85510b401c00101c4010301610040c41e03c002c0d40440c00078448002801000d4000700c100a884058085000079280c070600c1c02c40341c25402110004941215181c10540c002401c1009010b10764000c100305081603603595a0380c440140b0007050b00c2c0000c400b00701d0b01c090800544048002c15242c040e128a84450082c0c020940e00107402d1085001e1580702d020320648071078402c0200d030082d207107629581c02c01050101401c103000d12040d01c0d9075034441c008040b403428407550390604c424001441c2d68640c1c1200c002c2c50f094008142c001035420200d0100416640c22003a50381d095440040c040c2c2c0b40d580c4c080907900700c4231002e41d000d80020601c4e0b00c9100e684109001404012240c20a00039440921100c56040340507031b503001001c2410410440c0002402685041e4801c030000110703030b140c0384455403540d080e6000501a0030451000520510a15040d05001a81d00b03000b5035043ea610700d04855403215030080d040a10402c2400c442c0400c041d0800301a40c5c500c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 186379685 1250 186378435 186378449
    0xe0f0406090f060c020606010311030702060103030518060403260c0318150d061509181109060c0c130b1806010207050d03170a14010e070314011d070f0c0b040c 70
    0x418520113103806501c42074100c0c0c81d80d000900e000c401c800010441000c2d64001d1046a00604490303013103039016a480d51003050510400110b5a201c0191341e030380d0900070310255119002d81e403101d21146043d00308803070301e80f0441d2940710014000d13031000c80c07400400d842100001081d00030b008000304010880702209425840701203040083c1403d4400c0b426084242280c0000c00c10601c96600601d04a500142034082c0c080c3c804160401c0c003910703c200e500003042c800c059040c220b01d01a00040000ca4944c0440c0c609411504a1072052546160042c6903d0b039140c0c2a04007403080244000c005007090080c1e031005800300d0305400104580c0e906c20490702d0081c1802a200104513140d504025100c464003004071b003106010034001481114240c0075000c58030070600311034000c1e6400d09491064000c0000c1c86503040654905c1741c0199024100d6265009200d640030407442c5203025808a054810000c2c4180d05015600c1d090081140e03000d01e54003030b85a00301c02d00e51001d49541c5080821141300d0743c0152 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 186380935 1250 186379685 186379691
    0xb060a12050a0c0f210c05061308150708061201090204020f090a050a0815090f0d050904140f060f04110403050c270609150d060203100e0f0406090f06 66
    0x1808000c40042d49800850040d0000b001650f034940100c405040c4500580703485054203031040703000303110301400104010f00c2030051120341a11b5402090840e00b00c1080c25142003821201001004014401e280d500038040d22a9480c51804800c080d208140281c0720f1402644098207c0c04056003c0d03201c000c80c02e500400965440d0b543c54041d00854211200c0644280a003440c002510714029400c1c000f110f031904040c003c5840958100d2200403c0200001c5050064035185854158107014603801007003280c945030344508030720051200710780b80108410220b10080f010300100c2002d015685900c501c04803185520b042c030643c080b41c0580070f9105400307421040460040204040030448a00481042d1081c01c0038410f90241503079418a490a000010b001ca14081801d5040c0454281e0b130000401caa152000c0c0546000300e2104003e081e0103440855010052041e20095445030100810021900383c1460410070309248110402a000034074243e6580350700400c102c25412081421074000be020 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 186382185 1250 186380935 186380969
    0xc03040611010f11180607020d2904030f1407051203100302150d05130b040f0c0b0d060e06030a080f0a0e030601080a211d0310020c071a03130b060a 65
    0x181138150090400c0720071510520390300341d1850400380191009260018441100c85134191a1030100c102042c02000d000d0300300425991a0721598030400380942d101e1703901c5c90400b02c81e18000030b01c1d000a82001c0400103004000000100d24009502c42080d1384000002e6920780791450350112400c10350748001d4120288106441c485440a40900a1071001003030500c0319a5489503458a001340aa030020a201503407070214012500310140070242d6441051001c02319610303217007203502580101c0c810b40e1a10740c031428144101e000c01d80b02280c001d035060300209584500365a42c04482e0054402444c0d4180b0301240e04011280301d06003090201c4405015119a5610303204400d0300e0b038001c40404d88090b00d903100c10b660400a18544018072020701e581e11115445040034064104000200e2154180300d00c08501c248074810388000d00a140c1810b000f04000c0f0700d08400480c002101a03038580404205004210103105021a1040110352085e04e00c4080d6031603d0006000481c541c202403251040c1d81c0030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 186383435 1250 186382185 186382211
    0x1315240605040305010501081906020a050717031e010602030706201323090105040b0d12020c090906040c05131103010603091a060a051909150f09020c03040611010f 72
    0x80050b02d004d00003e2001d0380c1c0310b00341ea6079100c01380c807101422401240040e0010403500c0c0d010f401c810441d460594a4140b10b51100c2c02944000c50011852020010600010701048010f144501d60314038800a403035850030602a4407401200e8025002c070b9201c407401c081c3c00b04032402010113892001603803612046a00c2c80c0c1d5400c642035010300c1208110045805800f0325441c1011806148000e2000002d80e0800b8180000341c100c504059800000464041c800200040c0c054540001562700070f0103640d1401d0304206c40401c020b400078042ea0021802e100201e07a60803030300c90594009031800c181010711850701c4001400b2000b11901e41c0003001c0000316050b40e058000e64642030040d20b8400e030001c221148006c00301d10654200c0e0707110502d00c2d030401450500210f49207808040d21101c4140c280da170f400e86e02c1030300c0c6802000d080c4403401c100f003030000e80300d00c600c0c030400790116400460411b507581d400326035288164001c00086c40501d01130045200c409420001d52000300c4801400301c000c0b5294 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 186384685 1250 186383435 186383437
    0x3150509180f03030603030901031806110a09060e060703080606070507140f04021303110d0204140a050903070c0b0d020c10090210050a1b020d08030f040b1315240605 73
    0x10550015000c1e91402c2d103a0b02d1400002e0380c2c000d80004003d10b21b01800880150700030030184000343c6610a101005d400425130501c2030b1310760f4103010364a256039480c01c444010010081d54100320240805081e824025803960070607520000d6050524440e01c0d00d40000086050094050040681c8140300c80807808410703c90460760340c50001d55030040c0c1565020104000da00807284141c50101066504002103070b014000300000b01000b505107034081a541d008101914a0b8201d050302200c01c107004c3c450380031180c2c813500e913124030780002a508001f1160f440c00f8001c00300b0310074404164000724510018400d940c0c110707a9106002012584111040d03c030401c00b034600703800d040c3d01c54000b0025000e5041d00030070031500203c4060f81c6000c115529078880740041001c041b001e980100007008003a0018520b480114024001902800114542460704140050004045d0340d45181940c824000280e08a40c0050040c0a0880041182c003414104c40344410f0302143d0080c1c503051000400035403203070464 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 186385935 1250 186384685 186384721
    0x4060206070801081c030e030c01020903070f030807082224020d020d050c070503160906150f0f27030b0a0b010c0201050c0304150302030f2503150509 66
    0x1400380e44040c0d41e40c100030382c2d01203824421074040707801040024104803100800c0800b2601c0398100010038007070051110f817450300682e924500070380d8000751007001751a0410845001303107024034458000c1400c540d500c086da4010201d00030124580410001e4228090041000e42c1d420850418418240d840e21a102c13501c03900046c04410200024040e14070f648003003030b0181b805a89030001c01d02c3c00414002104d03140d105104140060045090100701540e05004040703803012802c44403803400d03040c0b4034448121a8103a000103078004620a4840649401c650814540680d5090191400381c0c1c0781015140d0190013120416030b00c0900310441141d400704041001541d0041d6000841039580c1e5283c00202c4a800301e11a01040d95404c2c3c50005611031002014003000010503a410b0587e28800c404060b50032a400c03501183c1c0100400400700081c0d95a541c0c40005909c51500300102c0880040c1c8000005200d0000c25445250302180e03410703101c0e0404020400900350701803c1c9040591880800520 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 186387185 1250 186385935 186385937
    0xd0212010513090201050301050d1e060c08070f0210050403170a05090114010e0f0915010b03061c1a0a020c07150806180a091a040f060b01030903080105040e0f120406 73
    0x300702e416404007440c441c403515164103845052840c3d0814081082c94220150100c0b1407000c800089207480354100043c9449600c038510101e0555401400981595401840e8804001070ba00c01e16580d2540002d5490440d5002d00340000d091b11241400c40354403548070030b844001d213a54420300c41c0c04000f6074006446009420000c01038038440b150350a00d503040c284105201d803840c140210b40c18110240c00640c1108403441110341007150850010340b504000d90095100d40400710801c000d600300b0800c030031400c55405e078003000d201e103581d80c0e10250a0b100d1040450480710f0040042d401600503030464004604042c00c40e140d071079481610b07100920a8000f0000040d0f08000030503941d007070840407104040080b000039002559403141d80030060401101c15610015001c1031604046c0740b032482c00703000b40c0c010041d0011408050270700c8019034003220700f400c4c10076103482809008030b580000da00e415650101ea010400145903c5210720b48140513000e400d0b940a450031620f00e81003020028002c0341c0013 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 186388435 1250 186387185 186387199
    0x60405010c0c050a150e060f07140732030d0b15030f0406050601031803120501080d0c1407080607080117030405011e03110f0433080703020d02120105 66
    0x9801080b01e4036001c49100030041d07070207586001300081e004101641440d602500c0041c20036483d00c41d46241400640c0c0c030090003580a42848040707580090b00c241403407001c160181c60045140e07581e40c004101c0400045029005a40031080310b040e01060030344c2010307618226234544400c2100d170745c0244150950141f10307140001c1114032850b205010f4070b10511090a926035255100c3e104c0c40060134005040300d0415944841e01c0c600141c541d520302000b64020713920035425918104000007280d4042c1c103c007440342d201119503512690700c40c0c01c091206074002d01401040180c01d000510700312094100415601a40b010051842d0303101c481c1604940c0030404800e01c07880d81e0719409480b0f02c21806010b000450f24180c40c01c04802c0b041d021a625442c901e1300203440040000c4100180e042481207283c02c61001a0400c65400118044000e503500201c050b1803070641f0360701480341d0348081c6052070300b449450000100310600940c1590100160170105540c0c4050460b100c19012009000c2c00c0d1150394 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 186389685 1250 186388435 186388451
    0x30106050421050a02010804030c0606060e210601052709031c02040b07110d060c020d0e010801050901050103090c08060106050d0608030901120e01061e05040b0303190509010e100206040501 83
    0x4940e000b440c0442d030094040d00d101c025680044801100007032046d02400484941c1c480081c07002c1c4502c41c000c0201d5659244051141c80c02c1014680c0c1106408810704428186846d03504404211927045581c1291002441200203103000320700c1041c04038031141500a8002c020308281d000c002403040400c5000c880c0002d41c101c0c5943d0f400ca010346d010f101c80c650390610840c000210302110f0085c00481c02000c1241f40320490f6a81d005495004040c440160001d9524901f00c40c2c10140c070540301942402d00c00340640c10580800c50f030600c144500c504254031000d00b24107201090f900000a444032078192010ba40c1c4400000c0c210350b010103018010340f0326015000a540d4030200070344a0442e016900c10300303552041a0b516000c4c141c1400c064105550310b03440091203c1d48580c01d160140200c00c200608645400100011104000c040a000780c10800c00b03081c80305416070300c403600c003201c41c20055107407079400004030f89411540000316003281500007030680294002410b80d120b144141e00a0000318 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 186390935 1250 186389685 186389729
    0x150303070c05040903050c0a0f02040e030702280312050c060117030d0908040510030603050607080402100c21030906050702071406031f0b1b120301060e01020703080301060504 77
    0x11090440141074031070074100030b10a91400340c01030f02c20390b8006c2c644103060110700700d0b03101d0404032110b5040300c040001207902001c604081c0101c13000703101800c01450401c2802d8001c40d608401c4c1e40744101500d1a450481c50400b0907201010020303640100006011011106010f4140d40c07040945e02d4151089100010301d4640c24024290041011809035003441c540c9210794025142d0314400300c40e4950300f400007088a4584282101d142041c580d00410f33414503506040d4103104014244000304250306c1c1c10407005d84c07070342d1002404c0300d5054540384001c131043c0e040c1074042c0b01202e815203507808924000c0c000a181d040d044600e0140c0209402c0210740c80e040d034180d90b01c05051251440017941e103411350019207868000385612220402684031100003001240340283c68503081810b41d58404100d15001c031110b842c90b00032110591009044044021105203050302051050008105050b9180d000130b91090000e20300030740e0f0140c0b503952a07503142c0e00054400c0e00540100d00c8044071309020342c0313905 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 186392185 1250 186390935 186390937
    0x60509070e220807030903060e070f09090507030209040f080d0b180105150f0c0d03140a020901050f0904180309090c0212030f061f030f1103160f030b0603010905150303 74
    0x448144154004180042d644200654001303050907414480c85010000102d2014040c0c035101160002c00780003440e080c500000c0804400340c0201036a0ba203003030354030000520000b0707030f01080e41d030101d4030407007156546c0ca8200b031001194000103040307490120300c02d842c0b86665009480700840485201d505101041007440724a8424071556034844a01c00000c0c1c204d143c00030051000d1403c01209524101c10040c26500e459580b07001c0d280001d80c2c0e9400d074070b600c0304c0d08900940c00c0301403140154030301080b480000341a030103000004001c01c6030000e00d1450a0f901c41c3e10400d11954418603015514a540c00c001c2d010a00c10321500f00c00905017144410140c1c0302040301d59064416403071060650710b40c10070082050400510854102111440040005245141c103c0b92070415541c0842c030407006141c40d8003511110101e0b440142410700600c8040854081306003502910780c6004a85500f903400101c005d4206503401d180c10000c008004540c00324180c10407449418040030b600c030804407490034146c4d0703 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 186393435 1250 186392185 186392221
    0x421030905100201020d110c01060f0b070201030b0604080109030305090f07050603151206010803131203020a020411040b0d09050c1005121504021902120f0d09020409060509070e 78
    0x48680c00280601c2c0780440c80407074050400d200043c1461142c501100c11030322030840d41c0c40003e40108018015030f1003401a0301c0942401c03404034400a252650042c0c2038003a609000303061644607002174465844940030703580204030280c000c0c00200d005080c0a00146004d0b20410004c0c000c0d00940702d1240070000b02d200807100040d240340c1c41c1d41d03035040b10021000c6a4240c4503a0105840d40b0807402e481040000c07501814501d009142e413504c0c004d00403003003151944e10402d501c21103205074001103600480d150140c5a0155070201d40500b000b40500520321480d0042c2c1e00031800443c184036803499a50100342c4243c45542110b2401c207100703081042d07086501407103600103082007210103120118035862070741180d5024415000d08807004001004ea03004074014680d48030105007a4043d03c1e038108180c901400e90090030b0383ca04100c02500e03100d01e216510800e49010386820030b02c821511144c0c010300c0c810303410040800040c00c00452107a1101039910503604010301c00d07004208040740f041c1191217 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 186394685 1250 186393435 186393437
    0xf050c0919210c09020a020d020c0a050d0204020c0c101d0301090b041e05120a0f08041203020a05070c09020301051008090606090c0702090907080d0915032007050102042103 76
    0x36041503001c0302c1410100c1d5507400c50311031040c0c08001134040d2081c0013908603e0b50b5900500251071506138024500406808050f1040100f401b0800c10740d02d9408070b010300240c06071400f690b0b41c0e00511030a494000c0e074050068000360840724003440154000e14030825201002d04120780e1046080426003071301c0005034081d103800240f4010400140ca2a20303048600ea00c04081e412142d0700680b251400c0440d10f0358a24081080080c0c0c418402d5480319084002e80c000c1d0920002e103040c5901e5503840e8400710310115040c03540c0011205695405032080d140195030104512a89039181d0f0b400b0340103500288111750141035550041e220240c000c03070041e84241c038550f0007001300355a104100181d19101901c219071003c010401d440141e151080c1c4184204c501c0c06c000d00341d688c41c4c58926071411f0340c030440140401000c1e42051044a4080c603030030014a00c00d10340823905d542c01c00340801050719001071180301200001070000030400190050801c5802c031224091041c40c100940740580208580010 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 186395935 1250 186394685 186394709
    0x61202121303021203010902030a0b03030a14160212010e070f0602300304050d0801050d050601051512100519080d030504032a1401090c180f050c0919 66
    0x80c91421810740100d0020340644100c1c3c4040031384a01007682503000b0703000b482c440c980000800c0410031040c003420540e50000d800440c80d081400130014040d94408080c103003940c05c001031081c90304000c0305000700125002401d80c01c5a60070024064004c00d441200300034a806000c400003603824640241100300c85a42c0c024000130860404501c2c0100d041c50b00a100d070214200da0091441d42440c06584180c1c030031001060910503800000e445600142d0000d8418400d2014030000640003103500c3e41107030800d680c0d00d036420341c080000308054010203540d91020356849040142d200d46003070100d0100c1e0000d482d014603030b95030642e25103805c000364015a013040e44080c089011040c42544101e510902030328010300940c070309090780d00c00c520242100e100c3c100c8000028409101071811403044810584000700110211903486408110b518803407500b0b800d010310351404503420580c101c81001614418100700324030f41642c007800c0c00d4000750b85050007603a00d1540c0050403803090300c0710300030340368008010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 186397185 1250 186395935 186395941
    0x60603110a080c0d0e0d0809070b070b0907030519110d0f0b06210d032403080714060f071707050d090c0308070b04140303011404111b0706120212 64
    0x956070710801404410f00c0000030004c058000c0c1d080d114507610480c20801034a0b90701c1101c0710082c646040546040419040604200500400041220106544212121100d0380d42804050501d02280c3c0003070070b00e02800b40000d000c0f0304103035041070405125044052a04900c0001e0112034604c8010050000800482100126566040c055030103200103000352290381c546c1c0807000b01c0e1003046c44032401030341c030044541036195094001c6170406000c9400801d4400d140710007c02070010b0510028003800c20019405d42481040c14074080107000660890300c47e0705180011121007a000c84901d80024020f1071456400c0e4482d075a0180588216a50781e400c3c04200030309c1e000241540c035000c491881401c080040000c06203005000018040c2c1da42900030700c0c0905022035144a00d54015030720f5042000188a055a02c00c8900d00a6409072400070321810a060161903a00c40c8a1503410031600c0d22020301d04400c40042d0039026604d0319514000c0d04001c0440e240164000c13140400000c2441d1800 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 186398435 1250 186397185 186397187
    0x3030606030c03180a0c14040b03100e1603080307030518060109180f0b010f05060f040e04030909020d0608010b120c0909070315050402040b010c03020c1e0a06030b04060603110a 78
    0x1660700f0100314013658000c0c1c1d100c5481d45182000018003154402c801d010708010614084020501c02e00040c2c2d4140708114002000a8503040900d62010803240d81d0300201c2c420001c20042d402251822102c581e01c02600c2e030814103201d400440319000024103240011705281d080c0007001d4074101d80c000090500d0390901c03108002504420301c10506074100d4901c0200440d0401180001d5903000b02880d50003541040543c503020013070f6421940c01032404006003a5101a40021a0f04403201814110b21030345503841e048820003125402404000d0003c50f45600f50185688448210b400c408000c1004820b404103100c520010386640c1c0c480d64200007102e03c15030a00d46025903200500720152400161a56900c1d4030040231100d071b9034034a130755035800c000450505201c1d020143c4801d00300701c032201c0020f540c000d41d1580400002070060f094040c0088003d403058002c443c00d094005e10769040c568a030345000b00100b210082c4240b05030304145000840720f000f4030950800a142c540450b182c8080588 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 186399685 1250 186398435 186398437
    0x4031a070e030a08031b07020303220f080c090a0515010509060c0f060403020d140409091523061801050d0323120915241801030506010803030606030c 66
    0x16500911044140d08522541c061061060340c82c03240c107005880c0d040c401011b801411606010b444890010040c0c003003d0b0b58008140e03000803004035800d0500ea40c2001c0608625a5070383c0c03002501007501203001c00d00d00c0001c0341d500d408910958040c40143e661000707900079038034190f0700945845141840300304694800d000074600343c0b1014094501d002d031641c00003458124164200805074000c2c40c20703c0101641800b0f02d1800740260302d8400c02403403003000345078802e10491240902180e5922108020443c002203012a0555400f00c100441942d028103400701d204ca030001c0302c208586500c0003607824a803000402408028140215030642c1c02c0c402030102c88500c280d0300740c4c14040003c2d01d048003803012100340000c88030541d5645490b0423400803104100031010340b4146541c3c00844495a80224088410780e01401c81c210710fa070309000170054042042c0445d5100703a00500403038a4003a0890310008124101d80c410310443c2c1c1300746c0e65103058584a010546413590300420400100c0d20301121a4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 186400935 1250 186399685 186399691
    0x7020609060415020615010807210603051f061203050306010c06020d091e050a12050c0102040b04081c0c0f061b0e010201050a06080718141005031204031a 68
    0x240115280c9004480020819000759000c00c041e100030516902a80b0390510119400881a650380d4079080c190a00281c1030b40c00042022007000b41500f2150881540c920103841c8180c003900d0100720480d100e00f040c684814008010354080c8584600c40c1c5c107072001e6441408100e4443c0004624000f1255404484550000c0c00ba5810089100019404580c1520052291440b0b600b800141140d052502480c006c48401110701c0c41400180300002292022907110513099100d415002007600d452001d440a000e00c8240f00180d42c404580860004001e000800586000c01c00f1109821812048441c0b0160340c03e900c940018040c10307803440050703901d51042800500c43c0d07101040040010001421a03000b80c000440014200c000c08501d550302031003a030b070704601810814410981400300300c542e91201845415640c0d80002074040101d00e80e680a00c140019041c01d090150511101100340980d0303e0082c0e611a00a07841443d001103e40f001300c0d01181d902040c0b40600d10740d41034140111001c02 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 186402185 1250 186400935 186400939
    0x1c0f0b1005011d04110c06060a0501030203060609010f0216030609170301081207020307180903090f061b0204021201060206010e0a06060804030e03010e010609060905060a030305090907170a1a0102010b0f04020702 93
    0x1c5d04c0c0b425028040402506610392000001c10307051611608100700100d09910840c145031040040c4413a85e160801240c08411081c07c101c21104850013003280f90840120f054a49103c40e000003208001c0580c04c4901c400e806072b40c5210350f01d0710700c01a8900031b02c403e1007140507640c0414401c1245020a00c080e00445000030240d03403086948003c42c0c028a6030706001074042e41d5841d0140c02c101900000020043d01145a0a001d0a4240803018041e41440807664000c4448038041d003045582d190116201c0813140f8229400651707403a0740103540c40000303003c1d81022607200e400045007540d42e0320131310701100c0303403681d801c0d1807515162000c0c1e45207005402440c0c3c055494180107030f00843d003401030360700403c90343c5c030001030203450980c030581110b034080c2100b44240d0350a041080071a62200a8030002041143c0200c0c00e030b2a020400d60b0b25450700400003046140c1c3d070041241006203a44110840070013003a40d8040d200044004a0880384980c2555a0010903214465a24100703680541101440 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 186403435 1250 186402185 186402191
    0xc010c12021602241206011e02071815080601030b070206060d020d03120e032a0706050c030c0d120f09021f050d020d020403030f180e061c0f0b1005011d04 68
    0x192400c0c02e9132540c807001319694409520307024004103590218580215481007003000f0392903249050001e4440d103841c460488616201c0310160105003103980714200c0000112400e42038569541c040070b449900901c019501030002e400003404007400071540038464003004001180440c0503501f0401c882d50078000540400801000c003084011a52055400c030111000003592a152010541c141c00c9040c412108144d03440b284801c880200e0004101c3e00780d401900740152280c110300c02c02c614601540800003024400d245542c0000750700154110340400c1403010500034445601566402d46100700402500010716290009248880c0042d9010a20700c500d40350b0324010444491000380d8005090303500540754002010001c154200001076807451442c10150320100c0310b00c4840c1092412889038500600c90304000a0f0580c0c0c030004484c190700007440250240560505284584c00000f07441141c0c0c00c3c050901245010168039091000c9550503036506100c0c11444030b06852051400c2001908162 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 186404685 1250 186403435 186403489
    0xc090c0e0306150f01031e0f111306030501051509040c0216030c08060901050c030109020a0c0f080c01060b0c1f15030b07030f020306150705120c010c12021602 70
    0xd01880014014494402d81e02c2c0d00c0c10444040004103100c48004c030341814941041c00310324888902142191000100e40015840c0e203644088029003520780d03007000c242e50000340017034240c3c072003a84440070390f00e0a81e01040b041ea02c820902400c180d15004400500d5424400d10380c0394038040d0005809603059105954018010004210080d040c54000720ba03081080c3da8240708507003041180303580c0002c1141c0240701e241414051003003548418000c2c00030007900003400d24000390180041241a80c3d100f02c01c0120314100d41403076202a000049203800b29401d0680c00070702c4411070815108074030700f0300001d80921602594078170100410010100c081c3e680302c954103204414000c03500300040d40220729078425454061401000c076180710741d1030303c103c0e0320502c140282b640f5480760000f801d22011403050341c2d414203420f000b0325114010027051070b290800602129825010340090649160079207668020b8148007110388103038010041800d402c0e0074101485801b51400d0281d1000c007002c5228008035001b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 186405935 1250 186404685 186404689
    0xb0a031e02060c010212090105060a06122901020f010e190512070b06031603050304060804210207050316050d121101090b010302011b1a09030f040305010e0606060301030c090c0e 78
    0x504000814883c595001c90740001d24580c0c1c51a080d0301c0482d40000304a1403038030800050315080c840c082c0d8401c01801c0198103070300300c41682c80000c071003079007680d85241110f0b5003d640a24450003d07401303005008041966200060501540000168041c050002c2e042c110280c1071121050138000c1d610362050207000810b081512004000701c40c01a00368010fa4034240041c545000a0f04240851810f9044d10401c04075002100391402d03590f04c0d103445406070b2101d04004234200c0510311404d01c0084160043c02e201a00000c1807001c4070001c1e0241c42c120500041410104074041c0b10b86500864130411040c00952280c6a0440d14019803d00e0001183d03040000c1d400c60302c9400c000c0314508a0403005205540e040461003401c0b60074590006110041641c6000c41d50440002d0494080c45580118031003003014402da980b400c8690409603101c507a603084c1540038003030525400b48140103d502082c0c50b0b05020381100c1c10b9030780000c441100c40380b0385a0b82400402030b480b00c0c1010050b0201125041d9 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 186407185 1250 186405935 186405937
    0x409020a03080706180b04061e150f0f0e01150306030b150a05040b06090f0102070b120f0705031003031103070b0109022a0c1c060207050d0908010b0a031e0206 70
    0x1450155240e030f600c0382818078040e4100c40200071048001c42000c244032001410440d07050768416886800030071000090001c030b81c0807406001a051050b410a081c043e10240f55001b003104507003108900301416a0754017201d50504002e03000b0410102c2000c2c00510002c07114501124048940c0c0c900001d01ca0741da81c0b65103840500075950030f07128074042000019680b80c52031100c006042c0803542005409807901c0095014404c0305001e600904c440492031510f68000d00025001740352031019256601080c10714841c1509003100e01c4c1100d22040e8001c00e411034800c1050fa4491000346800c1d01d0810305548085d120308900c0000207940740700422100000034040c981f007500a21814401503100c44040f2a00c00c1d0014629610003854000c02580c912038079400111520b80d00401d07560a1640344007900e0440c400301e05480003412090002401400300040020b19103101c41c032940c1d901c000c1d16100c603111405e84011064490b0b010507860024000710341140c60002d8621021a104d40d2000c80300d90203e011 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 186408435 1250 186407185 186407189
    0x10f080612031306020106060305010f030212070e0702030a020115080642010206090d0e1908010c09080601120f080f190504051e0307030f0213020309010c110a03080705090409020a 79
    0x1198142000412130f0680901406018000b85d04062007598142404c2c0e00c0c2c0040b16100c040d1090011602040e070f00442886100c018100c4000c016044c0d00e000c400113583e84e800141503000540c6890304940400c0c01261460044d5000080a4607581c2c0364080100d029803840c3d00d409404580b0300711040d81003d4122a96207184807001400480c84183d4400a410450010100780b10341d0040079a410486078050409003400718100c9460f140744100000354200e07035810380c0000100d07621b0018107070700454100c040722084601130000c9502ca82c1e2507040c003e1040e02c0c0c0d1140105209003601c00a800204940054409052400881402c090540715811208100386010f04007140c40040c0c144840d080c403c5042c0030b10384689050b0b181882c2c10b031001ca640c5482520014051268140182045540b900b910840990b801d86041d07490342800e4070b115000340100744074440482e2041b50788000106020400c040410b4040d00d90b4995036030360640a480c40d43c00010510760083d6201c0c2c5810060740c401c00b241e00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 186409685 1250 186408435 186408457
    0x1120e07050a060206060d291f080708030304110d020d0f1202011109100c0b010e16140a0f1211030a0510031e02010516050a050c0f010f08061203 64
    0x1a001d180c0400d0280e02e01032030b0080411504440b0801c40f01e40c40b014119040142e0080240b1400c00c1d5050342e00019803210781c03001800c4007210040c0142001180100e036040b039400c0c0b00ca1468203648452440e80e9190500ca2600c854005100280110301042004482c02c20054607118000c2050750014407074000d1940d007152000d40a01c0b80e90709101c03c4213024141e030480360000304545070702042085014002d542c6058400c040142040d04224881e2a1103080d0035403005403c1f0665844a0101003000401c840068141d9001e1540d0342010340300e0780080214000304c3c40d42614203e140c0c00e045940340030b0401508144003603105556811081d6100e941245102004d016440b4141400090156940035244894401200070f0034008518006045071074003c21440c0b0350750a40e441c0c401a607040c040c40444082c08030b0122a0301c2d05100c00400d8212032144200152011810140100001d00da810600d1a00003402031000001c0340340960080368103e400140703041c42100d2548406032841e802001005 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 186410935 1250 186409685 186409693
    0xf03091e081b0f120309150c1801090b16020d02130605030c060408060718030f1101020c0103050c09010c02010318050c090108070605030a09110907091d090601120201120e 75
    0x50340005620b1401c1540d035004025101101c20041059624a2421040e01ca00030000011841c400c00030001081d50110002c0070780380900e4504140482e40c2c0001c500513a070000006000d02c0c107980b05d80f200703500b5100300085076800c01c1c40c00f034403401d0000e009480480c0c110014040ca140582c2d80c02088a1b18050f548001080d1a4102000c3c58241242822110700076038080c4810b0254032000700725030b940078403246000c41c071401911034041e080480507030010f060b01d41c001c802001402000e400389035a2440c03e0302100c0c0c40c22034410044003100c0045840b04a401020b00c14041e41d90f00c01c0041c500b085005240208440c030305188000d540200840d41180d60381e00140c0044001d041403081203004007650805000950315000028045104c01018414071550300c018040030030900901d130008090b4040c0130310b01300b45072849000c0c3c01d11101d401540d040008601c00507140203414140c50744141079490113084981d19000c018200780c0ca05100c00c0b418062040b6485100105522074000e0700310002d0010 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 186412185 1250 186410935 186410947
    0x20604290123040204120204150308041d06010206100306023007020d020307050304030321050f100b0414060d06080a030801060e040b1c060609060602100606050a0f03091e08 76
    0x40000e000001c0b454020360060004000c00c1031103500c43c4441c81d4043e0f13800f01e41c617004d03100f142228542c5908020144113008c10b020401c0c00c0c40d11000340d070855403540300c4091500c49900581e41c8020884d000300c00116210b0b014000561240c01600160440880610700755000a481e91200001c600c0e8000c8039040301010003042036810040e4885880d018000b541c80d020840e15030035140e104500015091124440450325001d0a042d601d140c0041e00c0001045241000e4800d5482c50000361041e50303500000350f0010507001c0141d02142d0440710203248156412030349509115460308051000d4040c00d69501001406040a00c41256450700c65600c0740d0207503040800180c188107000c0d615a01031440d0050b03006c9252540c0360b003080303840070b0b280d1040301c000180d16100700581001d4005140c01800c004000031610f40004011078100c10341c403000e0081c951a0380003100d07540200b2054030300080c010410014418020b07480000c03114020380c41800d00c0d42c035103d8000e0600400382812940b900c000100 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 186413435 1250 186412185 186412229
    0x9011202190203120c0307080112170f030a05070509030d11030f0703020a03030f0203061c061104060906020c190e10030b01030c090e0f0705100e0d0b04031d010206042901 75
    0x42190b05c01c2c2d25410642c1503042c03d020081400308140280d00d03a41401d40416010300940b4036044007240050480b10b940c0b41a07901c00011a500f0070f640705500541402e02141c035950182d0144c07602e40d440a002020900440882154044450424008540000c00802100810003402003c005000c0d07001000c4138401881c0007802c6490040400d03601d40d2061040c4901075441800780c41030085806200a421081824094020220300c00300000d507220000d40018000e07000003c450032110240c0070b95001410039001d1044003103200e484031540b03030780000083c444540070544003900604981e8500c480d242d2a41c2e07a90764101000e80060754444d0340d0070700c01c22080109000b00281042c0b11005810510311500e41c1e617a42e51400d004043c80303070011090000c001c61040140701d51a600c01030807411506040d050400009505a800b0750019206031800708425021103481d03080b400c17060780107150a5856444001e208021412080b4001b02d50403151441d0502000c2803d01802e002401042c200032107001e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 186414685 1250 186413435 186413467
    0xa09030b0901091a06060904020a120501090c020d020303101205120a02011505010e010c150b040207120f020d090b070c080607021608240c09030f0607030501140609011202190203 78
    0x901300607003200940401c11541c450105490f45a4401c0e100540c0b03581c85402c080d119007140c1c421021009242200000700c280e04d07a00415a40c40954082c0c0e01c200340b24440072a00c4c0c0c4070031141448003070b481d41010000d84001615613505140100e054440080b407900b02c0d4241644280d00c03040050707440d81007803291701c0403048118006050908101c0e0180904100107849030744e0b0301001404400c0e40000441e900300032070b001801c0300b4000070801c655804080c6405c0400040f003041010000d40b0f000d89506125000140800c012421503c541c04090301d4402c2c000c0b8590b11180d021201c8110580b0000b8503c0f40c2004000c1c06805141c025143c440440400c450b0009d00319400303054164800e0304140b04d40c02c0c0c403100703101c0c85840e641c140810039501e00f0a401a28412488101d80510030800d025a038801d000c2900e9000d01d5241c0c1c0d00340060b0342e8401100c00844081307070720380751701c03c004002e80308540d070060001e0001d03424800c4001d4240100803a680481860031410940945c000080c951481250706d1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 186415935 1250 186414685 186414713
    0x18070509180906130b0403030e010e011d190f060b0d150c020c03010c0f050c070e0106090911030c04050607150507020309030601090c050307050a090317120603010603050c060a09030b090109 83
    0x2206403840300c04e5114440703c6140030700081c003030581e0b0b942e0580b1502820740044242c43c42500081c0014200301c1103500041840d40305080050143c40150030303441d11000021500c1035044030a1101074071903500c65034020700d10000748540c1705600242100002e00e2514a43e082e4160f90000000c09007d5003402906041c91203514070720a901d84038039100c0301c0750000c11115824050b0f150035a1034904c0c0c200000c0c917000d0f041d003012154416074000019825800b48040f0151000d01e50144500304051001c1305c068001603603081030002d820700c002e1005040080c040c1100901450b4501d1030f4103044004403023202c60035030f01540140c2000440c0081d90404014035401008141c004200340404094020124000908044100b21000039103074441445005020087d64000e580002440200391081c040b50703008440c0d001c101032801e00080c41c0c524040c030a64044942045c080d000741d803039940402c019a030001000c0300c2480700c01d0801102040c86014801e100d40d03c06800000e051220342080000701075a2 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 186417185 1250 186415935 186415951
    0x3012d18051503122209020d1d151308090907020d0f021c050307020a06022b020c070e091e010b03190f03050304031e090e010f0518070509180906 64
    0x70b04ca18014242e00b00040751075001c801000103008018910204c0740c0602c103940b043c801c00f8004500c2d03810303104807076120603020050301d070490f5850120280c0044d1601120302600c160b000109002032030390008090b108091038802c0c0d46403031401d0120700008601c0842900c1280041c1d100c00072800e54a50081142c0d09090003a000038110300c400ad400b0200200440000c110401101001081c4814000c012160075158026000e544414940d80004503000318100e4001c00c2d100600b00840d0800414404c17202c08002d00380180c5100303424845048008503004d080068180700320210031a00e88103480390000d041c0b136000000705040015808251404421564003403048d42030b0380404000070f850111445540b6458201b1644a942c0c5003810343c1c459829002644202d9070702e406068200754000481019103294103034001103646c0b2041e88066042075400313102e40000b40300b002d2801d48180c5503001c40d4003411a24141e440c1401940202d400728854880b025140c00071182030144001c001e00807183c0c40044 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 186418435 1250 186417185 186417193
    0xf020a03060e0a110d0e0a14150c0a021914101409010c0503070f1b0b0405010e060105030703060b060f0f0415020d0e040203040c0510120f0203012d18051503 69
    0x2103500342080d503100395103142c6207082e40c0c1c003040304d0080b4050002d0362000c0d4004044038821056480e80544582440051509c40c80800c03000520507482542035440740c00c4154000d010b21100c101c0400803003808a141521a80066030131628481402c00c14010480142040480d00e0f0131b01000701103070b1610140070b0400310f074100003140181c16440025a54841d12074a4644c0024020301800c1e102075007051220f054104082010000744008440c415000d644601d00030401d84244071002500c6420030f004d0680d040d0001402040401e1142e000b0504424008021928003400c0540500c500d900c02c20340240082000304040090700d110381034111203140140050101089141c000603c50034603c1d0101b4403495001c400308061022000d03030700b0080c1ca000717451030012049004000d861000702a02d50b404080c00c0400c1034880076058006d41c2d0403240c0040300901c10340806101c0701081c1c061880c90722a0b6200c036050009803031a02c0e01819000c8a0202000621814266045014099144882070013940 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 186419685 1250 186418435 186418451
    0x114040b0a08090a122001020307030504140a020307060c03110714030f0606010c0201030f09230708011406060a021510090b0f011d0307030b04060c08090d0801180f020a03060e0a 78
    0x10701e10129055070306041c40d0149038518044070006c0601d1804107280f200e9840802040021901944443e0040c1e0040b0034080b100340d0406280d5075664501c0d0b4000f901500002030030000b15000d03101030b0071114070038180780041d403c10301e108528000b02d07607000a0014222080c1c413002c5043c00e01111622006050103840c1c0c070303d000030018008540c1c04030000c1c101a902d01080c034480c030003540100107a0b035005500c801e0704a81880c0b21340c01143c00342c840c0289405200c1c00000e030748005108801e61800004001c02d003583d100c00030001a50800150b44c411b40c0642a840d409818010811620442040f000d290310141801c2c40482100c9409002502034203449c41c0c210303010703a0031007006846c0e42004203090002c0d44141e0b0119051912a82c001000c4200344018882000132035006000e400c10303181d07940592696401c54080e92810b05c02c0e03220001c20000070050140c2200c440c0209200c82c0012030108812988009a00480e03002e000c0e9840040d07036905003803041031058900541c0006801f00b09120100c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 186420935 1250 186419685 186419693
    0x4030f051912060321090f0e132105070302120405010c060902030f010f06030b0a14040809010c0807080a03050a05010503070e060406120b0a05010e10050f0114040b0a08090a 76
    0x901005456060100552060844400b25000301c0e024551003501343d40d1444e808505880006812000d07840420b8414001103007a1110381940000c0b900e080c4200040c0340c503480c440c140465410702e0103640b90402140140c051417041091040729540ea076071656503420081c14000d044c03000c1d9070310360186044208010441d680e88948110003054010600140005035480000d1034111701d103a802d5010b500344000490f000a45502240850303009109116903a52030749036502c00c84651000681903800306101003000700701d40760080e005e486018145009403034850b0312034880d20b401401d001c41e46044000f400c0c860320355140c01402d420200c180018409541084002078850f007060003150030b40409180003903016585d60300030100034070b00009084110101810800f820000407581c88441508040001500c0501994040d00c540e05480c03922440300d003003508000d6090014004181080301d92104c1201b0785d2050802032000308003440c051a60788403403020141403004000e104241541101c12100041 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 186422185 1250 186420935 186420967
    0x19060f03060b0a050907200601090c110c06160c03080d020c1e0d1202090a0602010b0a06020a020904020d1a0f0702010b01020303102601020d1a04020903070902031509090604030f05 79
    0x5a4600300000440c001c00600e0704a240505002c5520388110000015481e180d81d10bc8800c4044135035401d6401071045070055940e04054010070782185003000b140e1f2004941818940411707108040b010244e56036512440f1081e001a081c0c0d4449560000751040c00e00d804120100e569079146903110b03d4107040c400c0081c0c0390500184800705010400400d60ba451080d54102c948101e4004c110006030743e201c00000340240340290b00c10b4054001d48401090141c00040c0000c259a801080d504035503495134280001d00c3d641c0340c01101c01202d03224455114482c0e5010f00ad101e001c0c1d003540c994040c42c1660000b4203440d00c405480c2e0554204000f8071175491607000329842611040c40a10b410406a420300c0e20107043c5408910200394404140301e029102250010040c1d4485d8101034581c6040314000c000892040b00420f03a0305500c100e0b010007009440d60081c1d03904c00500708020750140451408500c1c8050111800b903c2900601c04020401d504541c4620f0007a07075610b8002c3c00c04010030500c0150b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 186423435 1250 186422185 186422191
    0x5060a051c02010e010e0312090a0b0c030f13050306040b0610231b0f010911040605010f08090c040906020903010e24040804030c030302030c060a0e10020319060f03060b0a0509 77
    0x108400c2a1680c404da9000b4601c503030f501c03400581110a02900500510866000002101e100740141403000843c000c20700140c0d40c07a042010061032608021080c900c4150384080e111107040702c0c281c0d400040c83c4da81480510300c105c0c05110301c000545082020480541c20380505c5e0418440024000400400302e0f1094208400a900015a451a000d03590b0300030119000400340c11841200d0900340b410b0300c1900240c4850b0712450019402c0d0070070800300300039074001c0d0107644e0000b0800d807100140c1c10f10540340340d608061501c080c7c5000c0103400020034180c42103007400b545c205800081a000500b00fd00c42d0104400115000d000c500020420310001c00c44511401c0c035100100101244c02e0125220480d001113500070170060849076a458043e403a0b8000e00c8440b8054060701c400210704180a02460050303c1001c0080c1108d908940d011100a4102501744041c4083c0002080b000c44201e124000160426180d060500761071072414105443c9110403c1d809079031071000400454880f01401c07a0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 186424685 1250 186423435 186423437
    0xb07050d200f031003050604080c010c020c0607060507091a090f0402030426040b0307090303020607090e01150309080f03090601061e0c03050c0d11070603050126030f070605060a051c0201 82
    0x90343c0d0312400780c0318034a00011740000d403c50080c1c500748010814210000c01201034440e00900c041c5a2041090ba2100a07288149d82c005904110840000f00380e58803250384140e007800d0983e910b50300c4182c0c03140412900c203030102074504002020660b610301455614280241110700703500d10300e000c2d07071000c0c0c4415143d0b0601505850303540b450a039003040301c004d80d4080c01d214003001d6100d00c4d01c2c00008040003c90300c81035005d0302800020841c2c103441a89002d00f941c2c0700402c1c0c2e04060740780000e00b03440300d1503242d041001c042c2c0d241c107040b0024031800014a01641000b41181e141d091581a40742030041c1a0700502c140302404aa540020389a011940e28100751411b21481d1503d060030251203920032000228003600030715800180e01da41109107071090303c440310102d85c0702503151042542280c0080c0a0071080c80c0802c069800c50070990310080722614020301c01e50b400c0540700c8980782080d41142c0b0080f00c0c0346845108001003400c0c12020440104000c50b1000e9001051803000b41c148855114064 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 186425935 1250 186424685 186424687
    0x24060d021608070b010f0503210313080d150807061205040213050f1b1213020105040503030c0c1c030c030f1404030506150604030302120a09030b07050d200f 69
    0x11240018030034802030720940051896075100210701e03110790284024040c200007174100a001180500340000d611301102c1907002c2031065044503044070103503500010051029100d0300741140c0700190078900034117a00d1500c00d00c082100c20b404d00351103032841c106421807000755001c108100f00169000e08520b104d070540800c000f55a4a0310f0000c103c100e04680920118242400240980e015844d030010f48600c03425250b0450b2410f8014280c0d800380700344000300030001c1c407100c08036890740070202c055001e01e841410710a180c1541c800c0800d007140c020000820058010703080b0b004850901c10a400e0023801e4900c07015440486a680141590107085000340c100010550028403807800707126a20302c0e940b080316400b170721107a8034a8026a82c0170110b425505c1c02240500410413410402e040c2c400f030341d0341038016001c000d149441c1711082760041700190b4200426414000046110741d00103030b00440c52540c0d4944c0c6c45c00c10085200944001c8801401d000c26160302c2d00c400344203108142c40e4000000c028a03 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 186427185 1250 186425935 186425947
    0x5180a0f1a1305061501050409110904180b07020c012c0a0b0c190f021003021201060804021f05040b0d1b02030a080906010311040c050d0905030324060d02 68
    0xca204401c01d02074441c12001c0041c4004a0014102c81494a1003081140c8a6039aa8129412a45040f94200b404201c01740010302c0803a8640d007204106540c1840036900780100000043d041d10340c51031211003840c0b101c401c81d01c03d010401104680c40031581c001811080b011500080142501d624550031402c6064040c0c8840c4119000000030070b800200348000740d589481e02c0c03401d00e034050841b14103184240c030905581d46c0100400101c0302a0440e0300340401200903001d00442240c0d14001230304040d8200200c1e1020402042ca0901820881e55104c0070b51500d0710600c902c1c40e04a1101002c81c441c0c2c01c1d0f0384c80aa581c008111000d440001005c0f540b903a1840c4503074009040e00c28241c0d01c0310000d45004640d2158000003400d64546503668540d52038075208141034403440c00b8080540041c06807051070a150800e600016021030f4a46005460515440c00c200101d8420000840d5a038100005000301440d5142041c80c001e04003070542200c0032007039000642c15100320249040749580210364 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 186428435 1250 186427185 186427193
    0x1302011b0606060315030812040503040b070804050108070201360807060c0f110a060c0509130905010b030106060207030b091c050304060f0212190f021c05180a0f 71
    0x584444040c41000c1819500300038500080030740800d00846001034500700840c5100a40e410000342101d8012007054600341c00180101e8511000501c03c2e107851200f080002901c2a154004120352130150080304d40b180d0420000614804000e00384c98216810201140c40750a100003030680c60f5403100c010110716204040410b00d1710300040c04007500342c000102d0440706010582c2c00070300c003240d00c40c0e50b00d164441c1c80850650740301c00c80450452003640102e0300b65000500d65031001003100514104107091111110006944044846a0344182c60700e0381030450801c40240207070294114120f0082c06000d080180c02551340c01e242c840541981c442d400400c0d40e03114144420442c500c0400b40e050000c05103102c2c0a0030b20f5100f641c04842d880d15144901a070340300e1034400d0302c080c03006078250a899a11441000c0c00114480340c800003c00f035981c901a03005e145148020106030314140384c0c03003070f103c450f030f012480c12100700a200070413401003480000858030000c80c1d400c03511603010f4606202c144103814 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 186429685 1250 186428435 186428447
    0x150c16030e040f0b030613120305060a0314010e07060516030e1206040302060f0f1b18030708010f0b09011a0c0312010609091b020613030c02090c03060a06030e0303130201 75
    0x82426009031910461030f86114054002c400146400e604071074094030b4000841003100288403014100394000480b12000c10301c01d0300505e402010080000c0403003926501d501c0034500881c103020086030354aa007091580308080c020a4020281303400c00905080c2c4100c031843c2c0c00e200d0040c00030100600b00c503800f295642c2e05010100c405910000310f03125407070702e407034065969501902d1822500018000260540f025107460358805c041074502c80310303211041c605801c0203400c241003401a03000f404030a03400c40d403020407845001b008070300c00124040d09602c06d100103c0369581c1e8001d004411000040c040600384a000541c060f154003400b65079130344c0602c641400d50258002c1e00a030f100c110300c00010700c6580b03d02940143c91400074108609402c181c14041201450b02c010405a080000005c9044642024042946000b07041042d5030202944c0000c076102421505c0800c9d009001c0300740003003820140d130101c0c050019800c04100d9207404a00ac01d0b40c9020041c1440b0a280901c50040110b902c903034 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 186430935 1250 186429685 186429707
    0x5031905070f08040305060c090112050c0909090c01030e010b061206060c010f0207020f040b0f0906040e010203010906031704030b0604090809090406090209100608011208160507030302150c1603 85
    0x10340c1c0d41081079080d1509081c11382c000c1c40203031200d22400300802c0700c0025440c1151100d9a050311220030000d1090300000c0508001030441d005204144031031f02c9603440d0300112500c00c141d0721001d0928100060005000c6030b80c4500c9a142603803504d42d0b0500c0b6501c502d0116000b0f4400482d04038003a5a0b80000514680700d440420501c035424117072103070343d980b4041d0040c140030351085488060740422041032102310348004109951208052003402407906040c1d907100e4000001600201e0003484848480c0e00b03a80c82a40312180090f503c10007001400b11040c880100e0101c8260518503041c55074650142c00880a072002e445503503031301010400c21007110119481030202070300000c5282f4040c24480001c0600c49026402401c845e000113140c02580082101911210b132034045c00c07642442d4491010040100d402c590180c0100301c0d403108040341d000d991410074400d01c01000840e040d4a002130812110f16000c5035100b5079030060000c1d0080708e00c140e8a19036035180600e049202142003c881c4a2980 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 186432185 1250 186430935 186430943
    0x30c0b090312070308040303060909050c21071e060305041203020d180b040b01080601081005060a030215030103060e0c0a030f15050c0c01180209070807090b0310080d08040503190507 80
    0xf84842c00c058121444500c1140291800c00446030f446031040107644060600900b50340000c1100c83c400c4c0707405032600d14501c00340d401c6889090300889011380340107206c3d0850024120f292604841500510b040800685030130300d4203000c40d080c02d548520000c08010207850030f1580218002c40508119400040c10302c1001c2d207400c1540956061145800d801510b05690715040c560010504040018500e4120382112006110595046411000074280a0310450780a20f0100000015a4504652010780e0540307081d000e07502c0d4990300e012022150000300884064000200d0102240d5690001360110780e00141d554005004d1498010b080d070308580c00911620340780406008164031020040e159106d4600d000b004180359014688102d4104980000c1d440000a000035070002d101d0100b01c0e40052290a02004c0c180c0c440d048164aa00111001400c0d820161420043c07000100300200f400b00040c01d080b0010700b8207440ea00d0303d034450000c1065510300462100d0103100d01c248100c605950300 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 186433435 1250 186432185 186432187
    0x10909020904030c0828020f011a060702060403020a09051602010603050c060309100e071404090209041106070c03080a090e04020f040c020708011104050414070c02040504170a020d030510030c0b090312 88
    0x806c07040e0f10502c07652202d2001881014401c951441c414442c004401040342010a084d89042040114590021100300d80005003884000300503150010000003500722078001103010700d40501000318842107000480216814903004101003a00481e15806844096455945d03d5885010080c0340104c0004c0801900e0300d4000c4441c00501e0214125050707e0380702100280c1081408200003c5e03904e10320019600c501c0803408500000c8008007040800e510180100f400c3c0252a00c13003682003102a0300a4400020000d1a00307603066010403a0409031010219100003030030260089a0303e23084200000b0700442c0d5802c445046c4600812004005145580c001d0005003240103d48110780c019200e82c0c0c0c00707103003407040710f410302e502501007103200321256510608139291039001c100103400040c01c10340340e0b0a15107135050000700b400c1340203001d4100150020b144041c80300100404860000b000138980c04210081480084c5040351203204443c0e86500d41078075070101ca8000390810410125011020b20 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 186434685 1250 186433435 186433477
    0x50606041401121b0f080a0204180b040b06030108012a08150303041221031407230708070210020f0a0b151206041a160c110901080a0209010909020904030c08 69
    0xa440145c0e0090780341950707580302007038641d807079504103070b004500030f01d00d000741d00354a07080b0400c81c50383c03011100c22002400891414148804a10709074000e03008012942d4680000341144c01c92210300d60b06111102c15103007900c1450040040000001400022030364030010000112560104242c2d4003428201001e10070300c0d50203251080b00c0d150400e0090112030700504254094034000c0c403a14903038541d08a56400b06544a00c011030305409900300403080d190109091a8aa95100c400f800c601c62042030341d00d640f0311160040151400c0203d0b0b41e0021980107641e1588401e8010035401c5c076240d0301144000d0303035407100702a0a001100c0c00390400c2c0c2028400307051b00b11031180012401d00a5000300c68040c25440d4013840c180020f0001c03210000c2242904c3d1704400c11501c90305030f40301400d00414964184c150801c000446004c0280d003d40700a901c401085410340c036006084a00502d400c2408100300b90142d4086600342100070300140c00d01a40c1c110020500c00500300322080410700f01c841c0032040b4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 186435935 1250 186434685 186434687
    0x2031b0408030d1805060c0a0306080304090c03140709121403070503090a08070602030a120b0a060207090605010302070f020402070c0e0a05010e010e1b0a02010b04020c010f050606041401121b 84
    0x7401104502002c43d00b408000d411000c0b084204015481c5c0080160030790f5500c0d542c907400386502058001c01010b80e10980020b48000900c05440900400f81011a8440c03041030f0007000c0d01c1421f00c881d040c41015509000c0d4041d0000104003c9a030510000741d036a141d64100901802c02c0030310142c10724080025801e081040c0840203100700380c02243d0128084d41c031103800a1751800355014840c05680308011041c00c0c035016420081150040301d030045030180006011400d03802d40d81d030107a8090b920810081c000c1180500039070340a8402883c0c1141001003070313103131646000d884000290146600040010038004000640c0007e0140061400b041e420300e41e40010051409128425400c0b03030520001c5130350f0f103c02d03000714000e081d0511058070309440310701c00b4015a404042c1c6641590340c2e5066070715603500c9a0018101c1ccc80f8070302c400028800c0b20071030350a043e00c00007232000c0d01c00c51013004244605031360030f40c015002003000c4c40c020f9914506640381c1c9004002c2254051041481c07209820011 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 186437185 1250 186435935 186435937
    0x70206060f0402121929090a0e1c030c05120a02090307030f0309150c0b07031a0a03080301090c0906090e06010318050d020c0405060607020d020a0e0408030a05010f0605040902031b040803 82
    0x2002031200c00b0400c0f02d540c0b0011900d0f4042540e080c540c0c0054004143c0d8085c9801f944698102e4886180010040c4400c11024540b0120410546406280700380c0b01114580521800c0892038803801c0c2985030000344803128212440c010241114141d0100c1c42d001030b42c43c100200d0014541c0801c407000c404685040240c0000d1039803080c44c0741880c40501100c10b59207d0b0340790340c2c01e0a07440640c1420741c3d15000e8050307014001044101000c0140e40340c03400304550718600c40350001c40c0203501080d680d504004104042d58101d603144030030721260b0b61040118075441a444401c81d00f100e00501c0e215120b060040f0060161004166580c04800450f80c1c140400481c6d0202005100d07000c82e902d40c0850f0b0240820fa0780c0403141c0650090045c0000c50160070403190305c0c030f0031901c014000e014250326600c0c1550018030aa8050713980003400710410101c00418403901d405030405080700050a4038100008095210781e004074400d198000c00440c6107030a03092807c0c04410b46918510b43c803180c031142c0325980d07 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 186438435 1250 186437185 186437221
    0x1606020f18040207020604170a060c0c0605010515040510021f020a030b030c13020705010b030a14060f0405060a0f02092d010c150c140703090501080708070206060f040212 75
    0xc10300407094640003841c0a20803242140d5014142604080c549100300b00d42d0040b000401501c0d004a80e03615000400314814200b0340c0c0c105132500560001d86080c60750072900160059802030001c072401090059403602a41c0486108840c5a403240303d580350105d0400010201140001149428000b01031195402800d610b9940b603904000c1c3c05044010103a482503c02211900031402c803413507070040c010381c1e0020540503000c0c0c800801c0c008034407000319260000307050043d2982040880740d1079920000703200080e000000007903820381c9400c00303448051302d034030700905040b66070303580d135007235440b155980fa0141d80d085280202030400340a01485100c400f42d4242207400c00c0440c2544010f1007540c003a0388411046074100700042a8022034a40c3d810003000840101e0741800032810105001481c88001001064466980c82140d24540000502800780183c0040705116010b020004040e40c00144035601c20001c5070080c10b900f00d5000424020300c926005092500c2d2b22004121404c0440c0d1310581d0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 186439685 1250 186438435 186438457
    0xf06190e04021314013b060301050906010303210b030616020f0a03050d0c03090f05030705070e2a0f040b130609030503030c030c0d0e0a121b081606020f 67
    0x103c040030b4140c40c108883c0280655003c4901e0303e0300610281c050fa82c8440c8410400700309400c040240d12403452004104081d011425007107800070016503003003e014080e0414041c000400e402d50548d07070040c200700b0b000c4840280d0300360320249015062005420100e40d0181c040c050340c1d41d45c20300350300c1c940d213000800036070401510855007246e04c5480b000419054079505a03480b82d042c01e040e80301d92000390840490000c10151250340a5011500e41800310050302d105100850303880e80703a8501941403821591200080031300d210700b0041d6020b0340082d1032300805880702c90900312401071060000740e8010b18581c0c14081202140104968507414010420041004440f02c0c100b03599203000c0700c0d0818a800010282c6d0420f00110b1766142402c00a55008a40700b48524104059105402d0444101d119041e403664007140d9500240400c1c42c03d100005d40d01c501e800c01241c1c031003864a1805054400b0000c100550004000d07841041c9004c68501240c1d01040a654410341c150407144203400c9544111 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 186440935 1250 186439685 186439699
    0x90f0909100b030d020703080d14130b0f060637090f08030307020a2d030806090f01050f0d0f060c0216062105060622061205040b0f06190e0402 63
    0x2d003552500054245250340d20f42c0c0144281c0e4290381d18900c0c0e940003411024072903900c2d03510582c0c1d8144c40c114920301c00c0e087e0a0040322070480340c0c2030404125002508542c80000c08500f4070500740c845204403031a11400032000f4113503c41e140000ca040240440210002d140390446070340308260302265003030031101d1242d080e1554644170404513481e0701c0b043c1c40840159124400c4400040c841440d00d0801020078034503518807080302180510801002c610440000b1012010000c952401c0d12000c2e8002031848003922456052401003082c00307191100b40f81c0324070068440c803c00c00031070311131060060798004030030b10540204444c0070f50384e03080403041c0b501d0740042600007140c2c0e24400e0b4451106017500c1c0c1a14000d01d2414110301c001008040c2142c1d8100c1c0c82042480286940007540949581c1c1c02c00c8846102e91030002d00178030400c090141010160304013001c3c080403c0e884400e181e003003032005903d121952605400294090042010040030b035007269000104498400c000314800d9009641d05 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 186442185 1250 186440935 186440951
    0x1505010321050906030a0b150a020102040f0e1018110c0c0103270209070c05010c0e0a080c03030f030c071b05040b060a0804030c02010311180a0603020a090b090f090910 74
    0xc2d0703040d00030044459040081400010130001e240d4000a03d00b030409000390814164219521034564001001000907071b40000c1d04214047c05440a0001407100c0440320f001d904181861014000541c450311640302240c042d00100c88103240d2144a01246022741c0075500c0c0560508107403074070440722000e07020a20f000c4001c20144e07201484105981000202d040e0f003111541d0030058110703000f40c042c1041104402c41140040c1091107600b07032251098982c144c02d15009410010b001103150415040c1e03401c0041d00c0406910f000060390711007451a103801e9241d0b41c60303280b04410350061030030140100d00c0b600c00001c01ca038011b81c010020b40d0003c3d0390500c00c44440030140102441200c2d2400005249a400200070a110390004100c10b803051402140f501c0b1640400d403155001301e1081800035a040180d4606860b10000c0800241360a050950610a1480d0040d0440f055403183c4941160001075840c41d682d51500b15582e040300c002c08180d03460801405d03455172070100c031400d105e800d481d0803d1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 186443435 1250 186442185 186442187
    0x2a030601050901030b0a0218060703110d1404060503130c060f02060c070b0c1602030f150603070308031303030e070312030b030705060406110a06060b0a020d050f0a0302071505010321 80
    0x20a4140c0745c100e90800d40350303222520024000c0d13018034240c000307294171450100d00541e1620010300589000f41e40b505114000c4407055030030402180c548030284420b1002c05210402648240c400b00d4401303080040d22030307848029000d00c0d0520008001c01b04103140c00f01103501e42c0c00a042948036590b5500319015030761a113400c641c041c0700700c80014200c2e0048400140003070484038024030b490310941c2146000d040c0d01e603000c0307840e101000302c25007015080400100104448070b226958000001c4008000091540c0ca03608402c0c4005030048080e20b0700100e614080c10b0007900100e500c4c0c0c00140480300515900d052050050401591720f0f00024244440944c0e20300d00050000103580d0000d2605142918000c0c050312611407440c1240c005004079080100846c5081c8901002016800c01c1142e8503100190b0090418401c2c489100074010140481d43c010440070f000d49100d5001ca080043c0c0e01c4501c0d041403014440c40c1042a210709042c2000401001200ca030360701c03a0090120742d100942612194 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 186444685 1250 186443435 186443449
    0x1107060e120c070504051f080c0f0118060818060a0506130c080601050307030e0a112112091f03060503010b0423060a030209040b04050705040c050d0e2a03060105 71
    0x407211440d40010814040d40c41c5c668800d9422002c1d0045034103a00c880440e0446019a19030b022001741c5d00b107001107400e41c0c10051800f40c200142440d1181d03100385403002c0d298a074032450084808001d1910006100d0140c1d040e401460000e43e80119503240c906200c840d0040d1808444440c0513064003040c14000048034044c0d5180e81581d1384580c411560307070f80011241604003c002008154a4840b03040044c1c40c144031060340240501c0e05040860f0903c0103000310f0000c080c43e5a1603442e800440084004400705034201640c0300c40440d5a9035400d01c0300000c1c0c0b54840e84050100b80d004c00e001c2e070504a90503a201c001210340c260024008151050200800c844541090082005000340740d050107050f10b118040d402040140702c000b01d07030f07129000315442c04003c4030100c414100010501080c00310411441006001c200c5050103100724181d8020024083c8400380d080040d1202019038015034188100b844200340036442d140d44040d082500c0d0701000d40300708898081c0c01003e00204950030120 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 186445935 1250 186444685 186444697
    0x19110d02060a12020f07050a1a010b030103060f090b09010504150c1709030d0207030c2f09070201060e0c0d11030903041a070b0a09020405060909060a0b041107060e12 73
    0x1071407181007220100c0d003a11880010300904031001e90070041e500d0341406510191211a000b000245040340c458505100040402021081400300c0000100100607030308040f203040d01e81c45000420101ea40c4541500a442e8036000242500103c1081122032001540f2040c812030088025128011602200d0400c803502100c00c407000a548004000d400d058110080c0e03003015900b01200d02e00040341120104030b0b040910203d001482d40b0100320103000142130003140e042e0045140840054100c102800c4058080d41c0c6507019190300700000c2da809001390700001c0140001c6484001e9072a04408549081e440b41c10090041854001803105418420007070343e220303d1002d070046103041d0600074800f60011014070214170030072003085500006410a00d00c01d000b91007001020030504010300c100405d5400040c12140207055410400450200014040e5048450000001840000c120204014003903404500100840c0002d041c4104580348d030010f0304449010b0182c03034440c2e142c5483d002c01031240c6 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 186447185 1250 186445935 186445939
    0x30606010e01120c110105010f081c050307080a0b03070905160e1813060606020606040612030804150b030708030c0606030a0b0126100e0c03030405090a0c030e19110d02 74
    0x400700c3d50108100c5502503400054030741840401780441403213550941341c098110a0080296003010001900104012850361071202800142662180b9000b00513000041c0701d0400c0000b0300c008540c40e260a5071080602100280c1a41d6515445101880180a0a6643d004c40b4002202c0414017148103005441103e4401000020000002f4820b080f0091001d03244407840007100441c0b5000511500c9224000d05da5900076210310b28107601000201c42580e80710303400c003039001d081c2c400000354466101a0300035880803c100e200c0400700050700040c0000448550144034003038002c24100b0000002e000c1c120507546c112145a07561600341615200d00000040101c0c8003d0010300c50362014204641501080d5542c441050f814075079464075000d00080c041c03009550f035401c100d0344420148000c0030002400d40c02103241c28901800f00701d80364401000c90507810740c1c604410381c41c01d11a030000590841c00004032409601600e000a980c140484400c5a401d0800548070b4240e0800c0003d03135002e1500 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 186448435 1250 186447185 186447197
    0x14010311120402030f030d09020a0e041e030207090603050709050c04061704060b0a030b061801061d03010b0a0605030114030d08040602031503070b040905090105010311060c030f0d020702030606010e01 88
    0xe0094a1604004080c2c01260b050042d01c8040b100f0300c8040000c0d21040c9800070012031401e40c1c80c0148207043e0419000490001102020007010405144820403e0403000d000916180d0303050030101c3c00c0818030b0700516030145c10035200109020b0001650003e5581c985001c1149895402880c101403185108078000f01c2e40c40000400e00001c15001c8d25030107070182201040e241d00d1100043c0c0d01c2140e035041100c415030750710240300d80b600300400c21140c022020f00d03100d140d40d41040c40242028241060a41c080e10315021200540e803020340081c14010390140c402c03011140c0302c4401030300ea60824010241ea40031400304071411441c000403e0302e4290266140c11107240c030341342c0700c00c0c0c0a07500c018041c03103000102c4039080280c2d40701000404018160060743c5911f03141845803110075241c003d000c0c90810b030b05000050001c0f9401c4603d626071140c048400550f103030081d24849003540984822400ba418000c6400c10700249a60010303c449031089041d03071075541e00c0400569a0030003011249001600d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 186449685 1250 186448435 186448447
    0x708030115203306010f03020712050c06070804031b022407020114070c06050c0f0709021902010902060406030e0f01051303080717150420070c05030706050307031503020d030914010311 81
    0x101842500c1c450030107c2c50007515020a54550310f1003080040305400015900241e21007005070103121442d007241840c503200d211400c180d20010004540740b0702c488000a2706850680440d5a40b81c07110401e180c0410300394941361140c400c0c583c0039402481090340030850000900304030035001c0e4200d91645601003003184c2001e003441411101500000140f140d0307032080c0b0078640800d0004200380c01c02010f0301c14015a613008407482c103c0010003180d4814056a0500b0002030040e550312080d0741c10b44145141c001150b880c02a0314030702c0d00c4040448007406519180074401604164860601038034065220400503032122031007110a441010b1081c43c8604064000c113049031440c05007a09a490014004500400030050003a45010215065004040000340300c504000c8020034284c0204803c80c003400d603040c94000050207a10008118030101540c401c40322481103603a000380d001864018015030308004081c41d01a100d40c5080c0035100c1011100c4001c0381056100e40a03000c0ea00c4112000582424 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 186450935 1250 186449685 186449687
    0xb010902090d080705070611070513020a05040314032d09010c0602041a04080c010306150302031e010602150c09061c0906021c060902070803011520330601 68
    0x340001d0721440d800140071100300089540100076000c0c540c001d0b0b0140c48503134a8208050102d06004441c01104c0e000145c00300402c1d03403900d201d4012101c0a10780035030381c2c100200c5d04865038070580e000200720003016040d1503090f00700000a404907035070011010a00041d08010780784040340a118000031024208868495540725410814420b403040101505054454040c1d910081002130300f0f041603540810304001455082000024044003030070100203580c10b0485648500d56035664000034150000041001408403240c5600c182e01315403861034040d42c503280001e449c0c441a46180840300082008200c541860b002101c00f0020001e200b14502808040703c02d0f130481c4140e2050000c2c90f41e420810010403000d000038514200e240e10034801411522036404125a070039000010814414480503001540c0c0d4003c5030b040d14451916219428541c0808980725071142d55001054001d2000d505034441000030890180e0020b072003480000c00d4680114049060103031064006c4200600210b1183c1d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 186452185 1250 186450935 186450937
    0xb0117070c020a0305191a0c0f161a0603010f05011412150a0b091609170f010f050703061e090b1306060c02011202120705031807030b01060f020a0b010902 68
    0x1c07480980800c82543ea2600c803103007014160213240c0c0c2c0480d00d10503860f00300018190784121144494858415038141070640d4410b5004c0d188140203455400182112080d28101c1080c0e84c4540c40512100b120300b2014590440d05400d9808a00960800c82c0020840c1c0003030107207074141d46800d5401c1100030740300d0007008000503400b06411410300822489161030319005030454400c1800b805c011030200030f00320a0045001005204402c2d00440c01c1da0300548942c040843c0c41121406403643c408045074130351a60070841e803600e0b001902e610344651015480c11a41040d44201540c2e1010464180d03950942d20130205206446803060384a1141481070142c0d952222540c00d50280040c244007410401440c01c4442e184c00c04404560b0340c020301e00071980e01c03801a0982c45108001903040904800c43c0340c928010181140d414440040000741c24901040881890340c040351044400710742d07607803c3c0f881c085102030099031300069200705219030040c000502c486000398030003154207403a8a844668002 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 186453435 1250 186452185 186452207
    0x402090a0204031703040302160602070510120504030c0b09030901050706020c0c09131e0206180f040f0914060606300702010e070828020a05030f0a060b011707 70
    0x10079800d02020011810703a50003081d04009a00340c1e40d641c1d007030508000c1d00e00b80411a08552a046d04841170004a030302017102402c81d04165803840d05c06141c0002511081c1014000c285000d2403d8100414581d000d01c1020035103024031020000764451084058030781c480c020180d804501c0820903140000e405500900c000050304041c0c1d00054071100008605001c141c4010344001031141c42d90301070081030140c80c4502800340d901c00740311740f03980da001ca2210f00524105042001b10b0020303200d003d4491345c850b0b06044000400401581e22074014100040030f00d031400351030281c100d584040c6420301c002080c1d800f03250000c1c003680c100090249802401d005451040c03400d803a2861000c40d01c0740102d404503000d444260004206003080c0c0414a241009940c00a4215886083c9444d0401031010f01c0c4040d01a01c1040110341d03074150b0011419141039903020315010310400d48181000310b4007040d070103542ea00c611401e20070408202c0c0119103810091806542031200040441c51050080c840400c0c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 186454685 1250 186453435 186453451
    0x30a0c0f0506040b07120b0109051909050108010603140102070809091b070f03080702070302060301150c050a0303051e0103020f060706180311120705070e06030f060903130914040209 80
    0x12511281d640c1402c0410555007110100212000d0040d040c5c0c100001d0112900903850800c400a49040020004a00d81c8a654003801441d455140d81000042400e8080c00c00c1407004d103d1565a0f202032802811a844140d50038011403181c1d10030040c045c001c4070011500622a1800c041444c0c2c10000e48020283c80d021241e401180501600c00c8000041c0130300900441003464482c40c1810701400500c0c00a20440464100a900b400141c0d1900180c2e415210040c081c80c205021740d40c8103680c000860180544244030340400502059415040903108414803940803205901c1d03e046800040d100f800029485618403200030006d091040142130403a0040d500032a000c0200054101c22a44034201980011040a030108004074100b09041e6910000307190145499040d49405071243d0302409000c400107192004114135550800c0031f000d028404506a50b01410310842072540ca9200d40340c40c003084500313440001000e0089200742c5040100065031100c1341d5a480c0c1c2040018100100361030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 186455935 1250 186454685 186454703
    0xf16120f1d1e100b010c05010f1e0b0108180a020315092b05030c0d050f06011413031b08031b010c0507021f110304080312090a0f030c02060d14060406080f030a0c 71
    0x880450024009d03404000a04640055481c211400c0f0410800c00003902503060344c105142914940d070300c40700440e409030320481c3c1c02c07002403440945641044141000039506104e101c5841c80c00e8511520714a0045503030f041212821102100e00c00300c940025480c0c03210200c1c9181c40500000d0003070004551101d015195645080d0b200b40206e07040b614155010303c0d914080004000e001e5801200b503a2000401501a6080c03002c8400241030001241c00000c02c944a068400c800f06a60b041400f030140c460721040d2034803080d00f07016a0ba00d800c1040e13800b08282d800e081481000c1e90040007116147c40e0090424034640303041c0390303000800e41d842d41c0140e0104a000815403140d900700b80050700140040c80b020310f41d54802c1110405902d04080c0180704c56411041484000603004000c44002c0c681c103050a807c417802a00000d5098018000444002e40c10144244003040000012a104800c103c4081007141d032200c18040e5550348001c0b4001481d40100304440e0342c035000e13607204601075115603000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 186457185 1250 186455935 186455957
    0x11d06041208100506070f02130204050a18090f030c061103071e020a021009031b051f0201020702030106030c0302190b03060d050c12010903080f16120f1d1e100b01 72
    0x82070450344513907016500d440f8428107e00440ca01404000304003000704100707500b06400c2c180010f040181c80d202c0c441c1c1c030100c1080e0f4296050450b030420041540c01c803d00101007401420060030507550400119240c40c40e0440240c80e040f5200300f40c178015038182d61982030a40c40b4280c0c0e0401aa1382001d04d405611440c04510300603501c08081010802d00b50351010100d902d9460203446901031035080b0652101c2d5070030240425103c5075030016071a044146180c251400603003090b40288284040690554240f260200c20301840c050701ca0102c034401e503030444007244001245402c0c1c3c4c61502400c6411982000810410719044040d52821400ba600342c485107180500007807410001c0021090031651520707000b506054210481c1944902d08807050042494000740b07181c18100c100110400740a80ca000300c0c2c00d022003030391014041ca501800c040003a80504500396038503109084210f040c51192001c21040003003000058000700f007040005018a4080e4041100507091861109042105030658 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 186458435 1250 186457185 186457189
    0xa030507140a0510150501030e0c0402090d0c0311090903131a12010305010b0108100b04090513050a06050115020109020d0b070309170304120905011706030c04020408011d060412081005 81
    0x8840e0401c280704000244e981c4854021140d1a901980051f044c103242603a0240c0c1040d01003180050a030040f100141c0c3c40c01918001011070b024180050042c00e00c0980c08003c01000d0404050107050480e204241c65503000d41c40c0c0da41c3d01c15221210905440402c04000040da41100101211410203031103050000488522030305050980c02907881382e440e00340d44206942c11940141c1c0014007100d500a0035401e00b03001a40702e03c03461103081c0c031840d52040080c00e2039070305408408125174002c00307903030188046041140c060031080c000e0804020700c1000d056111343c014420f01c0c05107903018117541c048c035045840301002040c0003003800041c03548071511080000d0241c001c4500c1d06401612031500d9007861308004103044160207100c8180680c400d0244000c0c3c0c6c010f21545400c00c001a0964019a5038402003402c0500b100001a0080d0011030b02040343d602c190070100320402c0c100111151612040352180e62404295000703032100820b49010040750313200d0361442e640b044c031f00034a0310040e59807580 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 186459685 1250 186458435 186458443
    0x1e09010b15040905010b031e07020c04020d021e19120b0901030302071706070e101206090b090906041e0813030c03020306090d02060a0b01020f060c1b0a030507140a05 73
    0x480032500c50000502072003d103c0c00e215240c054210682018154070700402440d01b0b801c60002d43c7e03030744c02010a00040a861080062501c5404054400c1d91615011a0302d6006074010f14000c03503400d58108880280803024030305035080d11a18014242c407800c074259064816240e195070000445480e03549a101c1c5031038143d2024020342c440e5000b403040c180b07001308411000744280346480458201000b4841d0041e40040d401c041d403103007102d4000301310001d00026503201012102d200702c803a050002c0000c5907280396110060801007511600c1140d590f01040b66120402243e0041800d40c45100f04c6d4840381001000c40031a901c5401e00e6494019404200f815031300c510350041f1748800c415401402142010b0050b0f90700505105c1c0284001908848041d4075100b00409030790a1540c0c482035100c0c5a03108203c00b013081002d200590b0f60341d04240194444039407069820500640304d0001c3d26080c4000040d0006640381c1550361682481d16035619101138542940c540360141c4104c4c1b000030301045041c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 186460935 1250 186459685 186459709
    0x303130e01051206090a02010f020c1003050907050303091c0c08070b191107051012051609050a0303020d080408270901080d080a0e07151112031e09010b 67
    0x86040445585401d042003c8044610640c09441d0840d04c2031246842e03001410451040c0d0901f00300b9000700c11044120314140c2c00c090010360050040c4513010500b900f540c1b1031405181a0425034000c50744900926a0760b1148410b29608504145104030203600c0707000410f40443d00c6460307044407150b0380c2d40320345181c50041d0b0000100c1113000a1301c1e01c4c00901c0101d540d0018030007401c0071a40d8500d4654419104c2c00c4510075140034208101e002e82c086407003440c903034511b0101014100300b5428080c0484c4c071142c001c0602500881c004820126203403034110078a40803694568001d080101c82e09004454858006c0c0c07045440410a010b41a40b08030b44c410300302d041d52158243c964000b0000410410703203200690100740d9a8000380c020365000d941c0524140e900510b0380c940400d175003241c1c01441d49084040e038004401101c0902c511a032035a400040b0205925810003100c0d101e054002c80b00c0554441521659a0741c00b1a903948180040700c0c400f003d074450481000042d04005000100d00205d00d00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 186462185 1250 186460935 186460949
    0x3030f09040f050c0a030c0210062903040b0a0c09030c0e0402011404150309020604091410060306051003200a180905091513020a1805072309030313 65
    0x42100300150800303101e03154000c81c0c00e440520140c1403070f01000d84184240c500020400d6125074004509900800a8042c05007003650b007040250355555441c82c085041c07550310b08588012420810031001c1c550f098034084c0d60001d4040d03c1640354081d04800400d0344820b01002e11214141c000007107038441075158020300100c070300c2503542d01c0c142c8001050b0803050320342c40c00750340400e00c01440161842c80325181c055000f41400600c0340120300005426005d560300102445046c2902c2440100ea01d00001e801603001200000d0800d44504059064030003c0c003407580c0007102007407948201842a0450b900c100580360700b0b80010080005101c045a2140e0340030700100b2038001c4640103c18400d03510f40d00a10120b4800c0000b420701c030100036180d02c00c0c03030720080c001c2c030811001c50310070300034410003441d003640c0186840d43c40c1e0754994410800041141c0c50b40142403502c00002d01881c001c12041c2c114000d0090120340040350300c0c1024041d50003d00d1540c0d05403006214480c5084510840040a4004 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 186463435 1250 186462185 186462187
    0x8040e0a18050c040c0504080d0f020609010b0d0206071b0609150201020906040b0c0f0304090516021c03020d0e01050a0b041506140304020f0315011a04030f060f0b03030f 75
    0x35203198000d5401e07010121856a080c2054500415804508081c0d00724040f02c01007100d4210301002c80d61800f0710380000d0783c51301451a14011458001501d920390400340d800340d550640c0d4116015003200c10001c4080c0e080781108079110014078045009081ca00d00c1400040600d0074615190014074255400c03207000709171810006d010400400034800d050014610007589040100c0002c103030300b03001d6403040c2139505101161000f05480103000003560401c0d2281140c0d1681c1d031303807080c0001030002a28010022800d82c0044c107102480415003c802e92030880000100d404502030880007940490855501c035a6101c00c03d0110140038000c3d00d0148908440c0820300c210b19200b04000c80304100001203208070560002c111650f00b08d6500140340304c02501c03c50320f0b070f620360012507501c440c0303001501d62602400d00c3c603040c8150f90f05056816114001040110040c0c0b00214910318400c0e4040a01414940e03490803000412030303042003003e0003141c82e02258403500040460b1442d0070015000314a41c0f4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 186464685 1250 186463435 186463441
    0xe03030405160b040f09020307030902090901050703110306060a080402031e0a050d110a0f030302130b071101091a07110d050616050306010e100309150c09080a032a08040e 75
    0x204041c1c1c001415420103a50300e4a8a01020001c5c1664a4450b0314034044d000301c0019201402980010f200d603401410310840d51505c8803446d070081100b1a802c0740401e282c00100c6840b080703e0004d4038480c8030301800d07903480c104210805031000740d0001c2c000c0340e26108006500049402c90620140004580310003841c2c400301d1072910b6410301185c01d02c02410070518441869000a001510032a095000000c210200d4030a01742103010b40301c1c1071800007031344042010002d41096035200074503000d801031021f0b00c200c00d081c1e001164042c20500c00c024101c2c0f81c0042d50445000a400280700740cc3c49800484a030380e0480020818104111405544c1504a00104451030320310100c114240c062a14119165250600c0003a00d6500221100e501640310003030700064450007603102c060101e400c076980c000d0b00702810040d07070701819103200d070100004c8491f00000340d0f415001a0381c48489900da1200b49401c801d00700180034424000c0003044a5100020030600454030800c010409401c0508510340585 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 186465935 1250 186464685 186464713
    0x10c0e011d03072907020a030305031e0f090c1f11011b030509060a06060c03050a0512090f100203100509060a030f0804030b1302010c03030506010309060609050106081e07050901030e03030405 84
    0xc4031210f003c0d075a42d00300303c81d1300147e8480d0040d10a072a0b150811310f0b1241c441404c04030704980c5550401d92010b01000c28480d00c204000c9255103e010b583d411101060020000c1c0700b0740c40284980070b041c0d1803900d072a0b0b00d8028003410009a4101080b400000d6201c000c1d6840b902c04100030580d0400f1a50310001c1c41034048040c80040e501c50348041c41030001901c0e140f401810440741d500003604001c0003150945031180b1500840e90555403101030300c40e00d4207041608984034072400095424038450b120700040c0e40d841034000c1e03a115086507268000d441d45010144a034130380f00149034a911a100c80d20110008801415801ca424016030003a034071103085203054100aa40074001c403480311007004c00180141c1e4080e000b51012581403a0108050b10745070011b80141c2101c10340144402d003041d40c04580451140e03c8641243c02075624555540c50f200202c3c64000b000d06002102405d5000c005141c00c1c1c0214010003030040107240000350000c030300c24203038155041030303500f1146a048030720034210390 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 186467185 1250 186465935 186465989
    0x1020309060f07031412151f09090501061404091d060f0103021c200f03120706110a0906050304020f0d05010b010e010503330d031808010c0e011d0307 66
    0x900d000840e402d01e061001d40c9500b010200003441c80003071f8190700c03032004000d49549905ca800520856242080b901580402820300d12a502820314414078100c0002085071040003600d40da0103980400500d441e082003803a50250111045190050032442071000b0004010440d007881a400902612090350451042220120441600640c041c0b8001d540d40301044035540d425441c0d03602c418035070320144d9504c00850208034101c9443d030b6160003412445000340348614020064140b0600040054a040b007180f14010b01840411000044400e207040c082c0300d0048004507003140c0010038080c6590f148100254000500c1e202c2281d40c1c1c3d4680487c40c0103542c01090301291800d090074100e00350b240441c00d400503c592640704000c0c041300c1a10139188084441e455015660001d00008000c00e01d80c200941400c0d4214908440354010700000588240306100380c80d00f05070030744d844881c1c004402d001110300201801d2151400907018200354100e6608105403801440d14403c864080d824030940c103845 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 186468435 1250 186467185 186467207
    0x420040609080c01090611010609020c010902132a0203120c120702060424090203010903032306011706060c1506100302030903120717010305060f01091a040b01020309060f0703 77
    0x100d07501c18120720070f441c1c0e00584140c05407869494080b500078012a1004e003d4465540420401480000c03100038110041d01b052085a009890107454521a13400c2d00c01240d101c040c1c2c1c40311140c3c4001c600100100031424003030401c642441103908240c0e095004c1d50000300141c1c1c070b61056000024a00071160b0008690300e51140c954005031103245450f072a9641090100166a0007421000b11960308001d0075a00100071303e07402500030002600e1700d140190041c410301c0d04441c00326074000f401400240d0340c0003a081c400d0b0750603500c2d14078112603185210162040a030525921072024071801980100401400c000042480150b504a091501c00d11203403c440240e0001050700400130000000ca0000480d246840e110b0318500c1c8990f1114021518208040b40d4a02214078250000007400000148240600007504032021140d9032104603004455079840598a401902440040c0a240641c010b02243d5010f0060f80d03d4181e50a0006400c1d9100305080142941c000c1084014140c0c03003461581 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 186469685 1250 186468435 186468449
    0x2100203090310020d020408060f04020a05030a051009020d020d0b04060b1509060a021609020301032d06050601051b010509280f080405040f05090105330420040609 72
    0x403406400390003083d1101141041010095000200c2d004020600d90440d002041e482054130543c3c184051562003451040d6005d0b8411004904041444d140c0840c00b443c1d540d500000500031b620824078054098852a60146c2c0c1c4400350f85805405030721089184003015100d00360f4460140b41910744101100d1014000900402840d80fa0250541780c01d82202c1c0341c88001c60b806911554480002c03450b0042d0080c2205052494800c002400442d070f0300a107050780d1150300c010a590100c3c05540382018010201440002c1440c520840403526030390125421043c1854100c0c98241501e00302c44240c03c950383c8a5456030b55030fa0403c01d00c4803041c803940b03040d401c54482115161072506008000b50b9104a0003410700d4401d00301d10300802865104550041c100a082444022941c60fa518002c0608aa1410f459400d00780041c02580703403044d9400e016508842d0a0001e000c545102c2040940c2d20214180c10503681c1c014030300c070030304030408204844002c001d04c00d030b559040c890f00800701305c46988111 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 186470935 1250 186469685 186469687
    0xb13271109010906060c0b19060816090908030c0a0c120f17011508090102070f061b030504050303011205100504060e102705010914010f06080a020a1208040e0c0702100203 75
    0x1100b80c2c0c0c0d202c000c11b460a40c001d032016841d9114211180c40901740e1602c100c002501d00040024540804036020421380010310390300400d603580d415204260b071460300c0f000f0070513242040040c440c1c48104c000f0307041403205454503481c0b0306415500c07840c601c0c15003100040410004080d03400840c0e40701a00040703442140080341e00c41d500d000d0402941c4803240b0410760604c138a1341d000440b141c00135416591140d030025208007401410f414094002c03c8400c03900b21924248200e0403000130300901405020f6076100f0300551440c0e2920205081c416806a0100c17940c0c00f500d0400c40c108203d03406102e0140c1c0c01031400003504464200200d24102007441802c0303500d070504a924000240c1c01aa5040b43d42510759442d00c0b8040c6450424010030440c80d0003010902180316841310044150b00c8101c903100701d224100700c0c468458108981e205180a0f000f5402003aa9100380b081c1d940740c0d080c2d0505140302d141c40034101600c400c540c18044000315485502c4500100300c132029440c12400f20b100008031400a9 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 186472185 1250 186470935 186470939
    0xb040605040e0d0516050304060801030b010501110c100302040b0c0304141008040b040201110610080d0e15070f02030307080702010305102d08121c0b13271109010906 73
    0x82d5071610860b0035280300380440032901c1212010a8480d1140886e0b020058980d901c4d108c80000d003c54101b070105942c0c05134802e0000c58154001d4940c03804041d00c0304001c06a107002c0c130f400c20031004418079030b903420950280400560f0240c140d002d408101c0e4008080d58840e41002d0019022080150340640b003103860070b0070b065503240c01c5103072030b604a0341040b078140450f512800141c41c920038108848800e4401c0c10100000910010081403c0c0c030b0041003501e0040807440d0003241c113074008540c416844039001a20b40d90200d00a00105011341c814040543c01090079000642103801904045c0c5241c07400040f03041c11036034503200d815484081060b203400b510341000340d003604020900c02080101c1d045900342c1d00000f138184000f2002004541b0842d40c0741c14101d401c840701500001c82c10030703901c00e440b014005d8880c070502402d156001d014040181c411000307100400904034280d0321044014202810790684a40c26087c032480750b00490030f2095500445051110300c020583c0940d041c01e25010003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 186473435 1250 186472185 186472211
    0x1050705030a0209031906050f0c030912090a170f120414010e03100c02010905060604052a091503011d04030906031109090411100206090c060d09060c030b04060504 72
    0x141da400044400c0016118861000442d2501c2c0000c400103a0140d2422a84003c00c00243c0000c1e21914420904940540342d44034400958007042c0d66143d001e070000301000c840b014524002d00100c0e14003c000139801c5542e0710000202c0380600e601c80c1441d81000e00e4498440008100402003101c007900420715040c901100c0740ca20320b598003840b90410002d0b548400c0195001c010390f0000311882d010030000e42c291580068001c00c56030b42c0031100d9002c5e03071001551501d040c3c4501032003007552850440c1d80b041e0750602c00c8007003c4c0c5408040c000e190140550100764031040c0880010b000d144032203a03075030750404104000e040000c01c20b4804001c0355108010020740d02c100d02c0d00c100c840d00d04010804254004a2901602a202c026600581c1c40010001400140070580b080100c0a0703070180c40c08171240300d0884c1c4600c01221070200c6a480b0340d502000e982001c0d001840c80b2400c4c400e000074020525600c1c2000d98991803410800070f0b4642e600340807285041c0c80752030b00500d8200c8040280001c5440d07 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 186474685 1250 186473435 186473437
    0x7080703080d090f021e0f012f0f0105010806060112020915090a17030a08090325031709070f050303130902070c170a0b070e06190207081006031401050705 68
    0x400a8150311140d00c0b03002c000411615560595004111b07542078100002e4099a01100301000c9124070310000c0185c00c25401003d81800e1642c082d000d1030314084c00460190704210940c030040b20140314185810011000a2040f240271304101c00c042c2c4014244500010f2042100950784003106204002c048410354440d50400c5110b803a512a40740c480c0301c10340c0000c480f29a298031000c0c511030000c0245003031b250048024107000ba0305444907490350b1106030650796640105400031250160507004590000c00b01511840c045100785007900311214081400702100105581c00b4645621172a020b00c1200d0441840c0d40103403c09074019414942000b100c1e004811440c0301c0e00840c02e80c0011000d0a02001c040b0440c06400c403820151030149003141401d03a0307203401c050242d58600300b00c0013207110b1300d100303901082c00e041e002007143e0704000d0f07600d0700a030190707105013115070542c802e06c0000150340300b0500420f9456500382500042207032450409460740389641104c0d00242c0d1620040200c400e41000c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 186475935 1250 186474685 186474697
    0x40506031503010209040903120f0b03060a050613020711031507020d0804050703060501031b050a0308030c0a180b13090e03030c07030309081602120d02030f090d0804090203090708070308 82
    0x81a5091058070716010900a01c50364080720b4119081c11002e1083c9904010090700700300c1500c17000c11045880400600c102c403c0642e5143c0d240c3c00400100381240c00c141c1085402800c0140074102c510707100c29440c0102c0e442020100c1d522000c5156911032440d05000c111f508140320203041a040c981b080000303484144d0340034035105100c02c0d500401c0038003e041051002641c1d00190812055071a400d00170382c180c021907420049600d000c0301c0032a01342480f5400d0000c490b4000c90890a5031a0414030100d550000d40b09102042600c0440448001c400e80d1004014058245502e95a010300140711265000541050507040c0c00d010b9020700c0b008000084a9101c0058405240c039800145800c41c0078000350322019000b404081103a0942e00301903800c0303c142c14400c55803c1488050300c2141901c50a00c03290150241e04244145002040103900412700c16000400c002e2289506035280e501940040d04481c0701c0c0c96020003005160b10301040000d024040c1540143b038842d107150b40f4034002e84120 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 186477185 1250 186475935 186475951
    0x9010c0503161e031e0924090b040b1801090c030f0309083909010e061c060e01061d04080a031b170c120402040c0203040e0702030a1404050603 63
    0x29880d407400c1c144925003510403940c581d003650980c3d100001004001d4800e85403d06442c148062500d05c5144180c0708411104c1ea1019081640302d41a2044541004802540103082e40d10b5008a80001c2d40301e50540d40300300c1c8103402007400781c10116900018410390310807100880c0c2c50050381d00e000c40c0303800030004101c0b54003c42200c40c0a40920703048600482c03648c0b04034410710402c1400b241c3c50b1100c402e14003500304080040181202c218003500144202e01c1e1030300360002c80d00c400600809148407500c07584844044c080c9041000342d04103541500c0c40100c0b003030710307034540c3c958008210076002c0c0600002040341558a110f1050140c41c20501103001402c01400b5840c0010b51b402198000e8024400c0404481803903200400701c40ca010b0445011501c1d0a692154168001052196408181e035080388041080d40010f80e01ca41c01e0100400da520848025031000b8807000a0900d2017101c87c41c844c0940d40c0c095034588100200c00351200c1840c42d15442c08180a21040c0903d4980f441565448118 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 186478435 1250 186477185 186477211
    0x30209040204200a08010810020703050d090633050604061b030c1a040b010b03090a021903050313080f0303010e0a09030c021906080f0105030c28150809010c0503 71
    0x103c02212041d07200d07190031402907240414850301040c0c000c4802c03412030724071700d0a0314403001d00700410307000302e11990900a000c0340d420f0040c0c20f00300802e40e20042c4c406100c0c10001845d02c04600c1d1605100403800022001910b003105440b0040340c01da075030300740102000c3e00d10034109810b2540c081d140c04a40c1640e60f0044c00800c1c00b1038245840f4203e82c0c80940d405c040c240030000d10b0740780b03d00800c041c00c450541e01c0b40304241c00010814105001c071380c80380c554603010b4005040030b41e0070011101e20340f0f04107080642c9111404000304030188020011340a00d002c031841d085242909040c240b0070040e05003c80790f0400e00041081c50251030b03106031321081712900050801c2e56468207881d83e5031003a0003e50810000d4007980e45486500715180305450603920b600c90036958140c0711504e0780000b402902c1d050b0b040162041000e01702240300c680d0060001d460f4402c8164150b01012200c00c19900140769541403022826441c0d0308800d00503084245903000f403050321f24444000d401480098882241c5a50f = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 186479685 1250 186478435 186478451
    0xd020c040c0c031d0a060302030a0e0d020d050f130e010503070f030302032a0703060c09080a050a0f170c07150815060c07120803060108130c0608061c03080405010b010306030209040204 81
    0x3002c5040c0d489013210007440524000d4460000900a400880b120015980392a03901c0340c40c0600010543c002034a03d0380100825029101c2c100c83d02e8104480d03801c2444c1c41400800c042e0030082c60880007801c5d0b0940f942d8030301e40c94003040510301034896215501805000b082032000c83e90200844540b20111100300d030740000e984107000101288031070380f0039507402081070200402c00160440f1800010f540c0c0c40c030760001e4aa035140e9444201802000380321303610000c0c03001c00107038248804101150048910900c6007500350720510305c0c4e5100125000e40b5400c16a41400403000401d8001c850b1907852400044d2850032410610644030002001c0d486202c0104e03041103251000c10041c8003505201034142801c11840c0b801ca44290003d0707507418085a1140d002450720302840d5a107101c0030350001c0200800524000003501d1004018141503040850700e10745100c071400b0080c44040c058460381c2c40b82100d20305800c046003120020b040b903904250526104102507a03139a401d55802c030f034049034001013081e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 186480935 1250 186479685 186479717
    0x311040531020f0f0d060903030b09070206070311030906071103040f03060203010504060503010e0d051806030c03070f0e1e03010f0e07170325020102100e0d020c040c0c03 75
    0x45003284040041c440881a10842007000020090100d8425100103001904100412400d14a19080705402130040c0007130b240815001d4005c12901070007414005a14000303800403a1500c4003c641c1035000d68403200034018902d5043c824170303420f600c40840c1e00307095051021820b0346629002c1c00a0341003282008034208100c00a000f107900070401e0101c4002e18540da86040c1c4041d4009202c0c8074880c52601c80006140d0406004c0c81c0b01000d0380b403019000d2400760440c26030302034101c046115000309081b00e0b88080d9884500085025202c0d05910644902e407102d002021002500c203542c08115901020f0400e07038131110700c40b800b51156071070240000326503007020900510550109a45541c00c0c506e60228801c0085070840550341e000010208007001101207698034400d01c500f00c1080313958403c0c03482a00203120010018244144140d80340ca03202e960011090307588119007445542c00c258045503007543c040009040f5160b0582d8140003404100002800d615641680038081c040b50f005188080 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 186482185 1250 186480935 186480961
    0xb070c050f0303070e0316050f0d0809030613020f0321071a04030e15040e06060a021005160905150d0c140a12060605031003030f0c0206030405240103110405 69
    0x410900001c60f5100d2820082c000c0c110050319001c14024020481c0360b04955045000c4041503420181034050341c01410390a10503240b90303802c1c0555403000c0c1070100c0340700c80c0c0d01407180c54001d840103094906241220300400c0380b4001c402c80030340d01c0b03a80f007100404600d81c1c1c1c400c0b488080b4001c1c07001e40707615000c1038100003c0c0c0703445100364181d00b280c211040208058000f040020484015a900e02c0506444045940c06200f240113418190468000117515458035900500c08800144140c4400401402c52501561019100c000e0700322f41c2405c040e11901c1c1d200748110001d0800f102c0c503c4c1418030140c40000300e446a150740760200303611003030102031050041d20319048090081c40706565621a405d4028002941c4520f5000c51600b4040300041651040098034002e034150355011141c649141d40a03203241c0c501d112220184200f1140c7e59003da5128009148500e0040703029010002c4080250b26107007020f440e40d4500d600c040d03001480402d03240d0001c403003594400d07100002d007501c0f00481c8400d0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 186483435 1250 186482185 186482203
    0xc1401090504110a090b040602060105040c0e03100e060606120f10030209070206070f0e1003050901060b07050c030d0216090b0607020406080f0105011a0a0e0402040302040908031609030b070c05 85
    0x103810310b01005a040311641c0200407084e0b03607942e4510170b0303921102c05c081036220382c1c440c0c1001a84118018002ca160692100075943c03110b08108041b0b0044101090501038805082d000440c0d640f44001e100410a1051507805401103030f485141c800382c0920140400c074040c10b403801510880000940041c50148594040c6400034460010f52070548002503840004075076810000708220000016180a6406c100020030010000041c1d030036a40022401480003c0400045649641000414600c4c2c000100216070003080175018010000080c1840e08802034222801c5600c4103000b010a100c8200c2404203641a07404040391380100070780012041c0c0100e0a0195100d1725051001466903000a80440e1484e4440020320690707036140a101c04040c0290000d184413581006040a4244900003061000300c2c0100018106a103940216003141c0e4801c00c101d42b907480000c00e0208003100e000400031003503180d280404030541580d0780c0b8a01114060320b014140825032603600c0400a0610050074 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 186484685 1250 186483435 186483439
    0xc08071209051513060b01080114130b0a0f050a150503010e070207030b0a05010302010201140603031804020c01060605091507080702060901020c040f0b0a0807030b0601051b030f0703030f090c14010905 88
    0x10f050030074042000405400103000c5480034907001e041c41440d40a00380141c100d40000c241464610741c190103000c04014640710a8030724942d9041032202c1d130340c0c0f140e24400280c04a2201c48860606103428000d030020b075a00811580780d11004803005141e80178040f2410341d00c00c40540d500390313140c0c1d2005910b402d45075040101a162100708114800d40c1c55444035040364001d0b4002d106401c008405031101c4001980e0f00c0b501501f040126080c03410b40d80846d2202840c010304010719254001441d039003104c200e9000400099000a140e41e00d500d0079440c270a034000c8248038494508000780d40c85018074460908002c0c0101008680c2c82d007541e0007848400980b0300094000e0080002c800124001010050881032040c440b0301f2001ca032407900000ca07041600e0f80455100782544501c001911590490040d00c0022103a151000b910150284003505005400d019090f844040f1458081c094407541050302411500c6c20745100301040409d82c04000702d500110200044040c240012030303000d429604030507 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 186485935 1250 186484685 186484723
    0xf010606120615021e0705061c0e03040f0302040f0207060f0e010c03090519080405060a050909011208070b0c040b04081b0906150d091e060c0807120905 67
    0x2628540210048204520740401040302c1d6880d44200f4103a5034070380d14444016405225203254641510300202039021401c02100e4926035102d0004800c6e40c00340140c81b20360460500791544450150050301100b4036003801460030107060001e619024081c500c0082d05c12a280d038140c5909514942c11541050313001441885002d81098185024100c1c8140d013850075843e046603c9145c41c03092040d04070965011010b084082601c501c801c0b43c03101402e005980700712003000006080c2c0e461744001c1107804165160b194403905100100003078190140d000c0480001c2030382c030720000500b2400444a03202c0c1d1110204241e52500100399030540540e0304080801c1c18006008200d1440c009040080354105490f40034190100078144104250107030744190700101c811001c0250304208030701070403080b0307400040001c4407052502c8014682005842c0001d14200c039000120502c41c86004080601410b0b0622600742d0801c800c0040c900b048040000c140301c2d83d034014503404c200c810301980841d013a080240d0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 186487185 1250 186485935 186485939
    0x20a030209060403051e010519020702040221040b10030b04060e070302120309091f0b030916030317070c030818120304030503060922150b04060609090c09080a0609050f0106 76
    0x20b9480414485030006d88020b00c0c6103404540050184030300c1501c0340781440d00013010a00100000e0b400041e012030f030150b000e000114400340030a032450748071000c01e00e0725102030500f820501c01074071002d0520035640407542c1081c00443c2c24149281d4005d6801072000601c0c8421402c110306008080d04001d50018480c146095850000800780c041c8072000c0310384410680314100049100481c0c43e01e215060078446908001ba910800051035000c0c122100f41c400c0c500941c0481021141d10382c0046001c40c0521207441200c00030722240c1940a00d950410070b6000036980c401a128100c0208200c40b40030040030f4901c20f003002802020400d0011965048e16400c1c1840c01a14a0f001201d41900078a40d4800003044584843c08040c544c94404101c0414500203880e0055110480b810095855803a0562a4000e842d1751048c04000c0105a9404c1c038201c0c01d0210042c1510700500680007049400002482482c1011800c14201c541c024000954074005207040c4c2c0c140350260021501c1035183c0480 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 186488435 1250 186487185 186487193
    0xd020909010608011d0c010f020709090b0703140402031e1204080c0102060c28030e0a12031b0e0f01090e01060504050a060809100905120f130522020a030209060403 72
    0x10400303440301c07075009001c2000761103655800c00288460031803696000d84106c0410354040c1c118410b49110610680e62a075132034100d0300f415030b81e80c0d06044803035000410030400c03110350500c5154800c629400309803410f400d0980001c0d50314100e00010303d1200b48040040000340311304100c001c0c0c80945c890780e51a1650382e00c442e00c4d03854042d52801e89015005010020300c1940f5080d003110307a4a00e02c0410305483c6000ba010501750011842c502000b07059442c4103000000c881000700d082203d11401c103021200215a0004041d039550441c0c50160841120341c441c001d6030850a64507500b01c0541d062001c0e03442c8000101e81c0c4000302e50100d0001113880001152140d23119004201303446054542d00003199441c80c0032900e540c1c080710740c503c21740c2007050301da143d80c4000c3d0440b14605000c1c00c12910814481d1814603026480b050304100a0440002d4072040090641814402024101c4904545404092606083c0320035000c40f9860a58002007903188940607505039002002c001c3c0185460380d4072490 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 186489685 1250 186488435 186488441
    0x40b0a0f1e090501050105010c05060103030503070e13022a121e030f041b0f0b0711041a120a0305040e19091211010b060a05160204141f030b060d020d02090901 70
    0x2d401d40e455401c10001052a500030342c1c504030f181e41c2c054014030781a03185031000c50304c0740c0014001d801000328842c0ca00d881580c03400e42d99481540300450060f035403150340800300f11030461001100300100c6c0400344180c4400300851200c1e0740c086018203056549100d07852801000004640c0c01301e05150110500441c00c1c140315030f140c4200d00c14041d10707000700007540d07500c141404248180c40caa044400d0051240300031900150242500c60b0000036000e100752000281075400d000c170004d000001c800846489845c2c890a00050701c030b6294054141c40c451a03c00400ea48654095410400180e0b4085100304080c0740c094015011140c104100912151804040800c40380c001d420000e200607494035051101031140300c18000e401010310f460014402822b07a26908152590209010502a4540542c4507030040c07054000b605404480c80e440c11220307000c2c85c61054956000348404e40314060000500d6020820380000d000c070f0b50b60820410740d1000404d0700200580080d0401d10040c00c0c0009210150 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 186490935 1250 186489685 186489701
    0x206090604080d080f0411120c04060801021e040506030109020906160b0411100e211b010f05120406020306060d0905011b02010e0a0b0c0c060c0a0f0305040b0a0f1e 72
    0x2a0700c0629980398102010030486042e50050500c4143d96240c40d0f50f82383c0010041d420404a806a401c01003001000070101e81556104000c02e035000502c240f8410585400c480300480e03001105410b0504040c003092017030005001e0302c400d40360b0003e04401e444e920041a5680f0390307800212203a9003c1c161500ea590b400f0300340c504541c01ca25410400c82540340c88a4808407042581e5030300360440680c2010022110104e40c40c4448501c0030704148140410140700304200c5640d144100d8007018840000103000d0603c841443e4100300040c032041050481e80e6a02e1600075411980c0540c40303458150014586110b107080340401275280000010401106400603203401d5082c8010030003801080078142d00760f91011110030040e421040f02c20000440d034000c00f58100c403641d100a4240004851902c1ca8424191a5000341010115808003030039481900c04403001c40610341805a4101a900c0403104036010b0482415251104514007070001c0b1035000500400040c0d40c121f030014103030001c2100615100b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 186492185 1250 186490935 186490937
    0x920040501120b0a1d010221010605071a0408042c0121060203100e18010606020102040b070809010c0503041205060108030304020607021e0d03031407030c12090206090604080d 77
    0x400000c412800702c4511141c036420801e803c0655542d109040000c1042d01900002e10004e2880c001c500e107024406410191016904c02402e40036001c0a07104030303541644000d04015040142c04000b079102c4940480d40b603101883d040d4581c4440c502004140603a40011000685462440f6508010341d071150440c00802252b000007641c8807100e00310304c3c007034078070031170542000301076a00c00050f200784d0085521104648040ba5025201c00c581051986e05079000700081c840010001010402849800010070140c0001c5103801d207042e085c090b0a01400e003000d0505200801c481000307901402d0a40b102d55405800d03030396556181c2d040c0422901131148162518400c0310004a9001000000c5a005030727001070150741417140d15400c0051441d80030161001c0381c200726444a41e0b0740c407000c004540c602d01c42d4a001c140c50f4950002009502c400170880b000705410842004a0a90090a801c100b0103640c0c1012503080d0307450002c00c0c1070740300728030b07402e40c0020002400046081000c580d0b1030065041d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 186493435 1250 186492185 186492191
    0xd1212020a0905010e0312160303090c120b10080d050c1006061e0305011208090a080604030206040212060411190e04210203030f340c020a05060a020303041401092004 73
    0x160500303041e1f484580d410700c00c190450030803001901c02c0c00804000d602911071701d00821301020b41c0e0f1f12080034940c40e40c403900702802d502c1c02c40d0701041200011150320505084400c0c2c1c5c07203450304100c01da40d5480c1c11042004d0010000b59131105110602188448a8099800380512941d502004140303481103c90780041c04d0161075100d00b4180b02e8015141201c000300c0c20020740407030645584084ac0d00540740c456001564490000b000380c0c0a012080c440c501a80203441d180c9800d00500243e41010300320900550070400c00c00002591a10200e21106016114041140111220f288240c1003a400000160140000300405c021071108a094481280b0089881d10141c40340f080c1da50b40001daa28882c1811941c0c0011649540c08103e50407a05114046258016480124511400306070700d004000403070684400702941000820280140b4060303540034034041203140001d45900000e030009001c210605120103202c03909401a030030160b08601303c1300c031409002030b18070740c0c011034524841d0140742 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 186494685 1250 186493435 186493457
    0x6151b071a180103061d1e01120312020919030c140d060216020a030f0c05010f0e090402190e0414010603020112051b030a0207030305010506090d1212020a090501 71
    0x22903040034007a4450004069030601958010614035011045591410140c0d41c040026002c2c20591010250032403107041a812400c11018080c4c084210103510080480a000108074801e540311a2410380741c0c1502e80802c03840300314492140a4880c1840c02a07110715540e034504918014001d1100071240324444146409588426118400384041d60060303100200308215004910729400420034424219520301b2111a10390001d8107807a240e400640d0105100c80b51b00701001400040310010700000d0078140c0740c14030381d01c0000b0f103440e10b020000c2e8002c00c0050085011515036a0b40d080c0a01c0c41100004c3e901503c03000400102d9208071401e94514030140c1c01d01d0101c20061046e201034a4043c4e641610720b0020909490151101030040700e12818034070340615900042a001e1030081c0c002c424090f9655049090040c150752041e08441c1c8980010411804036643d504401d6064690254485c40107028212042e1801c1c820b08a20101c0f080c0006800c075259980a251441a1002600c401980803 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 186495935 1250 186494685 186494699
    0x3050d09050315011202090403050c10020414010207030b06010c02040b030706030e1014070804110d0302030414091330030f050c03090a06050c160f060c050f04030b06151b07 76
    0x90700a1007800c1c0740c098481006005810031f200010340c824000d0601a00d80301e41251010f2401c01e4000d01010b104d9808182400f40161041081c140c550091000700603141c110340342c482100310b020342028144181d17200e50070111b4481d904040e5042d60014203685016035170300f0015001d030607021421040c601580d60014052003951042030021200500342c06130316515001c040d01c5021001d0000d07075072900c0c81c400800f0149d44011101d00114403a60185440d9881c21b2141c0c1c0308076904009280c07280f0300e107804116903140300c1e948002e030558104040320900c606c9032021a8850b061090046101075002941303840c000d4058108100400c0ba5607000c0009503a41e203168441404103a0380c1c440c06401c044081004504240c01041d04040d0f09041c0358070f010920044440714404125003103036500e06103001c0c402884010b00c00e15401c0038450504900e0005030103464012803042c0d0000400d00d10081010440540701d100140d54404100c5c95241c0c1e5480c50391100700b82500700d035008640301d8031032000f02250341 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 186497185 1250 186495935 186495973
    0x1107030801150903110622030b0108010c020a060f0b030610051504030302030a0f030e030a091a070206040b0a170a150501110a06090f08031008010b0a03030807031503050d090503 78
    0x240e40d0f9148035503107003180d5036400e45000d5010b0b6160b00c00e0041c0521640d8001d070508244080d02e181a6448003a4038601d4004410326059000c070703680364945060054480d801183c20002035078855030000325802034190041c01050541c04460705031088904102c03941007a40074031000d40d00120b0b138405003400940c1c01c500403031055000c0100180c20610a590506020b420701c08003600c024100803980d86a01046a45144c01542d0006d000071010001001a180d61284400d403003c00408042d14003403c42d0081010780c800c52050340324139440050b08054084c420b10b08010b0707034a02c00d0040601801d0440c1110043c040040d15108450030b03070b40c0c00080641c0119070b441c1c07807410310074040c180ba00703420b40f03541e4000d141d101003c4d55015403480d04200007030038450082d80300340003c0990f41d00c5542048489800c450461010b0307801004010403e0000c6900030b91043e902040515000c11041c0b00802d204203400002e40c40200680f04107601c4149a50300500c1040558206404440101086030841411 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 186498435 1250 186497185 186497219
    0x3120203070c03030b03070902030718080d0c020d060e12040504050609010f090f02070609050a03170f1603020921010b0409120c140d020105060f030604030e01110703061107030801 79
    0x811425142c200010b070194118650070540103060b18a100c0d80e5102078400e0780e00894803900007075140d00482100c03040b4000c0150142ca26540240010041100702a00c2c00c500c07007801900c204200c00d14081080000d400a03901d02c400e840030b6400d00c07954265003e0b0f0581081c00303440e11542c2002d000403800d0914480d414101e4002c1d0041c5010030740345c42c125000034090703001e120a6440d000c00180000c01d81030f00600343d80d03d205000070151040181001449429003400e0004042285400c0c031844030024403000b03410580d000107031513511042c410140c0c000d11480c100580c1003642c0ea0b0800c1940244140d94100200a550007070011021032400c000498182c0200149003e512000901d0f00c14416034421000a22800c0146a4038545d440010714214940c545500180e4450b001c005050825454100c0300940c1a001004241810b0b43d028001e040030008541c100801d1039140411900e041041c1d0004603002001000000b203411010606540308030f60a83c04a0260000060802145c64a4543c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 186499685 1250 186498435 186498437
    0x6060f0f050306151b150105040b03122502031009061a0303040b0a091e140d0503033c0609130b13020609040501090c140c0706050306041407020a0312020307 69
    0x100e500ca1180342d0300340d54101d1030100c200d401d000c410317103005c903c0100300c031000d800700420303490400b98503000420050f0b8000443c2d150103138000c5584c2d8003101e0003100c10748030190200c010b421203c0c80001c281c1e091a003003100003e940340c400c00b080700c02e600d14070340d100410482c09500b082c0404840d00e413048003411400a003940e01513008100c10000c0304a5a0302500c11202c161500000240ea550346e07012014040c0742c581448216841e504000400d0000101e0100c41000c0c0c5030050340640342d46980340c903408020600c841650400400e0a040a9080a05c500f1505000c82d1866611a44c4c550300b2503000f0100c83c0c0038091f130041d6000c510354080e200d15140c4059030200210029588040060154820070b282c00c982044c020722410b03d2581d120301905010b04019200040d90030181ca40c0101080003110840c4800c2c00200100d213000100418501d003030700c8280c10401c2d92600c41c0d1010030f0042000700c5480003801d403a0400e2200c0c07680e0128034a080c02c3d000b03940e9101044820300000c0120320090342d01700 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 186500935 1250 186499685 186499699
    0x31207080412030e07180b040c1101180f02060a140a02010207110901050916050705010f09050c180703020c0a05030a0201050610090b040e0406090c260f03030406020f0d06060f0f050306 81
    0x100c02c20850061001c010b41d031b40414903990f900b0104040d10f904250703081c00f2402250860707403400300902c21301e282c0c0718001c207408003504883e40720b610b8103d10714500607000b07080000d8403901c094000c01d1030361881a040c001955580d0b40054009000350030004045a00e150a1a2012454505200d2960681e880104200c003903803550aa94501c1d241d00601150521806000c0107020170f0080c410391245100c103c00100c4c0746861842e045040c0b0f1588203805104c2e4940c440c08039124800c0f0380043d51300038120300300180d54841c0c02d60703824a0401005030040541c07000050080000e541034004902078801030f0303808841e0301641c80c0140d50384180c0380141000d004080c030007003125020707010032240c110b4090900041d8991141d01c5200040200b0b0b0441102001142c6103811200400e801e91042c005801003d4200803d003207410a403a440b01a001038190394001c00c5002c42000e00c0310807581c0210100310200812591010082c04083d084440403003c14114602c4085a0b0b00540841340718800c014081 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 186502185 1250 186500935 186500939
    0x41503140f060d050303010618050301091a1504050109090b01081c1409030604030e030601060e0a031203151502010506090f070807050d060608061203041d040203031207080412030e07 80
    0xa01e8201000300380c00d500494100065020402c10700080d030203042d1a503036244021607910b80300b003510b1000f540000c1c082c0c0c1c9410500300107d8003054200070304806940803440c070ba48503880c00c4601c1030312072188140c0c4503103040e0000521591650180104c03511507111140d8a80e40e03544c0903600da000d0b401102c05d19228a04c4000e8809100305085592001e07048009400d00003260701013450301d40101c8045011070701c3c01100750501d14040020a004011900e40b04d1160240310b004160b4144291000402c1c05002552200030140627810141c40b201104010f48030160350f9014050209040507610405540307020301040d401d0400e036200c031f072051039100342c0032040392101c04044818217070081205007044002d010311921410140524002810701741d03100d08903805c0840401080d424150800f40040e4420401009010900c1ca94400101e5585085640981e107500103e030035032055540050341d195440c020810040d03000340c20706000c0e5024910300b0040650407071055080703460816109019600c0030f002 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 186503435 1250 186502185 186502201
    0x903030507060c09090f0b030f1f0e0309030102160312091106030a11030126060f070f020106031a01061d010207120f0506090a141c0507020607050a03030204150314 72
    0x70200c421030700d4074414499959944800321202042d005510940750087d4122034942001800d490901e400c015042c07140b5083c40c3d10a0b43d905910800318500e454280f00c00d689041801950081c000c00f400075592054050442c100c440107040044011800c4810f1400e100001c0d8800c41244640c00b0032103a04042c00070b010410203800040241203010385444400304400e10070009903008103070211600079441040454002c0d1000341c0b0b000d0020640c014070400c102e9410216401da00640c0350305012268500b20f8000300d0140c4450f41019280008031188409400500c28100d41280c0040d560000202d90610304091481003003d580c50040c3d001240a020034200301c50303002d110030302c640c1b03814079440d82d10780e81e460405c00110307110034441c0c00888191050120301c54458140e40c20250240410340018403840109036041c5174a0400c10102046100454543e1001c40d038060380c00c281103984140092600801960080c040c10801c0362004800d65001d501034080c42504841050640c8425603030409 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 186504685 1250 186503435 186503441
    0x40602120304050a0f080c010c05030402060703260c090406170604020f010909110c0c0109030c1202270103060b010504050307050f03070b040e061903110d0302010608031c0c090303050706 82
    0xb05982c2c40c042c01d509200022210100d01001070310607040c66840c1c08107112024210747d80c0100c000103108041007004010fa990404582d404c03540b42c10021003140d200d04550188400302c00c289190700d609141842003001004002d000c821034221414407003151a803503809005912064400c055a0004011a00515140c00a00b03040030041c036020001c940d847c861641601d807101003519601d84000b070f406854803800d00c50550110020309210107554176582e215928141180301d500e04585562210f0400c550762034401d01c9075a802c8640500905d85950414442c075102072008480e45450100d415100e540680151012148010050491689005c3c14890142c0c504130940c0d80c54007502c0004150319501d03c1c0a400540752411010005140841c10300c0380c030620010305030800e0342c0c50003810800208110361142400d80b060b40d5080010640c2e00e030981c003620a903088020769000201c1c84050a038412200380d600b2021041c000d01c007030425041c05407013034540c500010700060313004c000b1200401c0c0303250 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 186505935 1250 186504685 186504691
    0x5030112140d02010b09070c080703210f0b04050711060109020d14040b06010f180605030a02122e03020d080c0c0907270e04030f0e030a03050702091501050a03150308070507080d050406021203 84
    0x40b120300a565690080412a443d40b9018440c0d02e035142b80ed9036681c02d0130302c900d607408075150400c021500700c000d000f2541d0b10814840d021000e074000071110303140585c54010a0080686241b54038041c142450192440c1c034084036140d00241c202d804004003244149a80c4414402664004007103504007107080b280307a840100f013900490b80070091100081325512200c1d102c1c980241c17420000868140721005080302594221521042400c0280007680d40d44086074806544450300c00e6446d055000410300303240d00c03184c074a54003521140410a400390454400301050b40342e00da404030141c0d01c014408000d00c009004060700700c900040020002409060320f403082c603006003882060007000c000064035000303542c0d00440000310301044080450500001c065082186506222100074a03080000c016004074049081015102d45842030803c2c0c02104440c0a5608100e0700ea90350781030350030a203036182c2d501c0c4180001441041c1120401c90300c0b0f1401c0d601915000e40c05000301c10181032030310103d50005 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 186507185 1250 186505935 186505967
    0x11d0a05120c330d0902180a140912070c03061802010e011110180c080307030e09101203050904021b0c01050a05030112140d02010b09070c080703 64
    0x6840450a5680c126405407880184801841480398003010722080c030a262a4500c0700f00b05103c459200b2082e4000f0140100b54000b988548401c81140b101000d01940c00020b03411603542c0010b02170400c110300c0c400c0d10440204c002070084214610880d0302e4404120340504043d00030f0800c214910064100400c0741e42c4c0201c0450b200075450780c4941003141e140c1051040002d00d1400e2050455812032200100c084090030101200c810743d03403580342c60303100e0003c0710f4512580e1841c86003440102000351540340e54110784c06000351519a1045a565401100d0035400301c0c4c0e0b17003010151031345032056485128070f241185c03184001c1d2401c1d22128a0100c00e05084003800018000012192601e201a001071102c400007440d001080c079134450704125035201d800381081000c000c0d800402c0e8014003100d0455802050081d415003141c1031a2000d1280711049517040d004561200c420140d0540000c4a180c804580101064aa124064904410241005108810920004001c00d01803501c11050b0005 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 186508435 1250 186507185 186507199
    0x6012702070303020c0d1d0103020414010f091512050c030105030d030509010f05160306090c0207210c06050c0d0f1d0f0a0b0c1c0207230613090515011d 67
    0x2170714014078100040c40c2010000602c8042c41c5400c914212103c45045c00403e0a045180a061100c044043d5040d40c0c20103042c800d080c054080003901c61036500d0014404200a04e10f601031001000300071b500d01054110901c0c1c00c010210340540c040a0440f4104c07070009006011200000c04d003a40540030003820600c00c0e540c0c603a407441030402d203800340711300c507222000b40c0b0360040c48091000b0b000c030341181d0850041c10340f0b0100c4094980303800103400d1007503e0a88007803000800081c5c03058048000c48400c010201a4071440004103070350070102070300d4402c00f5207042d80c402d800038803000c40f0758003c3c0350040800103a00312a544508103070310590042d800400f81202c1410f140c108045081003143d50300000ca100d40000780c01760090014803800000d082800d600d0f44050f14080002940c50310940190744150f007e81c10018030f180340c4034001d0407110f0300241159845500c1070001000e04011313407181800d0b441c1044001504ca01e14050030203115401611350b801c520301c01d0082c41000307c2e14020b500d60007440c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 186509685 1250 186508435 186508447
    0x41b05030d0903030201290120031801120b130f090b040b0910091218150e040615230903031206030f03190302031506070b0403020601270207030302 65
    0x60900c4021850340107a121480b20070301d145402421510f0040c401310441841c0c00b82c0840d180d80d00c80c5100b00c064801d290260b01c00344005200309d0220701c07010074001d540c403001074040c0054881c4411a840b1307203000d0b211203520108142820b001d6540c140f00b280d5000440100040d9904040c0c1e1100d515181c05510020746881e440d81c5003044000e041e10b00b03991000c0d545007004603400c8200821642e0301c1d4103203024440c08032282daa07001c45000480c0c1c0c1c03105000034000b4040c2c0c1d00301c1c00d000702c0b80108206050103c1c00c00151030302600081c248170f5403a002e6420941c010603400201202c0c4201c10903540d0358240602000ca0861403070f480c2000d04088130070340c100003014450f0340c104083d0203101e003111040022170402204261601d40c0c42e00056a40d0b402c240300c07082866500e031103180300707041301420b01503070ba9690b54064850074600d08504590007070300481e141c002d0011201e4182c1c8a14482e400315113146e40c840140e108070303846805580300405280422194200680d402401c115071007810090309100c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 186510791 1106 186509685 186509689
    0x2060f0c18281202150906090d1e0305090307090b011205131416140d06090213090819031b0e01020a02060a0909060f0806041b05 57
    0x925101d4100001c2c003a20340c4101d032120382d0300c5019a040b52200d403109002908a04142d010380c40d6a503203c01c07982458030442d059442d004108608100f150810000401e2501104a8034149103040440300c0a041503100c80180344030703031030b05a11000004141441c000c015842080b803030b4144414480070382d0b0000084440781102010200740e40d641c15034011000000040f0040401a00704841e044200d408920059080098030074500c0840e135960a02e04401c4282c00706c1a840440c4107013038400205140c0c0408641803000d070400089040000441040b40c440c060b0a5520380c40010b101e00310b107138000c0404840f036500340c20b0412110204201c040b14801c05410305009212180c074107806203a008105150341035900416407503840000800051040003a40700750130645007018004101e04a918000d1750544020a0040215907101c1d211894811188681401c2900c04640003240a07 = true := by decide +kernel

theorem cover : BRFrame.Cov 186330935 186510791 := by
  have h0 := BRFrame.cov_init 186330935
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186330935 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 186330935 ≤ n) (h2 : n < 186510791) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
