-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4262
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:02:58.594684+00:00
-- url     : https://prove2.me/submissions/7ca89c3d-3f1e-45a0-ac2f-d1dd0ea1de71

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 766366906 ≤ n < 766546762 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 766368156 1250 766366906 766366927
    0x604020d0f021f0305252a2108010b0306310203011e0807091107060e0a060b0d030e01030b0d052d0718110c06070306230306040213090503 61
    0x48010542c0c0d51a10705000c290f6995168040841480c078003081b40305110401e41c101c9900c01e1030301c1600002001000c0984510000300b40985210410702203410100c41c41c0044d44860080261503081c3c3d125040024807941270540814644c000107091501910590000200e0345814110f54000b0400c29110303a042290344101c14006984240921075118141d1641e180755011a900c8100c01c82d41e440c00a00581400e03c61001c0150150a46403500c0e114140311100100d000d500c41ca1008824140042c41c2c400d1642ca002000e0380c0004400310321540f603060f416030200b50041c0c1c46080030320091800103015010a80012241c02400202a026219180b1101d400c0100107c140d01224a8608118a18a0344100d081c0d030301c4017940520f50084650400700d410110760364218145036445500c1070740c24203054001d15490100b040301e6560000740c03600c84c10041c410a18000407a40e001d07000070351921343d08500c0443e40d1080007410081c0078010320b90f0f11714084103540e40150300185d405002e8940c0c8403000c00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 766369406 1250 766368156 766368199
    0xf040b15060d0c02071a1b0319020a031e0c11032103040b0f07170a1e0b010f05161103030f030907030b0a090c121b12060b0906030604020d0f02 63
    0x90780c405032140039404650781001c00803d2851040141c411851f040044180c0c0c03049100c141319402e420300c410301030b0080808032240a111006401d50043c81c04411a0800608004980c0300111420445c00c5c200c0140a82c01170148415a811803128150002040e000ca8079100d00c0307004810190004825904e0f000140701c0003140668000d90b1000300c00e4076a40008541e0040594011000c94031284584d51681000f460465001e00e0342e903400140365101070f4800403540c0300ca1002c429010b56441e601103071980c0004d030301154070742a807400c1c50038a8941d040c0c090140f49811300280c50810031821090700703030340e08004540080075034100b4a0307264140704803d03035039441503030100f281d01d6101100019440c40d41c620409c00d049401c484501401c506d0161442d443c022001070650300b940800d001498443e9050b00c280d40105414800301c281101e90707040503012201d03a040000d200c0c4508600313115043d07800044550700b00c2d030104c0c1e000030880340c0b601d402d510307105030840c009401c09001c4440c12150101013 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 766370656 1250 766369406 766369421
    0x8070f03200417010b1203030612010e0d0801090510031509020d021302090907210c02031215040b030c03100c05040801050c121f06050f0d06080a050706080f040b15060d 74
    0x1c83c028801c0c0b8a0200800503040704040b01c420181d07105000003807080c5003150300b4050b90402d4000025249103c54841401c1210340401d00c0e0105032240010131005200388125680507410003682da02190442d41ea410580701004c03150224507850315403100c2507550300401000516030007002c08419401041d0024040e42115400700d2040c1311060000360f40702c3c01100240c2346c013810306d1000480448218008001007054124880c21403005011076445002e407000007501800070080d00902c403840b51001c0009039008488840d0094010641310303c01501c00007184490780303501e1440402d010300c00307040482d0325000b01c0d44031440e658280030a021285c01040d009150084541901001c140d90b078541500a40c4100703181182c02550b00101000760034410300180c401000c1c155070302842d103c44400e140c2c06441c2d0503040039149070489185079040100400904004024a05005825160110501d03401c040000c001428510707403070f8009244c90441c0c2c0004940200d0007458151940880b441010090410 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 766371906 1250 766370656 766370699
    0x307031116060b09010e0412091511010501082413020a12170304020306060904020f04060303090816030302070b0c030d0908130b040b0a03150503060c071208070f032004 74
    0xf000050340325402c160810070f041c0d0301c10811050403510345039151038903c494080f01508000d000440400d0302d400346480c0184064207540c854003404065001c45084690680c4961440d905c01c0010740d00d242d582102100c01500000202030841d071710110381283c80e91000318001e60000014402003052803540b1040c010362030068450070b00b0182800c003c0d0040e4407095078060350542c00400000c4080c500450b5403a03100b0300c0900340321120891710b80814243d510a410850204003000001c5c40100c2d800c00052184d9820143c2c0d05e10901e1440c0c03000b03034a81d4114044c0d071240c5140001e20702c3e04801c0401c121442c1c0026904200070740c1c84141042c501640095450f0342160114240000d481445402071314103981c07000c5402840c0c441e500d0415070040030004114154019076400c00100740c1e5050100510460001c80f10302d64989003032820700c4134180500201001e0002d030030b00b80300b500d0394444038403010030380325080005020740c0400d260144a4002600030a0401c0005001300f240790124040c00c038158103 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 766373156 1250 766371906 766371911
    0x515030f0105010504180906091e02120a121103091504092004150c050f01020301170105011a0723010e07090b06030402011b0b0a0b1c02090c030703111606 68
    0x202c034001110305200340e109081a00e04c000143d04078000a541c044450984990f000088406c9165200401caa180c0380c2401c0e020b4100c0c00c440419030618000032070410883d240900058089552000d440c0440210038104000c0441481e5003e0f0b80100b040320b810020040c003206010a50b46520a002c2d40140a205070903400d0140804e2a0000c01e002c0d401a003004044031400d103424181480f00b9103407440500010031001141c0040403036410b015030013203424610000f680d00d40c1058a000d1200d1a0f4071b80802c5a81c0c036100040001b003054001c0d04803041c00c1042c01d00c0e580c00d207a040c00d01c040106a00190484007061040103860346055000b000350800f80019130300714030ba0307509400c000c88a030004a80d07000201000058010340c420f1081c0b172840c03003000c00c80c40b0024820b500d500028900031150300c2d000e00d584039036a00c55850140590000030700103010700240541c644d404070f001c04d600075115851164000c0042400c444c0250440c0c150011200e08413601d80107119003244079000c5900302031318181d1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 766374406 1250 766373156 766373159
    0xd0e0709111204030e0103020906130e28050403140c0706020708030c03030a02070302070e13020405010b03070f0e0a081f060e0603070b0f070b04060e0106060e01120203040c0515030f01 81
    0x341c00009407800715003409072090075a901c2e91016a00d240700941341070304040c0d08226209480c0e40e500302500c0741c1012010341021081c03c280c00810300003405040d54481807460212980c24480714045280e242c03a48070f40110f4551180d190903120800c114100d40100c40d8041901d54518200084110841b082513003100d103071903079170442139440740300d01490003038a50010000200b83d0781c220380090104c18424070454048035a6089406901c54080e140d01c0b1644110700c090200758a042c0c02414003502d0800c0400e441d509244101406140916440c8001d002007200e5680140d96640e048800401070074090321510505c0001300103202c2e2803003801040d070702c1c94140081058800700701c3c407512401c000380c0100b240303d09201c080240c54001c826443d1190a0030051030000410625549004a01c10640840c0b001001442207081d161160004400c00030700d5540303843c5907071f0301406005400911000069482d00c03a03003000391090742903410098002c4a4140480800200c2000451182d00c8403100c040280c0d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 766375656 1250 766374406 766374431
    0x706030c0c030806030a1a0109050a0b06032701062c01060e010c0c03061407021b01020601180b030312041a0618070513031428080f0d0e0709 62
    0x54203100c03003040c00194088007140020703010740d04198012034002e089960000e0507a869506c41c030a42182ca6100803441c1d80108240b0960340205900000e106000340019843d08001c1401e50000401c2034080081c0d4001c02600e1030304101c0c4002620514000a204070303902ea02403c045820000503100b0100d103218446104d4000f003c289030b05880c842c0e9074480390303840400011604038000f02d600303590459942c50004009951403192078081032250021415601e00068040d04149503483e9001141a1002002140741e90200d0941d05440030403810014012043e04a80c000b40b144070381690b0144000100c00a041c0141d20145200c5e61241c00f9200c090043e00d100e000c6640703070540303d003034208000f41e100142c0401d100c001c3c640d02034141e00d0960300701781c041c1c1581e0b109203c06901c1901c600351420f1160051070303800d2100d85000c02d21001c1d0305901514040005078010800d51001c0c3c40c80304007040d020024040d440c22180c100380c42a03000c4c00fa560400c13000c51340300d4440740704a4049a02c5c194044484 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 766376906 1250 766375656 766375661
    0x330d050a0c150e1e180a060501090509100e0901090b09010f060b07080304300e0411120112080909070504090b0108091015050d050303042d11061e070203070603 70
    0x6000c020303201d0289800d1030350100a8450a03141350720340c080761000500255100180f41313a8416060346a0100d0110710300000900341d4105a00071a0150781c51320200509203200300740d85c608903214083c0b001000e560707541d0b010f03005010000c8020100c00c0c000f000d00000b00f4054000d903003540110032040248030390750481c00c2018420001c000f4402c1c6020300025010072445080e0b150800000c1c0000942030b9001641845d2100000c0140000300300282c4016806091a00c2091809158070104510b0100075405020301c46e0414458903441c1c0801080c0102040910800d035080b0301006841c80104d0304003144080c1c07583e023160243c06c0301203141100310340040d03104007e542d0150200001600b0300c118031480c0f0101500d29000c484051007010179000403d42c40344a16a082603008401554036410145850f803004034050f0b1240441c0e8050b00c1c2c0003c07440802c0750001904590050343d802c5226501004500d9500620070b105036010758452554242c60300c0340c030044c0711051013201611002074840d03101f80c04 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 766378156 1250 766376906 766376927
    0xc040b2719021308010509030c0a030f05090405040501090b060907020c0607050f1905010c0f0c11040603021201090b09060f0f0702070506040906030b16050f090a030f1406330d050a0c15 81
    0x249c6600102980c0003181c02001c00000206841c6045482c02c1051070114054801c265011607090f90f44070980002d0200c80104160449000c0b038683d17009042c80741e8025910720462030940e00c50400003581c601000020080031000310044801c0d0340028001842d0903030244049030068840d5400c02228000c0c10b4840c2011954842c107030380f60000b894002d600c404d0680c0c05c981c2900c80e00700d03988041c080007583c1c520410280c0d2a52100011840d8200740c500101e090704007411101c401d500090600042d80401c0d03000c580d0061248d48103821382c0d901c0042c00c0385000c4941e48616004400040c000c03800081c04d0304070009480c0260380200058070760300310001100130f4010b20207000130320611403242081d02400080990000007010b0380c00c41a1030307031120300e1003596030042100d918560044030105100180311040e800901c02c0c03240c03050f4907020501c0c454410300660418090b80d03041d01070394516680303c0f09049151b64102c000c907418054940b03400540e00341d0034020402d80807585000c0c0c1d4081031082000c42c2 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 766379406 1250 766378156 766378177
    0x1b2a1a100e0106030c020a050f01052703030a050601050403060e06012d15020c13020c011514210303130501110a0e04022a0c040b271902130801050903 66
    0x3003182e01c0c0040850040003182064002c40c0903154801011400030089c58030081c1c04240009013504060407002503030180d00d89010b8640b0314075105189014030100540e40d0049a8000c08252a0745441c0100d54612594100a002d14a03210591200140003c0d49605850001c81c400305080440141070851502c0c59180c5914200d0403081444000348541c3d21580d6109207004840c03901c840c50340010f11207030000f40003c1c03da81d8003140c031032101c000034040c0c1c00e5040700f11140d9030800d44c1014011400c0460004255024210111900c0042820742e010498111120000d036a00d1742000300d070440d01c05a0040741511607600700741c060101e1840420460320160020b4407512082507442c014000603401030500c040380d110002c900314180b040041e1080302228218009440011045800c11084940d50b0768568010710508500ea44a01d103a080854051038285402c07041d00d9945071300b08100c0c0c07007000086480160000c990143c06a52000b2404241e404901c02440130741d0703890304c01b196a03008401030030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 766380656 1250 766379406 766379429
    0xe09040201111c0309061b020d050309070513020d05090c0f2e05040306061a03040807050c0415092f0a1116090506041b2a1a10 56
    0x2001903000321060810181c031036050340c440054a50721440c01e502920240800310313490b6100d900400a41c0e205c2c120200c407407244043c0600003410b4009503660b1400d02c0c00700038804000302081419004001c090001c1400a141604040c148072144000c0d41000006d039030745c141402c0108011850105001e018000b010345440300401c64030080255020300700184140c0c03031070749282580004200500c045541015070326540d039100d103540781c01403c4804a600040720b009080860102c120801c0d01281d400ca50400581600e406480c10090700389400020703034607030151416595400301c2e9400b00032071003151303c0a40300304451103240401030b417800ba03075030300400f5002c1d194814428404002c030080c0410601c0e0f03113400e1b41c440c004000b00c0307403800d0001d01d5003000d50100300d04104095415400345950008044d24103004101c201c500c2c2902d00a00d0f42690001d001214101c910f02c080240d401d043d03005000128a125000c040c205050390083c558104403400300c034480022120101c6500c000300300c90003c54903 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 766381906 1250 766380656 766380661
    0x31701051c080909040b070f052b02090301060f151b1211100f0b0619080606070f12020d0518091b0d1506170a0906140114100e09 57
    0x41d8201d4030210012203800b5028441c05441d5250444004e10441c400d07804100c0a01f49644050300005801440e00100f18042244012807035448091050074108100e000e064140401941000380c090000616059031800e400040e01041c1100341e001164882107080200010000007255003402d00201044000c3c2e803e2000c000007800707460400d106890500d0302d40c44001320340c3c0c0040d003400d2035102e203400000c2c1c032003500405030011441013141b10403080368114074040490205450590542044006100c6040300003906500d400c8226800d850742f00812100001052411441d4006001000300040c07040c0f8443c584000d02600486440b070500780a0307030000399000000c00951540040030f00a0041d011640d2110800300b46011b4061000d4010000c104507080d03002c0d1004c0c0800980c004810030848004040d50010107031405a00018031410104511005050080140401001c010800c0c00c021000051240c0a003188413a400740481d0050860341400b54100d80030103003a81008c0d48130280601 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 766383156 1250 766381906 766381939
    0x1e02030a0c0206250605040302010f0e1f06090c0323100312050f030708040224041703070c0308030a050106050306100804030c02040c030e0c150301150903020a06030903170105 77
    0x6004d0040e90038410031180418100d207544c09007181003044880030740b100144020150280520003440c19890810041003004c0440c0b1507458010040303010b16180341c01c0ca45480601036800510140c03407420b006000781102804000d0052104101c020780340545140b4150442c0c4141400074051900b04900000d9207003542c40703104001080300b4541c41800b0040100310694800080514451000d941b5002403500d031074010711007601c00b007400d81d800f20145100d5540080c2c0329242920291940f803152154101100c4110500c0d40c8110000901145c81c038110001c00c20000d4801903100b0b062040c414001071340d968030151490b000950756244d0201c06400c003104440c0c8075540d0340d039010340030b880e102158003059004034048810302d4401c080001c5c0c62302c3e89400b496074100301181341350205980c035481c0194a0401d100d01c50006024544402000141840a0070306c1641090007850300100000310ba00d66400019005100d4140c0481c003140000402070140e03501c0702d400034101c07a4040c10b0200241521307030303 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 766384406 1250 766383156 766383169
    0x103020d0f1e0c0e062d0a060801180b060d360c0608040305090f040f11030601031118280e0105040f09020d080a051c090506090a051b010504151e02030a0c02 69
    0x1061680d1018490f0786c0400700e559241d0f1040c00404032500c40c400390b035042000001030790415242d60318130a810610b07130302ea003611000110780d50b8949100c800180b400703044d580e91342240b0315440e1500c03c40c2d031400ca00d40b007011000c8115001140c407076080a504190344501c26920413a0403580078000c10000d100d01c200c2d90420502040c12040002c1000501d500b61002007002c5440c0329405048103540070003040000c0d6010b100d0b05c1280e02c0d4905c881f40c03d02002200025613800100409401209002d900d40f440041c2c0e2074082c0c0050b40e04100200c500c98444d4041c903da0402403144612507030500a09050760100d81c46a88003468028000c0020040c483e1a50308030382e401141c030b5004101c000c21500d1800500c56a1040004003551030105101c01070b41441490000b000c1e11203103d42d08150041400903c00040c81c4c0102e01d141c50401080b2000302c07005840328002c40c1c0c0001030007584504640c8203154880c1c1a41e5074010600c0280c0d00040701c039442240e40780038003c90038010940c0303140980301501c1c0c0349 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 766385656 1250 766384406 766384459
    0xf05070f080903101b020703020f0415030b091606090501081605040f0b1c050610120f0c0f080108061006030506030f0a05030a0e06070b0103020d0f1e0c0e06 69
    0x403030070303507182048400102e80341000303400741039101d19540c6807400b0100c07001c0c03078080030254000d100901c01036046400040500340503114440c4034503650707240740b1446020321142c50000d6420030a41c610310718020620644859101900c0455480c80d80008140c80b40510080d10980d00181d40304807103070f81c0c6d9028a40c40e4a20f0000b0000c00d010041c00002411119040888040c11600101e140c540340c680c035900528410041110491034200001c1200036180c0508031241400c81d40340601c8910402400a4028045c1c5102945110f0408613003640480d000b01d240151009190780d4507650380e84c0c651020341c0380c40098644001440d0440000c00c0550300c0b035002640c11100080565114440c0002980e262201e465004c6913141c00100e0300740111500a000c154800c40c00740e45152415105503140e03e0305100c1404000d1003400f960081e03000f8490020507601e010703540f00914100c400030008400107100421001203e06105040300428062100a00c0b14010403001d85030310048452174041c4440354084 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 766386906 1250 766385656 766385663
    0x602010c050a0e01270315050405120d0f06120312090b3103030b01110c0319060e01050a051b1612021006060302131d010b13170309040605010f05070f 66
    0x11208002d070017180041d03100620034524071110030003455403902c1da80207003038408524183c034900350402c40458401704090441c6110142030f0303651070081204240041400d0211503840b185040f001086066010403d90200b40c00303a210355000150091510080d50500400107096400401c003050500003640b203152040c1c80c00d13500040c02031f0042104600c528014000660000c1d40f80c0440e04455600a800c00064040e00c00203080301d18040000b01ba5900e100200300d501e41c01c01481c02c1028404182c0c880d401851151009100e00d040c083c00101c05404140d036085a015506000c568541c6200030841c1c16444030301000c1d80381c003510340e1285084407000c0890542075008140039010b541d5a00d105400180c15240c5006850b1030121420581c00c0403250230000d00361246412510340b2041e10b4102c0750440e1102e4022a80d0368101c1d040c10030700542580d000c03501602c403601e009905124080302130700007408161802c208490743c031801158030241f242002008500200b1945022641a180380c1d15032900 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 766388156 1250 766386906 766386917
    0x91415090a0b03100e010501090828020d050f010b0607050c0607080708040e0f070903051f060512150618040f03020a0b010305031e1912060803041e0602010c050a0e01 73
    0x940c2c02d46a01c0d994400c8070400d52035051404140700d0401a000d50750702500007880d080c42c4c0b031410610415526180e42500408096925500c60034101c010035024000c5540604004811034907450095500c0e101c2c01d00c80700f00c41d4242040d09034a4200703407040e83e400b0380d001030040c4150701d0440305003c00d903442410142d4005901300a0b1030301040b01d03030f4000d00050542d1680d4a13064917042c058480f04c034002406810030025240010004200c1c00100c2c06980c081c070b1644a40030800f100208001000c0c41d90000d50421643c4061140f911400328a103030748078105615014141c1e031001c081000489840311050302e00c9030040302240c0410610b607001000c040c4640100c0f103940f40760b0344454100c00c01c03d82c4102e4a603400000d2000114914800103072254140607240c0341411440c120301030403140e0403181c0c5010001d200d0300c0805007004c0c640101b00100599400c1c3c2e9a51600c1c0e080e04081c442c84005420001c0c4220b040c00181544144610b66240c04150781d001c0c04c044503404122480c205040d5812304104 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 766389406 1250 766388156 766388159
    0xa0e040219080a0c09020909010e15030607050903010b0a030305040e04030302120f07020f0f1b031203090c1207080c1c210f030504021f05040e0403050406091415090a 73
    0x1c0c840c0c881c00d001e0442030008000d1030a9500c0c010550074250b03081071380360718014010301740175840f0084882e05461036152100c0c265619030700440741113005001140d40c548154030a205107d0381001c0105036912066009004e6020b0720802d000a25070f030740c440140000c504200030001100c8083e00e264100d4842e2078098909101c030301700d50340c0314482a00c0c43c0d6000d860000910454503010003000038410b80d42000350107802c0f8510900c90704c8041008030340300c0c090b1850400c2041c80ea0140302c4030074100c05000710aa26800c1801050342d0711050402620300840396210350528207500041d201d000c40e03252500034141e0121060a1011041c1502460b11110443c5200900021080800514400c00d14481d8444080c22030038010442148041c001040c14588010311026845458241e00c055001c291445001c04035500d0407529441650302c0011032001d05e00c00d02c410158004020002c54000e6642c40c1e0541c5e84581c125503a00c0040189036030720001d00001d01c8074001301000548102c1c10001d1003050589d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 766390656 1250 766389406 766389439
    0x903101401150305040c0311010e0d0b06030d171306020906070b060108060d0c170304030506070e03210304020f0103060906030f0c0e0714070c03020a1e08010b0a0e0402 74
    0x10390300a203400024044220050107400d0444400c19540c070721500c0d007405a0b08194558080c01c03002c501001d41440920000c403103550340140c0c400320301c20001030846442c161071030515450a000130740d2014400e00840c0e98100340c2031310458841880c0028481e4007902070f10b0b0142c04a4911803128400c40d0b00d29000c3c0035881883c2e50784000303809242d0203070944203094a800c10004044400042015100740c507184800404203d07420000c00076640034605026500c220800030b2490f500407544010000d10803041080551a4001800700c00008150704558040e00040802c46229011109000c11034405100050146c40c04030712a9200c0c107018100000c029072111804820f550300b0703400984075012108403c8082090b1540190000c00a824841007a8200182d0080441c0b44054035440824400710700b200a0040301280300c030080d03034018148498160b842405502c1007442102c0705498407030010000891304c0040c0114902c0c0c6000411582e04642002c0d82020800f4016000380d8002c055044d841e03542 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 766391906 1250 766390656 766390661
    0x12030c1205070f020c032a0d0c06050c1501060c1e0c080f10050c04030308180102070f030e03060106140a0e1302040f061809020304051005040323130902090310 70
    0x102c08607901c0b034001d0703010110301a1078207125404160003030f44004a4140300300003040420700700f0114548030100801c01100092684031010f5006000941c80c05000100941c203c00207050b4640508103071800c8540d01501458800d10034855003020940111603100012901072100440c190840c4801030180f54640303030840007010310341165040780c0c0050f100300c1e464a0100506020810940d406219a19201c840b00728503010340c2c0700007014421a5004607407014017446004241c01c400070001c6480b00c55500b8108014001500c0550202e40300c09684402400d01085850603505191070701c03130a494048148569943c4150802c0080003003070801c04605503500141021003103002f103070150b00c50741040b55091111031150f22040030710101c0e001c07a80741c0c09100f03288501218108400140c803903480f82047d5040c5060207203c181c1d00351a1600300820160011300410b98503103c0101c00c1c1958a07108080030040c41a0800c198650b109040c041011604a400800e030b800c0019003590000640c14885005 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 766393156 1250 766391906 766391911
    0x50d0609051c020f16060809070909110117040203070b031509090304052d1012020a0c0606060215041401200d051326040b040b030109061212030c1205 66
    0x40d19660030b1014034040d074100100b5015240440107041d100d1595600d1403010340e8030f441020f05100320fa1000032147d010510940f401462119810f200044151a2880d015a50454540d000c1246058050300134201d40c000c1c20b120b01d074042d00a0074090308290300f248560300004d1034200b1103035980304662581d8890490340c50003900414000c54986040c1000c22503011098410a00301c001030034429405405810800e0981d441c06440c00441c242d0190b008460200c10314504103040743c000244404420f038401d00d00001c55009260401845441d003078100d84640d000c40040010350070740800f040120302c41d88c00301c064240c0074100000e00c0340381d2440104c141140c0000031040c8a000424101c0c42202c01d1b0054690050755041b0310442c0344000d5541e803101d03142c150801d0720101000c3c1110351a1203030040031030380903001040003203480315519414000d19238002d01608003680c0c108040090f42207c03020408070044e61020291038040d12040046004100301803c0f0020882500041403040305c0e644100b50 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 766394406 1250 766393156 766393183
    0x18061513050f03010504021e040603080a050d060503010519180c120614060d03030e15090106030501060b09090f22030f0f0e03060a110d060f150302040305030301050d060905 76
    0x80c1040ca8030341000302001d201160386000b81d040600b0400140d40d036500c03140e002c0d039018007141c900c0390158000c18003c0042e80c000130816900003c050354042c0d006000352440c2040d459050003519114014103003600c109645008914030003100115482c0325075002003001c01d018080710041c05c007080c1c903001899a041d0744903c43c0c5a0100c440001480440c0c02900d41c2c0341005680301019040c4000032901044d4681d401a007016682d80f06641545014010368541a4404407840d0081c00c00030580342c001d01041c0b000300c50030340c43c00500060050705442a01c0030802d00500c0c000280c1c1d121f21401038a01d200506c8000b5810240510110100e100d21240c0e43c0540256030b09900c1c2140c03423401074800c0340c0041d10b000900c8400990504a950b00003440751303001d0100c82000c01c0f20100e44052081a014920340c4507410707410680301141804900000c41e08940080c8905241b5035107548043c1d00304e00c124000501507070030801c01405242400c5d103041c10b09038803440c80012508015142c1e5420b2408425800 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 766395656 1250 766394406 766394437
    0x304050105071434060e1012140a2a03020f0c060103060603060b0603092a0607152009041a0612010e06041e0b18181902180615 56
    0x4240c10582d501d00c60080c1c10700c4d03441c0e940b11909000300a0a50a850701c540f0303100700d03c0c1d9580203442510403048608101103c040501c110480f50b00010010302e0201c0d00001203528000c1e01c0d139000c03028000c044807172034a564a4030803401c5c0c003003d0072400395008a4507020000001c01101c071a0000802c4424020750003250002800f0b4251700c0c12405440f02034402a03c60b4800788140164000c0201c3c0c01d10081c50300c400c621280c442004000c0059404111450340c1c01040440d81d03805103c1458842520000103510170400c1014110383c64000015191040340008814840f8580d20b041640c045544014010a03500b6008400c40001c0c610740c3c8102c081041080518004001800c129400300340c018004a034280401c44044c41c62030744c0030352103d40801c0c2d80b9469070b440200e5602d504000950b071010349007002c851071030503c0c070f001d03140019030000800d03030f10800a1041040c0f010030000c5245550040207840d90410300221240162005008650700070510308500341c400d00c83d17a00900b40801e584c48003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 766396906 1250 766395656 766395703
    0x21b011710080d2628151d07030c17091c030912080c1e070210050a02070b2802010e07080c13060e1803160b01031b0803040501050714 59
    0x600e00e40c0201e144008901c4e800b0792050003405038004a061203282d20500100b9054400090107801070040000343c0350b02001b10060108500102c000d80c03481041c01a1600ca10f5605c900e4011421506d420380c001001403042076000b51030b0342900c08a9030b0002400c20441380c602c0c4c000c80e04007000c19062070151010039910450b1500700210b00b1424016a032190030280f600d85004008490036125072491401881c14502e010380c004c02c000d0098031051500074000e03d25540e440800580a0ba100c030503040050b2040d110002105803200c021980e4403d0100500346901c408100c3e508800000c4605520965484407006140000c04104070002840204010049041044180003200d0112100d07111401d040107428070130554503081c2030340c110030220b1010b91070f01800140d282c02d40c09003448051002d017410a0741001c1c89011500c25043c0c1c0c0c0140c2880d4000b01102103030204c0840a0301c580034a580081c841000750b50301580207424024024020000413000481d0b4035070815003200c09401d40402c1b00c546 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 766398156 1250 766396906 766396937
    0x11030405011508100c1202030a0204050a0806070e0d030e030d0917012f070f0c06080c0304021008060a0b1201060813051b0109180507021b011710080d 66
    0x10b84120998840707280314055040c00c40c02d075191000030b003c005040d600d5000b0304100701d10440c0800091b0f80d40c07080c11500ca0906c103a1407000fa500900c1605e07c40d40034848081480d54000c45d1060103644a52a8120b607078070700702e050240560b0704820a4003449010300d00c0040549051042c0300c6501c0c00b5540380e02d007660801c1c4010468007240301c02011240e1414408040141a0020a56003c2c0c0349a01002100200b0303000c080039481840340003044540c5c403850802c2001444004101650550344403c42d85035100d85403150b941c002250007960062610900100690280d9003e0b90040e90282c0160481522030040700400d80c800c03818440541d401000400245e07600c01c045a4000c000c611a9600d985440c0e103d00e41e540c0d1000c080354150700c407205800d498070b03030103160103000030418010002e840000d400000001007400700c9281c00540112004040d840c00481e245064403101611506420280d90344196100034000f000010342107866480030581c1d8004001d1890201c1032a0780329000070b0038101 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 766399406 1250 766398156 766398161
    0x50c060423121912020a0b1902041502070305070b090f0f1c0506090d020f1c0e100e03120903070311030f0703140c03030304110603070c020a06030204090506030d0905090403020c03011103040501 85
    0x78040119006000280700240c405441d01d0b42009211105500d505184008e0340002e201d070f40d204101a401c50a50604581e80206100c0b046030b01401c192a00507a8940440100d40b05182495a000107480c4202003e460056803581800402900d40d82110000800b03d40b100d244c10784007603401d90311250402c00191000c104d03080d080d1b00b030b03803000d095100d12945005980308642035032001400325855491500601c5000100c0032044003c01d4200203001103031024140100d0010600d00074025041c0d105d002d501e07250200c030701010000e401041920310b507031a2098584400490b00d681401101c0030311191a80803c503101c061402801410000c4820100b51840c10300560800740c0a90818000c00011032a50034142c80000000e0300c0c0c1c00ea80f80d8505c0000c40d048102c1e400c00039804040036602044059155000e031094500780300d000c00003926001c00301507440014090110001e200018144038900300380400c1c5420030b109004aa0081c0c041200203420340302102500700c007014010003040244a402d0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 766400656 1250 766399406 766399433
    0x70e0106050405030624010809011103010b120a05070509040e07030f0501020a0224070c020d06051f06091202040b01050409060605070639090801060b0304050c0604231219 75
    0x5400600350300d03446c00b0890000c440000e10079046c00b0f01800050340d005000c6d08680b841e00c480c4080300c1e550350384400000300701c0d401051907240032403061300005000303444502c565400380e000350300da1f03a0a08180c002000040c00011a405441c2d003d10100080003891550160b20024803d00002d602c810103100000c1c900349500000c0d00d0004a03007410720906221701010705400080510b0303e0030316140980049100702c0b200550007805540f42100304410a61008001810b114942e0760b215080c666030141101e501425014510240d01c0d00c101d40c0c4014039181e4230030034107104103040481c02c069030794600904071125039014901041000400004214540c8210001d072507414049030382d598540700020030346101c003849880c2c9a0040064000c005802080103600416242c0020712040b6229030815200360829202116640700764101801306240c050241c070180c444800345109206036245206440e010300c9038440350041519001074240d50000d0010182c1441900400507003000e203454100a4000d20f07 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 766401906 1250 766400656 766400671
    0x80403110603010605070f03052205030705270703090c08030703090902031905090c031b090901020415081312030504151815180521040510050c070e01060504050306 72
    0x4000504c5541e410030140c8051a07007110512540c040d051070141c40a00c0b4001c504d804220064880c01000449002883d041c4c2d0310030740655050702d07074032030510034801600310b00c41c0d90841c4482e046120182c05106041da0100b00b618000c00e0826040d102c00c5032140094100402d69000010320500341a08600040c008204501c4114514901b04442c1d1450199101c40c584c1003d480380049000e601e010412400110b0b401001d6880b241c0612041c107880841f481c6807540119004400034200103410b209590807150b08125102107010518000c82e800000140380491841d007160140010405606540a40034803540f00003482d8101030a01c007005508491807015102c0c05c02d9181d0720000c101b04030341c0d440e5130340c055801c29028000c01e550502602e01400c2c00c081d4984020380c0748013403200009908a442c250260a16220010069440c2140c400e0740125500000c110b08508079951240d8020089400c07944e003556803841c3c40e1030012034128000c0c0c0c002c400003200824207000c0e80c43c0500201e07400040 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 766403156 1250 766401906 766401919
    0xf0421080708070501060b0c010c12020c0601151e0306081b1f0504031e0b09011418011b0509040f060503060705160c03320604060c020c0301050408040311 68
    0x246039540100030320032144010440c07000450040304100c400d42040c030240c021428107035207a070003901c2000d00901e00c42c00c00d0b8001903c03420030241c901c05030380308403010700c01e002000d42030b542c6c241103002040440d0101e1941c10407007040b458131440c5a009a600e0000300b01d9a4012074810310b002d0b0028502000d084020031011101c40340c083c0c0ca42d40b980c04003841c040150641450320362140506a44030301a550004c2c1c04500b48204074404801049000c0402d140314881c6005291100c0220a00302d42e42500100c0320890031101003081114080c001c04590265140086a510f01c88001109841219105030021030400b00d5071360094a880d0003001e8428006440c01c02c0001c3c43c01e0002944c5650181020090041c00503621100c484684411010a500408a125000d07501c0c54a4416807034030094504002c101c681c046565080d442c84c03488403410b540002001141c03251f480310b900600d1816025415842075000030552a1400c2c0500d9228500880b03425841e0b91550900320000c12070315185501c10f60 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 766404406 1250 766403156 766403219
    0x61c05151509180a050f06040516030b0606180402160b0703140a2307180e0106020a03181a1c020f040b0f040b032404052e05060f04 58
    0x31626045030340d00546080f494440c030f0300c40403405810301c1c2c002000580315008100d600654204000307160b82c00355200328121060070b200200540346c0090719000041a000c009000b00329185441c40c054001682c0d02c441c00001c3c014144002401c90380195000c41d100b22145a640f03041c40100d10b02e43e9409003141c03e0510082c000240d001010140c0181034507200c40d030710840d50b040d8804500ca00c0186940718207a8240c64141a8009040610700300709094080c030b1100e5020070f0f4924081a018101c43c51600204030f042050741c2c081e00e40085c1d0714008440465008400100405e0b05441c00020904200c843c503991740002056004001400e130031070300c603140100000b4812640c03c0c4105d4080b218850f1440b9245d000200444116208650120b090f146020003406009800d03244035403800407034240c09002c0b0209050030300003900c004444042d0302d100d1000d8202450312168510410031200e0b49804072006440c0d40000702035800c6106402c0603d07101040510414031010602030450f40c40c50080081c00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 766405656 1250 766404406 766404409
    0x1005060f0103091b1706010909080a2102040902070b0606070c06050c0f070b0309101509110c0f03120a11030105060715092604120b061c051515 63
    0xc0095045036040540c0c0e18650000d201c0c2c00500c00d0018040d450f07a00310b0042d503c034550f25400b030f03440754042c04500036032000052078201880745074999680100b9640c203082741c104060715071ba4a10304880310001c08101d240310035001c8904c020070141c02c40d900010303220307003050a0a504880004202501829040045001084000c1350140407a1158a030240d6240c1000c4411420701400c214100c46074410300390301060002142001c0c510a802090032648041c4140080d42c0940d03030100c1030700b07211918010060008110390380007100500584c00c040e44c5810951301e035182c6030401422120b42103400c045240c0e2103501031141826004941601309201e40d03090106a00000c0c4010b11035940718800000f43e44003000100305000060f0b8018181c00c2001100c1400c20458407045529440c0341c9604451220b442120440203413404d81e001a090142e00001c2e07542c4d494844080504010f80c0718940b6a424001050b000654003000d500c01c0703024180c0012107171091040408c0181643c0440e218020b032281c0107 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 766406906 1250 766405656 766405669
    0x18070228081b1f150e0f130b04030c0308060103020a08070f200c0901052b0204061508010602010606030c0207090f06050306180d11030a0309020a18200c070b09011b060b03100506 78
    0x110880042c1c0440c940c40341c07844511f066140a2004081c0c141364008c00003456041040c46850038020307140c1e09521354590004408a00c00e02c030b040c0f000701d00a6408600c96610a1400b64482d01c518108005c050340300455881c0b82c0a00e9002c80341030f80e4440c031034008860402d110700310300501d0140d0f00c02554009004d20445031400c00e01d030000c0551401609981503590b42d4000f08010010400b40c044e05d90540c10000f81150720900801000d07600b030940c002049446481074102d103207041e40c040e0408904044c50b007800341c08000800c000c008d0f258035010500342c0e42800024020311b0001a4050102c0884d0600d41c00c01400060398414029100e503240038154002c400c4031940d1f0001d01d80001c0c5200c080c4001404580032307420140b490b07103000580a0080c640c684c01040c440030008200c0c50043e039426844543d51048503114010f0383c1041c82e040003a0000c0b80081c25002e241414501d61003100d4216840c00200700040c252071b0740e512021403001c0da0400340a480c000014403c414007240c0b6141c03000c80c04 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 766408156 1250 766406906 766406911
    0x120e240a15150e060d0509010f05070905010c1e0605010b180901030c03020607050a05070617150102071802090607060b1201060b0414010c0218070228081b1f150e 71
    0x500c1100143c10440da590740d400c681c0f1180140004026a0030000c000c28020111030009540700740c58400840c0c90030340200044c40860713405a541c50084402917982800e160841c14007907018040803150360740040c8050050f180a0700c24242e902d0344403884204010000f150821145029104c844014004070700220174500950740c05513510b998508141c90054500000450040c0c00c6015641e008924075610041c800c800050010103070300251900078080200140c0740b020540583d00042c400c01030321524001e030100d90205000c00500707002d490b101050590303000d04c404840080d0f440f601100304e40780c40c071113240c8080102802041118140590380081d407069018141078a503200001c50240d078801c00075110700c2c9174041d1039120034000d21300d0340c00407406041d80c1d64405409080310400641c5603a0041c10b80c102c42c40780c1c00340c1c04a0a50384654a5030740c48044c140550040100c03040a45030360802010100b0010a140c1030002c1030301c0c44c050070454001280c5400c0114240301c08100c910741d4240300b01e4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 766409406 1250 766408156 766408199
    0xd0b041a090a050106051902031209100e1204260604120906030507230c03121e070e0d0609140d020f01060f030b0a15031203050f07120e240a15 63
    0x12140050f5010236480c45c06600c00181081d4420420001119008945c504189214040a000c2c1007070b203c1d865070b10b911000d050010411000d02003040000c4803180c5044036032109518000e0018040c10100741000703811103080d43c42c15040f410495901364403088510041c0348a1800f004182403508000b0f0888615034441c003004601100c880d411516620215040d000d9140d045950b80c92603603450016001049540400c03402056107280c5180b2000b6041601c2903105541da000032a10060801141e40c100c5142540c4540e038604150000940f1a00c3e05040c13084030f0b00040c410340c3c100081c001d240004150860105034185881080110b00c40e61b002030550307074042c140903580d030355000c0c18200800350400ca4000001c5a407400000b44003140e0318100004426503003c0c0f1a80d503030040e541c0e1a0344801d8403a8400280c000f81e1507110006107038070035000380c6506415a07600030014048041400404c8200c19441038012040c44981c00d12485000c0c45120402e0070088030b58035080e1145141a017480a80 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 766410656 1250 766409406 766409437
    0x8030a05032403060415150e100e0705160c0909050309131e09061410140303030c16030e0301150e010f032a08010f062303060c0d0b041a090a05010605 66
    0x6081e59a08076052490351b81f891101000d581e540313407810780c15007542e0f2403204400d070f9200443d0303640e10000740e2803040205443d20743c030f0018075081106400c041030009650864080c480850104001c0c003900d6022fa02600045496480140410152030030782c800e400800c500d0f0011015560055880031034048148040014000703420b8241180607100c9602c03100d1070306070300c00100b000d246001e5091400b40e9003e07088508012103110203040c1e40e4401603810003446041030000d8900c2c0b000300803040103018400c0c6401c01907940c4400101c0c0c04e441c0c1d0ba003130b66100511324200501640c541c000740640104911503c6c240024515100c40f14480100b920890a100d000051500010341c0d018108009040c84e100070071104543c107240d400200803900420110400c0210008540c51044a901400c400001d0140c403440d2100c2d59aa101d550041452400c00da27104c00c2c9016884d652441070000312207150031144a00d00041e410072401003801440d411207030745010010302200d42d1000c292040f100c08407140 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 766411906 1250 766410656 766410683
    0x906040b1503030904110304030f05120c070203010b0a0306050105040e0c0f0103051e04050105011401020c210a1505100608090a120e060d06380a030608030a050324030604 75
    0x420f007940f00e940c40032a00941400c1c407a20081005c0001540300b5400381e42e490100c1c50901c4012a0584900d000c12030814a140380850b40340c92010005000b641d200800000304030001c14040f410484e0554402da0720382e80c1d00c0004001c9410310f801980c1002600d41c015000c03498000000418000110300807604250b0740700300045202421880200c0224043c51510341d1920741481c005010380b0702405075880903c4032015005855000003040c0c000140018143c61101c185005c0b030010855000307084400030f10514105501260148600f00704420300c2c0b40f00400c5901d00f20701c0251420001b42c0c0b180003003000700380421525050101c0c000303056503031140e403103054410700c80703800c4030f0101440e040e10390303c5200040e49403501d200300e9020340112041500c20009282c141015000709050304003010182030f81500b00d0040d02903507040142032201150500280d100d460b40b2061345107802602c860b41c045040007007880212020154000100c0005070005200b00c008000820303181c0c0350242c801044034207105030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 766413156 1250 766411906 766411909
    0x80a0515090309130f0c09180515122103040b0c0705030d020f1902060c070323070b011a03100306091a070c020f0420130f0e0f0906040b15 61
    0x11103c0c10340d401020716950380102c40b6450018848082e412556901e0041000d80c00790184040f401241e540798a8401140c80e50300b0f015003c0c00b8000c01180640d0385c0b5210012940d03036904800d112595950b401841e11440030390181e2418100c00550144407042413080000040541680d80d03407014811001544440703ca18100c1c0c514081c0c50710b0700c0710752400030442910303028041e00900410200384510034200c1d03140c0001641ca0700b4040d544110416810841e120100c0d00074083e01c2c1e601503d103085003862801068112000d81c100c10b80844e40314600000400c6160015440c0740e81d14041c0d0081c107413850604aa0318075031008580300043c01a034079424010240013040c1c08903031041c5060004c0340c50619103203200400201c42104101c0c4a25102c4846c0001401c6c1480713080c5440e502e21a007007200c125032200440380ea402005442c115045001404141107000d01d08410090840f080c15aa881c05c204080450a00f002000c0a081d039120104000214445031900c5030041d1b0910040c0540420000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 766414406 1250 766413156 766413163
    0x1205010f06060e040f140606091503070c0309150f0c05160b03220209431d01020709020d06030204061206110a090302090a0222030c080a051509 63
    0x4004080310381c6414000124039401ca0004554040c0c100da0400c00c10001c0401c034022a080740410610940c0001e0021780340d41004801000c3c8058024600c0e600c0d118625645c105560044408a002464800e41c030000c05810010190141c007015540051000c00d01a00900011942c52103400308002003800d0000d0007010b00000d0365000c0e07240c0c00b20001980352403542d0341540c4103440340d51102e080c0c5042d86070403c4408182e006010381c02440c1c5106529284410703584144808102510451651401c02c4680c840f4582603012518130070f1400002c005005001d00703641c0290070707051a28030380340c2001403041c2e074042491130540b42400c1c0c006031510b84a04808008042c240c0001303410519041e40812145010151810800c1c8030380e07070612020010200d1034074140075141020703000c150144018801850316007511036002c0c002907001401d22980022569100340007581030404c49594004c1881031021b0414518040d0442000402c103061240d52425582c02c0c0130240002c210130000c0208011043c1070 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 766415656 1250 766414406 766414421
    0x150b1509130e0318190609031704170c030d08010605030a1e0e0714060403050a030806010201020f120402030c190612090f05060f0609060f13060e1e0c030907120501 72
    0x142c01c40ea1aa140300c00402c48200d8440c2e5403a210b10b0103081d4090340f51442070348100a0b51045e0741c890f00c1040c0342d6626000071050b0001d00707003602d6000b48400b00c1c4406e84138280c2c840c01c0610702c00900000e071001c0141130a000e01100f04e141000358160040c480d003a001030031660060a60035000451b1000d1065400540d200c01c4040c0e80804d003800c00c0c84241c40e4001401e202680c00901102864411402c100001c503c51440014900e81028044c0c0700403038011821250b1250040c00094503051030240c0394034495018500b20400c44050341305110650504000c00e445880041d01c0c2014a0341c4150300b1040d41b14014445c000c100449500543c1401605402114000303038048080c01c80c07024103240640c1c4076072040784d40c0c0240c03080d5800014164684043c0090007607201070100300d020302d11001031204e200b92041c5d1003007446403038143c00902680d03900d4000e84640c08203841c2502c3c443d8020690500c1e480701a0840d1070b00d9000780706026071840301180700c0c3d007151801c683c5400d21950a00c0c0550160072035 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 766416906 1250 766415656 766415681
    0x2030703201c0207031106030402030c22021303050d0206071e020c030d1707050a0e010813151b081b1c0f0603062d230103150b150913 59
    0x501c2c001921142c00040d19000d0360b1040d11108594120141445507501040b540a03605a00140c00751215040020040802a524442c0c030006e007848140c04c0d4041c1d03031085081203000c0400711410414460141310254120f100c07440a0043c6042c020b1008108958480d5992000c03070031a10741aa07a0f9008121664400c140941500d400ca180c2d0100500482c0120101c04000010f4900040341107100c3c0301118603449031622041c0225411800440e01948000e0201ca410060a012400401d5209010800038a00c0f0003002ca07140b0309101104001e482c444040c07406100b4490140320300302d4600c08110380c0c6003103a40980c3c2e40f9445503034404d4004101010040c0c85451900da000c021080302908580c09403805118140000124003a0042c01c82003140328440030204144054844486150410340b0700048070107280b40081450516440604005e80c0304840d0014014103031402c1c1c1005001d80c4034103200c200c450544100c0f104040400b18441d4031031485c4135100d20309001e402c0031420391084c620003c0703 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 766418156 1250 766416906 766416943
    0x1c050a1710030b040c0608100b03040305090a0b0d050702010f0b030a0f03051312020114192016170304061d010507140a031101110f0702040221040b01060203070320 72
    0x203190805012400c054006d180c0040c10050009400920140f000d404449512032828510341d22600c0442c0c0580150f1480d0750b00091413040001c16868010150040300a00d003400251800d080102030300b100c00c000080811941000140b101a0740d0224480c6005600110920b001008a1900b11280d200c2c2c402c001103009010080882c14207400106080094401c2c1c031100860700403402444858000d511040810169100b50300c00030f00c1c42a5199044030050126400d0f587d4000800c1c681000e100c1c01c0c04030f810781c0c12a8000c00184070501ca4924401c1380545c0514903240c20040c0080c5000359103141110000c18002000d81c859100d08211181d054102c0303403d030b400880540107a43c4031580035200760005034628000c008103503030600c1191100d0201402d11442c1459040050405801414059a000d5070038031281c01208947e00c480f00401254060250b080c0c5060310b00f50b0300791801a0890320441d0301c207101441c0025000030051301030384542400034002c441c503100c1161500b80042000022442d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 766419406 1250 766418156 766418161
    0x1020d0504050604030305090a0803060f01021e030d060f080601050118030506070908010c08101403010603140604020a060c050604080d180b15040b030c040c021c021c050a1710030b 79
    0x4040340700b500a62080d83e081c0312070307182d1230a0943c1e10750b25020058403812007000800c6180c68884851082c28106005442200880c0848861207200b13022002c1150f4200281000c05c040c080d01c41c500203040707900c1c840001d040c01c15481300c0d03548005025860502c50050380b524a46080041e50304c00070b6500404441061510880007020f94400340b242c2c1d10990b00700111441103d000b00c0d292340c40b4205142000d852a80307855400c01003626020180c5030195620301020011070b481801d0a520510040000c1402c0e0400c1e10600440c05003540c004000c10603480b0391100000e0b000324038650440d812400350340e21075540c28810740007000355540000406002101c50801c101d034489000d842101c281105141001d242c40030b00090b68207103580709034540c1003900080540d01d00780d845202c4070308440c0f040300c0b01d40721500d040503841a8440003010140e8406290b9070822511070006078400d2806c0c6ca40b0a0415032943c40260041d426500191b94003100324000600706008001204001c540003c8480e5260 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 766420656 1250 766419406 766419413
    0x703140304170a231f0f020d0b090702032503030b03030706060e3411070f0509070e0d06090602130b1c0c020a20090103080d0b0a050a03060e01020d0504 67
    0x20443c04004490780071041d40d45410000b0f0007a0521180740410002d046641070b190903a51040740c0506510740203613580c0d02100030310805407014141c043c04255000036103202210412884400041c803580465001308154408140c01e100b82014900c554204000b03005a10700e8150701400c5200c0110760113220114032913081c403c0c0c40c1c0220003200c0d40d01e04903c0307690b11014503c4460b2010b0700444030901131a03142d502c030741030000c007000f4508042d940303000142401313040300705402c00d412680b0400c00914665010b00607803070701c90a103503040071150400c0708400c003840700450035a8007010b10251034181e0782c00705003040c02419012100340100720058241c080d0b0b01c92141c5212504840802d0f0070401d20006002621007607032241c5003003109607030010250003401c0d50310300c162400c003609031002900c3d21450f021529101c02c0001d60285101d101c10303a844000c0301044100300d913000005203214010b00e000400c43c64842402503400d5035049540410088208904a8064480c1919454000d4900010401031 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 766421906 1250 766420656 766420663
    0x20d0e0307150e1e0604030305090609100504090e030a08011214010626120405090406140f0a1a06040501052a0c0a0803030408120405150c041d09070314030417 70
    0xf00320440c0c0d00444803600240350121041840510790300b02c04200300c10f0002c28056800f506104200920300c620f4082c59070007292840740038105000c081000480c09000c00075641c0518100688500e00440c00d12610041c0104404010b106115154404035041c4040c421601c0d40d0040c1001000002c2c008503030740d4031200d40c00e8032201c9100d565080144c52000103080340032450700802c214544410f03003440c1c10034017004208840980b00316082580d600c01d00905400e605c58040c0300e581c044800154a10705841c112043d1031890005140321a00c29440c4246035a81d001607800766102860301a45910341a0300540070341d0107001100c03012040c100e0540c0b102c0b0500007403064003090160364140c0450b03030b1203085941d00c5c002a60002c11107081480800c4030365215011499005000724112041003840e40b20601c05848143d034910701d58100001c05000d62041c0d4100040000586000722240d031800561050302d504560200419494100d2900e000040003001640d024000140300d00001d0703681c44507101e68 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 766423156 1250 766421906 766421927
    0xd050f010e0601140306011a0f1b0c011202030f04060e01060924061b08070305071a01080c0a03050606061e040b190509130b01031509020c070510020d0e030715 70
    0x3c003500d0180502c8400d0801140710303030494a103200d140c80c00009a002000140c9c02c0141191820a81408428452000c4d405144180b084a1020706840c03200354000505001c603001c00203003254010404d00048040e1000c080358000d810120010340300c24040080d40c050700441d80104605810020540000c0340c030019040e201d0b0351448090404150f0760701e000d60324a441c0507540c808040740079514602050354000200f01c4c051103403414a203400026941c29009904100c401902100310b14010b0181c15401c002c400c180100c03c0320020101442d56032f40c65a2044020406c0e80140c00201d0640011180301c07804031204402c40245503203954560300350300b480750032540043c00d0b402c0e450146547c02c18090011910342c64400f5183e00c540c01d00c16040c03000039200809040c1d04140c1c1c0c80c1418004115103e0014020341010341002d640d0b0407402c0c010340c0c0f4050f180d401c183d10616107080401d0b50307960002850804071a02e410082c00440807000005c0c18803030942e11545444850400101006a00124144 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 766424406 1250 766423156 766423169
    0xd1205210a0f05010503060c0a031407082703091509030607120606030b2d1203090406050405010605030112050a081204050d020a0804210204020d1e0e0c0d050f010e0601 74
    0x20700c0b0b80c01d001805491080c8a191341542080010441c000b1010b0002c082d40341d06814042844c0109200021090b91300310307000760006041c881400f0910822044141501c0290380c007080a89082890060b01c078840c00d0714261003494005040b0005440c0503099682d042802016641c85181801016111b603102e8030320340000d1441c102d0041882402403058444031000600340c40150019010340b228030b1004214010300ca12501c200325601030f600d1241400035081d004001c0d54691a000e4140020380b4041c0d04214070070703406c0200520105a00000b92411143c42e98105030890b44d85040150524031510f201604810000504070f0980154064050240c0e110307404803041115018030480c0c0714003a015000308518010002000007046041b109807041c80400d5601500c14140c0d4001401ca81c0a840d80d040d1140c0c503610070101d0740308600f002c1a00750070300c2d43d81400704140c41401c1c2521a9100340b11113109084440d2070070701340322042140700400c00f5948001c0046031401d0300c41550303a070004d20519 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 766425656 1250 766424406 766424411
    0x2040306020319151214010c0908010614060901030207030908071d130b19140412020d08010f0909170d05180309210f031306080606090d1205210a 64
    0xc888802c3d103100c1c155010b919840900e00e42400c0c405100410300312080182d948030510018591080401e00c90030210700c06548462180e240b910030000e00b52820340c0d209407a100303000410141152606405c582c84040309280043c0c0c4c840071403800b59807115054000319910301c41c0380804100710440f036036103513000703e0b40300983c1030107960700c01c08180840d0700d00360700409818541c0301040c151485121a11a00d090083c008154110080314101e08000c0844e002c2c0c8e401d01c40040e007034400c0c41d0103104000f02a2010314101c1200d60514500c9022610148605d803e0181d0780c81c0040c080c02003541c0304400b0300e0280d58030650390b880d15200100140074259072040244028003915103d48100000319184554090704200405910707542400f103001000121403003500940c1c0a154585c130301031004181d0350a2840b24107440ea402c21200070203250008000a00681040040004070f50b44c003007910b02c0c0150b002c100c607200b40048040c21115805441b2399481d038008010644200c0c000c607105d03000c0c03207060b5840d0b04 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 766426906 1250 766425656 766425691
    0x3010615081e0606070f050f030a03020d0b0d0209011a120408073507140d090f120b0f150301060902090102010b0a0b1204050a1e03180b0d0b0112020403060203 70
    0x2c0680c1c0c03210940c2c40640c0b100c01003150302c000408124101c0d601c540070300251a044c1c59662907441c1540e00c2000f90000103030780024022080d000038420074000403400e45103402000b6850b804116840702c10300500a5114840003a400c1ca860b1090407525480010030b480c107600c0c2080e217032003000307034010b55070486088544001d003079100800900d56950381070345261001c1c00a20500141d612591101070184d5071403da00a02180c00c100800802d49080c10554400a41a113020800c8003014015000100009074101080380825071010030940c1083c10070b64000029240c0003001200c4a5500c107800d6019402c004000a00111035405070840104c01c1e0000e01c09144681c040100c00c403014083e00f20445002d0100d00e00c180b4000000650003031103482221300d0301045490b0010255100c03540420020840e07500b41c0e04041d80400480140c0e03000d012415506824030030127070900c1c0109a05110041d40d40ca803401c3d400d82c0301304a209034402c428103045640301c3d2a810458060750044404801c0842e10484 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 766428156 1250 766426906 766426951
    0x5090a1514030609121602030f012301090b010507060b0d0b0117120f12060d0b0c0913020c0705040c1704060c1e0206040305030601030e060702061b0c0c09060301061508 74
    0x2824170094010341c803800d1400504844400130224080001c0e81c162081c00c54003c8203640900c102410306281d0b4800744081c03000e42c525001100780503004846a00c0c00c010010340c0310790300501900c1304258403010215812540402282c0406490400a08440c05810000500b00c031181c0c0741d003100081c0c038400d980c00540103e0640810307114007140c0010410042120744440c4803496407850700090014010004140070341c407410f00c106070a1710340c44504500000d16801900d0251150242000c0c103060a41c281034458410a484150360310035607000ea521040c90040c128454500b0307010542819001c0308441c103241c06d0003402008000c40070300110b511400c0d5000e24490200407030113038145690040c00c080c0c3d142c2d03600312030759003000d0049030501d07803a051084a040030903c034407481f50640c1e600a01e1030b4901610719500c581e150946040405d04100404108180f021800e00c900f401c1c2581c04034240d40b03500c0041780c0145115403004c4258900d0f1410140d1150344071080318000d51180c2103190503901d4910 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 766429406 1250 766428156 766428163
    0x501080c090d141903080c030a061a040602070f14130e0a06051e0402090c0a0306030f05010209030601060e030a020d0f050601080a12141c1401060c1a0103080405090a1514030609 78
    0x2c2e0040c01046d0740380300143d0305121030001154400601e44004c2110b84d0f4809003a07100b0324016a041541e1080450144039490b4100603032001000040b4034410164a003a400d00e44100900407680d0044c00d0042d400c91a4229640081407804112011541e40350500e083c014001d1400740c81c07146c0b1840030821020041d28540055600890300105680c00e00d0304c3d043c411951691042c0c505905142c0c50f010000003003996803000f1066140507900159658140d001010b08140051300210f041c0022600c0c41c4100f920f00007096649180c0c10381d420750f403c45c050700740704045102c440c1d801072451107440300101301c00d200801c20341d100c544a8007000b444011682000d0f1203800e0058000703004440d0501484c003400c01c112103000819003280c40e000880e480106021604010241c00c41000f0900f050212030805c103442c2c004851140d03442c0498022941180d80e2417102d885180f09041c41900a0004a110200c03035a0084050002440442031020f60f035008030443d140610140a201b4090000040e95018020 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 766430656 1250 766429406 766429453
    0x1f1205060f040f120507120801060219030e0d081b0a0528020904060507091a070b1b0a081803120612030c160824010501080c090d14 58
    0x10025000303503500d980e42001005401001a140060a03c11a0020494584581c1c2c0c1c68070680c0e5401c0c1d5249440e040242c8900c120002100801c510000100070203a40400c0c2d01e107107a141c581074447c00b4809820203c0780c0440021041d5031040101e0112410000844020b02104000380140390f020303d2178254864850552070f030090031903013020714150010861840381c020180c4220f40500100409500400c5121070221400c0319801d6640d018842043c1c0c000e60305200601d0300d0b00404814240c140200700e02400f45c040010000e094810219807040350540c103000c481041c81e00e03016254084418003c100f0403040e59107902050309120890f0010320080308403503075036600946205031501c840702408000600043d00c3c4e02580828041442500810b10101901000802c03c0206590410043c3c6081003101150140340d402d100e007007190b00e141c41064032030440c1d009007402c440350b5550030291141d46c0300b0a120b0513403001c80c2c10154000c20203004951200800f888040311001c1c04404004081e41d441c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 766431906 1250 766430656 766430663
    0xa08060c2212150510081e0a02061c05010f0b0723161502060f130f06090b100503060606040b180306071e1b030c0501090b1f12 56
    0x810807000d422081d565001810315100008680d001d54a01c030b410200748038000221101054a416a0340b0795056010b410b0b000190a1946030741e20703103001c1c941940c40e00401000031400351442041c482404c400d10225a070744c0d4028044a80d10300c20856441400d050220401c40748616120020030b601c07600f01d0b280c106a50818448910702030494492418542c01040301d815210a03019003a07d580d01301784440617503107000d101010020760400310800002e105d16200c2d0421540010108503403901c44101c102c1d004000003042410302885ca082104600107401800b034649810301008208018030042c0780c40c482c1e1401601c012066840d44100b513180c42c000d0b6070301640a04184000e10503a0741c10b0b4001c094400c0a415400c1c126550000400c2c200001280c0c11000326106007500912070003103142a000315042850054042e03640010764018548104c0382c060104604e5417034000800809502200320181c01403440c0103540b504a001c14844081c62100280d001d070403580025806804034250784e4055032 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 766433156 1250 766431906 766431931
    0x70e010602061515070629040e0c0d12050f030f012402070612020412080c060703091a0406020d05010806011d2e0b030403050307031d060406020a09080303010906050a0806 75
    0x200408940c40c070b17801c041d2042d00d0706541c52080911785501c4145110f404020000c7c1e021b0f40c800540c0800084952134442d03020540c00c0030307c0c14801a03403000d003480042c1c0d501a42491241c05411001c071906d01402440c080041000030500116401d200c6411303040b161030303c60381415040d4040410000c040840800000b6902541007401894011490300031007402c4140700509060703481b03120045251003000306071046940010b86916000003801700541c0f0440a040520035050740d555248040d00c83c1101c044460700c0c11a0100b01004101c0d01151190728041e001400556100d4402031348904007841410540110b40170032010800340c0031402441980d618010f04400c02e5141c5c03070f420440118810100b901c4406400204000030110091030086019545068a929100701c01808440344001c0800401020f054102d20241c00083d44503401944800c005da02c5410001040c4c0b04200b213508101060b020100004c42e0700c2c102a1300c40400c0301e000703d40c00b00c0780c00d0780c851100f500e440d010b541c0c11040c1300 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 766434406 1250 766433156 766433179
    0x5040f1e150c02030a0c080d050c0c0603130b0a0606081f091d060130020d170c0a24050609010614070f06092d02120f070e0106020615 59
    0x100320110108403022181818001c0c2032450340068100703103412200301c6c0c6202c041c2205103d000c904108500c0c10391501e0030214030b4408801038165440440e806038234030903200000018008001a640044503035801494407038541410a0b2903030103042e1500520000405c00c0000032550901c00e4803181c5a50b04603008014120700b840d1041001e48a0f80310508001850b450058038050410054180200354855048001070a40e203518030883c0580000c602c0b42600301382d07000015944400d0600c002030752004591140c103550200c0800a8002c1d00072010090240390200d0092100b0701f08029401070295800340e150b2142c0c0c0764000110760040c0e5403d9000035201d001849054003405401000325002d10a00c5d0902220340d031080e03000d1704a48000c6074000c3d1920b520004120402c44415940a40341c007044404100245030010b12011150010b07100b60f01d000845000c1000c284100c40302c0504100a031a03d4a840321941803103075500713201c3d5034018030540300060180484000b0744c403220803008101d0006803 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 766435656 1250 766434406 766434419
    0x1412040308190f1710170319050901090501031a0a1403060a140403050705070810091208041101050714010c03150608060108192c010b06070804090509030d020a05040f1e 74
    0x114020300417518240c00c104003148900724501034845440300c003802541d961951862014207403090010302001d000c401c1c048032150744c0e00710a6010945d4001c4ca000207107211043c205819045d0365140c0c0a4012f240701001181100c411038408002d500161308464281c0c994601e01d80031280c90b1519011110580ca020500003031041004105080c010380442d0502a1a8400e844c1440200104180a5a42d844400341000303000e0112410048075401e01d05240c0c07030141c0310f020442401c001414100100011324804124544910203280c4c4c0e0400000c000540e04140c01031300920882c1c555010303100c010f000005401d4131941140d84907910603034030710700d0544a284440d29500d0368502d044100c0f91316501c0c0c00e04118034140000e541c1d00c0d900c411103d04142c401d041c09003100c80500311140030f1030082242201140030842114116140b44000096a0b5907a941203411030140241d9600d14a000048481c00d895019025005492201907058200782d90381840b0800183ca0145080440252110406c0013 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 766436906 1250 766435656 766435697
    0x150a0e01020307120f140a0905040506040207140c0f190626040f030908120304140c0904110a052b0c08030a03020d06150c1412040308190f 61
    0x96a41801200c0c10880030341d50303000ba01080700070010001031440e03412032020f542c8200344485075a040c003106031404c503643c040240413107580c0c01800d026035118800b107420b0749c60740d43c100c9075016000905a000003042540c0305440340d0008180318851212640d1801d207610300f1503002c66107004c0394406821035500e4401d080da180308281000c0d260403c90043c01d0711a07004028010b61086200302c450905129007807501912031403850b0041c0b11030343e100b003401c107060b0605401240c1e0404d0300407068401c0303c0d100031002e5281151581a481e004a032031002e205c204101c1001d00b400000c400c94100b02030030740ba00b00744403040081c11562501c848100020704400d03c4d28018600c04940243c0803025030300d444507003c07451603224044100001c1d40c00075050801142602c01d0384c0240c8007640c0155800c01013010010000c004141c03001d4000510b01c1180021480704000421800c11010f109070b8035aa03a0741441d042907080a0701c16040c461032440820321903442010102d0048136242c856803441c00900300520310707 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 766438156 1250 766436906 766436927
    0x90b010504090c1e0503061503060d240f0203240f03121201081207170415171f090915050a050106180302010807050307030906061401030b150a 63
    0x14420100400b054082d0039004407400c072502d0fa00c5921940100c220b004960280340d040007820400180244800ca41d81c1c036010390303c0c12441d8000039403a034540100184a00e030090030002c00845a00499900072078640304a008280003048003080f00c400d5103049842a40b0040320003004240c02c801d1060940007080d060345034603c40160103242c9044030480404d10748800c04052129001003c1108a020030192400a0160a0100240008201e1a2155843c5d4051441c006101d14030b07840c030107400381164805403001018595030303140003142c4006000e802d081000e00542d25072003440d070001303040c07001a4081c0c40601802c080080756003440d1140b08070080204070401c841c0102d010b800044060124010a4003458000400041035450704201421014059680030904950741c64200050b1780c0100d00303d03610401e541440d540c4c036a6206801c0b8002c00c1d01e680001c2c000741c6403d001060550303844845c500811000e880030800c07078441d01c0400c210080045a184644041003240c6440310344030360403103007 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 766439406 1250 766438156 766438159
    0x3902061501201b040f0603050a08030618010e01030c0803120105010f021203040803090f070602100510170607180b04120c1d1015021b01052703010f15090b 68
    0x80301c1e49000c0542072041d1003e00e000c0b072032552040b220240c5414860111004c00c406030070001c840c034558616465494405011b04641030110000c0d0040c0c8840303c40700302c1c40030368000f40c000383d68541d115001c5d040402c1c0001d580700103002c480860700600010499400c450791055441c4a41e02c1c0c6001150b620340c56640c4241140912244200c5070440c40002d180280e11807003480f41ca9207410b01200d8070307001c01107003004826413100d102041130540106985404c40038881005c038082d521062280b4802d01e9503032080c4c0614020a140403c800000700c0e9650007540c07560f80b0400c10841035034081070045861300450364200c408000400017a502010b28900f4030303101c1c000303420845170303140c4800f5441f0302c039441a050442c40800401140d10306c902e2140020300134006001100e0064030100a55800345051f04100d4107841500388001a8065000c3e10100882d82c4c0d4030042d45481d030701c0d04180d800c4803145180c0c080c5d82480c1c01408403c40c0c9000d030035038620886402c044a03038036003001c0a01802508a805 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 766440656 1250 766439406 766439447
    0xe040b0c040b1b10230c16200f0f0405040c0e0712050702150619080f0703031b1a0c040902180315040b0612013902061501 54
    0x1400100c20001e00458840b08241d070743c42ea2100a80036061001600701c07411001d145c00c44018000215154988880755200c18513011551546050615481200146003a0b8000e4110940c200501c4130707565140c02d007080c5003c04020300309005200c4c207048140c124a41c403000f0707855495814101a400300e03078041e0291a4141d403495071b4240509000b0015a02440010f200e60841102030b5214050300e6001145c81c401850b81c0c0c1c03c03141400c4081c00000d40740622032818503401c00d815a030301d0940c1c880900545030a640745c0e9507176411086c0d0b43d000107100460214503c61034103541d0070040741c491512550424450840d00c1e1443c1c07010000248000c0c80703068003890a020101d450042440600822242c2404451079041c0d888101031402840c0402d400d04890103604100c006010303040b006400c46425102c00015400c86202e440c007514689114603510f03120000028140540640c0340c61011440d011030b9901d104c01b8480403612100e003100c0914503000d2000425819501c80c40050488100840747e9 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 766441906 1250 766440656 766440659
    0x80d03090f0204150f0816090209040e07091b030b03060f1012050601030c090903020d1b021c0b06060c03271e0405060a0f03120c05030d240e040b0c04 66
    0x1422a081c00e007403113072004500002449030400455000016103140d90041440034090031008032081d40038020110301070340208500700d1644458000e2140003920344113980d10303251075100745002001e40340e004c030f50910a00d16a0501c2d00d40a44a10011400d028010f0825591051603840c1000006041105400010031000841a040c2107103480741611800180c0f00651550800300300050480e04001101441c00c1d0b1010002500065003601c0c0285600f0107004040d1900e14100280415007006074100180c02d001d4100805e0b2400e0341140a8400c4048140644805050080074003034110b18400b10b034410041000380c03440d100c850b4a0b0b0000b42110105a0f450441c02003402940ba02c1c620000a511300c83c2d2503009440c060103516030003842030710004549841c151401c9420540e83c440a002c00714001038144070b007440f40c1d01d000c0c942078004048943d11070b100310092005181c1103442c01030741241d800c5240790401c0f0000402e0f003103c00c05580d84000f42c65a4481104192020303010801c501c008010 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 766443156 1250 766441906 766441909
    0x10180803040b0702070e070c02190f090e100b0108130c093b1e032503020601060c080f09031e1b0a03051f110d0203070315080d03090f02 60
    0x641c862442414204064244144081d1418000d500042d400c8812007041044495000280030300071601151449031504660003030312601140c1d03810042d81c10719400300205012400d500401c10301d0810070202c8102c6040c040070300c02200c024222507030002d46107d01145240300c10309200c180703180c018611104d000b030b0b458020400300d6071203a1046403540f08020811125240e00310700381400320111801005400110020a621142d0f0030100c4a000414000501c0703803448100240c91907140700141c04190107135811500480c1c1d101c01501100144101d000102d44e9910411040b803500b81c0c40b6460702e050200781d4800242c04d03000310b801c40c0c2d0580304040031151114403180d040640034480501914070648441030070401c2040c1000b0304c502071034602c1820400a10b00043e02d0f010300c011074840140c00d503445034100c00644000b102d4441200b4010a0000801000c1d07401180154a1030310200201801280e20198401d214840c40107190010000f010005000b80c00004095200d10355603609040c2560 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 766444406 1250 766443156 766443173
    0x402030109090b2802070311120c06071d04320105040c020f031b070f0321110c2103130509060a1202060d0204080f0c03010f0207051018 60
    0x28040055507072140c0707080c41071040c0c9503903064126242501d009010b5039810b0220202c03031111204820913a82c0041c0b280d05244c8111444000e015005044c1c440039010310500554540000c2c070012070034068580400c552900410350b17261241800d6005110701405041040020281d4003800e503a81d000888a80020f208007402030a000701c909003800e422941014107120480d0340000121055500c50701070b0318848000081a02c48282540c000140150020901e060814040d640587c03000302d100f46011080180024039603441c522203000c003142c021000d09040b11400ea82003810440c079044240c08030568281003002d0701da045e064203035aa03090344400800c24a1540005c500c1f8511a080040030300241c03810303050f21600a80300b195680350103818015042c02034088842d00900c10702c0001130401044401ea01905d000780302c1041696158610454016290020342c040b9901c01e51805c1c100c164014028400c2d10740603500f200c018954020364054031401890b20006911185440700b03508400a130800 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 766445656 1250 766444406 766444409
    0x3460204050319030306080c0108011401030b1c0506360717070e0a1e05070c0b040f020906030607050d050a0207020933060a0c02130513051b10110c04020301 69
    0x650070040f428141c02c00408940700c0d030300651925080410815102d0784d1100c42c041c196081d09885800200c81c040043c0d00801030903101c140c02085000c859038902080b2128406114000c1c401da44565940003c400014490041640648000742082d02000030f050346c81034404d000700c18112040b10741c50740c04a025510805442c0103c5502071101400300114680580780c10007444031083c00012104c075070301542050341c50f88841c4a19035640016020701d114205d000c00b0990000d030b072807860f401c0906240c4000c095291007680505003180104002d41000030f0042d10801495550506150f000c01100c0f0151030080c3c81c10540c00d4003481650056541d1924150140d600f1040d080b95003000c0c0e40903200c1034540cbc803881480081740400e041c50f5913106c2c04102c80d18500c0c4e91a1609401c10248000340c1e520780145000441035241004001b000c801840e24241034a0007141150342070032094070b0f0b403444090051940c075009014207281ca0101401080c8081030448205c0583c1c4680502201040c04c0344c00c03d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 766446906 1250 766445656 766445683
    0x140313080c1b0603070c02010503072c01170402010504051c051b011b0b0f0a1b080621250b0f0417010509060411150f034602040503 58
    0x80805104814112100c1e03440042c16100141549032003000500b0303a00041c00c0c085d051100020008030410300c954019040e86001401440780c0103415542042143c0000c3ea444d804100010084c004500b200081c4c54400c60341607403401c1c038140c145030a00c04440f540d1000380380d90010764503241001803020301c560301c04800302842c881c1540c03820724001050b0440e12000d800c103408096050b2804a03031351910003580001e40c410760304881c0d02d070042d9000088c0000d82c683d242800b003034141000144d0303100141900404088540c09a98106400080306c80444448a004558424445011282d00009079010305543c04020f404003079036240022400c1d580008885040a4400101071040b52809600d041c0b0b0b503c402c6000b00b05928107040c1e016070710f60000d40050002640e6000c0006c20395100390000500444401d4201c0d15000100003410300790b0415940301d280c202680c1a14107244986a1880c90b4031241407d0041c010102440105600c80756607000c8800c05408000101d03803514200b241c0500da280 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 766448156 1250 766446906 766446913
    0xe0f10030b0d060b1c05060403140f0c01060315180605070c0818030d050c15040c050a030302010b090c0a020a170d0c0e01082401110114010f15020706140313080c 71
    0x80c102013100c91441c45d00650f02c1c002c000710b20000480d0b8009002540701d98107003440400001c003c046903801c0d00400742034203000390300015070181100040d048402107a10070168601410b441140390019520055138401c104000000c000d408100d903034101d01d40214007820240440022a01c1d4003880e40d000309041c400d071f04103503490b0441c075040c01c00800010215601c0c1283c201900c00d000e0036210000880311240803c0080c0100b07050240340c4ea0000000c0c003004200c11300d91941c910300607000e4554840854480c01100e400201c200c00081c0441d41da1105560107045002d07900d075541201904200b0140d4940001072244640100039841a4005601d25841d040300800e04030000416100004014841440042884d0041c00042c00102c04000c4d10900b030280d0401112009507004241c1c140c50105c80b591544000603018401201003026260b1410a4460340c1080200580e6501c00500c00e101c0010030103109115680c4c1c000d405190080c0045009143d0116030780c03a011403e81103060004203030f80 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 766449406 1250 766448156 766448171
    0x30406110105070e0103150806100f12050c0d0809040f02030a0f090c2d0605040614040b180d0b180f0a0506010e071b030f030c0e0f10030b0d06 63
    0xa8000000303428450349000244500d1400d960000c10f212503019110341815150b003400a1090b24803500c00000c4d284c034608075010383c5492a900506515103118a00f2000040d6201181030210100d1520881c0c0e0010001c014940d401070034000c2d03940c10028213940c00941480b116866031303164003810b1000c0c542c0300d0026881c1e0415030940021540d586d906824800d10340f159400005444a440c20202c070010019080060458038469000c420b00b49643c00620004840100c0c802d500000070f00103035088e564400d648400c04c038042c0a01c51080e4091102008001c0c0440c2400c020f0703c802008403598060034074001c00e9110303136650188078401d8803004903440d0000318503003411804200294841071104010b040d126240e803603541e2119018054116030909a030001041980204042092402c20601c8403400900c1403c000301a5441440703000c1c0003904001003500301c2441020709a018900050400a0382408001088290f4541c004502c0a0640b00c10500a0f0381e5160640c1c200454020100400e00d40e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 766450656 1250 766449406 766449419
    0x30203030613050f0a0209011206120b01061103160f0f0302010b040f1a0f0307080a030c02010210020a1b02190f030c0503010606080a1a0a0303021509010b030a1104060e04050304 78
    0x50080250149501d0318020030800184e10708079440f500001e03c0703500140e5461400c0b00403154181802e49005506051000026404904084180d800b034090071058200da6250482101c1500407280000d0704c952023030090040070f00c1a0300349004110301c1101e81009000d100d5848101d0b042c02ea50081d00983d549401090650829000d801c00c10741c20480c003002591032500c1c0d010019038080da80c01d0300840c14000310b451a0386041108074043c05e403241c00c40c3c0507600c562a0007040010100e40890050180d0002410075100364000d40343c20311140d46880a181e0612062001e25000c2a0000e9a2007280078130500c2040380500c01c003030003514604084050380390540c2080c1e4240e980d5540001e000340e141000c1002102e51207203449801110f03112000c22290b03401d880a007580350348803c5940e44503c1ca00d4002040540000c1c24840044c4030aa007405607565102d40c490072190f1502215805400002183c0001620302d00021141c40b0014800a210740e101c1c6041e110030a800c444c101c945501c002414010b4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 766451906 1250 766450656 766450669
    0x6080a121d370b0a08060a0909050a060e061005102c0301060b07020a0b0c0304030c120501050604090c061115090114090304030312020d0914010b0a05060f04030b06010c08070302030306 81
    0x2a01220010300215182150080c1c080c8104103004c401c1040c42030119040340c1d0344010510040442c1c001c02d00c031a4225003070035512540300080484203146061641044041e02007452031007809070840042144d860001405258820b07880c980040081200c0e840c807030115044108600381d404401801001d8040700241803c540d915002038500d890244203250040e59000300758001e5a80d0b407c0b0281e1548111b84485141d402130380c2004088031b5844001180850030b03041c850040c45d0058000b40070b0358481000f80b108a0300c010001809404c6030034414850039020f030601405480b40c0e2401c4401c522a6003c142c80038840607103101e102c07230751a10200150701103020669600081e624000d103145c546190b50151855a16410301d04200740c01082c200b43d0f09040341c5c002c008098014114010381c0c2060200c0380c0c002d103005094188078121240010400342821415264082030568840d8901410740d15440040e500003052141040350708c1c0241070001c1c81100140a1480c407079002151242000b0080209 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 766453156 1250 766451906 766451989
    0x20a030b0409200618120703050f031806030f06010f0210060b0c06070203040b03241c060c050f03060f1909020d1a1027080a0606080a121d 61
    0x4a21300c140300004c1e00c3c01e01740100d00340f030f2607007140d285070071400d030402c4641440c00581c0085c1c40c0c0d000e040003401030001d001c801013030b5040700c1c40381748941c1d040c690b41000443d00007554259000700c0c19a0014044d07502800a0180c134041500482d0400d480702c1e0308040560b1955000005003400c040380850740d2010400400390085c2d411b0000c1d6040030b0a14000c1e21442c00000c1c107004100e0780044e460b800704c0c00490340f0040942005410000c2d0300c0d07001461440c61100e250b4045409500c1c104111100030720650960384041c03091003000d803031911818200441d100c2500314150b4061144c542400c1c81d43d000700c40304401850150320240e200c00c5040381c40300455454200c003140c105080408401b00b603071594464400b8805a0500700d4403240c04640d6800b403144c030001d0225040d204440302003550000042e800007003501c07071141400102d45031507a141c4c030388a400c0b2005184022070054105064000c81d801041000d1244c54000c20000901c00108550501c8088160720084600d048000c01c202a80110 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 766454406 1250 766453156 766453159
    0x305041404060303170a0912050307020706091805090705280905011805090c09091e011401051002010e0303070507020315242205060120070504020a030b040920 70
    0x2c0c080c6035450103008030603103105030f140313610030140000c0d514185584003403202d9401041542038405600d4001d0190340c029a00c1c5001740c450354200242e01c0b44115400f03826500d15001060b5903452001c000005040050f00c410b0103402000404a101d0b2290b042e002c0c080c1e907034a07800d00604031400f05d805124602e82c0d0494102681450010f01c95218110300354400340319000c00000702559079000d000c1c03c0c070070003200103603101400b101403203002c1c00006401841c5c080c0c2c0001544101e00a24881d50881e0747d910a44c81c28012064010801442c0c00800c650440d8081e00011544d0740c400b0340c1481c1540d208480640c00301e1400709900007035080801108003c0d00c07038400c004d6280c0c181000501300c441d05078211510700d001000204907841d1034103401000c219012009031500d801c282440c0c44007500702114018001400215114040050100002c1e140005000a0070000b814201440060750195407140c1c01c1c580c5071400c0510940311441180fa406006685a0898024118038440283c0320040c040f03 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 766455656 1250 766454406 766454411
    0x8090105040f02120102090a030c15023c010213090c0509010c02060903011503080408010509060115030203132102070510050d0902031903110c060412030e13090305041404 75
    0xe6207402076107021a8040700c004d2420320522a1080c0a44035000b040703074001c00003001c004100b0416424802c10303140c1195086601071001c1c0c038100c3e0341d1803041850901c007520000c50004050707040c4041341c03120110042d050980c60784100c0348a082e03a00903c018030300d42488803000c008102d11485000400d0240c3d150132481c024034503000814950000302c010f032081c040003170044921340d800d601030074041a4206103103180c1a81c17824448400e40152162000369401d000c0001c80c00c1d0000f1800c4c90503070300048840c0b0b84024924100305c009402c004c03c084e9859600b4200702010442c06000c1c0300c03205201810b040e42c0071030b024030001e0a00d041644078030f00070500743c0f0805090381e8000c000e07111004a4107800080403411800040d02e40032241907a03000e0060001d002105240d4006021605244240100c0315134010324820b008080c415846103080b01104420018002031103251540718400005004480c6a140602a182160181d002c00c4001c580001010031207440d0208090704c40761003c6a08 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 766456906 1250 766455656 766455661
    0x4080720031c0f080c1b0c030d09080a03031505060d0b01120b0604051c1205120f2509210b2406070516090b310207030201090209090a0308090105 64
    0x7501d40100d4000e000705000e61980000c042030900000e540203640121100132002d03c160011300d0f07c0380003118104d4040d0041000040c8a18020412682201c1c01b003401454a81a1500e00f00c009068210810001030f0340c0c2400051560f640101511082032103e200144010003c0c002500043c000203009017414100642000147da45005440440d6000d44034036441000d0815506260b401e20741e0020210340e0403c001e41c501d0741d03204c40900702c0400d90340d000b40d000d0303100d445000d031420400710740650414030341180c11f13200b4441081c0c0c8082012aa03080a458082d200d800c1505844600b410703510310b0040ca600180144011020002c0d0040841c40703580341d0080d0202402214039420f084d2080c00782074001035075010400b041000844600300c6602e01d08079261158101c0001d000c00e41c0e0320520603100710150a150034400442803001610810142006100000c0514042d401880302a01503560ba1310442c409030b10340c0c04566100d4810200904100c92151502801110002e020f1170301c0c0ea80b41c00c04 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 766458156 1250 766456906 766456963
    0x315140f01060c0c0308070c050907091211300709060b07020d03051204060504020901051807231c060f030804030b0a111902010c020307020a0e0408072003 68
    0x8800d042d40e50500d4100b41140503401c2210300d0381c100340e000600c503200c0064880d05121841c0310403001d90b141161382c200181c40e050000c550315801400b528950f214444045000161000b007504000741d405410000b055820121903409140e1039440c0b08100e000d0147c0240080d54144400c2d809000d110b50204055400c1c114204941d014440c4002e0042c0300f02400c40080c14001e2055551092481d21503034102d10b01803900320054070054604078000c002c088004036036071030854001cdc01c04202802104c002c0c0d41c0c4205c0219519400c0c1070b48402181101e04040d110050014001c01c200200201d210010040070b061480031100282d0201d04c0e610040d090038800248442c044074200d907040681c142036500c1e01342d40340300100400d090010711468006842000e481070f5800158603000640c0003000410000c140998407807003660f900950081c200c0300c00340700c45d0107844811600103005e0842c003403c206441c1c1e581d0007440d0000f0440308038a13056410340382c0246410802d80200f4489a02c908503650407500 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 766459406 1250 766458156 766458181
    0x30f1015020a1b0b0f03271507170f0712020d02040f0e0709090b031e010c03450204020c0708190b0118090c0609140a0305150408090a031514 62
    0x5900713110005c00080841c3e040c00c1d160094018440300301c035016060340c0c05074110300d542d500942c12800c41640340c400026552409540d02500c100710300400001690743d0070700e0111084030010b2a403000d00003c15248840c903070361880034201c1d483c844000140c0d07681c2070404150040003030303502c1210b0414140c001c000006a00045000441d41c80c2d44000c034003241d5a000003420040490209408815220500607060744150800b42c025440b40d10108150840340c0c50010403500380c0c0340101c07001098494442e000c8401c44002d0070b4502c44450680b240d905160340024107034bd110440e01d100d150b00c40c8006108001c002d010341001c4400d1800b001400600a0340c404840420510602c024000f0316200f02110601d260003010405510101188481d52030f54800307003ea4905028950f90724864007041060307800c11081c05420350390043e0080460102c60713a0300302c0b0f940500500494012806001591082e100c1381e4040014522030a81c01c0c20401c0204100800c484484000c00301c5146200d05220307501e0102c0703 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 766460656 1250 766459406 766459417
    0x90a02010527150706140403051b1908120c03070e010305070e03070e07090b0f030402040209011101020c0312090c0f09091212040c0501020a08030f1015020a1b0b 71
    0x10941400008100390140101980100d00b69005051091442000c10311140142006032161004002e040c888104500300400c044500901060701000812040d01010706a20000c486020403039940d00c008801b004401080c06800302c40503080414181d01400034a12225031203651620300a056190004c0018000d540706005107041c0340e40c0e1008180341d1840351000800325080602160369150340c2c6c8107100181c2400301c42c5000040c515204c0032941a9111003110801d1988040040c1592519000c00c8000d6100c3c07191075040c028000b25286802c1828006800705180e000041c40e01c0d40751b00f40c00b421781140300600d0000550000c0d03048004aa031448001c0c0c1947c0c1003036038499030b1640d0320703400799251004d80041d542d1800800704444800d02441b60005200714030a120b100c008540e2039005a0341e440075110010309051050001486403e038030764601e917000640c552180380540c0e07102504c042c004070072000c001c0141c005946c02030500c1401e04034a901e9000d040e00c071000c4070385040b50805550084 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 766461906 1250 766460656 766460677
    0x1050d150b07380c0417070e15010819060510030504030207061e030b01200c1002010c1b0602090405040b0604110901090b03040212060106050d1b0e01050702040905190506090a020105 80
    0x903020450000080069174082c11100451b02c94080e544c40c25180c0d82e00380c0b4425001c2070081100007c070b05148604080d8258401a100c4611540340c42000c0c8940e40e00580c809040961741f1040003500d80d84404011070900c04e10b80b0009081d05141c10001c0c10401c081e0810000c0c02141c02110141184044005111108900c0d0000e5512a80001240c80400c0d145201c28115008404042401804101c0211a08003100e040340761004c005026401d1750401c628400200c1c0b005083c8804405603000303501040e5200780401403800c3c2070301d0000350840c0d105840c02e5a1100004080081c5810030780304501c0c0144094584508007460b103000208280b010340a00c080e048800710114086440d40042c040814a528040e60400d60b140c084c010600d070002c03000c1e811000e0405100200000c40c1c101003401543c3c2d903550710585405400015140c0da031080804a070400c1d42c903098000807a00c18411602020045000c900e940240ba091076460004050458402c9401040c40c50b00140c0c0c1203001c840d8100c50 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 766463156 1250 766461906 766462013
    0x307022206030803010945053c010e0c0105090a15050705120310030b04031101060602030301080d1b140f010c050a0314070e01050d150b07 61
    0x404010384024103803562008040c02c0b0080008501000310f42c20010400700c040202160111010140c1105681072a421201a03d0411241c24110340031290b10b50400c1c0c0580c04032448201c1c94404080842c2008542c410200c034a07060b921254800d0142c491032100c1518001d0000748100101305031540e024910103410f100000071719614076101c00c0704600050404a11545012072074600c041d00326404003d00f160540202c0c1200b0155411b40815640512940105010240d0443d0707508190200301800c00d8081c03086845501c29518024024400644000e9001c0c3d522545800820b51034082145849814010401c184001c0260061204950290407200006900c403404a100d800c01c149541650980d500304029130110355041001890071001d10780e400c00158001400c40d10201005079800c03800248003005800c00e541c400c3d4003803c2084403600000400d408a42030b51a0030061641c40021003d00c08a0307000c060180300d0404000005040c1200d4226200b95000c180703803030100c030008070107014 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 766464406 1250 766463156 766463209
    0x30080708071706011211030f0105060c0a150209030d0315050102030408030306090c22030c091b03090519050c1003020f031602070b03070c0c080f030a08150306040c1403030702 77
    0x2803084e01001703079001e2107400030021000c80e00051034007079204035880040c1d4200c3d14000515803c225044804800600014101003101c40e030b02e015441c2c80d044844c04d0301617024031203240f06179810701a20032180259280020302e00d40d450312500d0f0180d02d5502050540d00203101c07c1043c18008401c503503221030200c43e42d03030b92a0744209a0204a004a04641c0282150412407510303030b0204c0d220800541e0300503185084816940c50305c81007966040c3c14840201002c00b880060418020341114601c04c0c410002d40d080103542d9200d180000a48035410b407829400045071640717608010750340041c14101440c040d03183c100d8140c00d100c0c0354400580b001903120101e82c8041c024600c28481403003c3c00402000d5072340d07800c1c240001070482c0e500320340948403805000800188400005504035001c49040055401d0028110080c0d41c0c6c00c1c001020041713001252014011640d03024042c0303512952141803411007480c00c040d0602c800300c001c44070382400380c1d000700040c1d80542c0da440450566245c1c501d60380c01006 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 766465656 1250 766464406 766464409
    0x90b01020106091b23130806130f0f230a02011d031213030606091a03070609050f0a08150906090705060301050402030403020c03060108030c0c090f040f30080708071706 74
    0x317014a9220801030400820710b800081e10008641c001c445602e4200d4845480b001034101064948240c0200300b01c4405031490001405494651555070107601e0014641404c41451990102d0441701502e06800c8404603004540c0c0144000c013800100044149010381c024010a60340d051110f01040c03842401314280510120300c01e2054040c4d6408201440000e40e90500080501078071900010700c40d000d4402c40d4034a04002030000c0840d107081c2d44800d04145000300b8040f000040450482d04424141c4020450301e0003000f807048001d04203e80c21109140100c40e990418601501a110503000820304100c5039582000b641d042d070310101c0300180d60352030314074007a860542d048030556018003c2d00d000181c40d05001c405480280366250903910301c00114000c116a4074021125440b40c0d04600780070402017085404050403051003103e800d0802caa040907050407204000c10720302151600c05146424540c0c0c40342074140c10400c54144002c480c14120310140c0405c0b0350302c02d091003413504070f000103006 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 766466906 1250 766465656 766465697
    0x3080a080405030f0c06070917070509090a0b040f02210307060b0406030b1612020c07030f020103020f04030c08100207020f0108060f18010e09030a090905061504090b01020106091b 79
    0x380001c00c0002e0340c0c1e07407000400311500d071306d000c549103c08030300d10799400202002c3c012111399108401e41c005d07211742e600384400c11040100c083c1c105d280e2031003440d0320640080c08800c42680141d0045c40000030480b024810070601ca83d01c424040c1c8002c0b20ba0306492022580002900c6400c0d40c4088003159003c1c645000c1001007500b640003a150049402c14014502140300001009541d25075541a4802200240d0003d13446030700b290802d2a40035100400114040a480021142c414900580b03400150520300c4a00d400c240c205660710030b80702c441080840810026030000420640040d810030b42150001280c5407000102c280c1030141c480700060050780e0b0700c000001c1c416401001e8501c0c070f030b82d4480c040d5070022003401036124800140c00416a142c42c0001034071107101d010344e00c0600b014100b1036807501a00300503050300d40041ca24a840f02c0040d84c60320180000c0c1c820000b0018800e441603000a080d501c0301e5000d0760360503280c02c90803030b25040b2400d41c40c50b84801d01d00780000c0e00345207500403041 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 766468156 1250 766466906 766466917
    0xa1d0a0807030509060a030f050f101205010e0d120b0409172107050c070e0c0f0d020f21070305190c090914040219150e0d02040e06090d0903080a08040503 68
    0xa020f000007503411b5000790180c0c0540380078401c24200b00716035550701d4451802400140c42c075030308004144204112140c1400e00e4042050f1080001040e00c850301039200b4a0081900c000001051009072154011081441002c130010f0b003c640510401c0229150305059400f452040c019002002542000f81500d0645d40f007060001c0200071001d9283c003081c010441d4010790310a0020340180c5500259000d8134104480c060790114506074070b0000c03154584080c59100c4500c03560105c0d028440b07614035041c00e401508480c1240f440360a440050345200202d81c134401850a0140741c905810300400c0491141b424614070300b4aa0005420201260709070344039040da90004000b2420700c003414a005203d031900d140594800d4682010001c08000300c1c1e040c0c0c510034026040005d800074070482120384961030070300c282200645815489545900031600b03441380c45180700f50541c170100c180012142c003002682040b0303200d407400c04159810340d603603140d151050b098490b080041410209042c81001d100301e44 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 766469406 1250 766468156 766468159
    0x2a0112091505071106040812040203160e04020907050c100c0905040f020d05060108010e06011805090703091202030703091a040b071212052205190302060a1d0a0807030509 75
    0x1040165000c0400c00900b030b08940760400600b41c01c04074512a9000910b250140754000c2915007000c00104424881d000001d0003aa8103205d83e40242513042d880645000107881443c1030300c41a80303424018401c0d0204080c1401040050070800c40745080e00104030102440c07000a80032a2029502004446490300c1c0d40189601c40d10b8607811904d040f130181c0c020803181454020a1005036075010064400f20f03c240700b100c41c080c0700703800051031941c418001d080241400008600c00030ba155008104c03698401c0f00c104020903540c41e01030042c40b819401b0421401d83c1c0d40f00652400141e07076002010a40644101d00b8159192241600500e1a041c16180903102c2240c40a40342d2a10707003440c3c03900c040c48141c51f9010508003145000030b2550b070300a0a2058143c0344bd000696145c05821609440c100c810548181c010035584000c1c101400c00018101d5009500030101400c02c0d142c40340480c0c00c2080001007001694014102244001c29158015500700b18030f1515211117040c295401c0c8a1f040295 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 766470656 1250 766469406 766469423
    0x406020c01121d100c0c020603010e1b1206122805070b1318020901090b090d15090201110f0d081801020a03050702100506060f0703050906030106020a03022a011209 72
    0x8060f842e000203406410711201403050118220781c180c142e48032165400040c0d08203030108010f02041361462203030343d085825444912802c00b40c550b8148441d800c01d41001c004014410140001807820500329204811f03071350050511003a04031500ca42c95041a000f00079460740382c1c4803110511100340301100061254408559450201c0801154201c615020b1185014009460143d000405d8801e84408400c183c644a640e141882e4240000350042154554050200700b0440000341107180b16041c2500751443c0440c0701190352001500c3c080c0008004005070340a24100906048000b4600c0d085003402e062990198645540e03000450f60036919515144d8000a0a59092945540300c5445165070750309a902d40c01020000c042907450983c0c0349640024140165403d83c0c81a00c001c20f612403083c10901e00c3d00c46c1c0c01020481c150000d034000805600b01c00c0c0c10328285601440b0400511101d040340e140b4448040d400f00740c041207000c0c1c100303040240c2a1030042e14141c5586c0400d051541010740c0b03 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 766471906 1250 766470656 766470701
    0x307110304050312090307090e19060f090b09121e0304020d0b01180c02031c1814010f0c080f1308090301050f07030b03030c0c090408070b01030c15050406020c0112 72
    0x1413901544001441ca01920070300d0350003d10400355101e241c1b05090180094801c802721182c202e05024406442030340d5041c2e50b41c3c102d1031080064441c280800307200d009440041d10b05000300e107007000e09403038610300c040034100110401861156500403880c904640031549075191400883c04550141c0001003190100c00c0020900c40c0300c11945600d1484480424010110721f5074049899018220340b1030804540c1041c1060800120782042001c00c0c40c00c95a801d0145040d217445141c0b08000000c3c42c0140d41d200340240c0d40000b1030049544010326801e02d03046c20306101c0202001d07030318000c210313900700480051010b080160a804031442e80074020020302460030440303c0044046002d031403c201081c0f6011002070b03942400300954022481442c0548280724000040c0f2250110080c411242c100e8100300450002c1d0a6401c5d80340654081c0c1da1001c0d070541003159142c000960005a48280102440200901070340081d16101890302030ae0500e901000750049000031301503218004074078900d900c3e074 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 766473156 1250 766471906 766471933
    0x70302030a1401021b161d13080d06030807060506090c070b0a060b0c060f09070605070308191b140301030f02120c0a08011a04020f0f0c07030f0b0601080907080303071103040503 78
    0xf2280f04c124004041500e419590387c0c4000d80030750100e00d10562828080d0000342400c6441c11004aa43d401005024a0120b60308103000c1101c180e41c00440301c2280c0403810005200c8207203d019030103030f001c1e40d80c14031606040c03607407100da4011100c2c01030103140302d48002940d0000b2034201c00000c0018612954403071007108030040d16940e088802c2140304542e140064100000054110704882881d280e540c9428000e880c110b80302c0784000d1a40c8800b04402100386400030741c0e440ba0242c10003026070036807410a801e04004007100403201c00031400840500042c0080b030341c0072a480004a41c1200c007a042600b519480600300704000010b6a80a4059100002d40c0c51040d0000d2807502d800b583c203005e03c43d0950342080124040d00d0350508400c0c80c148614012104094001c004c03e400e01c4c02155011540e80ea40c4a120040c0281d08035a02c0d52040c01b4440f9a58103c1402c40c1c0108841c00074040c06402c000c68665a800003c19100411002c90000c41d007002c07060040350080c200150554044240110 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 766474406 1250 766473156 766473163
    0x606070606030813051201200705010605032e06060e040507170408031b071208061504061d18070e060412260c0a0201050f0c0102030a090302010c02070302030a1401021b 74
    0x3140f107019511a040d07030f0340c181c4010310900c21003c2d0703a04540703580c05200c0f40300b40000d6040340000318ac43d17660b502d20200e11580e04104190300c4d648204440010b800c6403112002d10350094800f00c0d5115030624105021558002810000c5140243c50004590740d03480e0707040300d020304c80280c1c0a1418080390140802e0120010042d4421218115070054040d40000002018460340314050110217a20f80d54000d2144100c6c003041e0480401443d41d00e65040055011451f6481980102d020694842c0200341c2000d2854004d800460111496030304000303441d22142d6012002484d5404102046c22691071540d90a02a10080e0030344034064000c0102a20b0422105c0549900c0c80c440d08100e03034007a403800e1400c98100c580e001d040c10047c151140040e0700656690300b014003506000c2800340300301e1701c41107400d102540c0300300102c01c000320710b00030181406801c45000501090031904540014005a01c0006541c0f00c21540031070910010150601540e00901640220784130070514940180400c06000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 766475656 1250 766474406 766474409
    0xd0f02070318080a0803010b07060902090a020d18240e0102390307150f0e0d08060303031012080705030f031e1b0d14090709110406080606070606030813 67
    0x2c1c10b5036030351620b800100d035851090000007000080308000500a41e6807410107485802e205031030119107242c0d1940025858541102e030040000e601041d0015041c1190281268105808a0721389070009141c6072103100800c0320072000c090340843c4000800019032580141c104e0241c1c20002c40d2292445044c03640b1405207890704160340c1d9118406005242d01b072011440c900f00c034200040d881c1014a84c2c4440c50500086902d15006a854005460000140c0240d00c0000300a0010b030440e0352035040007408544001d007145009510a0082107502510041c424007503a140c2045907001840600e00401a4440c40600038150f0102289403507060f2901005503000e03440ca8940700c000c007201c11410014828086443d00070442e4500345000c20401154010840d0035280d160115508420f0350b40481222001d81d2030029650000794104100742e5140b080160f2060f11003440d034079140c80c0900003883c04901a0075540f250400203010000c0041c0e907402540215032284255455034000e41e01d40b007034076425 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 766476906 1250 766475656 766475687
    0x30e030d0c05060609071b0303021303060c080f10120212010204141f1d010c0f030914030601030b1b04030b0c09040b0609030703150b060301080604051606080c0d0f020703 75
    0xc420200f04c051900200d50b9101c0d00c0301d40c2e5140c82104030781c00c07046c0102d0314500059040c55030800c401b1080000300c00d00c02e0061030146002207010ba10522000703200742c40060542e43c02660401c00e1010103000102403000312000e0103203d005c070744418000034903180031814120311591300c00200018020a20030002184440c01c803958101070b1600a83c00251010608407200020b051020440700803016042180040c201850b002c0c44c0c6480d01c0d900c5800100032014280c001c02c00d084820003020200d01c80e0b10480a07402d1740913214951542d07a81070645280681030000614540c00081070003c0c0e400240c40c000c6400c8607d980060805200c40044d039031000e4501d6011703a0030807412500c9030412004036028042c001e801002018a5070701e0b0054442c090b5100307400750035107550300c40c41140c0c0c450020394080e0140c00d0240a403801d05180c4985032454401f180121144001d8080180d00d0f0090f24195114038512880c80e925510207080100401c00f0700702d0741c0705841c808a41c81c403c2c9a40701c1c01d801d141e00d02 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 766478156 1250 766476906 766476913
    0x14010b221d15090a0f1704120c090c090b040b0a050903030d38010f030b060f131a12060a030204050106050702040509070f0909060204050604180506010507031209030e030d0c05 77
    0x5803155204d4941c0d80030070703018043c04d0720446a80c00082c0c2682200080000e006151420b140c1c8071f01180b1080b0078a0700301910b03221782c8000c042c09114450721504600c0c1c01281001075455280000c2000c1a02440c464160050700204d42034069901600441d036003690014141d0303a9074516100310a00521414046200f0001d2505040300070b43c007481c05100d035503050070115078400d510b05801109d030701d10a01c1c141401c15803500b07984141a100d050113130404104449010f40c0301d441c0031003000c40c806080e0f4030006611460000804484012034103e1340d503c0c8105070180c815071798200200b6000c3c01320364402500140750000024005a0107805454080e20071181030105884519029607581c91901440c0340340d09580130100700f610030301c1d80808030441c800c07240175080960300c3d0f00240b044d030040d83c01624089800c3c643e07030501da809849625030000742420300034100380c51520024400c291a459181080c0e0350b0705080010305008a040c4440035030014120b41007000070f4038001f040f0071002c0c44119503520 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 766479406 1250 766478156 766478161
    0x4061706010e072606130510081006050d02060a03020906070602032508071206030506070e0a0e01060203120a090624140d02151e0714010b221d15 64
    0x7840750990003144058400d44143c3d841c0c44c0d842c035032030321000500746992207030741030003e402c001c60103001d240d103e000115410811180f8050400c0e092070b40021500c4c0c5982e281020a000c0c955031251030b1070709203806a0303245444d501041000d0b0000d01c1008030240d402840802c0303100810000350000d62003a4660031505960802508041e00a006018261404542c01d800000c0405102c0d00100c000000440d20224109540703444803400c00c00f041c1c91400000f40348500462090600c0c0d11200d009103129042e1201a6245c844000d41700c0c0070307803980800350a0210001c143c501d2003540000d074800382c10000410a20908110389204007040d82804010480001800940911814071201c400403028080000c2e5000b035500700300d0a440e407648419914070052049060f100c903103080050f040039031002c90503500c0b40b5508002000200600749005940c0c108000142c054841401c0d00411041080c0034444102402480001400d014002102e100551001201244c8000203121100f044905520a81c54 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 766480656 1250 766479406 766479421
    0xc0305010b0a050603101712030103060b1801060519030f0507020610050f130e1603030203030604050c030c0a0e0f060a03091e1a06011b03050307023904061706010e 72
    0x240002c0300e12081072a4681000c0003804051945840d40400541c2580e23141229a0115a500e40003a00180c45032551030440c0802414804100600020000e040604c20f44c50402d0040c42d40c0300d541c100f01445007040303101d8000b1034000d03006101040d6260006001515150700000d5840c1400c80d56400310b041e40300000111400c1400d200c3c040c4c00006400c0c1010030382d0315800d4801406c440f41c003c503054807840440704035241d058a800c0c400382d8800c0d806107075603041460800c07050340c5014002101141040041c4214043c1243c204c1b981d490030b50810030045a0ba440010300030100f01940107800040000328216046d526500030803880707108642c050035030b803d040301c0f0040e614550b200081142441907405011112034240c05640444149460090925842d01d1260b0050b44c0500031800b00b031010080c41001c6030140132071703404032081301d201200f60035504442c000c412964003c2203c07090300d070141c04910b80d280ca070040d1020b00111a6040800742161200541c0e80c4001d00c110b040c0e5611a60210f42071 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 766481906 1250 766480656 766480669
    0x60806031e07270203040506040b090114070c050721020114030705040618080312160f02060117010e0a111e06040b0c03090409080a020f060c0403120504030c0305010b0a05 75
    0xc400810000c1c0b60140c24503050721a041601a01140c04107030042c0b0f20141030490740019403145110f2009001181040d2610404105003e8800c40d0140d0424050086002100b0313001ea6114229103400d480c6621281001410500250044000a1081220315107165444605201c40e2807007a40e0320040320ba01503c0050050000351400800150108410050036103c0e40380111702c800749040d0311100a940c1d0404501d5648840340c0341c800500c104080042d40c0302c1c1d02c8000202e141c3c40d41801d24920032003c000a48600d014040c40e0400503400e61b21120000096014401010303642d0704980e030329100b0307041c880319070030244427401c0c403460101031200311405402e00201c0d481440584002d05190038000305a055400c1510829140d01c001d1024850559860049070b104074000c203200d50740e41d00c0c103060090910100d1401c06807141c3c05401400600e50b40c017400c8600f169000b00d903c04c0f941c0704040c02103d0f14801c951020307001001100002c030078000e0640c8004000c000445503060031540e500d00340801d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 766483156 1250 766481906 766481953
    0x3010510150207030816170a0f030612030806120f060f0916210f0209070909050a0c02031602210303010603061a22090e0c0f0d05061f0f06080603 64
    0x2001c1424010a02001c0400810509892268440c808030410036000301107039800c0030004ca40001e21034031b034244005030142f150602420040c03d00360a155104d4034080c2c6503d0000c0d0249002d8940c1e506942550401070102d4029004410141c0b03001d4107042c00d03440603105090f0351140c441e01502e5803006450303010000361402c942240b40184440d1040d00060000c8840c00f901c25503400603c06081401a510300481d10701c01e01c00c03a115100068100002d80045410041c110307203545290410381102141c0010a80c1e1504440d0310300904c043c0f18510114407c3c50881d5261204e0204a5900d400507803004400b540c140d40c05917400300315803035503030300740180c1180b2a6000c0421488200080b0740b02074a0300500010b042c0100340320004141c9c0d0340d00a04111340b01e240341e09180b908041c3c0b00185a1500c1c0300d01c119000170488001603611815200c81c1e4a4000180051024040c516000040804c07440c50000c000c004017003034551144c0d035400001d069003c00715100b034401d0081d4643d1603207400101c1c88082 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 766484406 1250 766483156 766483163
    0x240703050f07140f040801090c06030b0a0302040906060b0f0304031713060c1e0c05010e0a0b0c070f08030c03070e030726011b030608070b0f0d0203070e0301051015020703 75
    0x745240c58116095540642c8403003000312140b010807403180b071107500c403005100078180500001074050181c01c04000c600081d070040000c05090403500441070740c840c000700003600d030100c4001540b29014130b0f000009110390352201e2076401010440000b48503480010f98402c40c000d42329504013440328030300d0001c1e411013140c03281d8004a4022542001c07a0640d84414079141c124107086203250040e0f495021140c0048602000180d40d14907040c04001e002c0c09245900d9419100800480106540c2c3c559800c0e8028000e0020000204400061119060744083d80d0342c2c22035036081e07a13410116a0300c222075208a13002c4011442c12101c01d0954107001030360303004803903404098030724544c6144d1280403400c0c6c2a58854416640b202c0500c9608001c45451003105100da840002d00b151500f462a81000d83c0d0750f000d00c0302c08a00b8421041808801012500100300200d001030340c0c1d039503000c030655074502641d0700980c1640ca0705042200400c0c0c01c1c0c03040800e485815541c00d1410008583c2281c0e01c0d41d480c00010b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 766485656 1250 766484406 766484431
    0x60507080130110301060803040617062803062406110607050c1e03070b090d091e170105070816320c03030118020909060d060b0324070305 61
    0x3001d040303a08a00002c0d80c038401c079150780490070050000307400e50740c0c142c1103209582c2001908000407038100c1405c15000c84510600d03c4140b4254000442203410f1001184000d04d02d2901c41c2c900d02d007440044e90240d68046810015648500f0b000b10008800300c0c143c06040c0d484480c0418140e000d06190030683c42418010600355036010411611a000b003440d0340d5840c40340c9003080040300c02da503045022901f910002151640c0c103904141503500c401800f2011070b80c0281c0402103120741d100a55606070f40c441008003881c00701c140c01007a404e12465124507102020000c5c41c011520064125501030307003903135603900714603101c2071000407110f03111000b075002194449141c0601c29011512195100383c41e0f06103c0020314a000341c0e41074541c8030303003d4800d442d00000014054070500319402d051280304440214101004480820b400340d4014008910896111509070200101900f0011040c5000790664900c00080403200311240601c0001c000b08960350000560030611030f124081c86601290000c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 766486906 1250 766485656 766485719
    0x1504030828090e0615190509041a030a0b1005040905030a0e01140909090102071a01170a0f061a150d0f0b0d151103040b010e0906010825030f0605070801 67
    0x104030403003d10305d60128421000f8801d20b156940c0d40811902d0b600320b9515545d03540c0d01e03c5c5007040111400445000b2840c580c0c456040b207603450005a00400d0b5a100c000700c1d0454a413070200c40c1600740c1561080d5442030074401c0380c40400c040880500607010060311050f0131030084100541c0d045602000c0d01c0f514840500841c6264a0a88086c41c0c000d4640000145003c00c5a102d00c4801200211a100700501c1880100031400544144441308105100a010b403181e1720b03030b80da40d046040581c0180040da15490ba1180d251048001e0030340b1407c00800c025044c1d5a21440036001d0303000351030340d28501c0385081110401442c050081501c8101c0c0203240d483d211200d542c94040d4141c440481440d2290f68821885450b240c00c03008601031801041c0c02c410700d42c9003904d40c0c0000b00004103041025000100100000ca800040c1d510500c0030100110045440c42103100401e0785071980090702030791000401c2e000380001035104a0146030350ba60740e00740581c0c840002408420005030b50820b07006500b500e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 766488156 1250 766486906 766486909
    0x90e01141303180f05030607080c16060b120706030c080606120403090315020405040e0a050703021e030105011706060d1a060609040218120c010e1504030828090e06 72
    0x144400c41c1807190500b22500707030610b140c2040c0995150401105011480b105100c01d03d4204461644140b480c60070b10140c3c60312021745c08060146803a40311140404040507000c0084a03084481401c00180c80540307041500000503550740d400788a4200031a180c2852070328602c1c0b24882207485524040c2c82e00c1d14000510b070110304280401401030701000000307035020002810004601103510414403000d40c80e14100402c00c021035000c0640100194031410001000550120300c040840b60104c0303101d1030201c1c0031104000d6030346a01c0355144d4154a01030011421352940c2da90b200a81e8056130031120705070b03140010b01c96074000c49680a03010a9150300461400701c81d101040750b110a0240100f410078100b0740202e000c0e80c000b0802c6007900c200d1032001c400a41031026041408040c01b0005001542210002800c240e241c0c802d11401500084000d9000d030703d45408031001107a01c404043d548160035500106451507150400b251061301e900310f00021482030030b404058a1341c10746a10802d480d003d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 766489406 1250 766488156 766488181
    0x92409050c09100f060201020901090b03011212030209031006030c060f051c1b0203030714030114060702040b091e01090c0906032a120e0105040305030412020c040510090e0114 77
    0x30041c003d2482c5003c00804c0d19860f54280400034006600096142d80b04d040024241901d1508002c940c3e07003080c8010010b4452511046800d10f8020200c0d204281056030118064480e4a0040b40c141c403440821041152155102a084034025001445840c0d101d070811170302412050a4000010000d2110000c1c0401840780d40110f90001c0b00d0020b150700b03120101422a00d0101c0c03640700540c00100801c484550450840c0503441c40301061280b031036052140610100d040100b065002d280042504021525a03a121a1031400010817241492501401c50110340e50642201310040e0400800001c003d070050040e03c842d1281611072030051703810000d08500411103a0119807111402d40d12691003001403a81c81814146c495542c3e03459581c44a920000f81e51031580b0030301c80d5a15000c00c00001c258090181c0790840c0d4441004422101d000c882286020a541d0405901a01c0c02c818010002100641a030071103124030f005104446014008070308075002031300d00e2207420007080c00045044c58007a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 766490656 1250 766489406 766489411
    0x30402011b021302070b0609221a09060601020f010c050403140c0406180605120d05090607061b110f1e07090614040b09040f0201140409092409050c09 66
    0x7605000c8000341ca800003000c0400c10303180c4a2410382d002540a0500c0b141141d04c1d42d21040c00e0751181054108001c1540030000014203000c00d043d950f42d113074010030030f000a00d0110020b074403c0e11902d0781420182c15071951020758440e4090f105007484102c001d0343c1030069681600c03158550701d04040ca5503c55101c02c00381012200c0180c014203c1d00902e0350354a1003002c0240002403008003201703121104010032510107801a920882d205d032441040d8440008034001c1d45001d500d041a21480341c00e003c10f01c60702500030010051414215900c1214206440a184149a50769044032912554002c540c135102400940c00303894025000c80705241c09030020b2003844a405108560085550300d004000711030554000220861070b80d08010b03441d1a1601074040001c0d07003100c81702101e040c160313907091844610402c0281804111000020a17044450548000700784440080c8240b0300389150100b5211140d1085400e405140d005512201c0070612601d0602d69221004000c1001034104000c1b850100 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 766491906 1250 766490656 766490687
    0x2708041401031103070f0806011b140316050c01021005160e01260f07210f02070b04030c03030e0d0207052817010c2c12061003050c03011103040201 65
    0x2d070040f50b1064550307000210b1195085550f8680709149595004106100c0507095074104200d01014007000c410803501c05000030380c0880542c20b41045000b1180c1503000310140341662440032000c01091180c0030401c40b0791032009a083d00c1c01c0414400c140d404862060b142c0000c400120034102500300c0c0240c2054a19410505200d00220300c8441c0d100041c0d880022001c25071892001804030b40990003005a40291840c03c00c803903426040158140d8551803880550001612044a1200c1c98003e070b0442d0025600140c0002d03d6282600b8080e290100a000072000a4500f18280d81600c0c00420300d544c6a07500340c0e002c0c004a910702000c000100c130b0a00da1408031818030000d01e03822014024004001800600100060400710550389030031501054a4482801403145182c4a0440d2510011064001d281c480c02100c505070008682c800c404000b2900162181c0030030f0110f0a100c40c0c040000316031091044858413120740d401d03d4203036020580000a103070300c2400440d005601172010b86044025 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 766493156 1250 766491906 766491911
    0xc0706050714040b09041803023a0302120601090b0306150904020309010615080103030e0607081b1605040e0a06090212070306150501031503061d0709270804140103 72
    0x21800c2e031141640a540804644038001403d000301d030926008880350160f85e1741c03050300710001c40c0e24040d403180c1c0d8540c041650409041d401d03035815540c82c802401001c12554110380c0447c50060041c2c020f6101c00e0011040181910005d051503128045030425503103908138113800e603201c0f0300030300000311210300d210f5003035441c1440884c0d005d464030300c0610303c00c3c1402000443c016203800ca01032003141c0210008400c11040c1001800030a802c03040200180034162034060b0b0300d40f000d044c144818003070040d40113440c101c082030f02420703200001014602d0f50080305050110782c0d5104200800c0314158400c12145130850a000e001280d83c0794040b522450010f00b56814000700c44045a040c1407803900704486e1030b540da489680c0040c1e460031600c3c02518080c00d01b0040d120365070743c91868040051100a1005031901e500d200b1070483c080715450f44015060880c0e030a103850b0240f4001905924034600d910003480e5100a110f03007a0301d100030011640020f00c3c2441c080c01c2c100708225100c083c003049414182c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 766494406 1250 766493156 766493177
    0x50f060a1202032a03010501230910050d020a030e0607090305070b07050309130f05130f0b15040603052b0914060f040b070c0623090415060504031a0c07060507 70
    0x200384d00400c01018010200d000d80e65814040050315040301544000004110b4001c0813004980c41030403243d5a400460701c240724102c60210486292044440503c8840d00200e100524a0b4140d00444509d0740c0400c10f841d0540d80c0e000c001c41e0036104034070004d08907a1000c1c408003c00c0a0101c001d0803520f0048054130300d0851224003154030440c82a56451100d0b44d00c18481444603424410160089e541c2d2444009410f00390700c0d02c102000c00408041e1804424001042286800a00ca04192039020b0404d004c4180d480c10842d84462211105000d2403000b58890b10044110b900c41c0001c00500c0c0e2110030b8810700b071613030203008a440d203c10b290700020104040301003d904040a0001403111410040c0d448030071740303442c4164003d41e6005005000c00000c24002d00c90f01880382e9481e41d90003d100c0d0b900e03908036100040182c2080c0842d0f0b01c0c5498109800300c2c0150340b0800400a884c0184400480069500b0146952603001c950b401c60070101884240000f0701c5039007056800c04000d1401140d0030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 766495656 1250 766494406 766494451
    0x10c170d150e070314010302190510050702030115080d0809030d06090e16061202091807020f0d0e0a063b011403060a0b1b0604050106050f060a120203 66
    0x540c00a01404a0076018890820803140c00c46100c0b5840311843c6030034008416800907100c1c0921060200070b1185030407088020314203031b4007442d81c0014240213200c903048200c1303403a010341a64011003044e0f000b0350a010380c0c0d01c090620505041c0440e03018000400c00c0c0711560a0407075000d00054143e1138603000070020401301d032209005a5010b001440000a03110a008116a16113800d5241a442c04009403404000041c6c00c07111203030710740d685000003586c2e4548a90004141c07011040b10149030322a80400e02141c1c80c0c2c00501819580c031003204070b03014400c240740d06450191022589682c859095081445105d108144175207034500043d403842015a03004144020842021035500d684445407104114503603405900c0076071000c00c50118924500740600400c0e480d0b207442c006c42d803d140cad001506003140464001501090300b501c00554403642014549113010f4034881c45102d02c02ca50101d00a004d91402d5021140e901080d62030b0156050001c000c10006508003c01904545500303075002c1050 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 766496906 1250 766495656 766495661
    0x90a24090b0a06032c030c030712081e0718030501180203120c030720060a08010302150a0e041a060a08010816230d060219090e06010c170d 61
    0x2900e10404085506081603091200c000c030b440e40711204040c1810b01d2042d501d4118942608030320380a0f190380c0c0d00185422406071851103000784a036140e110009902e402d104100050b010081011707902c030b0091391204084428104002840c070001041140b002c91049801040000c004840326200c41d83c255640751076071400c41d03198114a110380c005120f40d8404511303003401070f030407410392103c42c945c20510080102a644d00030507800070111a00f09030030442e100700c13404900228000040c0815507604072224014206070017844200e01822511005030018420301042d502c0300070072a0391f960042803080c0108005001c4020b0b02141c8101305010b01040d03911018020203c101d01600c0d103080e90b500d8040c1c0c241c0350003006084030f000780003c0c00050213403009440100d090f888441c0c000c981c6589042000030700100b0740140041c062803000600f83d0800c81e10941504000a80c2c0d298501881d942d02c070080700440e4102d9505001451813803008000035000b44102ca820440e01c201d0600300942910072008 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 766498156 1250 766496906 766496909
    0x100218040603061d0d02071412030f040602121c0902220e060a0e0601030215130f05040507140f0d0f0905030c160302090109020a050c070b27090a24 65
    0x40f071a4581038482420b8820280080100003c0c0c0300810050780c20a40081d1111014002c40ea00c107666007491445950780d40b000342c0708810075041540d50b40e00c0000002105940548a248054020750450a69132004101610001400100407400d80c13084012004001e0400b81812644000d0f0958500c4d0b020300c480f09450910341401c80000358034610040020310700b5100034400100d07a810070040004040003c00c0280c11a0f5047d0f894403400705608090507018001e0201c4800c10f400d95a10002c0e0103692519800106c45c4103039020007103034480010032244d0b0b0003011207040b16502c00300000c01400c0080e1008100d0702c08020800540f0b0b4041d111030134103440d01034200f0350382d9510119000c0c00400e01404900c540b40700910001c02114950360104049580500c02c030580c20380c2c003041080b4514040e401301e82d51806420305903130780151503060300fa0300d0384c001e60b01100e01c200025600c0408039a00e000e00a0540d200103010001c96035402d0031000140c0540d0107640044500d800c0c40c2002500c41407800d00 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 766499406 1250 766498156 766498163
    0x1101050c04050a080601050a0b130305011b0f020c031e0f010504080403110111060c090d02060720010e0a0e0402220f18030f0309020105130308031501030b03100218040603 75
    0x1561907150400f001150500ca801c40045074016030010000c0d65500200f0f8412030702e42400e02ca03110903168101001c4a2503d0340003400d20f5081210107074100d004000d50030b4107207440391564080780f003140c5001c0b41d5032900030f5800c68040d400002001030b001003140410040028210496114210b0101040d0943d407081e10111484040800d0600810140d00050801c3c40c00038680007081031002039a0b1a40c2da0700241c405081400c0003d01c2c180c8503110441c01c0d80c0110f0700500307069501c01c460b01e8a110840b0400d40c100080d4001100002e1556220f128200855071008016124803414104034049158003d80300301e0740141c1445428203441d0040100059040b0185000a2480c1d0b89089440c2602c205030110010b09040e20200f1000039001a59101c0c01c107201d02d40011070415a200580b5a44107254461480d4a0040000010000ca8100443c86510460490503255407950010744c01d450140c000d41d80d0581050b05c10310405003003940501aa03411101c10201a0307109000414101c540c0c0b90070a8 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 766500656 1250 766499406 766499431
    0x11e0c0b0a110a08010f050f01051b010204030b070c050c04051e1e100f0801050402060f07262203022413120203011401180c02030d0c0215070c120e01110105 69
    0x1000001d440046d120300034001941c2400c5100303a4240001c0961003070144190504044104050820400758140c50103140c0c04840e50360b075400c0c0322801510010350703c4e50803034061185001004550400d03009841c001e00c50400751040090032945040903a00c0002c250003040010403000409944150000d28003502c4030242484206061034580855100d40383c010480da07030304000c140001a101e03542141c8651844101c2c194079400349251520920b50800d1200100b41505100c0c0e00300500740c80e008102c034030404442c0e00510b0420110392007116003107203c0071b07502070100382092064850008406e44647e071080c100915012030b5802040e8080e0b010340020810b844401c0400342182402d00c6019412540c40d01d40400c550302d8a40200001a10a030306004095240c070204c2c0c800394020010750301685d03101c0d00240125024010003d55405820358003141900700c0c0701c003040034917014000300744555070000c3c03103505006c2d840072041d9a0408044251410080703071840211800c030003840303010301411844640 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 766501906 1250 766500656 766500659
    0x152d030f1e06010b04050d030c032f15040f02240a020105040605090313150c0807060912080c1801110a050d110111040e0c1308010506011e0c0b0a110a0801 68
    0x1214a00b241c16080a21114010801401030b41e4a00301c002c01417079410710f0107407121156031404541240200080381401c0b2070106450010420700b80003e4943e001ea0011502035114098030844012000d170b801614031713045020104003600b407210800c0c0c1601810380c40b9110842d0a8034800150303501140c0303100c0050f5540c032305000801115000d81508072000200660426403801c1001041c00c50078400d034440c0c440d22400d1028101c0c020441002c141d60019130541e2940700798100400a494003443c01c54510101d401441d40650240b18074900550164250909000c51422030b0600783d4050846a41800562901c03200702d41010007060a6951003036002e48100740a00340e015000034070401840001c0d2b4102a4420a8040e0749001d81d0f0072100010140025601e500c8040d110912540d004011514180c43c0003241038841500128003645003a6201004a0b0740c11200b0b0140091802c405800240c12103658004500f03003034406034001c801040d0000c2c8014007180c80009583c001c00865000c80e200000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 766503156 1250 766501906 766501963
    0x7030804150c021009060b12150606030103080d150b0a03470d021906080714040902030a0e01181403030f0c07050106120b152d030f 58
    0x111100101c0c5099024840a000034034080d494814901003000d603c1c2c3e5a5034884140b00d641e03044402c00070320240c2840e580740c101210440d00c0e080547d0441c850030071264003151285c144001203d040f2a0040d240c6810600c1c3c1000c10b1010300322180720b8290207842c8000208400d17810000410440b111070710005407850302e18040d4400e40c11078017401c02c1e1405c544e400c0407010507856003039036440584007190040015404d800050741200440310194111926030710f41da0004120401c15826142d03d03803240541a0b540b0002140c03100e800c0504401c5440051104210344421900556044812120089034414802c01c025003103880054606c428441046100028095000044000c40c1c140300061445c41c03906042d40e0241030005011150542c4001600c84140102903221202508504522000410290510310599081981c0800000c2c540414600003442c155003041d80342006810100440074103d8800d01030007500e0200c10703815011790100700741e101c0018000414800700700d9010881019040c84d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 766504406 1250 766503156 766503173
    0xd09120509041b020d030e0f150124050d02071112010b100309080301060e01170705030a0e190809011412041a01080a0f020406170601080c03012c0f0307030804 70
    0x4024581c2c6aa81c2081c3d1004582d0104040060511504005c100200218000d51405c1003810511595009000034940c800b1210358900d8103d43c2d880d0b003e482c007500c4c104500707162030703840300b11000104908020980b410308079a00a01a0716009002e10303090900c1100c0402c180d0b10300201c0e482003695407540359030319034a05081800b0000701d1034502000803140f1076079855020320042c0200030a101491414225580c4124821320342000c94540368116805c0000b0b0151040d001514528545810583c00960b508000282c0129000810b540386203032083d20340796030b50160311141c0070604201d984145500400d4000c03004101404900c05444214a040e013450b032403c0302c20141c0600d040c8400d400411882c13000207800c81585030040c0840e910344540c0c0c0700140041a0a40c000e60b1a820701d802030360028180800c01c40c0c12154450706854600e40040c1c1054200c40e1200c0e00c100c1006d1442c000380501025400f1801c2031800900304464540c3e041081c82c52940d0007040c000c44c00107003410704110402070701e075 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 766505656 1250 766504406 766504421
    0x12150d060b04050109090c05040b120a0308070305070507020622081b03060c0301030b0a0b01031e142a0705160b31050d0327030326010501050d0912050904 68
    0x280401c2020030317407c0d9940540020184a0a44951307140c403030040c5669034008820030655940303800c071200500780d45000740038070008665071404246010005400a802201143c02c1031340e00400e00707403800f6241d981c0c0c00c503030320a107205c0f45207520750900000c10032007000c2140d110001e85c800d403965007240380715040516004006107040e0240109000420015942c0d403052a040704401e00042240e00050004900030850b030ba45a150399015403101004101081d40b001726461460302c040041541c48a0314100e11429100104081000c05140c02407281d003064043c1a819121740161340d035850460481e80e00c5020290003000c8030400005180c0601021019842d801c00c004100f01d59004802600c800da50207600c0c8201805103100d142c0c1c240406110354615118084000c40004458401745081840030429000880124540325074803800714900b40b041c03403d003154002ca030b0425a0b00744001180c864105807a0692030b20344426410000568105004100004d6640d0b82c540340c899200800081c1d4400 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 766506906 1250 766505656 766505669
    0x4030e09010b040305010e2b02010f060f0611120306011110050405032d030a0f020d0e0f010b0d0507140d060c0e10030515011b020405040f0b010e01060512150d060b040501 75
    0x1d04034420010240c90452608e04541d2016640d0840b80c2c007001c1e400352135641e030961003030381c94100c0c08a42c401110800100b0740b0119a102100100a801881d5a443d010180a070180c9014400560f06602c03501d050204d51a120702602c19803400d04407803c083c1c4000342c4040310203410215140c0d840071003452164400019141c403000c04c048052120711194803020380010b00c0103032500c040c0407103102c2c1901290305a000030842080f00b045200d40d01c80e11030306070551181b445e500f090780200162501400c035001045e000304c040c2c28102c4ca4a00c2c0c101c1c0c600c4c24403046a81107154020100007040d00c500c110064102c4a482e00c80442002e981008070751030000c0d1508003418580024072448072407405220700091001c0c209000181e402d00320070480042c0e2018029806400c001c00c003c10845420543d086191154580e02e1151740c0300d400c1242001c2e000d000c0da2001940c10300c2501c4810b000d00c0101500704c4080c0c0308406d901c050610225400f1b02400070142ca05544894039880a81454400d46005100 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 766508156 1250 766506906 766506913
    0x1050f03010b0d09021804060605120606040c0c0503030708041a07231309021c09050d050304020d060507022d0c011d030106030308090c030601060c06020304030e09010b040305010e 79
    0x140800804528081801a9070b0b40c100c0c0880d8070000070304154840401260014000c00d4805180002210118021941260018145480000c09080190207002404014405001c0d01d036181000e00004040c00d4040c04104038006da49040850014802140100269542c070f04052409041040281206405c08000e00040a08104d8015441149143e03c10403840ca088070a06076110010060b004948030f0005035041108001107000b0290300800c6030101c14203440c4182c0d00540f81050440f11200d001034110f4200350640b00000d4464002564843c0c40108841c94841c6130b622004112441240c400003d6409501000380c1000141d103010490248078804d2483c2c04d80d08040c01b17444000200c5c44c85e061100c85400a0203001c60189030314010708001c0c00030000d441da40e06000303007d28010380e2280b07014010001610100c0c140030504a0581e4103c1d120305840c4800f079901d600095200600c1a020881d05003e00c40c9640e40d42e0b030303285001b00085180d00d5241c41c11800d14a00310f5069a00c982c20b150b1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 766509406 1250 766508156 766508167
    0xf010507020d1715060c0705010306090b0d170f070f1b0303090512011b020c011b02100c060e0604141005010f0306053103080a090c031e1401050609060105 68
    0x760300402c82035510b195820200c1941e00c5107050a102d010f0107000a680c020804101b0461040e030000b41d09080394000d80c1c00348141c075603034003038002142c10070038030940c0102d0903041140100b1049201151000390701482d06180502011a400e8142c0150604880c1051150660000c1c49080544031014000c0e06821042d1640b030750764060300f100c106200d1240200f8a1f0442032412403804e610238000303501942c1c02000d002008040094403032004080040c046001c2c09d030703034480460325012603555a940c0500300382d081d54950441584e0142c525074084072f116898100039401d400c01032000c68001e41c4152020343d92138642c5a1807504000075003d0180419203010010450366103042d00741d071308503504920000b510b91681070142059090a07800d80600141e5058885800b60f1a942400d1001d4003035035510801d070300c860901c0b00c15100b2103c00601180d41c1b209080c8046000704c210803034070000c010548881042c1d40d84c1c0780b41e050744425142d00d4259640d0701c1007160b0750404445843d031180f401d00e003051070718 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 766510656 1250 766509406 766509433
    0x7140a05011106043206060a06080f060103110408010905060708090a081801020102070203120306100f1d01030213090f0605010203160618020909030a03060905010b0409020c16080f01050702 83
    0x6010052021740007001c1d24203d45082807031000280960070148186940d646204012a41d540c4001d5074003900403c5400310010b40e1511900f0300c01c0c010028000002255200d010044010303140790342d083c50000c0820031002545074001d2107500b2005100e000541681c4c0740484026045200013003980240307070005401b0000182c10101111160088030340d01d1400b109010004038024081c2c03142c000c5d090701c07500c9110562070544001841c41420200e4182c40f9480782c00c541220502c1414800401180c541103080031405050b07014400041c40600d030040c1400c01d04824034540281e564403030440e4540c0c461182c0003030f560a018400140c44280001c5103818091612102d102400e2040034080795921000041d082100b5444215580d0700180414468105000895201c1e8011418480071903d458800108001d00d402054122010304c40300070300f400c0c0f4060100c4041d60025481300d22034062160b2070b403105203590300f1040281a2100041072a044120101800c51f007005e0700c0f1f00c055500462200034207 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 766511906 1250 766510656 766510663
    0x1206010909061d040807020315041506050108040816080406110f0114012c0a05161409060c01020d0608010b130209091b0c0d0f170603120c0a0507140a050111 69
    0x4190600f03840045594a0509003c2d50154540c005e40c5800380c4241c540e9215080d0f61a90b02031401350848010a05e19034400c003044807218444d56021070180400a07000c66203d50192402c1c05048a8000c3c3c00400303640c0340b040940c82500102c2c0492840d010550a584040110f02d00c100da007480200301209410721849510b2405200300d82d119440b03403800304490688041825060300004c6170a030310070305003c100340f0060700c400c5900e142c0e090452024118603038441c03030329003540c043e1f1018540e1a0013881c0c01848510341c4018403800701c42d90200007201d00032090344a4000200140c0b000026641c04a0f000c00c241c2103246040400d1450050062280c41d03640d450540790001400300c40801342d0100b03079050400c40e0095520003e202d008100c0c60f6240660444c01c921900c071055076030281803003a04c450715050003005441890f015400000350121329480a001082c602208208803886a1140d664480c40c10319960000084610318007440341941c20441d42c6c9130041c1c0400d0a0122400c050729a00300e42d03 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 766513156 1250 766511906 766511939
    0x71b030810092f0717040317131a07020a03050c0102010509060f060f120a030810060903110603040203011103040f060c0e010c110609041802150f032a120601090906 72
    0x540c0e52020b0943d0422140742402c40e804141d05c1004040b00c0d012003669018240c100d80300c180c803800e00540ea1480811818404c84408608048200c0f003c107081200c0d804461241210b4000f01034000c110810240c0e6035030103100d0040d84540d000f03000d5001288002802d4a1001c0c0c482410b0f90300110038004000008940e80d5400003040d02c0c03000300b0b070050781c00040b5200b484100b20031031070041907584010b259001071218800c86c1901a0701c22459600e00040303903401f02620000d032a05401030040140c2e498480025904540010000b0650440f4040c1c0683c060f44240e070100c0b00b8000204a110030003945018081407045207080c010105250f51001901807102494010326406c95109040c14503030b640e00c1991111100500b00300056000100324001c04d018410f0107034454040906100b044001410803100340c1031411128504544070008860418505108030b2040c010316540300f01c1409580c48090075071180c090404040a090581c00506080401e402241a00341455010300c04841c0300da80e00c00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 766514406 1250 766513156 766513211
    0x2030d05090d140a03030c1805040b0a0f0816050109030c0b03090f030307050409060509070525021804020f101e110115031502030915071b03081009 65
    0x1a0748031540e80004100c40500100244404070030000078040c0303500080c0c40420180309440410566081e4201a510400309001c0c400162181d10307003d204a040503002010b412201a1006070510f031101d044030000281c5400c84030b0968410001724109c02005880b2074000e00e420309010311302c18115151401d091200703002d11808400d0000c0420441c03081000f20010728041c5905498682c14900c100406d682d10a20a1001a5051a401040c50314181143d0b60240d141030b01c801e0301d4205002080503d244103850814071065544100c0f9001d40c0750702007003110444482c00d4050041c07615104021006a425401c00d004049103a150400590000c0007040c05030085c03a1001c000500c9050212042d22841c01c0ba04c1003075003400039100f441d0104052031025244115001003002507a091410203d020489041485070b01582c0b8000284039004600d80d007119281c80c0401c80805907a200c201c00c0706420201702d00145c611010001d20289003048140034042021081c0a540f82c000c04200d28a80f4482111 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 766515656 1250 766514406 766514417
    0x120614040c1209050607180807051507060603060902100201050910050603011524141207030204090e060f16091406070f05010509071401050d0506040b03010f05091902030d 75
    0x202a4903004030400480300c82c1585080c001000280350803600d4520a5450320045400c42ca020340d40c3c10300098144080d141c0300c5008010072071800c410411b030000000c05040321040e0803c040d8010855034020f400c041d50040c500411003926520520500200e008205021a490041407000706400461160702c449411080443c80c2e40b60800002d00401c90300c04402031381c5104100c001004003600346400014003c924154100c0c0802c01821348540800313422001618004000c40d0001c44c850301c0c0c00035041001441d0060410b525440c10348226100c190340045035500c41005c00105d50701c10003401d1740c09954102900002801030340d0203050507405014101900f410140300030120340b51001519480c0e034012050199014050a08a00810b0280d5080c0c2090040d02c0d404945a01102006001800706075102442c0524586240c0b00074400942055800350f00c80300e01007020307030302402018115004a440003e10b82030907100645030a20440d0000340200b1913070f05450141e074003c105118201d0f2542042d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 766516906 1250 766515656 766515671
    0x3100b060903010f0504050601060905060301030b250e0901050f0d0f06020903060403180e040b0115030902041a04051807030f03020127050c030a0512070302030c010203070f12061404 80
    0x18100e0141d540a6501586400d094485504c0b00d07403c03e40c0991b01920a40f445070341ca40703108a54004280c09604c2c0c01079030400040000645080141f58406410280308008000600a80e011494080483c00c001106071000550030b190818404c0c0c010b00044801a8500c024030700410001c001030b2402030003484900341b4a8040c4180d0780c0484a00c55002003c3c1d907170f146080e00c1d000d0900d00d4014a500311f1182c05004c04644d80381401ca05500454000000c0d000d40d80c40e050b404041c01490550790420151140034080041c0c07668002d220411240201300c0140343e60080a0200b21640249021080304911030101319011021811a090b01d400448049440780301e42400d034050b121320105000103410400e40b140450302009803140038203202d030b000d035003d0072101f904041d80c03a060000003801c03503003220060001000b034501c0107102461183c01940e041c4603100080900b2600100c624402141203e05400000342d07205110050f5980d200c58108a407074200740350742e400c9081581e20b05014a90b079034407 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 766518156 1250 766516906 766516909
    0x118020d02041208030115050c0a300f230f070807080d0b0a050f090a200f121e0a181e21082d09030a0f030204030203100b 54
    0x102c4001d0600910120f00340150b07450913608540c400d119041403e00ba825494465500c80d134110ba9961540b40700502d58114662100203407800100d1070b809601e0042400c84000385103040000010690310384070301840c0c051080740078242c00d480311409841c0300e00440381100d441552105803146070740c004284a0722001c03140342055052040c0040988061000310b04103c40718840d070000c0c2200c04c1c09030798411400d41d4500a01450b0510000210361282030307a800030340c10410540c4a10b20051121100780a080b05450b592155540048509581c1c1b03000007498071340000041c034000b600304250300185d10b403240c140c1e86500d406142c042c7c040213000f62a810682c02860201c1204022036400c14030000048100c50b6405e407000c0404603084400c1c2218114500c4a542040040120900035407103d040236512403129140450310399140c403401411300582c0c00b440c0303401c1070071041c81803001500071070361410042e1001e06500702d5210440b0070140104814801624081002480f40d201e074070010852034942c80 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 766519406 1250 766518156 766518161
    0x20a0302070e07110f0c0f09241f0306051203030108070608130c0602010c0f110d23070c030312020f1801020a0501020a0903021c02030a02010f05070615030203010f050118020d 77
    0x4410500e24840c0e2103040340305c0580459200c4803128100d40e106140b00c510030a0200e10305003220258460b00729400402c019006d04a00da01c12100000d2140741e803d0b04140201c0c05e0408118001c400090342ca600a1003642040c4d00100c0c101c1c0311490040d82550b1509040300e0f03807603145000d000108540350000c950741100401c13501e8251070744050b46040098072001c0c000d0080000e81980030015280103003009285020781c410401480c1e0aa0103445c844603c003405564036a01d1184404541c01d242d12071021a14842020340390a510581003181010b10b10b0800414244500c010204124810071100d4846044142101d08641422103d4bc4041d107140780142c0c01c4c190a110040c245500000310002807030b90000307541c4103903482190b0181c1107001e007500d004110315060344020340507840103000078003542c01f0b5098403964491a00e402446c05d4401c1c0d81340310035520003403440140e640d0f00201c14811490300b07018840400b840070318100a10741c03400005000b52aa205101c5200300d9001562541c03204803074 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 766520656 1250 766519406 766519427
    0x1d060f07300c08060108012108042d060302030915040519050309040e030909010b03130807030215061206010312020a06051005040624031e0e01090c06020a0302070e07 73
    0x2001074122805034021000301502c1031050120014414000140403513000b540340c14142da4031494244090105000100c0300d90124260a8858000c1070000003000501c60100424501c031101c103100244c1d030541c1005d1080100303a00148241030042c010006c60810024103103041090090010165849034204681040c80303082604071206821a411b00a01074000010000e0f072009440401c42d031030410140340d8032401003035002940300640707500422210071508042c5400022030108102402e580741d480d19402e0b800b00c4011009a00b0016006d65101c4404400d072340d021000740d5507100007500401c5a00e031100d2050000030f00c0703040f900c500003050a100700158140a40d000b68100668103104400000f0700e142d601c00c441c4075506014010406643d01181e495648100c2500d54807034015041c000d80103884e0b0181c004252140c80c00054034460714034010410740b5500382c1c000180300035440c1080e4026034120713007041c400d6601003844000000d500260702012a000000c2d1103140b40c0b51b0355001c84203001e04 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 766521906 1250 766520656 766520717
    0x6031202061e0c030406110a0801140d020102100b0613080609010609061511010b131508010905030f09010c0804090203060a0f0503030a180302210f01060b031f181d060f07 75
    0x108c0c50280c0980c001c034051b41130350707103550020344010503000c101701e92100e044000070300507084070305000c4500c0c006400c640c0e0b40b400d0041c105800c1652050901d2843d200c2c0da4805001a80120284903c24800f0310404010300010541401410308010300003011040d100c072100308100c400e03170003007508200c20350203102c41a000078410840e4000f1580000b01410b0301a51814107820200c00024803440c05100310700403181d001000c0c60903d4080020005d56800c0024014140516004c503200064030000081c00504001e480058032801e00900707204c86d0cc29603401640ca0f0300e08015050040fa540041a182075020314508013140621480b030b1118000910f0340700030b4110300b00710007052803400045a664104107241045404148021004030b0a0321442e1007403903180318041002c41d1240c0000001c000968010300c6240718220f5480710300c49040048040da8041c401da942803082c099141c001d4148007494207000c0104a00c1c1032070001d006400801030a0700041c84041c158885d11680a1640d51381e05048 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 766523156 1250 766521906 766521941
    0x93206161206051e030105060607031e020a0507060f0e100519180305030a1103040e0103020f24030106030b060309070605070203070909080304060b030a030c141006031202061e0c030406 81
    0x3040d4090007100a4200382d1036211b07508002c00141a424068282e030f01203a00340e40d40c3c90110000e03010280c0074aa08405000031030140484460204804000c81c00007040280d5508615103d0b14100818040d00c1105051181100325130103100c555002080d0f8041c0f120f400107481f03101d201544260f0740c49a41c905052a4556202e000009008000c03024200791800c17911000d20429015000c0b98072445079004900b01989a00b00510160030002c480b4280400080c010380583d0a0300803184000d40c14803422042581c0000006101940e07260045034441c010a540544c1142011000541c6a00640c090345081004c08110070040d9582040081d0003012096007c011108090804046c1070f4411502031b80d03490f0070507410050034200000c1c0d0000e401c0c1c25541b4414400c031140d0f580912464220400d0b80e151003600b00740e45854240384a00c800452140d801a001c103000140040e0030003400400450310461440503403803002c600c1d0395104e940855044035060b0349540d2417030000300401101011070100b80 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 766524406 1250 766523156 766523179
    0x2030a0f0e031006230a031e080f0309011b020f190c170d030510030f0b04050309040e07031b05090403050a02070312080a05011a0f03060409320616120605 68
    0x205e100351191071102c4910207084000d082400040300091200600002d100f94510000030780310012a028184034204041c541180700c03d80b401580c205031480c0340e4a954440604e5807001d410600c42c20060014005041e81e001c00c0c00c48a6292908016100c2010314411085000c0044c1c030f510303080140008251103000e2080501030181d41e00c0c02c207151000428500004261047ca182c9950ba0459612411500aa0402d9a110149140c028000300d426100a1141700c406c0c0e602c1d400b550880d5050680104012803450800d481d00107120055064040215881405607071100301d6902d0f031164050421594510008a0892819110340e202424210000c015505910707841401070303014070130b400010b00443e40c80d0851000c1c0c82e00f00003800030a4540400c508031811005030007869110000500016181c3e100761621615525a4041c84204007030400d0090070288003c900d1032400100c0b44024550361915070118582c0074a144800c0d014807200c201d4118032000c0681222000e010050003000944 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 766525656 1250 766524406 766524419
    0x5061206041b091e0f0b03010501060c230703080a09090f0b180907140f370b0405090a020c0d0e0f03031c0e07150c1202030a0f0e031006 60
    0x114411009140c0c00300c00e26030002c0e280c0101d000d004c1c410b0300812649140100041d0742c039030003412410307808040161078822240003640c007886081c0c000c1c2034946036030302c00140ca850200310703404040022180c000d0400442d406a241c1c000740e48d90550754401c00c043d9841500303000981d00c150b4103611600c411410a40400c800342c1c3c15400c01500d421083c0d41d246540100c052031030400082c1250304440503032094204201040341e10001c00400358014080f55081b507010701c0801c111100c55110810340031f940d1486221300c089003d140107141f005544403082c0072402d041101a00303100c6d610560b407040d016000820b035000419412140008140d20484080c61140e2601400803242601c0480c0303d10344101c94102e02d8100401202c0d4403442c5440c030314082242d1030880310300402110340106268800d9031004a4420800010140c42e48516100d40201000d00d180c1069009040440c0320110b40060281010483d040280400703020104d00b0030a0030fa0f0481404a481d00e00144c0c80b01400360306101c3c000030030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 766526906 1250 766525656 766525673
    0xe07060e28052407291b0904020909040605180f0703020402030712090c05091501090315060803070f0c0501090b030f18070f1701020a0c1502121e09010c050d0506120604 74
    0x2e003006403101c0881e500c40300817a03440f8030302100e4412000f000300d0400c1001c02840302c0140074202c4c00400060a02c00460301240c50310108440803940190782c1d90600005e0008208405000818080280300b1080d560b102036460f5100b80c40001d01894001c008a030106000703620160480541500402001b07509040900310941d413403040ca4055250500450101014400784006829041c0c443c0302e095880c43e43e40350010075904020350b41060b81c41c00d02141000c001c2c00203200c01409460100c0708102c3c0d500700581c0c103000d20703406103052103620340c801c100011813803060341d52200da03040c0e00b07556560790000035036141200104030700c3d424090130102160200c01d46003500281d0340319015403414400b07c900007500302e10410b400d000110355000780c1400064a16020755012000d1004007505014030300e07941c500c08441c2942c0050b08000c403003aa4140e440070543c0400d500400e000b0081c09140c840407405001c1c0d2050018010ba00c945070000608a602d030b80310196004405c40003114514a07041c20704a85 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 766528156 1250 766526906 766526933
    0xc1609021c2012060f040204080c010c050336040204050a050d0c0b161109090618010f1104080d1416031b03050403021e01120b040e07060e28052407 65
    0x4552102c01c911506800c0c0b47c1b090328140d601c2c540040076015007060066906000b03a4104441e244410000c56030b41d1492880100d82411010303d0385000c03080d010a6810040b848500b0840c0124810300040103140d07216150340c8103e400a03100809070400e47c0c144102038002503000394086400000311450708402121030940d01034041c44554000f4404201004a50241542d40e18070b5a0b110002203400d900070314081c2071450302e2240000921a40c004006001c1c2c2d03041c003100304c0400c00045002c20240c00709101d008a00c07006403501c040c603801d80c3c0c0c2e02076000e400341108280f400c28445841c0d200701401040da1040b540400719102c006642d103450010315036449070000724004c0740000c520b03070040152000c102e0048170f8140c640c003da01810b044030f0030042001c80610303036010b920f4403003214040e07905005039000f401e0b5607612140b40301e0024084c440d091040c41254080c110107848024155150f051180c41501d0084400e0b8901d814920842c1c0609c00901c0c0705007500c0348000800c6030422000080010 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 766529406 1250 766528156 766528159
    0x40320010209030606280b19020606010906272d06050d02030a06051201150602070b18210a0b1305100504170c1609021c201206 56
    0x80048118402401d030702580d401035030198080300101d00b9a142003038081403854007900000c18482d0520f05022029601544603e840301d0001540807480c400e511903007070b42601940010a1507080a80008115420310320a810070405a141165103010707007403101c0b14140c82c5d00781e40118955201c518045000941a10545000c8580b070004180840d841502c8000c8074581c0d20794906290140e4100710180d80018030100e1450342e40c02d00810300d952030844e60031151011800005808070b5400074402c1e2428550008025503001039010801c00d00c40408655401c01c043c808015103091850200340d0143c241c5e102c40c3c0303090b08404450f891419001442c0c05503240640c40e45900358035400316007507a00e890450f0240103034104000542d02c0342c1c0c00380c0105822a00c80d8514448502c5582d10110b4a90064902c184194000341d0103050003c041d045400302404242c1411440d0400c0008100c4010304c0074002143c2c2d1540b102c800c5a8140342211440c0a1010034280c100c0d640c00402480103c181e50403034151f07 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 766530656 1250 766529406 766529447
    0x80106080d020307080304060b0d14010b09090d03110d1d071202010c0b090c03100c080c1219110a03140f090303180a0c030b0912120a02210403 63
    0x6408000010366400c07012882c1c02a52800480e0f0702c50741004c0c0c4c00240300f610040c3e141c4c400d00c2e00586070007201c90041c60141064542141088a6030b50a403072100e0900c900c01d0413040f09014020f00086226040e200650400151200042601c0d142501130017a512003001d103402100100940e50310302c54004140001c007510351090b11101010034480c1c0420020b030005001015090006191065654100240c00220746411030b10600017490001e0182074469480d4403981628209500540c10541140203e03000c0e9041c110aa10b800d81381110050031844120145441009807072020b40c0000a00c45504120507942c503100e52025020340842c0085011020f8010005011304125241150040c02180041d501d19101c0c141541e040a00000708049a406407050020000e0307602c0124400a51140d04c6000c1e05207000c0034024140701c0d034011941c21144c0704010aa001c0d8407035110341540089a5400142c40d00348a0000301c05c1707580340358142090342c41d400d8244820303d500403420601d0400c03100c014 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 766531906 1250 766530656 766530659
    0xb0702010906020f0d0f11010c12140f0610360519031101090e010e0a050c03090307060c050f12060f04060f090f11030c0423010206040b0c1b0601080106 67
    0x100da807000c13100c4801810fa0407407107044410f940301c3c07450030298201c5850314070155400ca19515084811032594540400c1440e900303002130b0040e9005107800b01c102c01004006c9440d020f05c40a6030310f60001d1809203d144090b161200c102d00032004400c0080240401d5920401d560b650010f694508008900c84000d00040000310f900c0c288401102814017040703c0c041c81451507407509130b007803285500c09060008404000c50035480020b9400c1c000c4c50355048441c01401c241038084101c4a0161590000c84410070402816000010481e60013035444480080e81d4052610704032882e0084030092002038500103081b0480d08201c2c001180030f200d0032203004280310700d80303402c0004552040c0b00e1764059040241c1c0401c40b14019a005554110003c00045200408562206516401141c090140c1c1e88081000d01100040b41802030b00140c115940c25102c0c400040040e43c0c0c1c02c00180b0082040e100356002552254491f026150096030114105400c008801211500d51100340240303c8150301c1c1150 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 766533156 1250 766531906 766531919
    0x7021501050d021203090d050703061a090c09040204090c0302031006020c010f030b03010908041707063902040221160807080a09020d08070b0a05010332070b07020109 73
    0x101030304a8a0041564061104079420b01030609240118003a0f0fa000500c10020b5a450306248a0252485140a004054107520f040030856901598014030308200300e403424140d41390f11010580161040c51400e0301c072940b200001e800b81c8150780003c1409402d200ac09150585c050f005580100740b4004d1044d840741d1604400c90b80e5107580303105980090508001c007240da500036440402c0321800600081900499520b075905594807990013600c5000403250342e01e201c0030040c85040b01410452804a0010584a21440d004218007a14160f079088a003110703030801c0c411800c5c04200640c003400554552010340345002c221007002400401e50700b40800002c820819441400d9240d02154560842903202d103401115807810041c1002e40784e5954104040150303450700604007001d8460f5004d00c0d030303071040313840c150048203405131043c0e042c6814103005000051100250318000d10940244440d101603c0c1010446a8812000000c0601400d0303000700c0c3c0248040f0081072001d000b1380b48d045525a6602 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 766534406 1250 766533156 766533193
    0xc030a1d0d1109061008070e030132010b0304020d0204050603010b15030106020706210903050c0a06061a1306050a0521040203060903073201020c0a06060501050a020a1e1a0702 77
    0x17040c00142c1d0140020001400b4611400c0354000103030000901004d045503a907010450440440c0f00c86040309220304200d103a000d061130151008481c1e0303a0031400d10740e000c00d030340d8070a10b0310003032050340c80d00009101070b207007544018a01070000b0181d0200498603027890100d030740280680401802101c00c0800c40d01c0c004c50003500603803440700000070f070b1900740502705000300004030f001c03010003a00308103890b54034200304541d2000d20f018041c002100351421000e551000304185001100060610241307450a81e0101710404480c55410700550b91011010125468451041011005800300e2941801e8801e07260310340707204134070980454845071100341d0888c1c1c0d00d0242d010010310162005090030030300d6802506460340344980d041c1c4000441c3d60400c25034207980202e4021311407079001f142c018040c080980030b0310004140a003452858083e110b80000c1d183c00c0c8801c00900f18244070511007800700842200c079585146c0044665019091001c081d0401038001d84000005100f4a40440c940c1020741d0b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 766535656 1250 766534406 766534429
    0x160e03070302060306040b01200601060e010f08190608010204081b09060d033c0e1009050103090218070f030b0a1d0a091202030417030c030a1d0d110906 67
    0x1000f407415030b81c606041201a007007002c07400381008007605402c03140d19222420100c02c155113102902c03140d03040c03582c000d00b17451250b02210b041183d43c0c0c0d0011645908001032a811050721221045600c2c50001e03c000602046c0e0700c100140c0d880054000b5101001081076610882d031400c2c840884c0b980d00c800c00000500586405521401040080780001e00450b01c1080c00550700380701c01c4032031750740304810001000c48a04580740da80c000364101e0074045d801065044180002c4442c400c001c011200014072050315070103200d040c55a514101030a40d503898120071205141c10002c0c80d41442c00d8400180b0f00c10302d07040584040f80c200f00804015183c01c9a109080e00c200d07100144601c1010350500c4c954480282030400300d1541c0d80420800700e214010300d41c2d0412981d80003555203a240100c0c0b8030400d0001201000d03550000d02550000b04c0c4080f0460340c1c8100180f400340c00000301c1103410b08445981c1c0070a00e600c03036000c0301442d081001007800d216483c08211481c0e041c46d03441500348906191070 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 766536906 1250 766535656 766535659
    0x20a1b03090608070c0b19180309050f060f0a0504060809010902100323040501020c1603120c0201020f060a090c170c01050f0408060f090d021606051b06160e03070302 73
    0x90507418002c2910075020b640e406652458000c1c0c2040854403403481075501030301c0903420b8001a840d91403048109000f000e140445100070b440361a000790300c008228001d40d0203000d21540030500032060b2a0348042c1961051301d0440a480c2d511540300d000030b00305074401d20a110210f5000d1740020a8100103110b507594041e0040e281d41c024010451049000300030190689416a101c180441003216028944500c0f8a1080000581c1e8226890140d403a10740d5800d010401c045075a0410f00015400d603c2c0c2c1c0750200e0403400e00c041e044d041480181e0600e00400000d480c00c0c0300742820000b804440c0d810070114a4080c1c844242070b0b5895440c2e021001444000a40300b96000c420b00300243c5d485500140030000029140c0703400c2545801ca80c604103c025140c90300c0c02c80c451410b0050510742031120208440640c002001410f4200c40c1507808005d8030b1003081d02f40000450f1140394100c01c2a00001442c1e40e44e01a10028981b0ba490900301d104140b00b00d034005800d000c0720b00c0c114100001c034902903030740 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 766538156 1250 766536906 766536917
    0x51302030708060f0a0b0607050d020705041505030a300e0a050105190c030905030a0602090f03030405130207150c0206071106060307120f0b0c030f0f04080306040504050f10020a1b03 80
    0x3180b042080c086d004421005070810820044032012400a0001030005201640a032a00703d00d03200c01c00c802c1d942000040c0c05607084048041005d60f0740024083c013a20303030240740c0381ca20010000308076015980c401c2110b00026000000324401c50344c4429058100301c3c08072035000101d43c80d20300448150007030000b010082201e14000d400b48502649240d040513109140098030117890318003007070505588040407200300f41c010600d00d010707281569041112120903001103060502e02000130b6010303a406401d4400d5940d00250b1b5406112a1071078060320403180210a1100e26001c01000356103171411120000080c072004840c004100d00031941900580d4018002c10f6001e040880d410b948600643c011240c0500300b2103403200154140641c28030414080d5805610303440c00d80351185010740010286107070b0401c0071080200040706241500d030031a4060f034000410341d0300c5250091a0248200f084806803052007504126800350341c0003003144094690307400c50102c2c4544612000310b850450700070081031 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 766539406 1250 766538156 766538161
    0xa2111280c0b04020310020406110f030a140a090308120103060c0305040203060105061308011812020c01021f0b0a0308031f0f03020d030212160314030f1603020706051302030708060f 80
    0x2e0100e00103a0300a030000f07003619041c900000c916422a8410340c00240840d680d040306402118061002da490f0001c5e00c4040c61a00d450b860008140b0301c040c0d40c1041202c1c0c4081202e1003000e02c500c80d0b84014640c010b9580b41d850072120078901c0440001d1000300e8005d401c0c46e511600e40c0740b085c01954000c0354041c0045c001a400d003400c00c260b68005444660f81c50400920001d200e10090061041010030b24140d00c081c1810f038201600d66511a4041b141903611221610b00d40c1c0c0da00084140740310114103103042020a51001c041c1c06800c3c0405401e50251b020341c1d010061100c000000c500400c0d541100781400f415075940c00c001d03110584035004220000300300810250409190107400c05100c0c0c03050b0307856003646580380141500214080b207500d40114010908143d080f801d0b81e40c0016051041c1030842c40c000ca401c11300c1c00c1c0c0040040641a06079289040020300a406a8503c540d00c04410300540c81c000344502400810f409040c1c2c405d00c40c9480c0003c44213000325406018032084d0072081000c2c2d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 766540656 1250 766539406 766539413
    0x609010b0909071b0602070b060102070533090415170706020601030623070e15040b0304032d031a3a02100809160b0a2111280c 56
    0x100f68a213580340300308041c4803040d0001800b520003042d419106002502881c10b00f400024503103c0950403040c090f107000c982d000c0031011011240300040008051501d0024801000c02c0c20300d0044424090304541060417001411500300001d00039206004405c481c40309406900f035645081c140f15610240e04640010300c085100c07600542c3e20784003010182d0b000480403524104403103000300c85e08000141e44c00c18000701d42c074019000c10742c0070804095581c14182012000394043c8005000103051020711688040c49070100100400f18698024070300c28110500c2c84050040c05907202c2c01c04114200c21f02182d100d1810380d0108052882c01603c820340403007050a8240c07403150b2054950300d50361400b40340b100186c4da920100021100c0f143c2da07000300c4e824604202c1d8a0211014000c03182c600d03d0b02028040c440055050703600c0e00240385041390708040706542c181c46d1000c5200034000900d09180b82c4516024400000301074111540011544440d20341d01e0b0b02d6924081e04070f0580000e943c918201d00413 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 766541906 1250 766540656 766540667
    0xc0712050c18070822030e0a21480f080705040608010e03071b050901060e010f0c02010219080408060406150812070b0702030c06041101090b07020a2d060203030609010b090907 77
    0x10300301801c0b040c00103441d00504003403404210443c40c250780044c00864204001c412b0040c07000d012003403103111403111300c0d0881010042d80746148a035202043c285070591264400300304008104412045e082030b0f0311109260380f60ba146024942c0142d040000c0021210014440c5410741c280101c0070754104521a61049030421020142800f0b0810b400c07004541640d41700c02460080405031101e400e1002010000b400340c070b441545188c1407103400500100944d130045024203401e1740041d02032996206500d04200180900c0d00b0124551007080208420000658040d141d00d800300000d50800070368849130641d54501c02d80b051501d00307005214040c000f404039801c6580111190040e241070a5099a00301e1610408071015030b686240c00b24440d81c5543c004092034082c2801c02c80141c60501c0d40c0d00401d200030310621070b00c0500604c2644034004215504000108480c80c128841d00e2680d40d103d00a54981054407242d1140f2031131000050260304140845400440c0030f07104107039603690048181c44c0d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 766543156 1250 766541906 766541927
    0x60c05210f0316030f0e0c06030a270b0133091d010906080c06030c0310030f0804030c0b090d031103041703030f07050c0712050c1807082203 62
    0x50034041c0148002604020350300c501d150044010f0b19110030750000b401d41d4001d151000c01980f0b0706003443e001031070201c0c48211488081d9102a500d0302c82407203a0000344801c50a008000b2030040d00c10b400c0008140d240d02d8042d008003541c00040c2d8aa03c1070005481c404220420816aa0101010126200032102107030252a0030025445640e800c10961001e200140d00502c0e4086400180a0001b5030710423100030780101c00050044844686c0814141c0c4006810742c9400c10003c000551203035440680c400180d41d0204820b13440d5640c0785042100e94025020481c2d054507041030100d03200328424280c0e00d91045c028000e14220314551402d4500b0a0b0944501003540820000410416070b90016041c0300c0c0c200100460b56803401c40f280c10b121040144c94501041000c026800c95241d00003440c505445099200b10f03102112131078903601c0c100990b00e4a980000e68801450416403080d2180c521800841e01c3c0d1810310390340d1400c100070036030782d80880c921443c4215400f03c0110307200c0c140400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 766544406 1250 766543156 766543213
    0x20702180717060d152f16050f0d120c0807050d090515071d240c0c091905060d0314090103060f0905060a120b070503060112090b060a060c05 62
    0x5215450035100c50142c5a4150303c5a00003a45400361019410240303810000d1502c22440418074801d4458140300780c507c00c54514603075014800d080c0fa01400010302020040c032460600b1106859903c10f0041c00c1c424461003600d01e0350b031030112040c031000d00640116108482c65a119450801110707143c100070480d02105990500c1030112481050314900c0c02c650250602c0e44a0040c889049420b984c00d549803800e005008003600d00c3c81d400c1207218000c003024a100c0b03e000c51516844001c44040c81e000104039040d41c031446100911400d000003c4070308079459040f000a000c01d42d0343c0b0b41802014845501c000700000c100149800f518032620000d02204041498041001c5a45800b402d08084054220b1a40300d9a80d800b400441e01d03107009260010070155451034581c48154494045059005142c8014044000006045603120b641c154040c1c9030040401c0240d800075041c85e10415900f04ca42c00d000c4c1d0380d0740401085540c081d9244103500c2c0c1c0d01030014048030480030120740100b5031960004 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 766545656 1250 766544406 766544419
    0x19030c050706180b0f030402041e182906041a03030415230f07020f0d0f0204050604020702031e0a150e0d0504061b030905060c0102070218071706 64
    0x41001940c1805400d0081a4660354014181040c00542950042e00d40c0300b002d80c2c1600f0804540400d02c0c20040d030b54400d4040b2400982c0c5241500e0802030511440115440c4d02e24180e8403050940500d1000c40169018a0081e410500c0407914282c0084400520881003c07012000603901c0c90182c01001928503030030b84028001003108042841c641094010490790703c403840e01041240c3e88035030780c0720181a0b140c20381000e0001076440010303140301e1280e0007500b0740350026030130081d03444c1d401501c1100000903100211840380c0b81842250308000c017070100d21a80c10300c0081203c41c5010700940300f500e50000c01a0a08a05952000000c0c00250300c80340c296001e901071010110b0b4500d148150040d0b83c840d408280b01903540310003810f11107010994002c0c40003d00c8140401540300301102200c2d444204000c411402604040e10a0082c503807125038004400104041c070448190007501c0c40d2442510184240007010741c400b03500c20b10494041d40090654a10480c03091803a41d0001c0c3c1114016021 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 766546762 1106 766545656 766545677
    0x70e060a05070c38030c090d020307050405041505220b0a0e010c0908010b0604030b0f0406020d0c0f020c01020105040b0a0c02070915061409031903 65
    0x14200100802c0380420802c044101d107001e0818240d82505021040452240c8030204c1482080b02c0511084960446130390304044d00e010f0004403220f00e091102d21001e10000d0022880c0076a03251003a15000a0070b03413962310030103004c1c5000741c42c0c4480086103800f11000b03135500602682c250031604003520451010200400c4185a03201e07013902256250030b05607002400c6050402070a0b9440e0140c00c001e255000801901200d6885000744010b0080900700032181c01188409025650088001070381d40040e0308060b98814403c0c940141003100c0640b6000455000e192800e010444418280c5100754040090204040c000d1000f0b214902e82036071404201440a00032241183c0c503050b0408015000780101e0f00074094204e0100300f0540c0c0c4819074101000c0c01e02c600303004116602003041080e640e81d0103c4046030340190041151061111002c0550300481d08180e0802020410 = true := by decide +kernel

theorem cover : BRFrame.Cov 766366906 766546762 := by
  have h0 := BRFrame.cov_init 766366906
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766366906 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 766366906 ≤ n) (h2 : n < 766546762) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
