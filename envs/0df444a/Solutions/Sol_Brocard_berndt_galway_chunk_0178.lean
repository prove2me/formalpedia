-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0178
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:17:05.734909+00:00
-- url     : https://prove2.me/submissions/c2b05999-081b-4c06-bbb5-83a3d0ef08bb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 31834537 ≤ n < 32014393 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 31835787 1250 31834537 31834559
    0x5090703031404030803061309080a021615050d050c09030f010c02070b0a20012408070503060402030d0f0e04020c0102070b0612100e01142403030a05040501050901030f02040f 77
    0x211800702100b0030302c1d040c0346444000181c003016042d03501c07403140d00c05c0c0e80b00c1406141d00f1940065410400007907170f83c0c0401101079510b0901d0071140d050740c06070000008900840702d08010740f8505a40b107080c6400d0789900c00c40014203005241d403920400c28001c9180944082000c80841c1009000004003038080d89400780c44c00c2c590b684540001c0d0010001c00d41c0c010f5004c448100e41d42080704149050003484411035004d45010390410b0b1190040c890350407035885d0104801e00840d44c1610603101403e0b26202810303200c84046601940580c805036600640521941c81c040044c40300d441c260042c03584030f40002c0c090303034001058030080d0382d008604201804134060034103402480840d8510100414402c0c1103271140c02021901c0710f481e54481c0307140c1740460290070400e403c00e04541d982e289840c0a0085120309000921800200003142e06048018200003040300d500201c1521450b052919040044410364031092082e4105911880d4050800c0d4150001d44003901d15880101005410b0a4111403 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 31837037 1250 31835787 31835807
    0x7060f021506011407030c02040519050c0703020606060a030b150711190915030605090f0d031103040b06060c07030503030109150b0915040b040801060303110105061e0a090509070303 80
    0x8620120300c010b210382c50781c10510840044820141441c1c41d10014281510019060345005e50841d003000108140310b08038140c00c0910b0040c0c41c904000c1c2c1d172504002a0040d0040400003000b5074020000720b9018584440038182904040c1340c0402d00d002c40c00c0210700190350f06030316201d0348040420034004000005d40903e0051030180c41a15094016003502100007040f0710940c0400b030380c1e036005595001022801c0c48040c0d45c0040b01809a410004c80043c0d541440c01c20b004464003459003c0d00103144a070040000360389c4903015290441d121500d0b003400301d040151013a60300000c1005907200304c68091103000300850054020750b4803585400310041c141e4001120f65189282d01da07a0602c1017803054030955003802415101d2a152402080d20341c0403621030754000030110744002c6000100520305400130010303644203641300c1030a000c50710415400d0b14000c0c1e0361143d03c40070008071421084038440e410072054100910218103141d6484502c41211010303a121000c982100d4014810306401600b000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 31838287 1250 31837037 31837063
    0x30a06020c0c0109050d0c0509070e0a0312020d020601030b060f06041d060f010e0904080d0204030f0809040f09050a060f0f020a020a020a0807030c0902070c030c060302031905010f0b0702040204030507060f02 91
    0x26504071303402d87e10300d0030f24107450203154800d80101000c03460407413185003480d66001c005003403180815100d043c8001701003034603000c000051040618580041e880030507541d040369880351102280351a8034040090516140e5031054110780305010001d4460540004052260360860100300c2c0c50802e603080c05010300c2e40080c01411322860300c60400003620b4000400350b210f0b80007800745803190082d1440000ae84159800070746140c030610340403018000924002c010070a030440b0108920200407040e1001c0e28072001c0040d209030030800a41c0e001c200a074200900123040103500194000c002c18031001240c000301543c0d8010380c440c255000440c14040007081c083d22103e4000d011540c55a40c4201003d000d0380103a160058010402c41e0411000004441c0035550040c0140c58107510b0b400c00030000e400891794228001c0d6040c8250140512911034241610040b12818050740d040c50300070a11070707015400880c4c000b0341c2080000b0118405111680241000340d445540d07c442400303000345000c054039150 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 31839537 1250 31838287 31838299
    0x318010c020f1b1203071b0501020604020f1201060f0f0e0a0e0601120305091017130203030a050708090a030b2401020718021902011d0705030604060209030a06020c0c010905 76
    0x1124404400107202e80fa10820154216805030346101082580c0e0828016116074800401e0003001c00ca4001380c02c40602c26034008664405a9440049940c0c020944004c1c2d00044010110364041c00d104240424524820002150301a900c000c030750302c440340c19403000c2c1c0c0040c94550144101d00f0360142081d04281104014001000083c1034941c0703d68040c40303681d451007400b0f1150401c040c09141510400800100f40c03882241c2c0c5000c001d000341c076000416100802e00c5600240d8140d100e041005841074000d401103080040d1588143c0707141c3d204203000c0c0c80780e42c0140682e03001c55884c5240c80c40590f01c036220145150070301030b2440c1c0c00602c009030301000749103903c1004102c0b0f0360b0009403842151005a11100911082035603800244241e41507900304c4007003000170880c1d0b580c05404c0b0340c2001c0400c20f002090011007001c2d160b00d034446409550b516070042e80110380480c40e039030003078001c03900c0050688054150700da450208903030261040c4041c0b5041005011607131f42c0c204001600038113041d03c1e1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 31840787 1250 31839537 31839553
    0x3050a1808090a230607030c0b0c040906060f140307020c0a080c010201050f091005060d020405090a030e010f090512070e01120606050402180103050411030111030619080d0f050d020318010c02 84
    0x800008060700ca1130340a10004150802454071445101c030642e030f04000e000d0b21604011411464950003400b4482c100390400500140d024850b4910035120307156503a5649910304000104007090380302620070b804520851011682c0350b80c0d01c015903001403004500400b0341c01248000642968402895030003d60240402c01c40044c1c004542e909140c2c48411000515a17503c00020340100d0b0190704c00780d000340c50072003044212a4001008074101c0d01036118200006046401120340314004a4000000fa40d07004003008181031149030074440f841c40e1803e0780c003a076480d901c1c80b442e10381090303014140601010405005100e00e030710508019000c1075605610388815000c86440a01d03100940a041641c6c40000405000541507640b0100300010001e0219000100c0394002d00d0304180c85252252180791022402d80461080b800100c448140c060001d10240f07175402e4500e0000448074900303002003000115400445c6100462103221380c1072000c090078048118180c21510748000440075580b00c844 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 31842037 1250 31840787 31840829
    0x603030a12020304020d170304030206010b0306010507030c020a0306022206020304030308040339031103040806070c050102120a0603031d0303030a0e01150602030319050103030f03050a1808090a 85
    0x14845141070810900541c0d81c1c1c03540e1010800d403451015014101d500311a218000c4000e10b6001180128001d03030071121241d8890718015500e01c4182c07211400308100f0001070b40040e000301c0c215500580020070a03009142d490320fa1409a9010079000800b0b500c0031840d5950702e80e490380d0710101501443c0700960a007821039a0181032000d014002409100d10302c103007a201014040300c0001d00803010070b030340d0405000300c100d090201980d10104801051280d0150850070340d00000340c804644208004042c9511344a03025030351009249001e42d103c0d50208410318883d882c41080c0d81c007415400030009410743c51414001c18180c801c89101240d1801c2e07403540c201da564008181c0c0e42014110360002207075070032050074500515511400e220703004540e08001038002d0300403003d1807083c076827507140c00002400c2d519000300311102400000c01281c00504801c0030325220b50b0010b0790204c1c4604000421603d40b8010a412150180044904004c002800080c07800d200c5031607001403440f005804401441c0f40f07 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 31843287 1250 31842037 31842047
    0x2040608070905130209030a02030d030e070501030b0901140607060213030b0a05040b160504050405010902090909030a09120f0b191b09050f15160519121101150602030c01050603030a 80
    0x4d0b04107020203030007180302102542c0c1401700c070182c654010126000201c40c4200500a041c84205c9800c3c113000b840d10000c3c05500078082c40c070502c00010240929682080c9140030100c1521101580082e07003404403500160552000782101840d819490b0b030700910b980b030640c1110500804e000c03441d9080900703200c0001e12000783e10740c00089000c2004400c00012000701c499004507400b0641c030509010001940140d00d82c002e282802055607424030658400d1b00c2e4035903138480d0311280400180c3c041d5081085a104200001805200e0203410548080984170055415002d43c2d6420b0820003a01240c804000d00d817142c0d5101342110345043e111084c0780600078200c008144a15400360165104103c0b042d40e0340b10b4215004500c440c04079851350910040b00c0c824803e0001c2c12202d034452103016400c94041e0680803500325600020115614101020445141d001027001020541d2540d12a00541d40408403050192000c0d40c021600c07032170818550b03400d407803021b0a11070181d08104502c400c1e09500c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 31844537 1250 31843287 31843309
    0xf0117030910020f0a03080f060a0503100209010507060504060c020f0706170a060308040611010c022107020f10020f0c0904020307050d031106040804050907020c091501050c1002040608070905 84
    0x102c682664241500c0802e900b040300200f1905954003550020340c0806802008441c001c109490031440306950342c00602500002c00d000d00c61703140d800801e80c400c41480380c1d00200070ba010189009030525916a4810f01038520940d022074001381c0351458030083d694104542540d62007600002c18006d41303400806004803015140c0044100b0412001450007001e070b41010008544c0400215983c91b40c8450050501d24800080703402942003030000080c451000540e99a01000c0c2e00e0101c4003801c0c489644c8103591301c9818101d17040084410400c00079541c440c15900030194a40103070100034276078584d8a042101c03100a41c0d22441c0c03008280409030b01c00164500c1a1b4074103131400d140368401814180c50b1416242c204004620494081104020803500500100d410070b49102101d41c0f94040f080e6215205090322640024881c4002000c090300345494040001040c103000e841d1020600800307040c034901d60a206a142c1e00085c0c10402a584088807640c081100d15015250030706000004503240d00c6 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 31845787 1250 31844537 31844539
    0x100302070b15060417010e0717070605040305060604050702010b09070e13150302041512030905040c0512040206090a050406090504050f070b030406051012150f020403030203121e0a02030f01170309 86
    0x594074001491700e0075402401100350000031290b200f1303900c40d4503100c44112410f035480c003401088000a119400351080e941a658001d02400c1942c0c1d40034144401000024010011992910300441d120740b607002c0c8490140d880e965882c41c0d407503005420300c8042c080c0010300440c1c151601c49151064070310417180c1d6060760ba040700c000ca4a00290001c2c0c608009090700710000c0781480118000405404c0b0b803880c012505c06440034132207480850341c00d072020701400206c125645a0140001c0040c501a4002e100c0d141e4018205400e131911100070800721070701da400000c2407030343c2c5405010500208011140b1070041060050002d0b07401c00e003c1141601010304001e00c0b075621240416a41050388110102408407204005958400c1d400c1994074400c4010b10900000d1420482c0c120201f800d0080764103a9804d90021072034041403004520700c1c0326000b03200514507032003840f4080c030040e400130071a40a84840030002d80c907400c04001113180000180c0c000d034036030014112440c20708000030083d075003a110 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 31847037 1250 31845787 31845809
    0x30308150109170705090c0307080601200f0304080c060310030303051905070302070c060206060616080903070b0706060501030204050a0e09011d010e01050112170315100302070b150604 81
    0x101040069030082d8003900854401e01c20560740e810700b0361001a086044500450740c8594648954101002c00d00c801d0b10008001084100014440d502801d0342100c0303540e03000002d0003218042c0c2c500a00741041031110301840d0b0800a801c0101141c204036022a450341110000d203036091180e0380e440703a00d2441c40002c00b4580c035a4000742800c1c251441801a01d00800d10501c524940303042d0080095104001c121040c001c030540c0031801610000d010303480f40300003034030a41c944a0b0100d40d000d024a03900904540011040001c6081d94800f440802c0c024489949080c0d10f6030814039180302620100e0300902e04140c81804200980d45c1c0301c20203142250340c014040307241034540001c41405008074002c5040740000420440506000540c0642c100b212504001c10131a6265030b4845400001d804014140801c00e0440c84114424a801142c00c45811f4005106841900300440d81d030410364070140c004a0b9000c43c0183c1801418044075900642e40240c079007a0980721000074026004030b002e1152010 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 31848287 1250 31847037 31847071
    0xe0105010f05070c03030f080f010608180c03010606081006030c0e010f0c02030a08030105031005040b150316080d0f020307050703110411040305030405010201060605071a0403050739030308 83
    0x340c00b850071035100300e800a0b040f07201c40d500d0f07080160a034140310043c040080c41c0480000c0100ca00320f803107a41a10301a07070315095151941004100b01540c0c1e800b596055020324002c83c4480d0f0740074402ca40040c08680c0b14031441e032402180702d00140303d46900c000c0030b250410505020240c2d02c003010440c50301c401d0900000c900000b800c115030744c00c08503600030b405205500d12042801885006103041b5401281103a509841040028003601d5003070358000c20302c80c121404582c0d410020302240040d50800380441c1c074018201e00b0505101d902c00d03802070480390800c0032450121944180083d041003018001140740240c150340d5075aa4070154880502911460035186002e6503898002025042101243c80c0c0c50781d480b41001c0384c8981c45481f802c0d004d9861300350001001d074020810303104030b1a00142c411590380045404012607090062080781081400c12450000030680303944406424a006103035468146101c0e49400010501618802546005c4001300000b81d441302009a1003002082c00384446 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 31849537 1250 31848287 31848317
    0xd080f0f070c030c0b28020a2c060415030b1f080903090307060302041805040201080414011b0c02010e0109080a0809060d0c02061905010b04050f030a08130315060e010501 75
    0x14007900c10080017001c08000780495003501840c1100d0415803240390100d007007400311002049202d0b911009010400001e4040944041d503201d044260031008244071fa0151703a00c3c0028003d0307000d904151480f40300c541e00754010300d40c188151040c3d4402580c92843d00c0c0802c0601c402c1e5400e00000040800072441c5c00941210014020348001c01e0000d4101e0740100d49580d005070294101c0d0203280d00141c210440303044112070501406000b41d806846d00c50207a2515252038801d11502c5241403a90742d00c5a410141c1d441c00c50b443c481126503030356036100c40c0803003501c00145130003401c070b0000381045460282480150700104840c1d10315035000502a41d03550080c0040784035030003084412100c051801c008501102e401041c0ca070303c140d018010b4070748407c1c10909698200c8a0a0240c0107580d07034203000500890418445c1641c80c184001d045030401e1b45155a460540d51000c0c1c059141034100210801c20810b07500c000f032201c0100ca8509110190038288081d01c010814440d180c104142681c2450b08 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 31850787 1250 31849537 31849547
    0x918070503060108150a110f070606050901030605040b0a05010302060306012015010e1311040b032b0207051503060907050d05091506031c050919080d080f0f070c03 72
    0x2040c010301a0744056a42c0c00c009074030381d00703001a440101d2403160001600d812030f92041142c2d03d110020440c0c01c0140410714681643c00c000012118540d9441001c2800d5844420150085200d0400031903d868189860401c092000c2e00760300d4003501b06801440140e9900d0140c903400744c070071302e00590304d00c221117452101548401d68400781342c0100d00500c41e503c00e0100303000d070503254059407024040e121009c44c2c4403003800400000e8429402e5000f1185070f8542900504040ea0000782118060300d40400070b4074064003114018110b0b440c45085c15403445405224810047c00c3c1154910b0041c8511405428180b02c0102203902c03940b500c0b400180345d0380c000d109a0b6070300c003c114401c1045241c88084159a0798100c03100354964a4810001006407400181818600d520080d0002038180b03441401d68140d00008142903010351440c002c00c65562046290400900418000f007000c3d01d0740040142c011071000e080545039041d40020481c0c242c103403a403401c3d00a071151074020015802400c040ba6 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 31852037 1250 31850787 31850789
    0x201020601031104060902040e04020103230103080d11030a0c0801050a0b0702040c03020c0a2901030302150a0e0d02010615030212010b030403031104030609050607110709020304111206010603060803040302091807 93
    0x1071b40d52001c1004907021050320303045840b440c404c1c1c80420088000c00c1220640b141c9034503458610100352401440090460030142040f00d01c814008140d1001207070906035a5002100d04d403010b55500e41c0350b42d48090780142030380d005003400c1e107110031058107090551089124052003e0702407a1945070300740c440c130f00ca94105c2c0c030082c00440981d09204400c0c50b091411f81e402c09800c8207901800d101c1c0c040322821040d81d10341200d074941c0081403030000307074400035042c0c000c02402118080d0751800e840170462014840c0560010859000088903410074010200c0040303c04405801c043c41880580d940280d1000140e05503481000081d4490380d59203001c40103030442250801c3e03038900110b00041000b0160708070030002e6220b40700f596465940e14008980740c1031411108801c951009008010003071095004640190166490003541c40c1ea0300040356440c0340f05caa034100e15034819030042001d20340c14030488000d004694081c500e0b161071030300000c4441c0d0000e4441d40d80300400c441144075441c3c0402c0100 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 31853287 1250 31852037 31852049
    0xc0703050313080601091a01030b030703051213120203120d061d01080d020f06070c03180b040806010801020a0918090501090302010c030b09040506041101020703050f1c0507020102060103110406 85
    0xa640e07042492202d6038806181c852a80d2622070071002040c41001e90141400c4000c5039201c1c5403081c070b60000114081d0601040094050142c0c400c00f1021030803c0c0f000c1d0030380101c4102500e54401700c03c04000c45644003070744101040d80ca07c03101c0100580e0007040201c00e80b0340750080c850b11400310f205ea56005096583c0203072003881d164000a1442c0c4003600c9168100c1745030000350b0340c45013045001640c582204240c02d2995800490000342c416000712040d0384d00398004e11f4140b12609203078040480013031881d00042c0030400045000c0000c82c50401226001d00348400080d828240343c0d940c0070303000c120300c0c4c010b50f0401035000d140301c20b0020359644210798068000000380114603045c00c01030f0003800310910220009084c00480461400c02d41c0710103008a500c17100424141d611501c614185c20004500c440c1140103550f00080850410490b40044184803000f514070111024a094110030780750005005001c003d229100151ba004240241100c0d0400c040200d8591001c000900505068003c2 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 31854537 1250 31853287 31853293
    0x30615080a050d09060215010b180301050c0c0c06070305030a020a030f24050109030b01120501090b0702010e070608010b09010c020402091e090a0b030618010b040e030901030501140102030f0c070305 87
    0x51090290014108000309a82d40301c04031400d4171003100701c0c7c0300c201114508000543c6400100441c2c003c00e801040819000e4510410341460038000a0a60300c00740c0d00d0540650021844442c0220280641228104116002443c2c0b0140b83e6000e81203000003007800b0020355000c115101840d0203600203c00480781c01008004848880c0800c0544074203019841413003458003030001ca2554011556407054a802ca5403026944c0e2910840e40d03001281920211055502e0703c40440002d02e007003010a0040b109900045414500c0841e658584200c0d903000400300700d00000100100d4248100300c0d01140c3c42881d0841c092071180c000f00b00640f00e2004000d400000401c05501c8a003e00701800381e003a24211021011a00c803002c81c0b40640300d4074001107a068002001160794101010308407100c0003244030022a2080480000500300d800e00741542142da040021070003200c0da0700d03208150140208801d2a0601204031000030742c1d17030181010080383e1841c000b4203140c00c00801c203c20302c0110380c00022 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 31855787 1250 31854537 31854553
    0x30b0307030f060903080708010501090506070503160804090e0d050403020405090a050708010c020c0a080d0804060905031602030c09090607050a0504090e010606090f060c24050f100501031503061508 87
    0x1c0c0f8000d104800007030b0b0001d140c403008244079512074005941200d030140c5d640b000d0141004200f16050380003150803943d504c010841c1d51480c0d03091851402466001e528210340b240d1034800d041d02901c1507081a940b50b900300c900782031540c0341c111040e10184d0350180c0d0001020b0342c601303450500c0c0c09680d00010345944103140300001c00c06015000820411119825552040d14080c14455011040d00454180b500411544501940b00310005d941c814000d0700040f49801da5503c40c80d01b1030b03201c9200c090194400c0100402507080401c03060000e02001c0d07030314480500d091030a4a41300c038806492b0780f04000c400600317418481d02c2002950301504410000300f01500d41028924002c108620030417002c61202a000200180a000325000315a00e41e2100100b0410641c1c0380300c074200c8445461940d40c1c00c030320045100c0848511800b44256803070700751f80c0000e0504002003000004150311150400d4180800208894005000f0354101c0340d000743c1c00300fa2003c41c3d050941444000fa00000024402c3d450 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 31857037 1250 31855787 31855793
    0x509040e1e06010e0a020306010207120b04061d06010b0c01020c01050f0610020d020309060318010507030b040b03030702150a02010219080a15060e0f120706050403120f0c03030b0307030f 82
    0x15404104110118034892220000c40c0c481d03454442c00d00c80c18107030043c020000703054804a600150751281c3c05105861580740c9810394680203400340310054601a03801c604000030005240f050529002c1158860002032601a0b80039959000500402041540109140d00c207071600b501503820242d8510300a00462510610080c0740ca030080392180e1048101c074822181c1c0350700201d4800410340840d405503140038880f50034080305620143c1034a5400d000242444c80c1c914080c4992400340145070707004120303004070104200540c0d40001110313201c0c0c7c004104920041e41d4030b008414011180150781900e5803141201a80240150b0f0014a550284100007030a100e40c0942075520425a01c0800c01c880d49c682da1220190040c130b0300812010490161003004146030154500d800c44d000100f10860280310102040c1c113010907940034401040010a0030f10400a03094000b41c0305800524000141ccc6040c51782c010208404038501a0500d980c8411a4110351800c0c860070014580001d00100060790500d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 31858287 1250 31857037 31857043
    0x90f14090114030303010909030c0204090305030601030b150409050408090a0608091006141c17040303140f0702120a120c03110a02030705010f051902070302030d021501090504030509040e 82
    0x44900c14000400080740b503048903401c460031500090021400e50b030800c2070000090401607419002d20402104c0307980140c0d15070080c88451480b0740d55007512400c002c00090195288031155500c105a44403a02b0380303508043d010760741100c6104001246540f200e08003e03010344034601c40903401c40340d09880414416048505240540004001c403244800302d8010b140407111140211410b40f80e141c11180d14070315200341d0003a00403024411840d40b09105980b070302c001c5204c000032040038500c041000c20030b140d080120380d200c4403c1244498907104110340040344c5482140e5000788142e1810b0300250304644c00700a0302d041b103980408035000120b03c0c680043d041c0b5844900072000a1a401a15109008042808a4a15130180080480900341401520202d90242c449005c1007000c4c054080c0b9528126603000150b80c2503009008aa81140149070620101c5213908003550305c00c4140030b03030311313040746404a0454205040015083d02c44e071608945900c20001203d91042c20600c280c20816004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 31859537 1250 31858287 31858319
    0x608010305061806010306091103010603050d0f0203031e0907210c080c0109060302030606121e01080609030304060c030f051503010c111c0e1f0f030204150c03090f 72
    0x5641100e9656580d07640001c954140c03180443c6039900618010070015050350044102188203804c40321500640310003190840c1d803079500a51f059071165121640e090b8101000c08495005840274602c3d5240c11201460211064000180740244040018040c141d041c000803014001440b0078003a1010038604035490444201d40603103003031180c03a1000551980006003541211410784a00d40c60030301d000015802504020052904454100240e613400074256000798820160704441e0a140d03c41940841012070058010599990003102030004a034000401d0300c2c0d115510040c0030500416a110440160510307508400040341000207001c40700070340712201030b03011000354000c000020184400302d901da503240040708006d42020144c0340100300c42700c1954660a14a0401441074803286002c501c44e4050ba0554103d001c61054054140a40c0585002c808405d20302d4294200b50038600414010942500a03209001c101750040f410503004c0c11030007004200058104004590b2010700010103510 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 31860787 1250 31859537 31859543
    0x30f1202060c0711010c03030204081914070f1e0e0a05041205030606090105030603010b06070b0f01050d03050405010c1a0705040f051009051c050303040602070615063606080103 78
    0x40700300207104a09007505582c01036402c0700801e0038a00300c44005551171564140706070109502003001041e008410400641c0f00d0401e43d006102c2d80040327080c10030368003600a05100d021b80012404000f1411a00307007544c141d40c0441101c03490100c1051000031081c1c526403000240090107170410140314042c0c1d002c28402ca00403c80c01c4000551444100c41a200031200164480d030180014240e55101d84091580000c001d000002e03e42000000500745420a110440b030644274201000301c54103074854042d00620b41541c180840841c903503000351007030007a4090141000340061802c0140030350b00031242002c50280d41c1d1798656060000d00103045078444e0155190f0380c502040c0002c2c05061055043c060340100e03584140115040604101680c96210300610640c00000d4110000c6001400154002d9100c0c81005a4507603e5280407030640710b001070003200e100c0c0003000400415801c5641c040650741a00d5861844040c00d24942c103402c0c51101800310f0502c1015030101c0c0d40c0d81c000b2042410307280 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 31862037 1250 31860787 31860793
    0x1e09040507030b030d021c0f0306080307080304021206040206030630030a03060611030405010c140613060b040b090604020a0314090114060303030903070f0204061809140a02030c19030f1202 83
    0x4000901343e941c0d10b40c6040f202041f58008010308403180c4245519800702c1454680494210f03550080c2c1860f43d044144181d030b10010000a010451900202e004940f4592030701034019460b050700011050302004084902504c3c402c22150b240c95140d021118518460724100500c0070340c0306c3d03203103652a00031282000100340f034220046400d0740590b40f00841c003502c41000b1494039003003000443e100141d001c0122003d0500c80d07040c0d00140c0b000d0009611407030409000a80e181240d0620f00240c1e114103030250b001c2c80c5407542e000e800b9109c000585074454020b940140c0d03a0748403110214000c18100003ca1a000f4044081c42a0084103402501e241c0d820310122100700d44400c005c05841b80300030340b02382010340d10822081e0300294001800444c0b20b800200005445952591410700310b21351500a21952980c0d41b00d80b0040190500d2043c41c0e041400006150300308032a80829520b010343c01945110705e950b020001401081d15101202541d481a01c101c50281d0300e103459203000c0e99601c18000580 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 31863287 1250 31862037 31862053
    0x201051902070612181e050d030507090b030c07060510050a0303030e060604060b070f080909070509040501090b01121d010c0801080d020a0305040b0d0905010216050606040605061e09040507030b03 86
    0x404d90300404600b08120400071050b8032165468410340d02c01000380100000c1e04481c190040342007840303030351211502c41e03c01080714605008028a48081600b012040940a0062190102001065450312070780804001140c0e102e03c1d04140e00a1202c1e4440340c3c0c4528082e001008040e03060f000303084c1102c10307841180d441703485a82c104016160785010740307200c041e4240070843c0417610311889076144601035000b0030300e04654480410042ea05c00c68103d0701050002a851040e82007a00c500313030040400c410200449075a020008100d414008844030b10192a415a030a51052150300c280044000304003c00c41355901c0040038180d50001d11a00040d8064030448410150010034118440f07a4169165440c00d410043c5100c625040001e141447c0f560b10802e400005600344000c0c460740c0500c880400380750300309103019450000c00034142030007070b41042400c001c2500d450701650141c40d10740358004404500280e645c80d60707026800005900c00d050a06029606401d0f900c810307030075001501036030300031 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 31864537 1250 31863287 31863317
    0x10603170405030c0907090302030d0905010f08160c060b03010906060305070f05060f03130203060405100c020102161101020a08070b0105100e030c01030e0f03030103050c010305060a06140702010519020706 90
    0x35014600c140c503019008080b502c4914079204681542c018a541400c004280e02d0380c003c81d207491701c0c0031445008030b14200c1c014800c56810104045292410345429030742c40c904085003a0380084c286942805000c0d00300448820443c0c644c010990000c8060020040d04000781000d00c0900714902c0181c0c1c1074040c02c0408180c10301000800300c01d5590144c0b0551802070460303d184855032004002869004c002c1c000c07200140d40030720100703024034080c90040000f030000c1c804080071078917007400780c41c19a0300c10010940d410486041549925401074815018040900010703410a1405213004100003000500388081102040c0310a050303c1d001e0310300450a802480d07040c0c41168101a17555459803002491104942c40380d045681024258070664102143c500902c0d8607540003a002100c0a404c9040c41285a50f89032240d550311440444103a00070500d40040035103081c030b80d440484010503000400c01c0559019404981e90002441c003040c44103030307521000075100d1000c2d01400d0001010a0292408 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 31865787 1250 31864537 31864583
    0x10e030405100c11090a060510021c0c0c03020d03021207030c0312110921030c21030f010e07140a1805041b0305040f0c080d170705090d11030708010603 67
    0x511380c40701482d0903900891040003011040100180181521010301060f02e40b1003046101c8107141c0c41e0014000030208186141c50682c48642c1c200802000c84044404038034217803c4001102e4041d689140c007907400741807c90411a4542044007003074000110101050350041040c10080e000e0742e1290400e902402220040e03030004440920004030500600b002c0b890805c20607950201605030900c0546104000181160840207141b82190414041c009440c005003051384110101c10303580d01d00d90314240d24880585841030059520109401000a00841c011103146c8400c00080d4a503035284c28004800810842d40740580f02c003554805000054141028001c1038584154800c03841003d10740180f044000780030081060303606190320707942d800105003034040303000151007044042d140140e06032101522481c4c0c020540c0b405014114200a5110f6010042e00d07400c0030216500d4a00045608000d06041000540641c4c580034102d03000406202c1540300004170b03442000201030107411020740e00c40d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 31867037 1250 31865787 31865807
    0x31b1b060c04060306080601060f0509120610080709060506030403200709060305010e0f070504020a12050405071d04030f030b19080609010b010903050c150408010e03091206071d01030608010e03040510 88
    0x1c86e2b4505081a00700740600d01508808001420b8800b8440e05022180d1034030800703030340030840d001400b003050100000c188100d9019209203a014040f5614190118100d480000c001a0400c4041d00d40110314100a804c3c02c211840d041d41210360324bd4550200ea001003400d484121855880e280d211040c8440c04286040891605009800070714a802d09000180d4031000d4038070204074003500c504000740400e1103114081c1c1e008000418585003460100a0100d000c5071070404c1c0b408400b010000000d0b401514640f90709070383c2c40d0118031400b07482e01055101400511071900c02203980404514200c00103811403051000c0300080c400320796110019540c8031072500014000b5000704603000300700c2c10001c004425070074241d50010300d019900c00d405c40c210b880c41c111200c0240c00c0000e40c0e01a510304200304030601c04e06c90014252906180300d0240806000c0200140d0305003124428411980c0a41e20400044c034425000780b15010746100c19a03220340c06409400d1180040b00300480d000c070310890b000c030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 31868287 1250 31867037 31867049
    0xe010506010c1401060b0301080123190c09080316020a050f06030f1003020d050109030e010e03030d0b03190c0305070801020715020f0409020a03020306040f02031b1b060c04060306080601 82
    0x11a81030320b44038200e81010483c1100210f40d240d20001070002c0d0413000a5000308800e200004400d00c4d0405007a03a100099803034035580c0712800c0248a07510025030384003100c00030300c002c001403d60201841a21110f625a1000e29a030101042003c003008000040202c0039100f150360014098846041107403403410800300940103e03040c0005503450041c914001d0308001150584500c643c0d4a50000f01d012010303980854499440c1c000081c01c154100040e1101d41c5003d0070f01c1d4500c6803100021950381e01440c40403608040d01c61807903100603182400440d071745207945901c00070300c43e039241042029446584001c540611a44400040036181071003610701b10b036032080300030a00c0d440e1015494007a4010960390b1071013040803c00011091220300c020801c145032503e0168403840c0c4201000304440c00242100380f118010810000440c00100e00c800494a01040b80d42d01c881d0303500c8090000240009040103d88282400d00504809040c00781c01290400c0c2d0302403040513115040c1e00e480b00c03400c2c4900 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 31869537 1250 31868287 31868297
    0xf05061b0a1214010303120b06030618040c0f09140a05040507050108090f030a11160605031902090904081e0711060705032b06060207031106091302030405060a0e01050601 75
    0xc003007007a00c21652051100035400010038010003120520b2261002a0b0044020441c080c000b150189200d0084440541d01187e2850035454148041031000740c9002e030107558641d4440000301045000080ba4002d00010407002e511242c8400d02c0301d004001000c03400ca600c15501c4000380992166004061040e54481d0242800501d09401542c40e00005001d540c20303070003144544551090108081c040f6900c4540d1030380c145100740d89806050000d60202c1c0220344c00c0d008000c0c001c0640003002c59400c5094507207054003000008075401c0c028000e103582940d102020109000502500b400608208020310080070421042040704405600c10f040000303042541035144001035143c2440507007686d174011400e4902d050026103000141092102400c4404a400c001107003000b01030348582c0e000760400d0300041041c0d90075915441d40d61600741d83c19610441b8002010380341501c41c004038412042134030100f5512030405142183e00c901c021507450b0750b054581440c2d040a0721050184500400b0f0684130 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 31870787 1250 31869537 31869547
    0x4080403121704060207031b031409010e0a0b030609131101030504020609030114040b060307030c0905040201050403050d0f0305150603060103050a0b1005190201020f04060e130501030f05061b 84
    0x5454580c0201118440c240000c202c1c0c620341080c0000b0480748203501c80d102c0107036034190528000e0b14520b030b00d25082d00e4010a4030502d000190b0000d010006554510b40c21944030b020440040b10449100303070826801980d0f40500003810340c80781c0c0185000c2c4d54101c03155903480d510f440d10340c08840303000f07100a409100245105121035000b58401c94000c1c0c006044070307281ca480d8001280c00d4078208481d005a042ca96004c1000703000d0410b42a81e003100c4200c0c050b14000d459a00c602402d206240201f003140e0b55a00e000c01e0842e0701407400c03a00150b910405454104103081e402502d00e0803008010004213062000044250418904002d11298000c1c0024110307120300c4e0044008060041900303110310760300c8854415075a41c0400c18800752225544141e038a000a8a000340460303002d443c203c06580c014406c014201041c00140c1e1f060b07403030510300041413030701d0040000c81145450f030049401038584000441401803080c0c400002d5801042240c0080e21040d601803a01c10300302210031031801007400 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 31872037 1250 31870787 31870793
    0x303040608010e01060e0117190e0303180309060403140c0301110a02011512060510091503060b0909070308130306020a121a010813170d0b030f0111030a110c07060509031504080403 79
    0x2050b403c2204076528258003040782700342d00d046480542110702c2c03da001000700451000c036800c07002000a2204051420000c8020120341c0c64012800000c01d018100c2c000a020303d20100406ca543e400020000c0c030000b02c655000c50056804140003400550910081243d900030042500d822252440c008420300c0c10103840300001008060400c055101340c03641e00151001303a601440404a074a40c1d50245040c0c81c605d0007a0884094a045600800e000001c2000b60b000c00b0824800700ca03007111480381d640035800d207560101c401503040288618404130f1001341d17480d84200302c544201d01c080d900308820107601800c540c044400100c00f0f0300003000d500010300d102c401c503203502e181070303102d200b500c4d1b42944243d2009281e84c0054140b10340f041c0da0b9009032803582c9003c0040600201e0072038000c03c81c5c1280c41039654500d00c4006c000f00b90894680c2c1c85411640c29100440e07400d101e82e034080e81c04081d200c0100400c1a481074150078468441e00056070780108030b00100900490b8007518071440d25246036 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 31873287 1250 31872037 31872077
    0x70b01031401150b180405060f09180d180905040b060f03010b1201050708100e071b0f11030f030405010c06110405030a030903051605010806010809010b0303040608010e01060e01 78
    0xc007010055500c4201594014000300d50350030142c8050250309440f540d62a0740900d504820700030084c4654106000d100c3c8039152a20a0510344505441921840c1c0c1c0781d07103030890103054442c0400020b108128052842c16070200101a0003101d60420221031340c2c1e50380c00301090303031402d03900507042002600100e1076503d48106010710940c000360010590400c04070000302c1091041d228030344540d44078030030004040d62142d54580c0c0445001200c518080c20030012400030785008280d17805010103054528184100146c0702c1280d503500c001c003640605a585020a060514907402d58020710030f00302901c2c60460040280c42c2603c80603940c080c0c180700e80380c90f410050820801101711003102000f001c1075503182800f820aa90703000307442d000c080510791714090385010492803c00000502c580018070850380e02c0710300a90841000d1a0100254072903100c02c0780141904641a5414800000c0c0052441d40003030301541203644100205001d60303a543c1c1c058483d2400070343c800e40010305504100740042414 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 31874537 1250 31873287 31873313
    0x30e060a0c110d1101050a060602030403030e01030b0d05030c1204080c1c0c08031804060f0b0d0e030a030b090105030a050a030522060504050906030d080105120a060c0320070b0103 79
    0xc0e14002e610842400d6405003840c4040e115100014151300c0d03444440c403070902550f60841d1403c4800c000700b5280c040c00035101d01450000030304111218090b02e80b03682c4660400781113164000c140e10021851458240d6607a07111407070307082d5030780180410000c0b100801c000352403c030b4209201510031400c80b1030402c0010075400210114003a10998108003003a140d0840c90098110b400c0119039402d06100c030580c204118260b243d104030301b0034005200e10010317120f04504441c0400000c0b511550f403004e0300c002034086424850078901c400700b90900741c6907141d0091103000d9000d0f2545403981e604c40c001c0c1038484100005c080c001e903122400e0140064842c400810050307074158020082002222042c05644030240d10a40008601081c18400c51509009058002c08120001d004282404001071300e4503c3c14441c140c810341000d44d0000c511380090040b1003010307601440c01c00283e600194007030000d25450101c089030010000b0444021181d403c112030045801008410840c1c0c61566803a503c4071070 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 31875787 1250 31874537 31874561
    0x40c14030109020c1005040b04030207090203010803120402010201020d140106090f081e0708071d010602030a0903021903050102030c03160921030e0d030309050f03040612020a0203040f090903090501030e060a 91
    0x10541319400303081301481b445008030710459002c2c256040c5030600a103000c0031034000310003048c030420040220030800421150740032240c06555120741d59130300060380240145500003100b9400c200e819540075030b04610150586101d61105d003225600c81c5001041e1101900404405500216411052542c10703140c204040c0390040c11a42c96071384402ea490700700401d681c000b05000198a054100c0807540b0780989025080620055003003100d410310082005d82c0922000e4014111a031043c1260209440400040c0d50408020b49d62410b100621408a0340200c0e9407501d00c0c03140d1a100e10300c03248510f4031344040796011042c581071001c0784900c0c149080c0020b8411010300015030440c0c00c0301d072200b00c502d030f00d4217001c2e80300000e105c0900d003440d40c28145220180b801c00c1c0c004020a0190940214032010301070400d0000585a07851000180e140d48101d81051098040d250340c00a000107a41c1c010700710051003a520240c0c0e03036540b00c0064054602d54000200a074004c20000386900718503600440181e12 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 31877037 1250 31875787 31875793
    0x6030c040314060103020f010e010806010e0102010f0e0f0705011701030b0c090406031a010e07020d0302031009050108100f0203220201020a0206030711070807081f021e040302040c14030109020c 85
    0x9600c0e0b4424180342c2080c0012545600030300d00410035450320508034502244c0a0030200c0c401c0300148002801284020400c50500030b07000c0017041c441c0d10075804101410700b484020442500002c421959580103107103000c1c81c1b489204000b01c0d165210f2594510f4159140c5c003540c0c1580d0a59541090711100140904080c0606100c172849a03900e0f4041e003002503004c2c0d41c0407400b105000906030103021058010141034400341c1e00303008a0b9036000440402a50381c80c03400584a45501c6030080c1c3d00300043c2d10240b50103081000110703850401140c00941040b4125080022045c1010b4400680c00104c50521051210043c00442c00740c0c0600265080c61052069803240301c0c1d15800204a0b40050f184038001a150080f4290600c0c4100301c41006051044020131a00345003a102f15034590501c0c01110100000c1c1d64090b51203040c83c0c0582d54100c11040c1d681840d50481604003645070401d10090b03101d141000403000c8100e008074084d01081c0c6049800f24a13581c04c280215029501901103541e91744 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 31878287 1250 31877037 31877039
    0x9010e030301090504021e06040513060911090109090516050a12051512030c1009170712030b06030420010c0f06060e0609090703020904080403150b03010f020c07030206030c04 77
    0x602400194081d2508440002c0c00381054014004207651510710b061160648100700750301e65542c01c0944007241c40c1118100744480d417881ca0300015210341d0b03025078441414203c228040002d4200900301c60038007a6100349100780c0d24030031541991420b40e941c1c1412030321018020f082c80d2240008009101c140c0c1030502c0380c1a60380740301000b01d8104585500341202d070030300d0124103803900d061405000c900b07810045042c0305000030810788800304d400c560107120b82c3e90312260042005104c0703c64051400340ca40a0345440342400c102a0300008030549800013480c1540142041c50880e0544e070046410418801240f803c444060302140381c4400d055040c030859808000000b4010f030f003000106880703030401050083c5484400b9040c49409099076110380c0b180c0c03080010403500010b02d00d0450b070301115500c2c0345480c0c60601c52800d1045810180c41032001d0410940106d4080d0481c4070444425402080504401c9161400701d014402410480780c002c180200003610303042020350703000400c0606c128542 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 31879537 1250 31878287 31878311
    0x30b1603020f0c07090c020a020a0504090609080703020607020606040c08040b09010e07030c030c0e0f0406020a050702060f03150303090a090b0f061303060b0d0807080a0e04020301090b091602030a080901 89
    0x3d4002807003950310360340548400d00c005029030007450345180700750001380406940307035000603011121801101d00440e55204410b040c0200da8100510b540d8101e214156544054140251036000c115940c0740036100d400d001c11f449040c00e03c03c3c1d170281080c0781d0302c810320f580310b03580d6490000401406042d20366481c2c1070717030814090050000c00d000390721030511501c0942c03642c80d00d40a2801c55510280081c5801020045480905942590f105034040790050b950b00080109468600505c0700c0603421200200d058580c6441c15401540500c0c0e0510554030b9440341982056540d01c00c1c140c8040d000300c0950f50802c014441500040f03081c0c0001070040b07003e11103840104d50185c101c45d002e090222440c040801c14040c1c40c2c0301d441e49a0400303542d00b2a542c90183c403911241c1c82454001808100c2c00039405401c02d200d2800c005000c440104199030702d50b59644840c000d0004906803512a20902d404a40d1102212964010200a64028505241e401c482c00d41312000c0003041030404d95221a280b00341 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 31880787 1250 31879537 31879567
    0x1003020a0b0705061e0613090b0106110105090d0f0e010207170d170c04050603060f04050f010f06170703050c040305030f0a1d030a0221010207050c01030b0604030b160302 75
    0xd010116241c540b1a0068100a03290900281c00c5225001301310764000280c041c86203010794001425900c0d0030508442003054070040140c810090038000b0201d0000c9101984a607025801c0360340b0030300070311003a00e420014a4450010b650341070302103070100c0b050654050003441100c009903414015202c00700c3d40d40409443e208181b015a02103a0445a100444a90801e000c0101c074003000e041d5910a00d07104054202901c40d81c0180c6200740000300c00903a15a0b80c0411a82c00701e0300140c8148400c2c1803200001d200103000b80241c0c4910704214401280e801c1c402e807680c960400301005459066180c28005030014600030f0403100b600c00007000044042881007004188120383c0072a41907540e1801d64000b81042c0d2104620804040891240b0307203540c2d0300080d685449034040300d40c20400e001c10601d10300c099440405500243d400403900c10284200030400319044035080e03c09110043c0c043d02000154445da0100808403200e000104841d003072424040c00f500342c3d00c0d08005141030220480658 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 31882037 1250 31880787 31880789
    0x180905010e010b030f120406051b100b010807020a020603060607081e040602060f090a2003010905010f06050604030f08030a0b0a030f1106040b040e0402030c040c05070605060a06050706051003020a 86
    0x25030303070303460307102420300f40c1420404009a035100401400580002c005031046034402c034403541042000100d10748598111001c0302511484400040341e15407414100203001505100841601050030000000c0c1800d001003083c40c10703140d0003016903255540b10400c0100c250003180e030595011005216084104001c0c0c8d8140281c034500e103c0c2240c0340e500c0c060000f4505840100b452880c6180c09051200000000580307181541d0701c6105400340140e51100601e89420750b003410396056003020b40308424040198400c408400c3d0f10241800341c541c45105000e40751149200c02440c1c1d0305000054400714024001442d0843c036040c90200b6401c007401e0003d581e20300c00d500b0690390342c005041d00740f041050300e0307101010b0b8034025070341d0a080900e409184541802030303104a0422a280500080c2103603001d00c0361064812006008200c0d1080807071004110f03400071141100c86074038040128a86140440c00402116016504c592606085a40311801380c80e002d008951301c000b604070040300682c0c810741c60374 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 31883287 1250 31882037 31882061
    0x7051201090203012904060303080a050a0e060c18030c032e050103150b03010504050d0e0a080601090213140906010c0809030d030f180c1205070e0c0a030c02030c060118090501 77
    0x114142d0440f804c840b80700c10001c10141b050380392000400c00240c1002d0b9042d440f505c044000281030741c900c1c2c05c00c805040500141c000b94011001040380200d1648080d0010180d07099103e2009001c03c0149a80d8041c48108542d041e44a034540000e00141c001d821200707810f1000135080c0941d00002d4085c2510710a03001124192148060900540031303901c1750420071202140244541d040540390f41d0307256240003a94004022948900c7d83c0b09440e0103500e20b0041400900320f41030b40d0b82d16034515009401102c180074843c603d5842c0010000900d10000020b03a5000b005014651190310064440e5445034008603443c020030301c90385c0c07ca95002e20100100c0f031080d442c0031421100f0400803504071143c85d500e100540c61030411410101e5440880c0340305990350200714207914442c4d41041d81c6490156448003822040c443d0400c07004100c060003804103a0055141440080c04500c4182c1c0c0300d008803d0b5070501a440107004000c502d403072a02c0c103902003400c404000344034812911060700f583d51481c031076 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 31884537 1250 31883287 31883321
    0x706030204140d20030a0515010812070b0f1308191b050307060b01051603030c120c0e0918030c03030f0c03010305100207030201060e071206060906020705120109020301 74
    0xb0000c000c10840001c2e02a403044412284002d02952000540079001458941c03c419201040100392410400c50381d145802000f242c4c0d010700c0440743c0030030b80d05007400381031401d0183c20800315a003e840b2013515142d030380c840c2d0513800541e500e07810110140001003d04ca11425104540c8001c2802d1f040240402c018441c031800000c0800b000c05840ca1100c488121001909002d11201241c40030003903440c03266000300003060341c11007800126181d0180220700c4690003040d00820081507010351041c180c0c05c140c2e803220f0f0408030103500c08004681d206140c0001007003050105003d51f01c0d203c0d9a066000070105a5441e0100c2102120351071a0065501c0403034590000080c0002d4260003002c10760721081d0804018590744c1903a50380d0340c1300c0340c00320303580003141e900402e0701c42c2054000e401c084050080c7c003100d030034a843c1c40c0304010070170502c121500394a54070304000072074000d101e0038451041d6800b030380060000a14107014040440c040800c0400c640d5030b00e1108000694080c0140c21000c2c4c0822a1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 31885787 1250 31884537 31884539
    0x70804051221060a050f0405060607060501120c090b0604061b05031c0e16051003020c060709090f0e0c010e03150f0702070806060d03030506060702220608010501030b0609040302030c0706030204 85
    0x201070421000380c007191165004ca00f0070481d42d50360700c1000c602030380143c801164a8403000041800c034050f5042c0141107509050000c00c80707500103441c0c1c40409000d0380f41c3d440003680d0740c0c1c4000210781800070465000141084103000740741c018210310f444640603000c0041c1c00d540c1d50700e034035045801a04400c10200c07585d1070000c0540905000e03101060410320090700750821140c03c17038081e498203485880e02a4070020042030f44607020f6810b545100c2041c01c182d482e107107400070300288a58800d008850703546203002000c01404803588100c031380d071100c0c200003801e00c0e03003130900103540b008044660654940b003444484040b84160080450040150003515141818007a00190900714a034120500a502c14010000265113502c3c03003618841d0142000a40ca8032601c1c081880c80c451003802030340044c01081d4100e00c00003404003550008455100070001144c80b01d0416081c0d5000703220140040d845140403c0c01071414a250707030f030040d2090048903c1c040544114500f00340d5541d124002113075010030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 31887037 1250 31885787 31885837
    0xa0203010f0e06031b010c050109060b0114030907091d011409150c0a050706020d021303020103050c07030c020f0406050d0c031b06020d030e010213180c0201020906030708040512 78
    0xe0340101510601d1081e00b81031038924046039a031030038140d01e007140c18899a030300380b003c0c3d00610300c5034043c540000091020110710b0519401410703a0040782800100030070600c00e003002d10329054a018103030b150b028008191030802c1c00e20250581000c01d2140440355022903070000d00910600c0746003461030342880d1451070607903181424121200751400001044c1d1003000041000d00046820a5020f81040380d00c2e010325050040083c0600c010280e42203100044031200744c46000d0f07901040703901c01d0782e06101d01c0ea030302c050201d01d6020b841d4006000c200c40307842c000014540343d4080504c1a501800c00034507255940700040c2640103041c025551007982c03813400c1c01800003050070300d0024800068419855481c10308003d554891180074481016a20802d44c655030f4405c2d0110307580508020071080d10b2a48409041d0804404011040d20f001c0c0781048600f042c50040c002c4d02c262520040c4070300d080d07598180094602c0907000384220f40c04e0142c001c80d0b5034650300c0030b00070303007481484000c0000104250030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 31888287 1250 31887037 31887059
    0x6030b061c02060403030f0912060f0e12070602090d050105010e040302010b0105042102130c020c0f0a080a0b0a0e12071a090c0607050309130e061e0f0402010c0b0a020301 75
    0x1c8000d54100d451401580580c881e001114112035151030421110305c4004407c0310200120b4000001066042034034006203c11500442900051801c040240f0b81c124500c3c155903030b920654142c1302400611021000c2075869001c1e00304030001520040d40c40100c0e42e0343c1c41c212442604045401550714023400203040c2e09100765410780744282030180c500382c10a011003000140300040101911282c41080c411921512000840c9001c03006d0f01b80100c400108001e511031810300d86050040242840300b106d1071030014000f0084500d82170280c40c584141d0b84071052001001094102020348410301030302c0c1013908100c64a0480811996291200c419152190001201c040d105245c41d602c0c0007848070b16403021034000340046048982e00d68414840c90064254018018400e5210622a030010700c00b540c00c1d00f0654201d02010700b03903800c50380d034a141e8031220403910303041e4a42001070800254900700c81d03114203034105005041681001040b640ca800d555602220000070f480c1d004001004584045 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 31889537 1250 31888287 31888309
    0xe03010906110a020d05180418020310051e01030b01050402071b150305090309030d1d032506080c030408090a030f110405060604060c150b06040603140606030423030d06030b06 77
    0x641b42c00c5241aa0711104090151403d90700903108a650381d6422070307020000c0310322100c050b5010702070f2401486440700320b400a00c811180c820381140300c0103141c001c20f10b81004040c10b1701d5001d982d40210343d00b08814072009401900b0210b8264000b1802c0ac11030f103040d80300c914010010302c4202c444c503001125009007500c10180c006403280d0700038003401c4c1941c2d5020406110020f2035140c1560121040386221a8200400b45044d405000303203403075907035064641d0040984d0303100704120046480d5a980405c46001d0130845030804440400d1001c10f000400c140300402038060010041e60149899440d01d032490200c014040714081c10900e01d602e41404c0c9801030a81c030120807522103003000c2c602030003d4408400304c80010f00404c41c80c0c1c070084945007194414640305c4009050f140e216629054050000c003054a555079107940c00c48001001c078507160741124842c80d809801400176125a0b1002080f81c0c149040e419024001031120011002403031091100446c0168134000c045e04000c0c060000c5c490340 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 31890787 1250 31889537 31889563
    0x70f0f0503070f03050d030b040605060403050304090c17040b0604060321090902090d0f061805030304051c0504090509010b120c0103150e0f04030905032a010e0109060e03010906110a02 81
    0x200e0f00d040001c6035000c10070042c40042800c001c42d04640703d40000e40203226942142c0d9103c88003040102c14810004003070000c0d500d002400704480711610505a0b400c044141840c4070104270b000c000b40008246000755600300b50b0250011480640b2aa00c24900f030030340f010400100908424400040d9170b20801d428001c0040076021858a80f0b40e0000c100b80100d0040050581074400d4004810040706a0203a0100100d107000140d8400c16031038081e459610560307081e14544a10a1104501c040c84400d003907183e0015242e031444c1c14900403801019140041c0a140955a600c07a100000d8655200b05085d9450b0f00340502a548003020001d0704991180030710794002c440328401480760880103030b03170644c00880b085d006041d01d60703583c0b900f02c1c2c80c0d862542015406006040f0000601801c030b01445103400600e029200d0420512130044910f1080101d80c0da0010b801814104030040c011a4400000c3c0c1b0058004500c0c1020750f00e0320b0064550712003071006900000507803006001e906011041401c18 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 31892037 1250 31890787 31890809
    0x1501031a06090f01061b08070c05190b0d0b030a0f03050406021005090309010e0d2f06030405060c0d0908130603050c07050c0613090f290a1403070f0f050307 69
    0x300b00341003c5060005014000c01d100c040700c048a40d40020003007107818190b00010321552450940380102c62a0030a02c1074a00518803410301004038107284003024141ca003e00255801e000803c02003401801c5544059501030180a0300040400c0100c4410b0142500030344406e95218608480285070100505d0700c0d128952900c02800760f051808011a04a00b20918121101050900000f003a09403100e070700818400c0f04513540c005800c40341703030303c0600d0098001140304540d240b03106001003484101c600400c83c1e0000400141120380c07020207011010322045001440004030360b40c0d02e03110b50103e111041c07810401101000190381c540156035106c890549500d06018069a407159100d4158004510451000c00d4500c240f10b456042c4e44014880c039003003030108a5441c0c00d02c00060803542d01c00440800c107072099540084540c419008a00800f8101c82640c034908100c03444101c41c1c41001139403502038148001140a00c0051100c060300b2000400c0f89030a00d8442014a0060107a1001c41248 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 31893287 1250 31892037 31892041
    0xc1003060302012708060a1a04050103080901030e0f10050916030206030c0d0f050103110a06180b1303050a0c1401020a080d0513020301020a11010b0a0302030307030c03021501031a0609 81
    0x10b40d00c0742c46501400100c44014141e85054000c3d104e0034105a0403103845031141d44104524003131550089400f103554101c4407140e40c40c0d10424002951001d01000d80b081c0420400700129521039800102c41ca402c0106031380c0c1f0040c840000034180072080c01c0f0f15140d00d80755000d00000e1303181403221808001c0425001d20140345140d0101d2100d000040140c140c035480441c015400514031741240444144020b810030007582c591401c0b0407095242607031a4002d10074036501042e4280500661810005c96118105130249000f030354111650001480340d0b100c501c0c0d038a00100080c0f00300074043c002803040c81607001290030100d0300e039014900070114034119031042070100041564902100c040f01d05140c00402c2e0f90b0750303582d1200061605440000d416610000381c160080740d200740d03d01132560955000303204044014041040ca601c4500010790315410401c05680001e0203200f050141d81d2007801602c08044040c40700d080380c50400d074000d8034040c040c06011f001210030403882c41c0e4000341c1203400702514 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 31894537 1250 31893287 31893289
    0x4060e03010c080c160204050c04090c09050f060708090301050c031906140d03030b090703050703110f040b0a1209050115121a100504020c030a020106061b02150c0f0c1003060302 78
    0x8540c084d000c951003040009082040b0f4032030f15010001039801030018030490071b15028205050740180b14078410f00e0310b000c1c500001c10748120040011104c2c001e094018141801c1d0400005501c0008110b9405000700041040c81e1800c0c0070380f0384070b0440065007644034a84006000c50b2822604a00e003003180c0341007414000c843c0441d1002e6400316050b00c40348a80c1c045031a0940003007444801d1036a004545404002c60541c1c560020352241449540c03c0c441180c040d4807042031801400300d43c00161400f40002c0c802072415402334038910310300703141034800d085044165808031480b0000660310350751107607440110390a9405100004180d0703d4106003040b66107413240300720300c1c035140d40d102021003805000c42c101e401c0c103e0b094005810000c00855844402901c803d43e82d038003191242d80075508041000a500d03024000c4102600340b00034440c81d04504581c200040c00746001d0100c64002001c4c4582c40c0486410414165901c4c40174006140c000c2500d810410000840d040c140e00b0107040c410b0078401 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 31895787 1250 31894537 31894547
    0x1112030406051c0f0b0316060c0213021615050105060412020f040b04020c0303060a08060403120e10060603090b0f13060504050307020409030804140106030b2a030c04060e03010c 78
    0x48804500e0710780c0e01ea034025020046295000d400b0700d403200d07003401c0c00c0c07136200700c5640e00c040d914040c210201d860140e50032020448070019413145d0300101c3d0009403000094240603403959a0100e00e400011b180600d1150048080c405424042e0340e680d000000c0b0a449103464803e43e400740a08603005424185800066514400c0c0280002d000d108803000722000d685580d0402101205d00a1041d526448685e200950b20b0704100c034101d2240501d4100002e5103030004c90704078010340e055660345040c0d030f8a18010300b024000c0960300008501c02d0350342074003c0e110705101e070801070121a84c000c15080c0460074040d69141c0094991510001c40720180642c0d034418020202070310340d201c0d901044560760b034203045056014004010350002e040404480030140c0c440242803250b445241d00094a010504280d42201c41a000c024100a805000324000310b0780104412118580710101040c5c0004000d00b0090303581041e82d1550161034046820300071150818103800c3d41150681c000c0011281c0c04400401c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 31897037 1250 31895787 31895789
    0x20d090510050c070f140906090405031b0a02180106020d1103041a09090903040e0901020921030d0e010b010210110406050304020a08060f0406050c0304020a0b031306150311120304 79
    0x709022001540310300e003034410312070303c0002c000303451000c3c000640d1140c00d41c1640c02501010340c0705d514111300092461030490002d07805590490015401c115940210101c201d0340584000214130448003d80010782ea840740c0a50410800180c0900c50352400d000a440c15840340010310034420b440710303c0514684000266030407130300d000840e111901110141c201280c4608000e180e00490103a04202894600100038000c481b03480c84001c80513907039040160300300e0107464110b5034403c0c0080249040c0080032400304200b40c10000a6074a00440c03040f50a0131074001c0d0300c0315031099440d42f070452025a014407d03810020031501003449800d040154004082c80340d4040e00c400c0c80008004a41592540c003141700250031150210f80b00c0c5d0a000c041c0401c00b034170440e4101ca00c141018001800c803040d00c4281d81c0207030f5010f81070340c40540c00e20f440c40101d40c00003001c040306e1007401d020440200322036010f105c0d884000b040f80400c90714118140280b9100100342224002d00d20b02010724420100042250 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 31898287 1250 31897037 31897069
    0x3081303171008070801020a0f091409150301050901050609010b040f090e030708040801060e0703020906090d112d0604030302060a0f0207020d050c010e090603070e0c040f0303080403020d0905 84
    0x75065994015852402c400d2a80051245205160022580320015402018400440d40310040003400122007110500514044d2140e0750301503038001355080c01d00341d000542020f621075440b441d03400350b00c02080c21508100ca0740425607443d00140692400d018580c01e001d00b124401040c0350038100001800d060fa150b104070b0b40d86c15920904820340b04010b0054607405070b0302c42081543d495071450010701900c3d041c01208000b6100d1004545424020320031140d01300c6c00600001d00f00881481003108288096500303503081d0302ca90740040c09a03511034019400242e000110440d03003c000c0c1000c03e01c51740d00c0c442d450f030040782d00300000c1c40420340015034194812144007001c2032100b42e100302e04029000f103d000030f401c80c0c1c030139000c0f034104000031410801c516000e030390b8031211001d0842003066540050310000d0305608816420311909510442140c4d000b445e190314903146c250782e2000100000529801540000d040c41c00b48000c2650521602d4840c20b030310301e04000380c9070034000080c2907210011062 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 31899537 1250 31898287 31898327
    0x7081605030a0e03120405010c050403020a05120c12030409060b122202040203010605090f04140c0f070507030b04150507080c09011101050702010614030a0f030302030402060403060903050703081303 87
    0x21041510b94201c4000402c000c2c058a4a982618440908408080d0742c11510f035400c00740c207020354522035420344003103e4008002181c3c041c980018800a0880c0c2800e218481c06410384c0c9025542381c1d8511314034081e50240044d0342e130311702d400750301400c44140ba00082c140b080c040142d424800c14045615800c40c8454502c0745010340000c03680850b038004400000c1d0441c1c004000010180e40101c0581030000c42a47c5240e504a41101040708a480e1000c1c139001220b148000700ea00d05405102802582e80c09010301071a080e400e0320b0f024585519503004444140c4000200410001c20203428103100002030000d0296042c000ca025010740c0008168031202c46010404a04c241c0c45400c003c243c5000160080205007800e100007806801c0b6401381d10302c2c0d81e00f068802900380c03c00280704030203a9003011404400e8901980c00f10702035800908140e901c03060034400400070900500c6110340852080d20b0301c46c2e4411052034086c01061005001e40f1a00d0000c00400020030b4000c00700c6c02800c9404050 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 31900787 1250 31899537 31899541
    0x106090902060339090a080d020a080306030703050703060f0b1e010e0f040507080103050c1005030112020109080f0607180b09010c1509080408153306030403170708160503 75
    0x110300c020300300c401e01040040e503030b01e581360740240443c0004001400c0300341c1b09483e2858841e4002c5d0b07a00c5184142d1280160320010007800070440782c401440d04240c0017030640300341a6491701d5003490400796030000e42d21031340da904880e0042025072041c811451416102c207129522952194200c03401441c038201d0500c810041d40c403840b030381c0e4807080c00d1940d0300081c0204000d06003101c0082c0300d1802401b0032250362007000207024030751030070310340e01414081c182d03646a1a50782000005402da4641040c200c0c180700c290403011499a905106102d2200e42181c0146140e20741041c00411200f081d00d0350440a00321500c1c103100c017650a604071001580f0a007009500c0c40d40c00d203007921b803090410420605486c5440014420080e0081c010002c40713403000216001215840704200c0c4070401956641001c101142e0004070301400c1c0c92042126001784105401f460b0f00349004500d0035401280c0850003d02282c50820714501780024050304076000d480d01380c01c1441c1c01013141500700c2031650311400740071000c00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 31902037 1250 31900787 31900831
    0x1003021008090a0c030b090601060212070201180f060f180b03040803040c0302030f010e060c040f0312050c0102030f011707061b0f05030f0a081302030303010302040222080c010201060909020603 85
    0x3150030003c60380204240701c8656681884071525030203644061050080341c0001510501c002001360240303503101308882c5400031650040d120414030055403000000c100310b00144601070402d10800030016038988025009244500412070030349140d075210710704a00841884810179802c141c81e4060b40c0450704540c0d98466050001e101c4955510013541486880c404858000d010341040700c05115510031100d2507245d910b84500203008078018400d04000300e0404001185491481c3c450a01c0b840c28000d2034101952401c9080ea842224004941e4811500400000f01407242420441884030041d051850500c0c0300180b540680c00360f440c85000541460703100784140048118001c03907011044a03520000d0200c803030100c0d0401000840070640000006079004041c008403030645034003e014501d903038216420880250420f50341d8107000c92a14034240c0300282c60101e0800901100f000a2800c45021000203080d034200360042c1c00740c10b0405080c4801600d81d00c0680781c103c4040d60016146600420b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 31903287 1250 31902037 31902043
    0x8030304060f090c08161205100507051903051602032805130e04060e15060d0602120708061e150a050705070f03050607050c060610091a040905100302100809 69
    0x2030003101040c40009107450700004e84410901b00e051101c0d2031150340b880210a2008006d4002c0c01d03039084412240301c1c01c10b0541c8629400b1400382041c80c00d01c40e030040c3d4041d00603019010314020a42e9002030060340032190195440110451004511b0218031001c0c1d8801140c00c0e0280c013040318040e00f4281c0c2994010700a8840520702e60745140030841d80c9203036800c41c10f84161001d644e4940742450b01140b2090201d90b4481116054011041e1611901c013404680100404140d5609a007071085010101c004030754640581826510090300e070030a030301001001c2c502d142c0c1320031050904081483c0251a000b9012000c004036480726510b07014000c1d82aa00b510038684002c1c942d00964001080c506454045802602e004508403505580e90100507a114852041c4c13401840c0e02400004416162542c000010702a0524140d25403980d1a90b11100441c20800340425440300401d06002d6100300c0d200b0707180d011004e400107040443c5540c01099020314378040c92030400c2030080000d44129410 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 31904537 1250 31903287 31903301
    0x5040807120e0d03030203160905060f030a0603020603090c150405030c1203040b040b0a1701030201140702040b030106060c2a0302010f0908030a03060302030d09050915152d030108030304060f 84
    0x76110700303d1a14a450014001d50045924042c00000004a6942c042c4036400410a945000d000b2524144a0a07084403203904000d1040001c2e5850710404801030322954040c60040e01d01400606110140104000b40c01c03400c221b10100e141c0f0248400c0015540006c1c038002d1440b0f00790360307045c200541c44942034194865600407050306200022300003401501c45004014100e804d80d9400d228070102124001480400e12021380000c11032a14001088031180042031011720043c000554480d6040201e4296481c2c0c0e402100840c3d84a00c01c0c0c41845983d13031980d40c00e6480350b88404501d891b80b03212080d178400240000b03810040d00d50f906400075400b52030088068802c0c4401c8035203c1d9904507000b0060022808100e001c0e000e030030000d84405006018a10a03554020001c1ca800e0b80c0d0040700c0d40b120204002429480030000d6880307860348010400400ea0303c05134070387d1400c103407030103035001083e891200d411805804c004000400020070040166508503501840100c1d01415052a070320240101c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 31905787 1250 31904537 31904539
    0x120f02101404020108070c03080109050a14041b120203060a1112040f03090e100303050a050708040b03010302030601050a0e0c030a060b1306021c1d010311030109050708060405040807120e 82
    0x38107800c0c0d0001421504201e8402c5100341c0e1499281ea54941c402c440351112150001d01080a200040c0300d000400d42100b58040c046080029010000032260955a64240d500303403a40c41d5902c08a8515241150312100508402c0340b0035116010792f503000c01d0b40c4020080c1070350391071642c540a01c904ca2104030100c0b00c0c00000b1a41041039810b0a0400c1c5c262045608821008110030210016000100806271885100302a050b840304a2450f00c0c1680c0d07640c000c04440041080810002001600142c060300161030540480c0e51250b040d072062618100060700724078450b91131000e0403c0300076030390b118040d80480c2c1c2125042d126200c0301ca05c1c80250255401c003100310580400e850340d89152000a00c41154669803c030360824000030032141015001c204202d00040b29406007240c200c050998001004606140020b044103120341441da89402c00c1c0c004c14101a29502803080b030951080c0d003070360000d408031000c000c0e41c01d1655414103188035062000780b2240744060005d5a01380100010020808 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 31907037 1250 31905787 31905791
    0x4060806070509090a06051804020105040f08010b030705040b03030703050c1f020c10050702032704020a020708070f050915030c0405160801080307170c010204032907030504120f0210 80
    0x5010341c000d00707241c010700c2e200d034042d071409000a800c00c5654094181180d00142c0103042c05410201414030180c00204244d0500c1020000000e2240308504610001c212610001960500702d004041c1000201e500052041e42403038208042650080b04403044240d040c00d202e03940d69031015440f8100450001e9072100c840200716841604901e81e0001c2095090140580d040c5d000c1e4100300400b101c0c0c00780c80ea030340180e00910402030384185504402c420703081c1301c070340c1d04001004400008059902c012900401030b00040ea04004400007008507030064401c45030b280d009a424074010501640004100d4070300e49500420204160b14207208810048401600038002d61500500e070010340c00034100042d00150004000044200c00403042c2d03050694041d070301800845450340d07905030a80022014641c99507080100100180113519030240b122a20607001e412005510703601110404000c8c080c070145030074101000009501440211020b1400d0704144c03070241080507007240f4000070401902a10b0b4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 31908287 1250 31907037 31907041
    0x50c010608060118050604050c0d02090a05040606020708070605030106021f0b1509030c010e061605150a09060605010c0507030602130308040f090606022b0c061b020601050406050a05040203040204060806 89
    0x200c213401c403405071888451052103141c4a000520003124001c03035044250300002d2148100010850b0002c10101c10020b0200e1100790b1503900080840321594041170250b4070600003000344050500c0518001c2580342481801d540c50050040d4490711f080010001c441c20705a032107003020695901100c200d41000c1c04501030303d2a0b5550240103a800030111034403a101c1d2480401280d803150005070031141000c2d01c0c181c2040290b140c0c19132203880024003210702d40260b154113401804581001849035082081c08104132102d424403c04a079200c0d0442070400c07400c0a8040301250002440d00202d03a44194016030f902c000149040e00000742d030300024031000c80014000b4100701e04078030230b4003903500f05a02000b400c0e0761180260385d40d0000e600d40a5aa10701210003070a840380c0d00c2403116054256042002d0b5840d400d81d01c039822200301008000f8000400004449200d0381003082078054403040d10200102e03410030000494007207007442818401c0e03030000002002c5450760781060000b03002c103404036a00c45c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 31909537 1250 31908287 31908299
    0x31d120313030501060909030210090212060403080703050703090807140102091306080d05210702070b0309030307170108150a090f030518010516020d02030c0a080708070801020a02030901050c0106080601 89
    0xa040780c44151059030030301e01c010844020600c5564002030b495001400c1260042c62244090402d60400303070381c4a04c103880c22a404200c14011103104d03520903502c9101514104c0c00c040d0481d04040d105d0303001c240c940001c0b240082e818600b154089034203c52441151039001640c5406441011642da07080b6094103591281411907410030b03001d0b203003014240c0b103407002c1c5902c089400d0301800f404080d1a801201d1480c10f040202c0c0f004640001c03071841a25903258585400e5080355109039128031203503000100308103030030354000c07a420740c85000d9841c4a94036514140303c4039034414845108800803600c0c0b0021690f10720b4164441c9031540d9120560b40e10410039420f000d40203400008060450003d0008015900e600c01d4045a0360f000e1400060380341c520b856001c0c02800b1400d04412a010710500c0e05078003c079171f076014a51006095000040c2101420a440c250516840c2c0c0d0081d85a80e005001c000d0b6943c0d00070069880f034100c00c1c0b9086440d50f0380c244815000d0209581304070b0f21402a00b001040c6 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 31910787 1250 31909537 31909567
    0xc040e0c040e0f0c1002070b0412151103070e040b030d0807110a0201090303030b13060b0c0f010219030b0a090f050709050d020d06020d150b0c0c03060103031d1203 72
    0x12614211420041c1c1a5000e408903220552943c80210541001c240c0103558070b460075403d40300e50320030320480c0d4a45440306030f40d45c45a40031750040b54003126001d40040c10042061b5121404540c88079003804000300f06c0352505014000130f80240c0074480c2e6420342c0400380d00c843d40107c081d040010104d40b00c40b00e000001600100741a01c01d940000c0e400910708414484c00503020603002da040c1d5441711414a0758030110000c2845c022816400464a403600e400c0109a0040c8406404401c040ca030f900e400d01120303289060740c0040710729281c0e4014800070b82c004280700e0703200c2d82c80001da08010940c1c00c0c0c407a0000d814200f09410a01d9040e2030011020001e03442640030380e10600c5242c64110b6590b8544c400c02442c0c6440402c0258819101c141000006640b40c01800950189280202d81810604041542800290841049e441010035491041201001040c2905e00c059002e0015075055440042c52520412428040d0701c403841d00d0040742e500d0754280350326600503c10540e503c81e88040080d541d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 31912037 1250 31910787 31910803
    0xf0a020706050c0d180506010506030a0f1b021006061403040204060806070e0301150510030f0e0a0312050a05090307060c05070606030605150a08210708041203080109021207030e0c040e 81
    0x4980f52045c8005402c840b0900c003c0072640080081480e40e103440c040000d56400100043c1c1c1d190780b61400b211890226010308401c00143d107040058070302c0021002032400c01c40320080e813a06810b1a00400c080c542112101c1c0c80c400700104000e0342d994580c0045000ba000541c800c0000d44256020040010341c4007510814102084000f40290344401a02003e8040303213014181d404160446a4000705001c1e91107164001c85415021900301c5c000c00415040260b240c41c2500030920003009801010b803c1c0c86129030010b0008410809810009001c0707a1b0380c06240170003048152745801c03170042d07140280196903440e81c0c851070a100060302c074540400a00800c1d600151103088074042e91758189020102d401c160388603500142403584003814502c000c40f505554801038030750100a20b00100d10300c3c5004002424a001000040030018540100b207034105a03c85c5e01d0061051204a81059112001c260080c4039840d01240100001c1c0310641007038040440da9034024a41403c1000c19140455890 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 31913287 1250 31912037 31912057
    0xb03010b101805180c0703200a0309050301060b0702100e04050a020912060c0a031a04020307110601120b0c03180105070323010312080709030c090504020f0d0302060f0a020706050c 79
    0x281c89664400c2403055210590310008548400760001400e817560fa20040c100c01780c02407818140940416549101d907030300c42e0354540441c2d00100a51400d140d0028034500041205800070016249042e124540b5406155002449000c0528030200c101d44180c00899403150010001c01903806c000001500951105110314000d46c95100c00030514840460401c2c819401241310070314040d9691811002404240128807411164104129070340e1a103201a504c42c00054580101c81c81c2c840c03a02500d40841640400840307000003c00390002801108840d41201c0c0030480151241c03580264a514000325005500c0558038100405c0341c0242e01d5008801400211307420211070303c144001c40041e004003400081c0503103201c0400c1c8480a0320980790756501c544503107003200c10b00d0b442e80d4684808600c9070740113082498480d018041507182207004803a0001040b5606c0c1200e4502c0d6071302030741783c03100100402c28280c070060011300c1e00503441d01100c1c1d510364800000c104514003400d0341172807034112212070 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 31914537 1250 31913287 31913327
    0x40b0c0102071a0403080f0a0e01020c010203040201090b070f110a0306021303020a0611070b0d09020a03060506032a010804020406090204060914030d0c0f0203010209041a04051014040b03010b10 85
    0x4014900f83d42040307020307581554950b4081d5448a24a1006590140c0110440d41c0ea4084006080d6402c0c80500700e0401001c0c00542c2d02c0c14a4000100300340f4907030300803c448060030484840026045840c0c0140107074407451410f10710303554a0004288160980c80600751034000549400322076001d01c58007040d2442110200c001c031b9101d071011503aa0300a40d11181071988035160034080d84110001034401c010f03080360049998007840c0c0c0031401c071803041e52048030407945503001c6c02190b180902c0941d100e880c500f8101006687d56049c801d000e0803083c0c0e0964144102e02000c00d0a5440740e80051006d0881c2503015907071603540b00c2d00104400001d1144001c002800d003031601092601141544041040d50350300c0c00200551780350a402030b024007004980c159400c02001040c0d031078034069122101a5501c402041c03d51010900003070341c20082a00700000c040381807e10501400341d881c1080c1103c29100010303076080c418007084c0180051292a644500010300d98036089034802c00030070808400c1200 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 31915787 1250 31914537 31914563
    0xa151b030605010c02010305090c210607051213050703061e0e030906030c0a120603080d0e060f0c0f130f0303090603020702010c060515040f0c260a0c05040b0c010207 73
    0x4504640150240c280068008555403000d50f120f5084160056000428ac4025039101e01c005104441070341c1e805d0941a0306036682c9214020103201c0254814036608080d49000d58041c0b50f18400c10005003040d08600c4540504010700108000c60005142d1081e000c200004415080301d0100c0002006601c40b24149801d848151001106682d07082d00c0140055085440b648040541c03038001c4020f010400940c828808022401401900010340c0100407203952400340040d101c060740d079261801491540081c041c445040d445508450f40300300d13811051502c17000004901400751142c1301c070b041c03140103c440300807541e0304280311100102c074030944510006984ea410140c080c0d01076180041d010030f100d42c100b00d010031287e8000c1540050320703c0c1d0195500440340005003c40348030514115600f036a038a5240355a54104451103040000883d00d01c8146941d0031507404c0200000b4032050790030b82c8440711007c400d401034007074a018000710390050785c40d00ca40905c014000d4012a0060350b1138500800 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 31917037 1250 31915787 31915841
    0xc0a050303040f031719120506040b0f060307021e07050f03070807050907050702030d082202030709020f040f17011505030d030c020f070303030204030b01150f0c050a15 74
    0x8211002c40303e6076042401c50364a540c45020f90300507050041d80344008100020701c04038070000c84003465142d032a2a080340140ca862002c50450701c00801c0c0c0f50250b450311500c4007040d41c482d40c0030079600c0d40441c4c21990f282e603081c004905011a90220303183c072901440021040342008600c0340b040c1c0d20f0544030a400f800c11501010f170b0b00e214a2045d03090a8004843c24011800c000d040340e07a20034420b0500d81d01d400c6003580403d1904001110060003e00d80c0d200b800340802d4a07682245042c1d182e90199000740c0b400b034000a4807925503216107080d407503000400702c14a1040400b95402441200c40b402070312a503c030b00703001100408080301e94047d483c2400c0703d110f59441034000000e90780e018008000c0820601010b400078842680700d20158412101c0041d0b550f80c00f00700e82c101943c46950056110b918602c0d0148644006030002c0356214030101441c000254081d82c1c00078101c0785071601e04141c41203070415a00b011007070007000c0c2c030340700d03014000300c410901c030343c22005c81000e40c2c040b00f51a00d90011 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 31918287 1250 31917037 31917043
    0x140907020a02010804110d1514070306050609011206080604080307080601021c080711060a020c0705030309060a0c080708070f1401050408040512030d1503030f0206010605070f0302011803020c0a0503 87
    0x2800701c0d0204d000b180c04190b00701d0300400001030150900f404000035440e8000a00c4600304413150194942c141070070008001c2803202d400510071700f01404403d00341800204107000b1b5032002f6040054202160080c3c0c0c000f0340082c0d00404081c400c2d150641420304040001b40e2088810702c0c040740c03450020440c030354400510228207400810503041c0d46007181104072000203002d0300040c10001c41001160340f0a01c144140d60040501e00001a41c0301c81400c440e0382048919480140b29030400d001c0b800458a61108a910121281c509642ca0000d10f28110006005904003d41007007000314049041200c080f803450015400b5100c0100301029a814017400c2c2c1c3c20481d0010080003091008000c2e900340034a08140782e401d11740c00c0c2c03410a03500d410040300712000c2e1495007511202c2c81c0420428980c00428604c494666031003d00112740c14018040e02c144551301c0c1c010710582c100340004007407503c00e501c0000001241503d280030403001d404c0c0295210b0024490382c1c803546c14004006110b107000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 31919537 1250 31918287 31918303
    0x13050307140a0504020a0512180c0103060b03010e040507090c020709050a0c0c02130608011407090b0f03011211030a110411071106070c0b03070c1203020906180f04020414090702 78
    0x100b030410350034142000c0c000a5001840c40c94180a000c0c41040d1007014000c0c5501d1007803183c0030005103140300b40c0e842180340804502986061504c0c00301e0a205640b00d03407084a054501d00740d03080c0c0c03da40700c82c64000d01d450031b540d001c814810b01e00000c0070039a03603010418400b1035400c41c0c020702140d21109070308404c841e40012800b012880440882005091090401d0f0070380e543e2034000260142e8840e0b0041c251b40d4002c402041030208801002522500b00f00c03040040d050446a482c20b0040d0071259500c80e01c818000c0710011502d40a201c1d04126a900740c0c1d0000500140982d000380032503281003450001076258131032080d401c0c0810042e004000d0800d44031065000107411040340c0303c0106010320b40d0300180042d1034140c064500400c039210000001c40c000d1520303a03101c5240c06c050741030110080b00b4030700d06141054010041e0107031950f01c08090352700d1440540310341b07030400c0c200c88005150300b021740d14580c3c0c02c1400400d000901d0913980c00c0e103410324001030310f044540d6603510200302d85664131 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 31920787 1250 31919537 31919539
    0x50901090606120b010504050402040f030b1e011701111206030c090c09060c0a0c08060f100605070201210e0f0c060304020105030f0415050a1a01020d02060c0a141305030714 76
    0x640064409400f860300302504003807060400d51729080e20b0700081030580c0d00c030340c01100812038070540802c2004204007416038400c500f144192040d9400e440d681d2090700040c4221200d11200c030700f071141d0b554820740c0864070291140c0041985da02401c200090000320440e04982f081c004e64501050703504290100b20b1140c84546040c519005504040008940000354440ca2034854800c070600020007040c1c0c160041c1000d400100214a401d540c0300804490040a101d02201355a80c100402c64104c0d056805080e4242440b121141040c1c904400c406103800c0769102c0c071401c1c941e07140c9a00b400815000510407140c415103003000035030418040c1c544800e8500900184c41000000c800517640340302030790042d00c91140b60101c0c02c00101c20105841d03054079443d04542eaa951180400720b030410020401040030f001510703c209454501a4540e4001414116003600009805045070b110b59200f01145040d2038629458144e03111003d0a28a000d003e418080d2160001c0411000c0800c00700848441c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 31922037 1250 31920787 31920797
    0x30905030f0705030c0a081b01060f06050708070203011b02070f0f03140312070306090b010219021e0603090307030306080303010b0a050a05040302090f071407020310090807081201050901090606 85
    0xc01c500408103036844440140c1d00fa0205000200500c40c0078402a1141390140319402d847e042e85803030100040b212480c81605581c9024400c004601d25002c130f00b0100c550318205103882d504181013100003442040402035255181c800141d20501e004200c40e42240c1d0307143e00312420141c48a9019003d034045010340303040805a07510810001c0d4003060102d4400c084101a03e060107402803c01c454694182d4071000420b46500c02402114500e109070034000344244010050f80100c49001f07035003404000e401900030501d078680e856001d00c08802e00310800350040d225590f04d241120050780c8a801a080440010303007056000102d01200006a0381600c40113482c1c00d1400043d500c060710030341c1c000e1703422200b4040103000c0000580c1c2c0d55681d1302d219409a080d10416481c000303030b00a00e80142d5401d8440e14080600000780561000a040d04008400560008c0c20845500f400c180c1070203000802007050300c0001e2035013088490b0f28086d9040356419245c4403800c0c0d0b2550200030a4500314000c0da80058 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 31923287 1250 31922037 31922047
    0x1030605060d0209010b0307020304150801080c040506010e010c0203010605060706020d0b01081902070302070512010c080a06230301110703020a030905242215090b090901060809010b030a0b01030b060103090503 92
    0xf0030506d00940c1c0001c0d07540101c0f403625990355216200c1c210f6540d400780215052800401000c1d90500455a02d128202e80801591601c040040e00c035007554403000b81001030a998000844d24258401c00245c10024122501e544c075600d04040a90b01801d00d418941303040450303010780c5500802102d401840045644100038410180c040004d400c031a0060341141328a26001600752111810b180002d403580c000030408019142d00580020400f52030010194030304070f0108242c031030b640010704a160350b0070740c0541440e64490009002d040c08081400d000d00340024401d040507000070300f00c01507501c2a01c4a0400741da5030010000885600c2d0072a19500c0340800c0c0d0390510a040c9401030101c00c05400420215140f128580c40e200a0281c000307020042c803000400304215001080c240c0207040e0700200c503150001400224048980c180b00e41340c10b020000303012a070342d80402c1d0801122080c000d8200da00d64501401d1214080e036081c0b1060300c98003403c1d40400d4031541b0034001c3e00710241e08103004500d85 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 31924537 1250 31923287 31923299
    0x70302090c0403020a24020d0509010e0609061206090708040510240303030203010801061e050103020913020c030702130c0206012c09060105040b0a03031209080409020304030801030605060d020901 86
    0xd03580050611048150070080800140d450600170000b60070030b075054040c250314140740c1000c410b00b80700c1c551003550701000c41003000c9548081160343c2d68200b860145098810240070078424001d0a0723070303681c0c0303c0c502080048040a6403414640b0420045801c40883d0321101015540100180c0e009000ba4100820031505071955803c9000b002c00c0c0f00c803401410440140765003441319529001140000d4001004218aa809021708000b620821521203040d1440310401c800c1030305144180d606064004c102e0b07001d156a43c0c0040800892410f00541d611a514000140c0300d5004080c120300ca507403280c4040802c1c104500c00c1194081079900184005e0342440c0e20401c01100002e0b402c0100320003245070a814000c1d101c42140209041c800800855041c4010442950b240c16001c44c0180040c12041020a51204c02165002c4420034001100002410410540e01c180d8004140c1302c4d0001091108240c3e100e8011412240141002c0240ba103854013041070303002c0d40c100043d5114004c44018000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 31925787 1250 31924537 31924549
    0xa0303050405190503010e151e040204051803040801020d1808090f040b040c020109060509030702100f050f16020a140a0b090d02190602160e07080601141804110705070302 75
    0x10f1003541116004042d40c3c2c6000007030075108004400182034001803492140d8500c00061030360005070b41641c41e900800c5000143c501d00900800180c4255103a4011818202640804051900d429001d9a41c0d403521410202e002c1d5220030b040241462820b031140c01196a88c80e121030a01d9400a22180b4040d5894100f004081840d4201c681c040d681d0500100d03180d44611130140d041c0440e40020500034454240207084880003810070104e90003c11212005a840301c0c110b044249450a09607064001c400040700c1c240602c850021400400040d02005032000003d525500d5100311030023000030340c0310004601109240c0d0809034100c1880d400c24814401d408000e422003883c082c03d2202c0c181096000500700e0942c540386c2c1c0c00007003207050342400030030b80c18004030354007481c0365031144aa0b52070820501d108110007041c0c001003180020200d18a6131080e4580880c801c00c1001c11506c1728100ca05a040c6444032402152007640340030010464040808185e0711044e40080203400d0a528580030301035 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 31927037 1250 31925787 31925809
    0x6060c1104060f09090c0807050105190908070b03091006050303270d0c050a0902030402060304030f270501110109080f0a090b0708030f07050903061b07050105091b0a0303050405 78
    0x94070070b40700c24001c2450a2441d14460013000f442d000858402814140051141202d400c14092a0004101840700380d800c10200c4946030910390510300c032000468012990510700b03030460070281c0102e0500160124602c4007460140c0742210540381c3c625521203d090854106206054041d00f00780300c503140818410380c082c20301c00d0011144410b6590418005107082401c05002c0790503c14030300d000e0001e07081848c850800340442500451840c1410740000f00c0900009000500304800c4810380c02600e44a03802c00ea4044980c501b00c1d000d40040d00e10701801956580c001c0a0004034840d41001c02c6a105000b4840001d401c400345a250201024100c106580300d4642c00040c44142040014010034960040135964003c90025840c0c0c24034001c505402e07032018000c1020010184038100403542c0105449800240290b180036500268400404588c00340c0d14015019510f400100003c6410201d80300c0c007180e0310211055a410300b810104115080140000f800048003444140180e051200c1810303 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 31928287 1250 31927037 31927039
    0x140711250509040f1101020a08040506090a0e040b01150203090d060c020c0a082401051f0201110a030e0c040203011503051902073e091003050a050303160306060c11 72
    0x8044545030408110800010f940445890a411441406214480c0c00d1100a00000d2018040c07808268903a0002800f40740140c80c440d02d0002445503891356040c008000a100300400d044151030981400c7c45c01000920803035544000d030705982002c4030701c00f1040b0b8504150040010018450640b60803004041c0c81c05d4290a600c10784c80e106070140d031481d25420003891f002000709251508195043c1c2058210200009280340e0403006125581d210003589a16000056011a0b0042c2840b4220302411545541c44003540002844150141d0300d41c10200310340355008200c40c0301d0b14481091200704d03c404d12403181246401d01040018034030030307000303250401d00780c1c0c000e20084200ba0314054203e070b0100300120741c10702c00310302d400f101c001c040220200c100340401003c0400110075480038407080c0320950403c1c42a58400001028040e0f00980c203400b854202c01110519059403500c0c4d0b5403503105070b8002d5240d11161440b40e104c28481d00400096070003941c3c3e09003d0390880d541d0390741c80c2d09500802c2 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 31929537 1250 31928287 31928353
    0x60a0305030f0a02010b0603070e040507020a0605101d1e04030509060f09040f0e07090c1709032205010c0f05011b021006060203070b01060c02120303010306140711 72
    0x1040e020000703403960340e1030415195030742c940640020342102d540d001c1c20303402400144200244680c006202040c2181c003500d011843d6594548102d0410344036003002001d0078500001e102216500c9449a019284801e05041080c40c000000700c05411040710030114101d40100c0d00f280540c80c60340d81940092007800c180d400c02c0403074400102c003600000ea002009c42804a10b0f010300c0d15240c01401c141a19102c800c0085000114034142c030b034000d5002c2e1006c1c0356103404804019600c594580c40c00c411107181104a9810725580c034648035400b092019085070103600f001c0e540c0c072888515100c21600141c40318030904000c1da480d400c01041d0420265050b558034078040c0e6180c0c0079007400413060222540505070100901e4440001c441407500a84210742c0300703101c01400519118020f40c15290360707081c03000c0f0359001880000ca108000366810241404040000800c100e45a0003203011107448400044032961181821500410540321420301c552195008400b1a80040101c4080410940311 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 31930787 1250 31929537 31929539
    0x1b0b040f021f0e0f0609100518040e010c0f050f040e0601140a08010e0106031401050607060209030709020405090c21060f030109051510060c110d060c031e06061403060a 74
    0x403040102c040d152020302007422069006050700d018190590550401c0f580c00d03042030191008200015404141c90741030000000702083c0c1164500990002e45c040240300340000b11a0340c807101c1c0038001d00410000890304c4840602c0c04030f03001e1400c2c1c0b54090294580c040c1040e20703081354004280e03405840031341805250b0702c400c220b208000c030060241400503241c94005501d00400d02c010420168080e108051406d0b000313007072101c1741101035411206c04895498484200e4109940240b00d9020010362511456800240c8084c145d009403040300c008803410342040c0c3e40c0651161243c03240040c10f82401d9401e22078200d10940d1400f81641100c005010202003843c4a0f02007400c480c6852410f0700e0303640c002e1041441c00540c401103c5e900c60b0741000680d070401c1c03905a000e0070030b000c40f1500030f200c541d000c0711441464844a82c6038124582100c07003400741481c5040b02400400070b465050421180c140c3c0c480710600c0d0309001d41411540d0743d40d80c200000b410902d00700b0761500040c0c0125071009031500 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 31932037 1250 31930787 31930819
    0x9010b070f11150c0606120d08040c08030a0801080c040c050301030f060e03162a1517010e01030203011406030705060d1107030302300a0504031803030509011b0b040f02 74
    0x3c1103200c1c164103410700c80d90b0764180840c80c518260006185900c02d0030400540003107000c020800c110985180c2c1889070094586280244140d0300d6034009002510001c00e08198190344060781a040f50301030400c1e50f224440c04001d201c01d68114103011400304034100010800030b2100713040c1c003540c140110340001e450000c4180e280e04550020f910b1035000d0381e07106404002d002115000d20200008102c14412281c0311404400181207030f0310480c08110412607a003004180145418805c06007210480314007981c45000e1400b000d5400e0000760301a62030244605107280020200074000c200041c0144125403802040105941c4407822550440703403181800020990f5400191004910a860160b00d0b03007840702d02050000303009501c407524581c0080c040741ca1b1603c01103d07640c0000c403d01d404103c550302e80c02c081e15062488094400346084107180001416031010103086e0802c002d036140703030782d411441c21142252200c503403016040c0a9401d0105000810444c0303030241151001c0c16000117500812 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 31933287 1250 31932037 31932049
    0x303091e0f1b10030218100507050303070305040c090515041107080c0325030503070309020f090f04020909070e130f02100504030b010501050c0c0405060103060b0703090e0609010b070f11 82
    0x94400b00c2c0503000c1038200b42c5418004628090507501d0210f042c0000780b440d0011040c048020700380034410300707508024a140301d00101d03080c05400c0011a51f607400c003500018010101100d00f9903041d106181d01080040f040c2c09094061924000001000041c4201b04401040e0300c04030342d16051010000200060080c0c0c2c0039110440c1548061030311421400c511401008281208001c00340054905100207600001503e0700300725940341c00038041d0100e1001c64114900103d08a60041c4400e0030428a024550510751045100391140b6099840d001c4459a8881c03180c02209415698100000c03400214160404d036014016070181643d25450740100e90002d130144c00c14000103900080500a0041d01051940102000c0c42c00b40d180028031b4180c0c5844048410b4828412760701c0f44081001603201ea002308004c0c0409d911144c1d034421041c034010704107031602d124202c0c0400f07500c8000780541c0b4141511904a905c0e4100c05498007880da62402d81c4200150001c8824083c81880f05500e903c1d10 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 31934537 1250 31933287 31933303
    0x40b210303010906060c050d0c02060d0e010902130b030a021207030605010b0304031103270307030c080c03150c04150516030c0b060a0506090609060403050105070915020303091e0f 79
    0x802450340ca5050407415003d0390001d420240c1880350100640e80041c40003d10a502c01c2031600c2c114142e40003600c0050000e120b071440b4218600d0410f000065201d20650003088034510031255414647c084424801c240c400c1134081a074107800856441303015040c59030344000845504010f0300c0c50310703460b555545c0c00c031a401e070002d8215007801b10812003010740005885005d0482c0c41c00560400c40b080342d001d44c941c10f0280c250f00ba240782c07005683c40c0ca61001c00503c00556489801c1002403030f124002a40d880700b0302071400b440f03485804820b201c100b40240d0714034041c01c0c1c2d01041a103068145007580407000c2c00510540d080000c10800c0a528120301c1e010141c800e440790f52140310300101c6003009040075a003c0e081c030740b06c0d15021800700100c0c1d40e13035001c03240d40d4103003035400c82e464842040004010b03000b02d40c001b50455080c842003141c6194404004400d6950b07080c400035a1404040c4d04a0f40c03030204131080380455220201211184056043c01c148a00303d00e0304640c400c1601a401508000c44 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 31935787 1250 31934537 31934599
    0x2011103090c013b030a020d06150e01050901151e0c0308070e010804021201020c07030804050913051f0e030703030903031d0a0803060d0c0e010f0b03070c02040b 71
    0x101d2001c1e0102d075070740450000030315a113480e070758803c01c0c01ca40da00c2160403e60a0002601c240e4400800080342c0f01800110480703030700100360000c100f22600701070b03024100c803074620000c8040c00140400c10041240805060f03407000b61804c01c5507070824180f01c042d0020200103000f0301407900069500c00c130024002030501d859941d02c440ca0724046180151910313030043c10440920062aa0f4a0800d9138030040060b4003d4040300c80828009054001600a00c10f54004404901801402005205c001030040c0201c2e80240c40070201c0c1da031020f58042000b840900001c0040d0406c60b2406c12a5206101c000e0850310300000010b5405600d241d0700b0b28540c010f035811404a9201c805403002c1c150148102c0100c2e40120075884c10329800804602d80310079108600809800740400402d04035104c02c005015000d41c001ca0304414262100c240c031a00020034820130301c1201030070710b0215408002e41d0569014402645034111803640b2942044081e00a180d4155000a10004106e01d50816408a100c00ca00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 31937037 1250 31935787 31935793
    0x9140703080c011103090a0201180801020a030209030d0807080c0304020a0f06030902010f08011401050c0c060304051005090102091f020c03010f0902041401030201200106030203030f03071b0503030112030201110309 94
    0x103940c900e000d0a44036101050b074401501401000f02d01b490100381d5080f4140e09103031103407454040d0700c03000e803129816801001c09927101141903220340350541c0c0100006242102190710002c8007403011030305000110780c000006003440010038082c00100c0041c5800501c000d11401c2c0c40760b00c40c60340041040b80c030f61001d8006901d8421003019940c109401428035111443c1084040d070601005003503500700003244c9410408001010503400b5824025518560802442250f503030038242048c5941d8100f444100c45514039100102d00d40180500c21540c4011000d80340f0717500f455003040c418024101c4002c03a44154002d00c1c1c00d8125550f000c2c0314002212858200001d087c03846401071000302c91544440410000040c401403015070780100b810305200c0c000d200c01d12451030300400c025000d0042e513032000750140f0002c00e04504500034203014601c154429aa40c07a58080200020840100c20720b002500d26001040103102c400400310707503103000601038000400d141c50580d000409540c4100d4000400ea0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 31938287 1250 31937037 31937047
    0x110d02030f1506030c0703091a04050901060f090506070f060c08150d0b060607020d08030103200f010e0906191409070f0503010905041e050c0a050a0609090914070308 73
    0x7000721100c54200300c485080080300c1e5400804070303101e480b02902d050180440401c0210403d071152001c07030058860f540c3e90303c491f0783c00941d4130b00d216001070040e2880b034514180007207512842032a0750192510180d854001c81c610384024400030b0341c415042650080c54806001d0041901402000c0850106943d071109070b151140500c04580d4102d40700e50710464003a00f02c1004034040700c0b981c80d00f01408807441544d0b0101440081c0c015840c0c020020204d43c4003000001c140690000304011070101405068520b200100070020129003402d28180410010303012500c003810820841c5900502c0a030920101408080e00e10320110b03441d5002c8001c28605003038142c1241001c400d02501715030641094002c5070520b07103020307001b070005001d00031503a40d40f14005401e0050701108518400c020015003212004942002038030342c032191203001d004030001000040e040c100900e4083c101c40d170f6590f505c4581d904200c05003024003c60300d0300b555580601d000c5000c609400f403202000031845031402654070 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 31939537 1250 31938287 31938301
    0x8030a08090106090e03180307030b0f040203070501140316020709060915090b0a0902250f02041b050a0503060303040801110a0206060405130201050702150a09030201020c0d0c0605030a110d0203 85
    0x925055040341c07a1882c00c05c541030300818400415180e0003a07e0008500380c001c1d141000c241390240d5640003402280ca08414080507031640e603070070b074002d40c026002d8034500e544900040d12490301040d44064000801c00020744032250a500d00300703210305140706441ca9643d1b00d0310305070180d038465002140103d58425003040401407410108000301070b0560207000d240080000a03013a480036100e0f240f46190001510300740ca1100000106455210003481003100380907040ca4007012460600880c0a00d10746000000a640f0180c0314810f402d0807996164030b80000324800315050b8001030101ca40600c4240000f0509010030b000d1a4014200e10301c030152031b1492010020300e80b078800b5240700c1c0a0f41c60f09041c071003074590f0240f0606040da020300f0565554012807012403030818a12145e442001004a5403400140d0b10050542c11603000343c2c2241d1108800c10104020000b0502008010b010144400c12440c0d0103900951790116400a000800c070203e43c100d041b01e6403086042424095000003003001e2 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 31940787 1250 31939537 31939541
    0x1f02101a010e01051305060f031602070e0c090312040305030c061302010c120c0c14010f030e0c0405070507050102040305030301061b050a0221070b0a030b0102030c0601030305090a08030a080901 85
    0x480006480219001200d40001a100c1000d001c0142d040010000f0600b04d101e410b01240001060080c01f01681c60100318880031440c4c0060751424002081030800008440c800280030013640c50076202c5e007c035038580c060b40c610250f000c501d44d2509401404100300c050210407010700011402a805503a80d085011801420500b000304240d5503040180390781c20150b40c1c040c103900c5886601c2500600300d1428030340c0075582415441d000403c41048140045881c404040407140d9502c8281c80341002002c812005500f83d0316180c4100c1c059500c80a1100e40034909134024640040b02414400c1c6004060b855040c20799119400981c0c81d0342c40000100039003a80724041c00c405106080000801c100e0a6940d191240c940c030802a07c01c900e00340000c0c0f50f9144180c205220140c00c08201c1e0000c030395400b410000e607040180e0041c082860008495515400032007150500141c001c05814141c1c21030b5416611130304901001d0350072000814012664482c204014100400c031500c3c0d00103640340018240307003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 31942037 1250 31940787 31940801
    0x609030e0102070612020a05090904050a020a090b060904051003050d050403120f083402010603060c110a0b0901090204090f02090603031e0f07050d05030709120f0206091f0210 77
    0x3046602c0940200031085c0d108109041a1020310000360b5030701c009a004907841d0007800740e0346500c000780805200812100017200300c5001d100307940d8268066696010801100d5118100c0344d00000200194821132400d684480d92201c1070702c614407040f5449072070740392074001d500311440e0210310002014010300a00c81c403000b403c1c080510705101915aa41c000610522000d808034038014004c5030051220300c60880d00242d020058400a5640d116051000740648200d100030b07034000380b50078480d10b41c0c00d1081d08444103030302498008000c05a880c2d42c2d44d14025200038284c0d0b905550701d01c1c003040140d58034002d038104180100c0300d410205553340100300000b08054503070f0303109a10421540e50144c3c1030010b080742110000499a440b0020020030040e00d00c100c640060250083c641d14001c0741c3e8100d00914000c1c9005e40c1e031007041a465502c0c02072900c215501c00b90203111050302500043c500003004080c2c0c14405440c40d801242c0444c1e001c03c80001d90780c0b0310b10250300040604914604140f103000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 31943287 1250 31942037 31942039
    0x801060e040b090c0d060b03010921030b0307080c0108100518070e04050f0a090f050307060e0609010b010903080d14090f010b03030315010507080708040f09060902030910020c0c0604030609030e 85
    0x101c4031395454000b810034903071160000c080e140c80d01402500365500794041504990084d1503c103151551100a120200110388808042403401c6803512941c200090701741c040c0d80c2c104004080035032005c0b0066424540003418030309140c400c0e48010944e80ca5410a00c1c0c504903009942d0705a9050051002d41001040300c02140114602400c10080401c101c840c00e41001d92078000042c81205410000420503035480040c041d07110010704601046420361240e440341501d40d0070307074031b0a8071002c0095090307a80018007a030000313140799000c1c004604a80010b00b020207040f40001006121820a10040c0342d04650082d400c3d0441094988030f10028044c82c0c2007484100d019500e103143c100108101201c0c000398071070400101140003c20880348404441c0200c1c0c00c4181c2a445070745d21404060b48880900609100d141000000524031240e030007500c0c00340700d655002c2d000f80c00300007184a00035003104082a425100b8254400c2e840c0c0c076204018400f0710300448002c62000b00c241005002c21504445203 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 31944537 1250 31943287 31943293
    0x10606092306090307080a0503070c060c0c090c0c05010c080603060a060b03012615040c0f03150c12110711090c0f0307170702031e0405060904020904060801060e040b09 74
    0x508440c1410514940700c211044903169203074207049011030301d03100c1c4680202c0a6846070040c030f00103001000001d0b0181c0ca21843d07030490b0040e1210000c480c03041107404010a042c0c10180d041c0200c4000d074202203224819860080c813201c0d100e8803201d003990b80240320315000c104542d050003030500703003802100d600c0340c400f0100b4031005242c140310040340d200c1481030141c84032602581061401d00c12102001203070040c01218a4404c5504404201c44400e680c22101c101e1000d40010754030010840e0401181d07001401c103c1d102100204900141006141381000c000480400d0014004c05200304444030264002240c0c44e03200c14074100c00504620340106110b00021000c00100021140403148805001c0c00450303240e03111601c094590300410103086812420003810028415400000740c0700031054242c00e00e6000f01c9110205041d4403c40c0242c68100c0c5041055203100d040a40003406603000c05000003a0095035120500d08440d411b0700818021030302c14060200780000722442d071760080c00c00c5001e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 31945787 1250 31944537 31944569
    0x12060604150503090c0402040816060f08061c0b150103050c090d02010c08160305030f0a0903092105060a0b10030e0303070c02130e010b010207081b01050c070f0801060609 75
    0x301400d440c48810704030040100000c00101005401c2c001744083d040003810135506d0755140d0f4034a0303884404540180509034201c210002d0744511440d050306801e000c07071305d8216035a02c0d20024802c4a100040308407488030503803991500001c1400801a2240c10b10750210f201b100c079400001400d854000e0072b40404c041040c07000820b541d840c054605045035090809031603040c8246420030080c0580700380484619800d11104042c140c001e40258403d0700d0031000310500c1d80c2da00d403914048846040c0050005181703404141712401c0c450044c03040b0002d403003130001504025652a94500740d402c0700d42030421511810580660700b07040c0701801502c0e05504060200103003900089949000080210301042000d83c1d2000640d11609442040401d1210301402a180760444042c003034501110041d0062285010000d0554000701e031005000ea13116422600d204a441c00440d0650404015410a801181c000003015410740007400020800000041205481c01d14040c04055440e840403154042d4884 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 31947037 1250 31945787 31945799
    0x601051804150b19090501030b060402070b0103060e030d18050f0607022109040903030501060905030307020d0609020103180c0302010201140105100c390506070203030a0c0f1712060604 81
    0x2c0b862011800c0264002406280c860004840480c000340c508000c14200c100400c003200250002030603280660302aa034075442c1c00e0306110803031083d13030005000c4030030307000c014000a500ea801070400801c2c1181164100710540b03800e607003100c07a00c0c1e940001116258000204129003448080000781a000c0a0140c51800c200082d440d07407010492600000010804130034581d2031035080d1695107601030000c010040303031407401034000c080030f004e64404112441030014840c50b0010407140401e038042d040c40030360f81050340c5440240041410890606440e00c0c210742c104140541040600e5008881103180c4501e10f0001a0031a8201d00c005e04440c01a01c7c0103201c145c503024082001013101d0714014000d904d903818144408180903040510300050f1007802c606041803268201d414405452400c0000f55880c01040701c14415042c009416070000e2004c50510350140d50800c0203240500c42004030101c00d6914a84400c031082c1e41c0207441c803004650580007442c6400903e070300c07090a54415207410b060607 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 31948287 1250 31947037 31947053
    0x3030c0a060e070f031112011a01080406090501050906012309130f1704091401120803040606030506070309150519020d0f020301030809120303070e06030a021b0601051804 75
    0x850041c0007140c4a4010442e00300b4100102070041c21407981e03510505840e8504070841c1115064824400c0d00f40c1c0900c00e0440c401840342302c2d0200314444141030051806c500542d43c1c00c000400907207040c0d90b510400004100300b0f0041c54410135140020705090340c14000e82c80814684500d034003031210180c03c1401d0003500c0c2e0040c200c0c2c1081c442d400107400f5104074a00030350303441c01e0748000400292510240200851281001d4420382e00c00c40001d1101c907004035441c0503844002d11076403440004e0454540042240e600045402c5405003c0101d1116181d86440c0c0c54000152404070000ea62095024140141d48407440d00c02580c941061016040919030540c0e000c0c0d81403483e1001c164009076030300c8210040d6100c031902002060f025900d80d039490801d451150003910b06d40c2d01950000e11a0000c0103000300c100da00c920307601c1c0c5030303000c07060f01050900015400003420020302d19420081005a030030701480003074094100200030074a070342c103240c00d05c441000319103100700f9000c1080c003d120001d0620 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 31949537 1250 31948287 31948303
    0x30408040e0604020d0c09170102030c12040302031303051005060904030f030c020c03061501020114010e0703020f0408010212090c030106120b070e0901060305010305010b010801080a0f1b0b070501050603030c 91
    0x40c9841000e40d180c0b00c001600920840e10001407462038070703081d00e034015001101c2404a4403d80b000c81030091414036144e003030744403c41c0c40201c80c8004004074015031810803030441c1c009000b403040380d00303041d8004111000290f072904280c4041d40209103101490a490042766880481544e029046003000d55015080c00a2402060103240e01e5101840500d8403c01048202e403000404442e21420101c00c2d1021016405c45983e0055080206040400c001c0e0b21079541201c074400d00f08082507079141e030101c00942044119224040040200140000090014007841e40421070045081c3c03e1804d5024540360641e141e00307000c0d0341805c00130812aa115011030040030340007400d003641503451150440304500c5040c02c15512804140010030501c1c0c0c5503200d00d041e42d10880080245403441e1005503480d00092041d08081c0e03100320075440009240a19a03040d031803041c8650400d0701c070503603140144400b1903080402d0b00d13480030400c20244002409a10740144080c2c015600d0301e1000300e965601e039500 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 31950787 1250 31949537 31949549
    0x11090108070309150c0503010e060904050d050702041401080606120f0709090206090406080a060c090b09011112030903180a030812070509101e020607120b010207030c030501050105010906030203040804 88
    0x911090b403401d00c0305607090204d000c442c0c2542045840000b91016007550402c0c040c441d1030300d401038001101c604000000754001c5411000030304054402c400115035035409030328100c0e0880e4480b5a440c1d504007401e20f640303000c0c000c1803010f01100d18080060120002c0031103021510b580c442e2042460b001e00120b0014240e40781103030003094030205400030507905e21a40000640092802c440011020380111300000b40c07a100d01024000484038140031900c205a80c060802e203c1e400700145001da41c01184140c451450ba07400b60342240719441450142e0790011903038145260800609206e04040080680104100880b42440d9050441c1c55030311007130150b40c00d03000e2200c00440110708024040d20603142c840c400101340c1041e11300c0380030004000001549a103540310001c0600ca260460000c2079951294110750344416035164061500006400c0600e03400e419809014004404111500c8c80180070754000c0d400403c941d4501400108004501e62001d010184144140000030b00b940d000c0368201c0d20 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 31952037 1250 31950787 31950791
    0xb1612020702060405060706060e01080a0201050405040b03010e0105090d121103040609050f16090501060302070203061f080f03040e0f071706010e0d051612020a0e071e050409110901080703 83
    0x81c00e102040d1a846290041548540003003a600100445a00310304162003c117903103100640d07a0340c80c4107991901600b4000707020400512092001c2e00f031035441607188003001400880c00030210040e135401c603401500d10701410380005124011498000c0c240000c05202c00708100200c02420450107001e000103080144550b4940741740b0030500c4401c00c0203101035003100060303d80001c400c1d003c880d01d401c00c078030607842c000e41032a000041950280c42510100703900540900400e9440071b51340019143c0030045000c0c0e0340076000b40070454201c100b040138840c056050003180d03030754106003001003042c20040c801c859040f031000c1041751107940f040c0072070100710480c24447c3c030b151583c0c0700503101d0700b80c0c800c40c00c1d81082002c0c080344240000003c2d0200080c036444621030206498560040c0c07003170742c07541010703401246030642086244021951154030510a1030300c609072943c005040b8a03171b00e82c001c13146000641c020405010340040d40c49400e221103203816080c1c3c60041d010300040c0c900e810050216040c0750b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 31953287 1250 31952037 31952047
    0x10902101b0b0601050c10050a060e06030a0201121506050714011112040501020d05090d08060306011a1602060a0f02010b030d081503160602011a0402070c0e1e01030309030b161202 79
    0x64068420f1b03484601c0400300340c5020f24252200200100030490300784610a0030030800050784130a40549a00426018014000c031041c0c0b90010b642c801303c6058003641480c2c0d43c0200130b42880c0c01d20b840c2005040b41c0c4c3d55841c2c0c7c5006174106002d4490030341801c2c1d84143d01d441007103610386810104503000c046420590b11038640d1b80e030910a0081c0518400070f4601418401040300541022880070001001603c0d45071031a107a607401c0c503686250134022500101403a1404250548100c409008000c903408140420176005a000c02c9082c0c00890031600481e1001c05010085c68080c018080d114030280e00911070385502d10030062080c1e201500d412000030303801e0010381440d10284512409082d070124840c021603501c190003030003130803203850f02119024903240b074070300518060007120801d070382001000d9a03007818500c46071000c15024058a034130b07d90a501e40a00f10502480042c0250700a859060282d451410078001c644001012800300d4002c0c14002c03111550012000360703065080b0305e0010303294 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 31954537 1250 31953287 31953289
    0x5180601050d062d1d0309041a03030a0503060a080a03080406020a020a1b060e010306050a1406040e0c07060506010807170c040902030a150b0f0d09020411070302010902101b0b06 78
    0x14404c600d0341c3c0c81285902c51200e0103000110060014081c400b0a00300401005201040384944800d1405442034104019103412880c29401081d48845901c551000d20070000c1c0c0002d14503070103a80008080342c4c010080184a143c100d50520003040c1440140070400440c0c0e600030706c44480200010100c070b42c08126803140030310030404281155445a21400070030390051041452150364401c0c00b0002e0030001240e50507502c6805550b0444c1c201400c511400b07402c2c44240045c000300031003060b0300a00140000030704074600000d510301a0341d00541c802d9503523116040407070644000415440c1407002c02011303c805070b82e0001020107410b10300315881034513481c0d60101d4142482181e00c000c3c841c500100c1409401070103544001e020049003c28a64202d984004c009250b004450300c07410700c40c4051100303880504c0070790049d18040d440100001101e41048a5440c81600004070950041c0e540e0654081142040113000b00314400070b041412611104414800b54086c007540003c0c85040d2100110b005 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 31955787 1250 31954537 31954541
    0xd0905011107050904240b030c0a08060a050406110714010612030c060f02160b09060105010c050709020306011e030209040b1e0d02030307050607170a1514030a0210020307020405180601050d06 84
    0x1b039400c0d03c01040e948140740e4004201410080003110700c40d029607040c54146140c0300ba2400300f07d40d500c0001d40500c0e965034074504000c01d4003c00665016031688015401c0c40325410007001c0c4039109001c1c1541036103c41c281942124195049800d180004001d001e0109801c00d401781d0496603c42c6020030100345c0d026440001c4c1c0030b0314021286501400711140f00308801503028600c290f860404176085680e9802c011590010000c03409232154120100031b00654101c2e80040d5803240c0d040c142240038131640bc00544515441c10350b1000000d81c046510306942c0f0702030040020603074003103800410503a10000c4035441c8815010a5510480d0840f0110086403418025520015000401c1d2240d61822540240c4010303064001405550140c3c80000c8100440b840b8608803011600307031000450741884142c16112088080f195414030620f62504016034030041c80324000301132580550344810540c4180001e964019084000500d1154807140c2880c00c0002c13041d0461f0b2044460000d00600380c204000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 31957037 1250 31955787 31955813
    0xc030e0304120605090c18070207050307060306030302060a200a0c0c0e060109120c0302010f02150421050c120307051909060e03011b050c01020c010e0d0905011107050904 75
    0x214502010a0010301040e044200c0008280550418403c540e1203080b00703a1202e01d5002550350000c001003050074014105102254841006c0c0110354415466100291500030a1752094002984644050081642c140015500700021460a01c01a100900c03815694000130300f030768810303008c0402d2664040d441099214042c50300b00a180b0340c0303951030f6210070702c0111045032414040b4200a50000e1a140e0305030a510203541c2010351050301501395070045a0311055010000d00314855010729209118468030085e0195104c0c043c03022040848105031002d1060320441081800001d0040510400010444160250b400b01e90740d41e4a43c1c4102050b10340c0d014110030f0b400400c0500400e03089058001000c0020345205072218560070042c0c134101400c0c1c80b4202180700a040042805c06006402407010340080c02034403001505255100703401900f1030b4507020703407699107511500049a0710b60700049102d02a000a2038606c0c150b1807051000e40d030341c000d50300ca0540a06508800501409904402c4103 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 31958287 1250 31957037 31957061
    0x409140a23060105130e040f05060f010317031504150603060611031e0c070605070302060105060f0711040e01020d14011706130501020d0e01090309090606200307050a08040f0801020405130c03 84
    0x785a0a02342410303035002c2c2c0806011150f41c810000810321520304402458100c03640a07101078482282e000e4000480c1e000a0b0040614000304103421145958500916030030f40c0340103c15249091814000078143c030180d501400a002907025070207200c807804000c80c0c090114500784030302e0b0152071800f1140c1c1841007102041c07182c019804040b80442e80700000f04042e0b802542100c08a91301c61040252507c10f145403d003a0100170400100003030a40130035846454001440005e00743c81d0105c00500b03981c0300325031541d1072aa0303a5018000c0d0b03000d4804051302500021700603070010200041c203d6583e100150030031100e130341903009140070000c0035012140312840c855802d0000c250351102d2a80a8100e0401c00c9010034610038002c038020a584c410401180e03202c0e0380e183c41482c00800c1c01007007406003051100c8280401c01243e0080360040000380c0c5003502c40c0d0710069403107180809021a0b64955004210141d0041104024030390765585030750100003101c3d40c0051013080100b0140c004124a403001 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 31959537 1250 31958287 31958309
    0x40b0a14010510051b120304050d0f050a0309150e0c01030e06060105030103020d050a0c090204050423070e04060b1303050d020604030906050a1205091f020309030703030e030409140a2306010513 85
    0x40e10000c0400007d180598807510440700d00201240d0191041c50348012400005181840304015040c482e402500080c4d00914014a103227900d112039409480003120203600e20741c00050000030650341845092160a03020014040508100d800204284410721001c5e118600a0109600f448400d02c1000b82c002da2055101d400282d80f4500903000c1c0d003092040b24401c0703240400002e080310030000080d40d6009840d82241c019a140072003654000c2c15980c54640055480c01d000c00c0e0350502d54000c0c000d0311203030149a2a590318518246160280c0c400e4000c0854005409000020380c029461100741c600a0604584a00809100311108000c034032808240d1400c5ca0f080c001c0103900401c00100c40b209800301203c1c6940b00004103c10b0344030944402181c0e1340200030380d001003481380e80410405101001135034a420b55030790354101650340e100001320080000c803081c003031075140380d07c26030555501c00c0b900d410103c00503043b81840e1401c002c20341410b0020000b905260f00c1404c86108020300300030810 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 31960787 1250 31959537 31959553
    0x6071205220501030b031903120b120106030506100e0106050306040b270a0207030905060c010b03030301150305060d030c06052509031712040f020d060203040b0a14010510051b 77
    0x541d8090002070b1103181d0100345041c0101d562801c01207104201c2c042c1c3c031a0281800c81031980c0c00c032204050740d4042c41442c0d42d10f1501c400703150345283d01c85244414040c0007044250840c10710606013500076010280710140c9000410040084007511030460720141070460b220b80e11600403801410003210440c0c0e0110351480c551503d00c1d00881e555051201c03444843d019555000d2141c2c040f88210790016010580c41c410820240c50203400616500310040000f00d0b008081e200400c1c550b4000fa00482030f58440d030342c0009222130307141c0f0955501010480340b401400d405038902514120100381d01408258407000020403168041500704480928000c0440026101c0100140008210b01089946015031900c08800d00c0403103051b5982c0811240702c850140e01ca83d178401144415000c8100c0c0c000820071030340800720360244095803103240120046078162814403510000c40d00d99200c1c0240d4182c10900610654440e203031700d08a1915941403031031b52000034008941142c400c038500003c481c410188 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 31962037 1250 31960787 31960837
    0xf080405031e0c1b010207051905040501031202010b0105120f0403030608070f0305100c02070605070c030602040f050102010b01030606050313060e030723060601050a0c06020c070f080c010c0206071205 88
    0x401881e680c4202030540c2c2c0108420b0a80070039803081d50060710b00584c841f04042c042071600032108503070000d550920a50740340d035400100c0c058032801d0b40103413454600c0c0d10005002a4080c002c0c02c0600d1800d1802a250401a00e041600d001000d00311402d001e114000003000c00d030007980941c002d071400500303d0709040e0751082880b85a0001e070004403228010542e14943c4091180600e0300c0c3e43c0c1c1c4e150007500c117082c10410222a160404501900c0d54480326400201080903880240003505401c1905007810b4101400a401d40ba4031f294414105441c0100030059250b2040950b500803c1d110070800c0440d10038107060020780380f0000010300a00000460800300001d00c11120314034903240c404c9200c0a601000d006490340d80407514075000c5901000219429442003d500496521840c001414988032041052524130b1035003204e41454400e1409120194040241d140e0141d801d28050b8444045540480d10038040e03880000c1500024040c00d2486a0262043d80d540038a028021415018521 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 31963287 1250 31962037 31962097
    0x702031e0306031002040302181909030e0a0509040302061503030915030417040605040e130609050606010908030a020703080a02010612060b090604090b13030e060c0f1902010f08040503 81
    0x16640b140710b881444041003808041e4000e035001c036034000300210191a00c46844404034000200504100305442011070840d02c060720682030300700d0007686c0e0031790039501c24414401001c1c00c40c2c006520410849003000002980050318940c000110000101c1040b010004240317035024006805a100307828442200e110045040614451800f51030b002d09400040403051441e84202d0046100164003080244a1202c207001c07801d4000c0f6082d58005e0a110039502c0c0e500840705581c2040b80e1642000040c0002c540e40040520081e04825014515041e00796401942c1c9100c0d038400284254008034103040c0040c005c5d4040b900a15120040c100c070010300f46881401800041112031040c60614041141c4d8181803040400303903613201141000b00d48402c00c1c00c040c0c403816140100c04001010f1015081c688940000e0325031640300c24000c12211400c41c0380c20b03041042d82012042d020f016035610402603031740100303c1c00d00350b010780c2440c14450b00c07142052401c5100784104031101101c1088840701c00c00f00ca07 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 31964537 1250 31963287 31963291
    0xc050309040e1e03120a0903020a170904110304020411030112020909010f0c0f0f0513030312060305030c0a030905270903160c0510211d010507020303010824010e0702031e03 76
    0x104c08200c0079a81340c1d003001081f64401d00014005a020045040024000d4490001e1029103c12064189241c40002805a4100100d600004d030804001d01046080c14050a4010410420700303508640c1000e5003214080c0340300101070f10500090010550307440080d0301694000c400c0107010b118a03868002c0242c40014900c040c040011440021105030324400d0090360181d43c200480812420714640f01281c1c3c80c0d21b007025a040c400e655960001c0040c074100000c0084466101c050315088038141000b80940c20345520003801825440084500541b035600d02443c00c0d00300702e56840c51501c415800034034501480c1803002d248a03901040c0800c1c0600c0d61640c0d8211841101d100c0d2980d6258402240e8640e1000c20420007260f107601040d4404420740c00800002084541c07101401c0c1000e2459800d480003a0303011009608004014040d4403000d1103030a49110700340505800c0584003001d04001c0200520070700c2020102007011441240c400e0013269011001403841c840340d10094050300c3c01030341c41 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 31965787 1250 31964537 31964557
    0x6070309170a080c180a030302010501050114090a0b160606140907020c1f0e0d0605040c05060304150207060b060a020607030501060201060305030d0509010209090a020304060506010c050309040e1e03 87
    0x1ca20040d8064281e40121190151959103c010340e845402010700b1681021450f003250030080000e4101c241c8400d03086900031800799001007090b51500c0005080011610741e2003815120401c11081117807515031201044803550403040399550b9034a0350804020b40b100c400104040e0500100043c001c1c5c3c643c5610f4142d00b01140d900602c0d03180c40310207aa031016400c200c03a810001484a1101408070b00e1030340100b4003003a052012040b40040c0028400120a0318100d841e2907991007401b0500248210300b101520050346c51341d04c0c50805441d1500310b103552201c011040761b00062014100300705500100c224900240c116622244c0e6020084d440c0d0708110340c3c51000a02d44030001500c42d20501a2008903508140510300e01038004461a000e0000140780c1c803165074082080c05220345442e51542d01c2070114000040c0c07281003034544101520000f410243c104038036000d00e513011800102c201d82107100103c0c1e00145c0480700c05800e40c140300800c8560181c0d0980b921480603100c102000134200301c00 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 31967037 1250 31965787 31965803
    0xe0a031101030c2d021c11070803040308040e0408040504060603020304050f12040306090503131203020609010207020a0b1c020f07030306120819050d33140609011106070309 76
    0xc0f26041100d44030801902e0840c448008182256544042400e00f604004544103940204002d080000c0c4c40c0e151036001c00000548114403003561400c2480540c0103000740c003016620306461500c0d10240c0c0c0c0110301440030021380000c003140412101d20100c80c020032002c1c0041c4036250350b4603c0507000303400c100ca0a545901908042d0041c4040104000342c1c0d1300c4005401d1350900341551a40b00c0180f180e210121282e11007040b022000007601015100140203504508a141c0414a0001e00b04000608500166030040c8489001a981c01e060f0400351071140120a031100d0110340341600501e014401140c440d4070000b101000094448000c00d4402d000f910188025583c1c1d11500e802c008100002030449202440315003201600040189203031025442c0c8141002e519800c081d04951003205452140c001644d5030740c1600c44060030071200400e04c50b0040d000c89160800c202120001903145130301c07c400003d074215091307000d05881828040c501d001c90b0030910700440003a00130695144240c0d0b18003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 31968287 1250 31967037 31967051
    0x30c031f1d06040c020714060c0f0d020f01020c0a02040b03100906020408010c02030f090d0c030503030a0c03060801021306030506030106030b0a0609051f0317040308070b07030c2d0e0a03110103 85
    0x81801d019034040328030241d00401802d850845101250064544948d078003020411101d0600310080207080c21500800c0d000d400684030720a406803801c8034200ca0311301943d0041c003030001070120208a411003250191404541384500c01c00081c2001d540d0050300314100e2034007811001703100c43c0341d025000b075a04083c0200901c3c000f510060341e89010304042462206d50402900726203043c075107400b5210389d100d4020b03010003d407242d440d641160422030320b500c2102d603103049151140d075040c0560710042c0391000c0214078111100f6060f041808103806500107151320f41c00031030080d4800358003031402940c100070045000d05101e01c40c1e101a001e41c1c0f20701c001312070801001ca20030075803007400741080b00c1e80c02c84490111848c3d40d44a8076031081d4040d005950780000d010010110f0303c003200400300c00380f00304088003881c0ba1001014045900781d800c2d40d0104074040d2410001282012001a0034190040040701e1022029004446a4079001940341c0c015060150020070442d10303032164640348409880a0040e1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 31969537 1250 31968287 31968289
    0x30c020f0d12020d090807141201140109020c0601060305090c040507050c0f0309090703150e040c0b1602010801080303010b2502030102040e0405010b090609060108090c10020f07080a0503030c031f1d06 88
    0x1f489040c000d05108071900000e20551b4545034141d003802110707050001c1101030621a00d9820b55100364800350b41a9000610003c42420034003040d405416a410304001c681003010145983c1c3d4107254801d402a542c4070049a0f00da4042c00c00c0d521600d2440c0d04aa86543c01e0109240e100d030044494240a00061004500c925000780904e518000c00b0090f9140120328000c0c008801c4503016005440c0c0c0b030807404c804101d440c484070041804404402a20000c0c0200c1d20005185080c144c2c810754641e00240300601040f100c2c0401c5400314400312b5808946083c40c00c8140d07960003d00c0c07a000307515600c005000649241c51070300c41403041d03010324001c00c09540d002040c404070b40d10850741554014440e10004400798025401150084c0d002001c4441301d0341408040759198080020300f1015a000c80c0a515180d0700c200080005030041d100500240788466441c41da0303d00004e0025483e40001100248440442111441a05442c1c400d103401d4159152004001214884540d034001440c0e24001402 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 31970787 1250 31969537 31969543
    0x1140102011a060f07030504050603131406070206070309050f071e150903061e06030605011a0c030d051306051006030b030a050d03051905010b25030c020f0d12020d0908 74
    0x58400203000c0a1070b02c00c604821218a41c4003417800c405001041c44042010389544020754400c0d0320b014010030214420741083c0e0160005c8800c6107107283e114004011801e540412404d070003040341c0c140400c070304206150142c244805109100d45078851a01e000400b194800364041540e05070b600c07103044850312190407000f441c0100040307001160300e00000700000340c56a401380d105100503c85010141070410142016200d841d0310a54000382c94070010700c0322810490314006995031900096240010000f001612401103441c00c8114603583c0000900d50350182d0795800480b540b0a500f00580d14206031241001241402a000040d14185050815040000326003880b140c009004040100c42c0390412005000004c5c20b02549641e2100b4403054030070310b400b0b0135000e002c41c51102074035074891080c1d10b80b845521100c0c0c17111015000c0444e40100740c100716419002501074a44084c400689404204440300d0100002e108514010310300031403a5010854426010542d070303490300340ca5915289259 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 31972037 1250 31970787 31970831
    0x2006040f030e0901120210030f0f0c0e0109050a050f0301090213020c010c08090a060c030e0d0801090b0a030209010315110c0d090602070b040e04050106120506071707090b090103090b0114010201 85
    0x2000129250f8000054503240401c0801f21501c1d02e07000c58000c0d0811321a80581d12103a41300d40d03a07036071600500304c017241e00210703400225202807820204a5140c0000680900740c41d12403a8000e501c118030302c50281d102034001c000000d8000d003c0c00d600e2400c0b4940039000354004001003a865280030451107403076200302202801040d20b58018000000592508001042410b041800385603640000c89800d00c014085000100120344880c10107600d0300c0300032020345000524146c852840312400f4401a0345641891303041d00e4000d40190101a601c0702000d00802c000285400e10001c0881e91030302c034200000f00a03042000550b148a142c44e61444180d0361303040580a001508802404140200c3e000718901c60381c0f080c011800841d20766503c02d0707640340055a511050b5210b0300300c0020807041c650010f42540d6104074824555a0916001e58003d000702c28038041c010710b4500004040d030b545c0e071103600720140c1c0b2500101d491a0a513954000300c010010008002d0b8059400c0182148040303101c81c02d000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 31973287 1250 31972037 31972049
    0x102010b0904020f030f062404050103050a1502040b03010306020403060f09020a17031b06060a14031b0d060509010203070f020106120209060105040e0703060f05031605012006040f030e0901 83
    0x700d54a80d6800c10010b2080400d20300e805200c0c85a0405c99000c0c10003500303014260303501c807420780c5012961818441d140c9003890507006509140042001880005a0400864010703543e44104011020514040e20643d441803000e080301000201c00d0109d258000c0080303a02c94a401c200e66a1808a900191218104081e40c440d2041c98100401c54402c0c4001c82c0219040040d240707800131550403c0204a41540307520400da00600810200e801c001c0a800080d01000c00985001920800040d6840030240c080c103145a1060340e030700c0c004d078985000c0e058803580d20140074415441c01d4140c46000390000c4500c240007c1c540104800b03054010311401003503420703c0c040d82d41018550703002d0143e9140f0241c00c40c0d040101c01c01002030003e070385000e4180100e000d43e5010904901d025800741c004101900940d2080d000030102c098071010008020007200d50031700309540300c001000c000c1e12a1801c41441c50740c440c0641000c010801088450307e156551007a100c03000d122201406101e10799500340190 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 31974537 1250 31973287 31973299
    0x604051306020a03020906030c03010e011a0403060b04110a0e0907050702090604020702011107030605040b100e060906040204051c020a120305161e0b0f09030a02030702010c05030706110c010b0102010b 88
    0x1032404500c1980040481400d076003005460101da440100311640e20484881c400c07d400030006000514015100c00d00402c144405401b003090f22071042c820a1146100040900c2d5a0310b41900032512141c10044010344210080e035107400000d480038040800d07404003d446403008100003040c81e802107094a0500d03802030040c0056683e074605000c000d42c00030100f641404404401d400e61814200f03c0040514803a0001092900b0546080303030802d1409800403101e01980341050003114043c0312001c0d0b00030001c0352000390340e884000101f4002c0c4269000a608011440241d5901c13070940013040021610030355401ea501c03540c602c1d0003502e469039075000a0004904200307401069025403030b01c00595000e11041c100031142010400c0c0030142921045462441d400f08100920301041c0b4465403120703140015624104901c00029224450040000d044c401d1810841007806410403e40f260f803a4005000c0008503c814035500d00c5400007440f040b011344c204507040445500c180100d40c14800c1c06844 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 31975787 1250 31974537 31974571
    0x3030a110c100e070b030112140303070509010c0f05030d0c090f03020901030f030306081903081003051e031c020301080d030b030d11010f06090b0103060509060d06050709080303041109060405 84
    0x5140b02078600000600301c548510b490128080d513024009500030080550262400205850900000d1416192101d0a608203204121545800000706d468003402440c00b001c1c1c940789441c1045840e44007880240c203174400420034040c000d000c0d40c8103e00462560320b0b080c800aa0f42c3c1f03011168041c40d400002e40000060b001080010307140050b00e810303580300b0f0501140342600d0300691850582490038800c249074100030726806050700014460703044410700d1103601c2031a041d610342681c2c0300310040400040300c00c402c90940614006009032200035144440b0011448240802c42c00070b90428090005540285800401c04c28004c4c4180080250054041c150050300301c0780c15502e5a8031170011004a540740c10604126510612810000c0c1250b40c200280c014108400101200d07076035048140203c52b0700082c003c071503079070201205043d580924045403036503511000f04e60041c2583d10941d0b4a00c000710a1208010010b0142c080c1e5030401da801408030703030300c0360100000d9a106940030060034400130b036 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 31977037 1250 31975787 31975813
    0x180c0605030919050105010302010f110717030706181103060108060f060604050402120103060b04020a080103120504030f03080901050c0901050a110f03040306050603010b04061d070c02060c03030a110c 88
    0x6542e0056800c400d903084002030160b580c80b501d02c0ba80341124241d540388018421983c10201c011400348151800c680a03020303103218140e81721880c0c0241d065142e00da04c440c003c40c2c00100110b03165164400030604c04546211110464140407088c200c83c0194014030b6050315080019005040701d02d910010040d54560400e0301b04800005400950041c0d810400464980c903240002d0101a00515512403c0c0d891801d1001c02c07100d54011040c4114010000340445a034445c880d0b504bd02d1f04500c102d42c91083c654802e50300c034401d036400200a146082448030904d034114540b07600c1003034800001d102683c2c034240303128024480c6c034003203a020500034031035007106a01c600d15408807080320004a41081c9498402c8074a035800a034402c0390f0b99911030303041000e0303070500f130081c524601c0040e5800e1009500f40702c9002c1070103003d04210561070b1030400024618900c10081030325099006410760350340300201c546950710b960041ba1521101ca0902d00710302403450b018400c5401200403040075100d0300075020 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 31978287 1250 31977037 31977047
    0x3020309060f1012151d07031707050a150c0e0a0605030402040f060b07050f06070e060706090b010e07020c1516110307080a0309060801290d050403020d03180c06 71
    0x39100720901d04921030042503a0512138860003900740100c1d14500802c103d04143c0c415140701c1003d40c000340221b44049110842c00080c0c10050f01e500c02000401d0b101d040e0820b0025003c3c190303029085101d400000b0060200f0001a038070501240101480750300c2101c01e00f03a40322008258120341104207404c003004414440c00c00b40d90850310042004c11410900246102594100c0e00034588820f00001d0060401504000004000c100c650240560780340c03030400603013003148502000e03000c0c8200043d40300800144d035116a85090f4072070506201075031106d112114080003141d500000d4030840043c40b110f45070030f0351020f0204100c86401403074800b02481480c10800c4a04040352030b210014a040c80c0d5903018040c0501a09105008159001150400a00105aa6012000b44079174400140300a07212840c41085c484003144254240602074019000d141c4220b90f06a0311191600061108060780800c6420900034030780d4060145038050342462800000511000341040d046010800205000e9 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 31979537 1250 31978287 31978291
    0x40902030703090212010c02070f0308120417070309060e030105060915040902040e0309191505070c050402030f16031811010c0803090607030f06031203150b0d0209090703020309060f 80
    0x925000c52083c80650200e01100307401082070301165143c1e44010103941c1e041282d8802015402104030080f80740d030f10340105500c58440d40c0b4045d02c5115002400340503400c032028140c2e080c650080d5541d100070f420010161940b44c000c1030001002d04808410500c0c0500440740500e80080071107120b92165210780c2b890310b0407042c3d40d0381c0054488041c1c0002d40d5940c403941589aa0b0705024541c0e40c9400d1040204a21000286411121841d0740c1404500d06040e030603c085552802d15942c0c501c45401c1c40044040c0580c00582e1140c0000101b202c43c55242c00d44500402c020a44004030656060096050300c00c10901001d010715540c9004010410f03c1000d0346001d030041c1080c940340011a2503a51141c1c1c01195108010b501030414400c031107516105046801d021000100301ca1421583c0301070640f00110410010103441e1751501903145406440c3e0300040c260035594642e40e91112000710080c0d040f50018a02c220800c40c00905024024000c0320710644c810409409983d40b000c0d17045400c0440 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 31980787 1250 31979537 31979551
    0x90b041404050c0c34060201050117010501210501020d05070c05070801020f0f030a09050604080c0601050906060405060a170a090b0606040b031311030a080c012004061d0604061e1404090203 83
    0x40c03c0c80785481d61780d082100d8040d1046500100c0d05606140540000c41c0fa1101081c125a00d00001041040b83e10714018190005441c4232034000038242c05c281d07000e806241900b00840b071428003440b00680c1c00c03a40d025001841003040d40e00742d940c0c03162600e080707004000c40d40400e064104413041030341c4010307001580d01c0702c6142c400140300c25407a25860301d00301d42242d04883c00c1900140c2186941020000940103110885450301c203031420348046100b50082d441003500810300818884036041c001c203a03003c0e54220031044000103240903540b00028121a0200f5900e1706c0303550000c503009041c42000c5030141c0300a241c90511755201c81c4034944440b442560191b60000300380c0644407803a9018400d0500c82c500441d59940c4402c100314071642100c0b00303020a140c0030460407000700e01c0403502d44107650842d012428100c1e248001c1620801041001100d1683d026000143c0456115080308240c0c150b06250003841c1c00b0000440c105070742c6075100081c0c84044090612041200d040d281d00250b5000c24 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 31982037 1250 31980787 31980853
    0x309020105040332010605010906030504020d02100806130524060f07081209010c021f0b131409030a0c020409030c1e17070309090507090b041404050c0c 67
    0x5500d4980c0040481c6901d220854101840101462802480c242c4c0140c00ba50b24001c2222900e0100080c00c002424850f2105154481d8002402d543e5042441e554250700035102d031114054410b0000c084840072104103101d084080c8080508021600c2101d21a60028190764144010100311540b00000590380e9a4030901c10400a150700340341c42c3c00703480c080f0301c140303040b40d00d42003141c0302002d0942008100e81000c2c0c0c90400c440100d15400591058041d5218001c0e0782c8041101b0300380c50140030445c640e65008118512107100745140b40d44240c040383c0b14460140c95644811040030780b80d02c12456008000380304030307224a0141c9010741c8402c01c0700e8841d041c07107408059141d582020210340310141246901ca006043c1c0d05010a550b203698035500030303540a07441c1c80d610303540140c042c40a50185682c5155100c1c00603100030300442d402005030600281303981d00d0310f07622a01c00020321001080c2074021414000495030146021060f81c48a81c0c0002c00741204a6000d024840040d500125155010f0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 31983287 1250 31982037 31982039
    0xc0904140f06040c0501111504020a0512030d0c0f091a0d05041101020706030b1c080714030d140c030721060f091107050309131b03050412170601030902010504 70
    0x42040900c210402003070241c199441c09041038808242c0d1a0703c0079040c44181940361110010200d01c29200300c00701e02080c20300e902c81b4000f05600b041da54102030740182038242065401000000a8035000290b8401070109100450080f04c0750080e144000000c609014418400c550140c04000c00b25904080c4440c10082100d554009482c400d403026281c9180c111285019564103204050142003603050511040f00c1c083c0101c2c29100f0244030820001c00d01d50000410007c80301d0072500096080b00b1000c1035121500481ca03241c0d4001030075000b4040c40d004110f9003e071110313105d840c452081d40c0308490031961004c44c180d804c517003440c00211201c885e07180344001e03c982c0d52080001618058080c40c1e021070400030190b0480300b000ca020000d500050000f000050350020442d01048030607985607400d4141090303000060720350502d000380c10030010110085050383c15449584928004c2500c084009640d1500b0b803145c05101040440c415041f40000320154060b411031140684180f60040c545 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 31984537 1250 31983287 31983323
    0x30201050f0705011b050c06070201050709060c080d05010603020405031006120b06190801051b0c03071106040e0a09120c03020703110102031c02131d061306050306040b0f0a020a020c0904 82
    0x41800c0301440400300380041030343d2a54420030000a0327480303601800200a1410840d20103085108688a90010002e0f0352401300708002d1000d050300d401c90b0081c04180b00f07658454901901a420a024580c024412030213451013440c1180a1281100c080c110305030410b840b240c0b6040d5219030000c1404c4e8020043c40c1a85801d020030b001c58100510001000185030700704400c100545051542e40c0d0030341401e051040c2c060008001c4200c807025a40128101110f070f201d00086405409564400c0420580350b00800c0101d05160b00706084003486100c0c0c3d00d0904140c84d0054540040c0d0780c60260059110047c1440000e08442d80100c0066050040341c0c01c0c1144a0901030490f04c841e40201101ca0f008a1204581100320722094060849140c1d0045012900e411004034040002c200a1154029841440680445602c807502038400501506e441c2d18080c20100c81c042c80584004d92604031050024401521600c2030300d200840d90360182190060301d800308450356070050000c1c1ca032004403c007a0500 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 31985787 1250 31984537 31984571
    0xb0a090f02130b01030c0c0c09020705150703020a17010617100506071103010605090906041509020406061d0411120903090901060206010e10030b070507050f010c03091b030201050f070501 82
    0x31a021400b0045150b2400c41c00040a80700340080b804240107006804100003080100301c00240c03007040400588814082c10308034580700c4e0188441d016640498280310115078103400505c000324484e11a0750281d074011000806a001c240b0602e00040c1c00350300050300b550100c2c0d4809810801c171030391074540ca030303140c03800188140d001c1d2204a9158103011550700c4a03007020b00501004000459041c1028507180c0f40140d26804018801000d2a00140b00d0303250110f281d07440941ca898014000308011034480c00c011741030301501d01017608440141d10341e00c11540303404d000d2440c102d02c43e19080ca05081e982c4880401c2d412011301215110301050002420076214070104070300078210342d8018151549030140c0318504106c081d0841b403951404840500114580a00c2150069418503005035204001e040113810841324400654565003040384028010790703d0b030030401d0a14001c0e1012405140c131013004c0c42e40341500740320090110322705201030320000100d0030103850f03454042c10012803980030150254071 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 31987037 1250 31985787 31985809
    0x40e03040f090e1903120e060f04050c150d020a050403170a09080a0201020c011d0405010303110123060108070909060803030406050901020c060c09060408150108010e0304030b0a090f02 81
    0x34000d01c005900b002011010f0084a0500c0b4900001c3d040d4001c10b160003540800c20a5400b40a0003210001100002265442070b1100d404804c10307101c2c0c90400c906003100100090398190341d640f080d445841030518121189141056404441a141000160300c54010b908903140800504c2030601c070000104040071903182c01c42074440103032542d81018034800340c02034005400c0021141c0c0111500c40060340c00107203070341000b07030309013132004180011242a0180c182802d02d01c64115007458000820150090003200c075101c101c0000f0300c101140000c054148200b1010711348824518180466038079401140302c25005412850100e5200707460301c1150007500c03d40c1c0c7c40100c80d6400002080180200c0e40320741604000c80b80d00030351401d031140a540d6516100503287c089039000000d03d40c07449030381300301c1190010052501903805091008501c01d003a90b0b42485902c15950070489590480e0354080308035015264001441403460326018007203001400400400c884c0c1c08003103108030025a41d2811480c0b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 31988287 1250 31987037 31987049
    0xa062115020d230f040f08030604020403060e0105090105060d03050d0c1b0803070e0105040e0609090c120a151b050a0311030406020703090f06050414040216030203040920040b09040e0304 82
    0x400c1030160310044080300700f005020b01c00d0f04808805210000324680300c0300d06410741100116880c0c1c2c4810001800920996000401840c03400894004410064101c14424511980204100d560700030a0081d46403100030000d0005400300141c0d4240d1500780e21060a85600d40b508100740314500802080b01d45242105441880c4080201f01580b41d2003068524404021305c0c21a09080c46c0005210204501418480c810a4000d002a1074078908000000907a04002c2040c1500d00103054025190a403288003030f601d81585288582c10480180070314071440c030340100d943c00c0380b5890800403559038102d1b2a51104142d10b4600380752150524a0185001d14000d0000694407804c500c0c0203400404194068005500001001c000968001d0195810ac55807200c44034509a03181c00003030024441d020328000e0300b0004021000a15900002900949101c0102002041050038211101c1100601c007102c110908001c1807104a840320003805c0010000307040072a242c3c1c44141c4050958026810507 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 31989537 1250 31988287 31988321
    0x105250812180316021c0206030a0b0301060b03060f010c0f0203010c1205060f06030a020a03090b0901060302030607020622020102030c060f070e0108011401030504150905060a062115020d 82
    0x100c0110480715030382c982081200c5004500e0040800e40000e032600091001921031005014512002c5800072045c0300d08030703402025150343e49400604480140801c10300c150096207480c0000c261215090222801080000d01e12000c0c02100401120040d591490481d043d440550201005850900400320b00211039212418495078124452040790001044180b0403006032510301e00d540c6038081100e4019032021405070b59561031100c260083c00a100c030051401c010502080482c2806600040940784224246ca21a0311008412641c0703100513101c8034003079202c00b00000011020f140e440c02465206005603814030704011525418002e007203171042084068002040816a440050112030740303000d0900403d2541882548250041030411281c14581d480c40410203021164440320f03464204894240306807015450210f884803410b8591405031414075001045150001c4086d0990300ea00790300d10f0342d070101c90742c44951a040042642c01042982044140ca100b43d0600036401500d04071018 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 31990787 1250 31989537 31989541
    0x6210403030218010f1d0a180b0306100803030601210c0807020601060c0302100203100f082b0203030703050406020c0a0c15050910030903020709050103060f0f05060105250812 77
    0x810034940402256141000098500d020f891074220642c3d261007841c203a0110341810459007c20413040c140d4101880d810002802c1d40414015500800403030030701902560340580b1003519401442090380a501030a420510008801d035120700c1e10840c020164010382140310a4880a040031070b84241140070000d41c0720070401c51040e40401469004101a29012000b03c3c42c2d80c80003502c1e100d81c5017642e248107400002080161403102d0101001e4140d01c000b00c1c03c4285e0300d042d101e65595840d203014182003255600c250345424480e0340e2080205894001d07515541d41c1039400c07002010014422950780380e092000c0000064200481915684181a605000303400c0481e61812440b82c4003160040100c1000020041d0711041c000000f204083c1c04d010035a030380ca03480c3c2641440301542120345920329100000040c0001600720194203410910b003001584a240940b070160f4504868541c0420b00401070070842102e003000c0d00811305040c100b8800130015603690312000d80d000741d200c40c12205908007 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 31992037 1250 31990787 31990807
    0x114040801051e061804050f0706020f0c0604050a0905060409050d020304090f0501080c0d03020a06050f04150b0906010e03160602060603060112050c060a111c090509010311062104030302 82
    0x140d44070301d54980802c0551a403505a00141200c440100c1654600005c0c0e001b1908000302080030301e0020740c0c510309a07104243c42c0c1d00029601e0040c800380300502e101e00f404208041c10850102da0507200003905042a1a00b040f0b1008098007004c2d14442e0403581c3c0f4004800420420300009604800303a0f40030b55542d0b403404c0b21200680c1c0d00781d01c8100034149084010803003040000380801101e0f50995010309001070724181a030030300a0300303107000d012242490708000a0300f82c210030040c070482c0709802c001103060310a004902260400e010a90b0812240c801140c40c2d0360055840c03101c0844020204c807600b48100513103028001c8942c0c881c10140e449032080c44424901800a10301506d110f01e02c0982c05001c684540c1c0c3c4d43c0840c13400c3c45000f0140061201d100c284503484039071210403e8000c89441d003110340c40300e02450301c00c3c850460002e00c48402c04210340c9080401ca6040f640c0082c5103510039000c02c0c040214aa1002c2c0e6880300c404110703143d08401032400f102c1503109600a4070010384a240ca51 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 31993287 1250 31992037 31992061
    0x902040f050105040509070c031e03060e0705030708010501030f0603020d0614010509130204020307050405091312030606080406020a0203070f0311010c0309030503130201090503100204080d020a0201020304060509011404080105 99
    0x740116041c0a01031005100c40d455002d506903204c02036240c0044800141c0c18141c929420001410102991000c142090541c0680004d001c8a8a60384ca6903000c1e66600c4c000c031340d5070009850500005018100421840d0f10070b400c406680181100009461950b85c1d0002d568130300400c80032254181c64040c0b486605200e60a1180145026503183c0c4c01440e120317000300303a040140c18009208036030200c0400c4445209105a034081d11029003503a61a0400300060256114090801c0366050702d004030b1118000e00c24010003085800c2038075016001c0c0c0740c0c1e9079444042c3d008642d000c0308520040c84034501180c210070380260000c3c02074444034410b15580030843d0a4411002074038091604040550001035400360031a43e0255940300042d491040d00d10048500800b643d001707a903d44601c01c890100300809a000300700721307a000d4040310540c20035110142d84a4481d034001072b0141e0028002005020700400040005140c1450280c80040d610402c5080c107401030307002611140c0d500e00810511100038 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 31994537 1250 31993287 31993289
    0x10503070602030301031b050603010b09030c0f010c03080402120303160f0306060801050111070f09020c0c0409081606060905181005010f120c080d05030906100e0a050c070203070902040f 82
    0x590251114904048001e5030303030310040c803004040018108410000400d60000e0002500c80103240f5583c950b0342e501c0295198002c244560300c603002d8103080440fa4a060220010700307603410713150f50702d104c40740e500c054509542c0100305a8003d0042e86041001843c1400214450407410f01daa404600007100e000b050400808000028989004800d00030541c2040384c00341103500900e450703513000441841c41810580745a101c0030308054411400710b406103040d0007070310307038040d9450444a074003504074104800c0ea08529000307403581c4010000d29000502c45a05088014050740d004244681e6078001c0310221201100c0c044c0b00e6120040b150807048a050125101c5c03d100c180b0140881d50401e14415042606403041c0d02241c44901ea004080010100a14000300b040304103591800c4141d04000e000390344116010b54281c003606000601e42ea00303d07450310f030a0381e034548100009a41c0d040b055500510001d07060381d00307283e002d00100d00140c0d4101321400c050711010350050f0f01c55181c000034503608195 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 31995787 1250 31994537 31994539
    0x4030306380901030b1206010501111b010323042609090114030a0501150f060206040510151503060e0601020304051302090604050d140c041e11131d0105 67
    0x80c1d5204840480300e00039048450548020145a94620300801130b001060100802e40e08038034818424100d016002c140c10781202c9083e21240c00f514801115240c550b010344a194090040c11110354009521982c80401c0361a51310005985c842a400c003203108440045804940c1c251211080081d0b03c1d000700c2e80c13004400580c681950510b4407000005201c0340c01406001013a0050b098062a90742d001c01040c2902c0e44c00c90f000b08003241c0070a0881d64001604c0c05005034502022200184882c80040c1251069410101030b00754a2188a00f440281c85c41f000008c411010380c80001c40c1c10400c007019083d44150548002074598075011a41c210008000e042074199041840104104d80351480c46d000c40c04c00d800030060b03465805000041d05405650000d58001404e220701c40e0401000384007540390b10f46980100c2d00c000c1c01603000c01081e10007001c00d040e0818645444400200025004060407143c5c40000702c0c107002c1c400c6020100889143c4c1701d11240880c0040124a07188002e17800390142030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 31997037 1250 31995787 31995839
    0xa021503091906022b1109030304090905030f0c010e1b010509041116080a030e0a1a060111060c0d11130312031107030c030206130c060c06020d0504030306 68
    0x546000026200d14481800c1484508600c907140100583c3c3c0e41113940344641036041d000400c1c407025044c05010328a188080c0c00c50318010115500031056030a845502c44020020b41c81e05040100c00340103031422034000c803182e12060003440a28034401001e0000c4a60340400020340310080742616151150040510400004170f2001b0440c50360b00108484014005031004550340100c01c28202143c0b10780360340402140c405d4910803007001308040003802d1305450b0b81e5090040886141d05140c4440305500001c00c80030380850012000a1209034080e40302c071050400c020030015400319113051400488120818100010700d034a513425032803003001c01448604007801c0c101001e5032000c9204002d50700000e0601c02c0c1d106580c86001e80319402a410940380d2142040d10b07180d070361401510b5540820750840c09800342000154800c2e54030100019620b400021002c0380c640381c940c040d03600c0383c00c01d201521800e80802000b01e00140500400e405a8443c0e039000550718a0004100da0100044485040c264 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 31998287 1250 31997037 31997041
    0x3030506040e03190c050703080304020306090601082a09041b0b0702030607030228050a111c050c0109020603090604120215010320040903020c19030503030a09060902060301080a021503 81
    0x38200005403521841341d01102c01a0905244054039a0046008010700710f11aa0f00003001700b05003c40030714082e0b0f00c29011035580391070b209116911590300b4040c9450fa0750002c0b180420070840103132240c00c101e0b0304003407044039100000085200010200d070140c808480015031030b40103440d042804030050890fa42c0160410032a40e000a0701c0d2030016210a040507004214085140b907840e003485410b82c01d1003080110101c00d450060310680100881f5004151701200440c40094040744640d1112200502204280d0448070142c401c0c1c0c01c49500701c915991313103030164401a02d60b14010b42c000c4143c40010704c41481c0c1441e1280c2c1d02140100030724119000300200040301e29500a615044da03501400340e82d0503803040303500030002c49010800305038440e04024250080c9070300070034405d80c140307019100204c0c080c00c1d8120304122100709102c014280d60003080041c804a003030340d01c0203070f0007885184089840c044540003e85c25410a800c419803036005100d0f4003045250940c44414400b644081142c118 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 31999537 1250 31998287 31998311
    0x1020c01021009060b13090b0105010c031b03020106080d090503070501090f030803190207030806030c03031e0f0405060a050406030605091605070201020a020319030e0901030b070c0501020409060306090303050604 93
    0x1403240c41080c40b4107903071200603250411001d500080c81100001c5c01800003d07a03c600918058444420207459114609001103240e500c103001843d6590b0709a201d410302e5810009907261054860301c402c1e000c5569034100480d6484007480311081003516651401c0c04507040004040c20925a9031003181405607001041202c0c020000000c0b01f01ea030454042900c0340c0d100d05c09044d00351104110011450b00c005100410150801189400b4020640c216000305010b08207141c0c2d80d200304441516480c04c01000c0105148071000201b0314414982c640c0c50815a80d1340124030715402118241000c52400314007030001303561620a800090400301c44000090410301c101928400407024184104000028020f055900030049c054415038050219599a02031442034030b200d001d91a8100d0008444502d80300030f034909003194505881d00054611241d440d10141980c03828800b1000312000e5400340800542c00d403035440707034a0056000e500d0101d509901890001c040b104c0080c002403081d031030b00f51a4801 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 32000787 1250 31999537 31999543
    0x70507090218010c030512010b040305010c0305042406030b010e0711010204300b09060907050f060a0e030a050d0215240603060103090f080403030305070516030804061d010608070501020c0102 84
    0x14802802c1581004c000c03818116450b1203103803407000c101c03081e0100005020030701c10010401c4a02400080252100401c002c40a4900548016040004503c100c0d01d44250301e86041d4010907582e0350014840e80d03a560307407820011090703101042c24140001008007440d0849101c4e451036a03000001c610f041e040101801100559214218108030308007031007142203030400340211030340d504041070f01d82e140341501202c2c2e900c00c011103400000340582c00e030008503410801e00026131070310001e0807181002c034190340894624000010031a0305110b40d011035004101300707004003070103080e0755801ba06080c0c00700752600c103c0e0744015050640d00b490000c44105001c00d80651194080c100f01c0709140d40c1d8540c040100d016210b84003014240a807540c0c803403400c0290b04001801164481e4805100541e02e035241903c43d030103034a44a100702010381d42c010001900c02e0002d154402e2042c0c20006a801b0003080d0b81801e03415031408800075030766030381003840307601d4040101200408091005000740000c0e0340001f92 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 32002037 1250 32000787 32000827
    0x11070b040608100509090c0103290402030702150405060f130b0a150f0f0503060a02030609190906060303030b0102210912010b03010203090303070305010b070201080f0403090e010b0705070902 84
    0x4111240000c952002c81000f4808000d013001056103030030b410041e040a44907180014624080792520328081102c01110103c40720140440400034a0500c64400380303c0030358002404441180140b4444450461500446500032400b440c010440361801c4511a030f03045101074500d04810a003103502c040000e00b06002e65078002800b040200e0301c000701d0103110070400302d5904003900041c03d44c10089080124030310000c00700d45089040b00c500e030b101d10303101c04100c0c442030780c2103500002d105002942601002c0d2449039024600580041c1d03804013519410204c840f550000c07000261113002409066a041240034400915884a02507102c803804103800c0c18032920020b94000c01303072a51411038580080d80940e45d46040507009654a19001407100e413203900c01c0f280840032070711386000419042a4802038a030540d5068442c400c4545940407c3c00318007030001d000302c00b0400180004103144210030b0030103000302900c50402e501d64180f0310b0b24032704000e019000401d2061040c80318505500c08111104 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 32003287 1250 32002037 32002049
    0x10b070620041206050f0402010512130213020a020c030c03190c0b0a0512010b0901090b0304021914040f14060d0503130e040c0b0c1b060c06040803060111070b04 71
    0xa03001640904085100701e040a04a04100c1d010400080b0b1454040c003840560b48212000c001c145d4402030031400740c43c1b06440281c00120240084011007402203859604207540e1020701c40032031259400034100030558846c0c804005e03008200705858a40410803242c0c0c0040c1100504001700b14800070030360702e2058143c1084884041c200b10414012075483c41c00c05003900480040c3d5074000e80390040c02641c00024031130780c4102c0000000441c440c00c40262460200140d440314011442c281c10500b40f600042d0042c0e90040d0391300c240c0e0300c94070302d4112440000e0135840441e29806104900b044111007416600c0200300c1c0c2080300803215001e00d030301540c0d80483e084078040c15a080c0b43c10b00f24658058640304d9100102c0000d4085061484491041d01c030381d00c0380c0c07aa10a85602c601c0c000c1e2090041c03a54444299010100400141c2c110041141d0200c0c00a0810b42c24010541c1c9034900c2c01c2c2c2c3c143c8090340c4040000041c0021540d00c43d084140a0001000800c40d803072415819056901c900d01c070b0a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 32004537 1250 32003287 32003291
    0x90212151b090d050606010e030a080f1803011404020427061a09091b0103060311040b0f10030609110301030507061103040e0403020d03061a0405010e0406090908180603010b0706 78
    0x7a114150820151940c0c4600070b803210031000c20604e440307661004151003907404203103010007c4906240c00204000c145a001c0f50312401c18035a003c0f041510740000d45680315407406810841821344003481601d0000000f9400520141858014001161380d60041d05032011684103109060301c91150100103100d45c44040000c9035880c00701c02540303980c507080038580e1002804062082d040e50015250442c101d5495122001400381e10040d4222180c130311001780225a41d00000e4483d1910b544684103140014003281103144021000541c040e000910f0200800d40c0c52000341329096644c0729901d6a54101e0301d40c1c91455045031540c5981e40c81c10700c40c180030464641f20074041d5440034419a801400c02c801c035921a81800c5c50040d4540030304007441000640340100002c0d48458600d89a1400c200360684580703410300b8000119140e02c200381c10303960003a8403130400090301c0403540300c1e0740d513018003807141c40361140d49800024114052080c41103101d0300e028001844195000811109000c3d484400 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 32005787 1250 32004537 32004571
    0x1505181209010c05150f07030b0105070210030905070b0c010c020601080c0105040330030b010e030703030f0e0103020c0d0207051512070507060b0a1e08010e030304081b0d020109021215 81
    0x781d443d18001081710070300c0500100600c446003044100143c018071a9844c04d0001d1400c40d00112114012032a019522010300d891903840180207910030b111a85c0144107440346582c6401da5005160701c03001030000759a5481130718255440d4140600703405401c03840c000c3c0c07604841000000307009010303502001c0c010060b8461404101e100312107c0521032210800c000101c110414801b070007e00841540a01103450b1500241c07240c07401086a801785d80c2e0684a441e0400d14540c01102d80d80c0910300d11a0506600308a50b0138210b608000081c0f00111540c028041d16080405202800e46c0f10740408000003418400425006521070041d640100c10b49080c5484e1031660a00101810035004015000001100007040f00006036019524003454440629422983c0c1c0c01d80c00c0c22265220004086508140007240c0040c001d44024202501100c410600042d5164056420048001c010a015030340d03e4840da021400d00c481004052056a8060319003003e0100320108140c800805140440700c003545 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 32007037 1250 32005787 32005793
    0x1030b06030703351201061d0603010312110607020714010c020904030305241e0105040e0705030a061d07030b01051c020304020a14010c03050c07031505181209010c 72
    0x100344001560010f0303079518841d40764100036039012003114808500301400c0104044c0c03403a1010440d0500140b42500c80a0baa2a140084aaa401d10619030b00303611000d40030038005644000c051070103075001c1d0490700c1c2000600c400103003000301034040c0500150013110030411019001709041086954441036110f00300740c0200100c60701901d01100035480024030082c442810f5041e4020703407240f445015601030b0542c0e08102c4c0d02128200941c41988001c0d42615480802100714600140713007018140b40b03042c59268840680c0d9518100d4030b182c0003d03804803c2001e05c3c805405440010300b00d0034102442c5060f1400003401001c0020031460615490f131091019692003001100d0260841000c038100c0a01d004554002951054606034480c28801902240140034040b403100c1005e4141c4510301052615035042d40c440d00840310318200383c0150034000003c03400c6e10300d078610288540721002505141503c02ca08403a0142411040c442d880452500d620760000d204582c681802400d045081200501e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 32008287 1250 32007037 32007043
    0x201051012051006061706030f07030206090d0203030304050604061a1005030711030a0507030315052101020c0102031617060a050409170d09031e0801050409050102070b180106170601030b0603 84
    0x50306224400e1302d004000914240e0241c00c400c0050070100d0514800d84400080643c0c51014001100c031503040818100010701e400380090144d0100549102111129500000c1c01c5400469081d9541d401141c104406c02000e44140510f042281d0955410088800c1c046200c10503001c4100e0244100000421032080c000c50032200034408072011260360345140c40c0c2c0144940c08c492000c50109090158106801800440420540c0d41c0a0030002d80d9454070030103840752000007051880c06542c2005041480c0d102030004600c200c01c801c001060b020303401a4020304001c2560400c82e42e4900301005d0052540d99419540308072403003107901145460003410b04009201400110980c21840015645038400c81e90b08403913401c038046d48410f61580303032400a15541e4001059104005011031005000a24040e4882032002c1c1c040c0b0001070500030030f035aa21011210540c1c81c0c40c000d040984840d0000d917024001c043c041c1c070114881010b000d110001c039030381c0c589040c00010001c1c01d0300400210300351810 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 32009537 1250 32008287 32008303
    0x302011b020a030302070f05040203040b0601180e090102090f040203040c05010e1306120b07050406020a020418051005092a06070f0803010b0d060501110c04050a060b0d0204080d020105101205 84
    0x410702c10030542e5a25010f5602c080900c01d4003410111860b000810b458036200f80d901c1a80c004000d00340580c0d415004540da03180c055503201414640c0180880d0410f0065410340c400c51444000580d40ca8a0404200804541c056070a00c102d0040042100080002c4164021a00c0a08180e00d0100500c2c00003151120b80102241c003803498030340e002a00d203001070000200300d402218040303082c3e00c400304116568883c5001d900c01591002d8403820050800780c0c098925030107040c010003428061a60b8017414040d400b100890362507190814060f52080502c82c49200c8a40060521280710006564801c0024502070441c41118040f41e03001c02d20009030030292465a00c01d106c1603980d83c50b1f00b0f600c841a044002042e65540c038100c00801c481d401502c0c09060315907054002c0c03814038007030020407002e081c00500c1d468030151070311000036424001c2c034090080c42960040158079942482641032500c0300078a40b00c021a810170f824081c0014174030340030743c2c10344100d500307407410901003810440c7c40d006107 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 32010787 1250 32009537 32009539
    0x902010e0d0f12030207050a030f020307060515040b0306070f0e0f030a0b0405010b10080a0906060b030a0209040f0506010e0909030903030f0406031a2b0203070623030f010302011b02 80
    0x25801c440d000c000c0004800803910b4840d85208a40d80c02c2c400003213049008421005107164014031401010a0142004c0d40c0c60079006d2040724039240b25584e527541900d809988014003800707000300086a40c030b0070b03000b060f0242000741c2c003c140794908800000e00b400c20a60025051281902ca000c0b4103465005020380b080354090200d9a624410745040510000200c5040e42c065103840040301c0720340b420890020800302c00da80c840c0311335150170440c0d40040858950858030309603180b000142c0e43d1040c4028622500304545d006071200e010100b4042034130000082012014500303410814039030313040061402101d4050b1b4559006a41d0500114907521851850640c9031102041c1d0203900250400108140d0f80303260350500c0b51220440f401c94a80d601141c109274000c0d8240780c1a1301075412004d00070029a10700342962b2003180d554002c83d04280180d0011000070300c0c003e044032880200c85801ea0001d010220440d4607525203a514445010010f003c003d0420030186041014510707444240f22119030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 32012037 1250 32010787 32010799
    0x90102070b040f05120105010308030403050a1e11010c020f030301030f0f05010908031803030702060601030c09030b04080a0201050709180b04020d02130905090a0c030212070314010203010e0109020910030902010e 93
    0x384588048686400a1043c14170038005003680320b402c40707810301a990407070364441405402e64859990075182c41d0499480070007040700403402c450003165400585c0040f0461600c5440700c0039440c400103801c1d1809542d502c010342d40510034800a05000201f00ea04580d00200d03d2030701d10b5100d1a191802c5500031001519541c01c0c9003004090005080046000348011a18072a4480c2c03241c0d101a2030f40130807584900036800010014102c1e50280d0882080100c2c031789407060030a500c903036440000a000b510140c64001010030280c122540900c1466082801742c141100310500e00941171120301d0403607001d141c03035684600f80036110f515190140e481e1034000035001c0d034848140b4058a86407100b64821140e8250524002c151240400b06070062503d0b04413054107401030450302801180d07013400d031503d40d40b8812903e000012071500710001941d1303143ea9001507602e501d00b41d0303150f85003c0d043e00030348003091040140360f01d1070ba6440c80c00004416070342408101e41c011800140c4a1030300c1c0c40141070b0080 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 32013287 1250 32012037 32012039
    0x21c0506070201060501260a05091903020312060405010e0c0f16030f03050c04050f06090303120c040608010f180513080c01090b0a14060111010b030102130302130c14090102070b04 79
    0x282c041d04820181c070820707a1020700860007201075041f520302144225100700d100001090810303142d138204d240e20400e0031044440f046040c040e90ba088001282044c6c005070000314552804040c03083c6010f42210040701c0610444d41010401c0c084908064070712448024000b41113000c0522401c180e0381d80d12007007902448048654200544020150790700000000d1400c1c00107000c001c001400c1e41c040c2c5102926202804e008081400410f0b0b00000c0c003e6403520040c049044080c5a0043c400d00c2404101e41e0f442c0c66031729010010344481c2068001d08815190f0710403d101c0c100800904203003011142c84003140c251075440c1a076801c4091428090001440000e00e00744040c015008120840d2062440c881d555980c4600c0400300c590305402c00000c1b9002d080810301a40c45003440e1409422580e0001544e40703948400607003282c0c0314190710000564496010000d6180140804850800c039640a20160110400040840c006d1800c8030b1101c1c003002ca03034000d95920030004080035040c400e08542c2d070b031 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 32014393 1106 32013287 32013301
    0x706030f0e100603020310090818010c020d03020106082509091b08150601020a11040e031e0903011b09060804060b0303030a050105151204021c0506 65
    0x2203a280c1942580800c800d02c400c81000c032503a01c00080d11440c6106041c1090f0040c480c1c00c00d41807038180d00c10042815401161100c8440d54a0000d820248a0051b00c0c00708070540d01075040740000c0010001c141d015840710702550001000c460804c1c064910318001d903030b418100a428514080700810107401c0c81d0304007440c1580f00f54240380c01d07a007081d072485c02000900c9d84030b501a43d10a03480880c0c0c12090501c40380e0402400c0c40509034220560320f4455410b449020302d0390041d950b07240b0013681e00900b8401d42d105042250411411541c9000000c4d100d80c012880c502c1c40784d403030000348010610780060520101281c07520703200c00e010b10309101954001d100400c15144107459400000507a5070910003144202c003003907400140d42d41082e040c0086110340c60210b41b031400c001c0059a52480590726820307880b0f6070490300c2c50040240c04850303010030340c1a00c0c0024014850346050285c2 = true := by decide +kernel

theorem cover : BRFrame.Cov 31834537 32014393 := by
  have h0 := BRFrame.cov_init 31834537
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31834537 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 31834537 ≤ n) (h2 : n < 32014393) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
