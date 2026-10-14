-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0151
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:07:46.536804+00:00
-- url     : https://prove2.me/submissions/5e4e6c35-deab-4ab5-983c-2f7bcc24a298

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 26978423 ≤ n < 27158279 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 26979673 1250 26978423 26978429
    0x1704060e12070302070f090606080f04020402040f0311130c020d11150702030406021002090928050a020c07051503040b07050f03280908040909020103110714070f050604 74
    0x140c0c484540502816040c05007003007144035655030350380d01c4041d420b020b55074a03c244103081702c1605032180064204818403400d0180d840c03a9680305030980b80c3c902c1002d40c074607000e441030f03901c41da003080002584816040000c1c01140306089000c102a103000421070901804440c0d80189402c0048204400354041a240c000c000781d824100340d181d031580e61803071900c918164491404450802803103102600080a002161941c0d400c88074a270300292140e4050b8010381c440203801000440210303d40c03000d40404510019001d002000c44014900102c230f041d15400c0c1c4020300c03178940c001680701c1c1d0440701703105040142030262031a49406049101c1c801c0c4511001348054149010580410040b91150b0126685200e801d01d54a849092002e20040803241e9240079030113106040c1c005d48180140e6015900007150000c280e1410540782140307480203080c0e541d100700d040581c0c400740548c40805010292481c0c40c040d02c0c205040c800d84181d81c1c1e16082d11900420400a032420b8204419620981141d040d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 26980923 1250 26979673 26979683
    0x411090903091c12021507020f0c09072618030708030606160b191d0a060b0409050a0b0402040e030c060402010c02042a02010f0c020709090201020304120b010f061704 73
    0x3a000f01034114450244200c600205640e04d6940c0700d4550360381c0000d5003000c031802402c1401040d1541d40d41680e0b1801c07041d00c10102030b081242c4050403441c05a2520b680031300c0c40e0400a0510100d4101c081188180648a5005075031090500a15040c50a04950401e82902c0210310305205034860900c240002014a480b40740000380840e1007004066000c0072450780070300d484183e81807030b20014000400c4046c0200c2020726054490340c02250840040c51001906409055800d0240e284c84000d0640640002e0300306440305004030000c1c0b01000321a08484c0102428004c80c10148108000c1c2c0300c4190030490207070300920404c0b848040100d006034225609080c801915881803010030003a0880ac40d000b07070705255a00300d0f0f9580d17000ca88420002e07100b0550082000c03015440e2100101e4661700b40c280b006902c4601700344500c2c5090341c802c200c40c900500482c2e00781981c90341040f1101046820072100b50b01c54030010490350809890807030107002c140c106800c8c072400d13145030b072041c0d4a0b00500182c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 26982173 1250 26980923 26980939
    0x105070b07030204080f030903060c0a08040312150b130602030f040e0405010b0a030605040303050106091409040c05061611010203070b0a02070f02040c0203040f0f030506070503070e0d0605041109090309 89
    0x80079000754101c4000381080f01c1a80c441003400452244c0b00e0f0400b02d5080d009004080014204900319012150600e40903103e9160503119910200e90300f0310071381a20040c2030380d94800300c00c0c4144103200d54801041910727481a6120708003018418040e04a0b400700055510620569600704024000e60f02074510200e12a04903a079242806409402c8403070700f8a4001542100120a000d026009144654000d850030f0186980e94070086070030001c207126140c403144480c444071006250541456030401d00405140d51065210000036040e0b510110351682110b4040c003c000c10040030f4040c40d610b42c403090025600700140ca46a900039540010034012200394001001c004200c202c91800b4203007a0050400c2181141c04900a56258050300652000000e0b03d1000100440040c03c00c9003600c0e40314000d8480c03902e0710039003503400da000640010140200c170300356044140c0700d84466460041c00307800c010840d0b0900c0d0414000c1c1c048808466400350360310b40300700700b80348078004200c5200c02d0003915249 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 26983423 1250 26982173 26982181
    0x915120c23040203040c030605090604050709230c030402011101050c09010e1f0e130207050d0302031012080304060c0503060f1306030c030503070308070c0302070501030c092607050a03020105070b 86
    0x64200001d00c20816402032022092000788200800c400090300e2040804115988804003100e5483c1c40881d4024032940c800c00050010300d0050b085102420494100000c0030011520201810101160038020f080c0021080000b550f900107950011410107a000b040141007548400b06203120b555800c40c10b0000b002c40c414402c0d240c10069207940a0807000686120106900081c606004140c81c588540038280c0c082510002c20310840759485ea0100003410907003640c05050340a900010700300b5445000c0000001800c00701a803041d045980301d00701c4a540c03403400c0e04d04042100c45405841007004401d100301f100307a81703c0d1442d250703108508503560700031411071001000260000703400043c0007610245001080200000c05060294441e441d6900c640c1d84407031080360f02400c0360102400681c00440c04010b994001e5220070b6611503e45010114113031900091501c40d800f81d201c4068031814580c18540e104401d112180c05001c040394110f003450f00d1a00020494084c001e006810720162202003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 26984673 1250 26983423 26983469
    0xc09042a080705120901050103060b030304210f02031005040605010e01080a23030a020f07090506060403060e0106030803090307060c080c0403060506030703050706020601080709150e060111070915120c 88
    0xa0703800c04084d0006000d2620b04441c0041c041c21003031004440c01703410042135800a25010082d0340a0b100414294451079045402100e8850020041603502c0202240d005001d038074184401c01d81692411401318072030606203040e00403501c05030300600c00c0e0074211005101c0d09101103400340180b030f0056004501042c410a500d00b00d000c02111151040c40001426441c107a004103c1d941c804801c1d00640b89196640d00d440303400c0e02c008403804c0740e00800400c400c1c00040d0380c66000d000304e400c44800004500351a030383d42c0d60840c2d0041e62030f44c10b5540003040030b40030010240640c80c2d803801a450072101d9400c1443d422403080c001c40c0002000d058440000030081d03242004000d0045801c030045407041940c64070003945036102030203002c45c24080c040000c50002d40d07d01417003100c11940c5030810455881c0c980f0102c480400601440d04100b020b088011036440c08114540140004100014860964a103440226809640800318a100800f4001e001c07403203140c141012580d01c00d040811a550700503503 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 26985923 1250 26984673 26984677
    0xc0b1308070509011e0e090f0f070b0a0c0302010b03010c0914100203030604231f0803070c03080304050c091501020c01020606032e0c0e0a0801090b010b1309050c09042a080705 77
    0x2095903030707503950100802c02e47e0014032a4041220f640130380d0310040d0340030704003915031080f07000318440ba0b2410801e811079644078214001c0c00e54001d1000242a900120009003903c10042c941d400080340090240510703002001c0840d2552030444100004400c0300388081d4980c08000c1406103d25651950710079401400c2d01c010342401c000704962050340c6064074240c0041d03003030382229040390321f4901404102403400004550b0610b80180c0312810483c42d566a440995000520403200da001d0449004001c0d10350994003401071040c4400c2080b0180c802c0c0009140c500e802c1803060465201c40d0512640d520040746078100045111139407403074114a5014405850704e12100702d00c004e0700e407010b0342807032544c01181d00c500c0d44405c81c1c0003690103648020701d509a5101010290072403c00c0c10040000c104123000802001d0f4011030030030721040c5e45038441021510700b2103248480b10400124100c0500e0710f0300c0b80340312039403c41030400f0b040c03548070794003481402200e403500051050a07000b1a851300d001c0c2e02 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 26987173 1250 26985923 26985929
    0x609290a0b0706020c0c0307060207090f0b040504060902030105060117010306020a0309050f030a080c040e190b1e03060105060f030109020702010c060e011a031b041104030c0b1308070509011e 84
    0x441907520b040300d191000082d40020095651030040105901451801180700011240182d0081825a00f0841c4c0a4024802001079510140d910800d01c1c0c281e4481d030103014030880c002c400010f8814500c1c0141030a441c2c0040007581000300328520701c4100d0a0110003681501d4102c200103860300b4200710140d005001404c4040c28500c00c841c2c120380042c03000030081280c40a607903a04031440c0c960071003180a901550241000200d0002c0c0026003a48020440d80b031400a007210110303900c8403c002065035007681460000190040841501450800308503241c01030409440341031408808010b0312441d4081800f9102d010b980004e0140d0542e84600c25416900d604418100009801d141d5982c1c002c2c400e80a0f02220603003030f208101106d03c0c012030518050390403c03505040d012410300803c0f0060080e8046030183c40c6040c040030000c1207180350f1038800f03010311941d6249d4644141891101c010103a030301c0216198003044043c490b54507000001411521740e01d000354145092143c2403040342d06030b50 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 26988423 1250 26987173 26987189
    0x110d0f051b010b0a18060501020601060f050d090213020a030605090702030436020c0c0f0f010c0c1715090102071e110d0303020405010e010e03061b0f0406080a0609290a 74
    0x2500410303464841003903d01740320100c4000b040000e40d034800590710b440091140001080071081d40f09402030185006094245618000044103685540001c1c910211400c2000000ea4049107000f049a010b100d00340160404951003030291411260095880c82203006a40c000d550000c1c142c40d26000c45201e050f205060003042240184007540e52500035000144603104501c20f001c040f080c0ca04000e00e8101c030350000a080111500a01c0d00151444150041c044800d59000c040000c3c50000c81810141909240c0740901000e0b544201d01d51074080b005030040900d039104204480000300103040c242035212645486c021103400c076050030f03c1c4440e00b10360100c2e000000c0100348010194140d0041c820744109891340f004071130401d00110381f04000d880300d01d070305640b0030004a100402508400c0760628040702100d4503000302010408004d4110303602400109101ca400d000a59091f40503150150003c05010461010b058407010b40307a841c1130844105081200300392820b1600d80c54640c0300588414 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 26989673 1250 26988423 26988439
    0x6030d0311130914070507020a09050c0c0a0807021009230604051003051006031107020f0607021e090a02180d06060803040305100b040903090b09040603060c110d0f051b010b 76
    0x9000101c00303410a441003140003404400003174031490240d000e40c0c614030307000fa000070307041e6050000050003040302030041c540d010402d026025000c4410011540200e02c0b50502584605480c4144514400f4a00103881030140c0180b091014580200508040b00c04043c2900700b900e0880d0302141d80c500c03640d040036401c00e4004005400013a0950025402061802048007040c2da444d0000c50458500c0d00007021280020005100540b600c40e880c0c5240410003031403146003250070390002d981c0d0307144101c1c201ba249814400314501840d0010340c50790300c00ca036150b095184c00c00741c501d203101d082c0302c02c002e0310b01c260b4030000c0e1081884119070002024164040859503180e40301e06285507150300b511041107000c4d0a090001030f01d030409000d140d104960546500b090b09091202101d450303088101c241d030b00030303030380c0d0b003001002c54028040c030180020244c035094107c9050040d0a4200f42c3c44980c03180c240702d10102100d4855500800301d85110aa214a0402000cac200a03800c0c05080340c0b41f442a440045 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 26990923 1250 26989673 26989679
    0x80a110f0d03021605040c0504030201140d060f03050d030506060a03050403122417070b0a030906050703020702030105060901050108060f01020a0c0b0903190f0204050432010e0606030d031113 84
    0xe400003210054240300c0341010b51712030802003a6440b800010000072028042080107500504850345080020400d090504416841010443e5241d50101c12000c010320300070130902c20140004070202c3c81a28080c0f1251034010082215840303400d1090080654800010303050503c9801e03192561803c1c1217045c480d079150000307840036101682001088030000c0090000380680709081c130024000803000507054592410036072194903000343c90a1814191200003043c00a0b0051140313610800b5079450040e183d40d446e006160844400500040c085c00784d410050049a030008141544120301b143c00c080230740781110040707040c4040e0b040020042548104042003110000016000080e426400c640c42e10245010320f403000000910040d041030082e070035000c0035081c5178011b1030b4814040c075a5010186481210544038414018600308005c08411000900920030700510311a15441c2c4000d200a040000000c0d131242d0a030020241855a00c1c95140c40c044000741c190784d0301c2001c41c6d0700721003000da07 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 26992173 1250 26990923 26990927
    0x10e090906180303060901090c021905030d0b09090a02101b0b07180b0306040902010c080a03050a0e0109030801170a0f0305090a09060b07030c080903120d0510080a110f0d03 76
    0x2109031400e1000107000603103202e507030030b00209980c85041e00400301e070700c26441c245024004000c00b5803044114011042c210300036440780c0c010904201c0c0320300015541c0320b94192a40e0200e80741c1c101c9c1c485c80b42c19074400f400b240c450001080e111007a012a404030b047d121a400c160b500302030341080300703120340d0a510303d0405101841d20720a10520041d203512807600080c14803140356075154002d05004500074008070700c15003400c0d4020040303a0720605049440740016204c221482c0c000c4402c0074006610b5800304564601d1a001d20701540028400030b1040b0019a079002d05025030502444000c0280701210f0703400d05008001c40142c0c0d80d0000c0861540e503640e030400038002e52005420030300071900e4400c0010003807640d201e48401caa045541950804106030383c101d0742518140d80c00c0d503c448061203c030100342d800b841644c01508507800c905031341d584407000d24410b654000307020080101d0340754130400000401042241e00d06500c0840c0c0000803c51800280f4007920060321950015142600c90702016 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 26993423 1250 26992173 26992183
    0x8030705060f09030301030f0c050a08010b03010b120a0201030b04140108070311090708071206090509010b0406090204060507080f07050102030106030f1407140a031404030c1202030403110f010e0909 87
    0x6014805030340c010364820051801d0400240c0743d4001ca40d10400041001c41c1710070816401080c40b400c00c81d1170182d0b0b04c1c1c0005103100c031190012845d50755a4040d250451400b4403c6100ea11300c1910800000b2810158240d11280340342e40290600d0b4807801d8106042da555400207440140ca0760141e85a561612403150ba40c2c0b07103902045480219000300c00850303240440601c0c1c4115210350340c00e41e01d0f588a00d009c0360460740c0200134080300d580798400482c60780070130b000b0700380314412070000001e4000300042080241d455a9000c54030f51841080244507030355102089941c02904407400c1c541c0d80c0154041c03480903100308000a4115403000c0300206030b4960541241d031070704a00d042c080c0110441800200e82c004016644003011944070160700c1d85c05084013010f00900780b824203000400102818595915103070844040f000103608903941c0003040400c5d0956040c00c04107100460501e419543c034040003034001d01c2c0f654400e4214034840e100c02da00c2844035024450010308220041d0074640300d059614 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 26994673 1250 26993423 26993437
    0x30e100c0906030605060307050a0302120a0b030c0619080403050c010501230f010f0e03010f06030b060a061806050d0b060706090c08120316030b060406050304031701030f1209050a0803 81
    0xa4814400140b0780c1d10a0080328207807000180342905e15180e10800341c0d85540010308080a00d5001e01c49410105a0618150b1080400c20000b1540b2240801058100462030001500c80c40050080b018215007442040454400078102130030369880e41d00301680d1a000d580da103203525608240c004110100d2600114403103d00207850f20010101410812508800b560003507400200c880502d988900d00c698400380884101400010b85408040505800e071211a04140c1e800c04502085c001c003420501c0110303004022a1403c0da030100c050602b0850b54000d0791040300d04000c1c010a9403142c14445900c0a4000d240007014039035100541d16040001d40000541a11907030706d041c00019000305c000c10140c080d4403c114000e40395980f00d012505200354038202210406a0710103801116440f030500420141c051074071429102c1c0781c1480c00034140800030360f24101506044004000088903a05456400b0b50312031014124101c1c080001c50350320f041d96206660180e44114001601030012004020b1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 26995923 1250 26994673 26994677
    0x3070b131403090307050a030206030610050f070b0610050909010e0c0f0a0f030e01020301080c04020c03040503070e040b070c0b010909050f010c03140c070b060d060b030d05030a0b0d0210050a030e100c 88
    0x3011b80e94004000001d813107031201030340000c402c04c0014a10718110010140614290803e41e01306151014009120b1b001328208075500c10280051042c9480c0c0342c0000d000b11469890300d1860f141c0340c2000308186017410300c0341200c21441b02c1c0201340d810401109a03204288400e403125200d05c0045802080103100c0c0300742d41d001c03c0c0303480c080180034201030003100c0c10f172030301100149044840601400000e500030085000d650202340004a000c0d54140000030003000c4060488502d41014140342425190292900041c029a15440300000c0d0b10352081c00d0442c1c03484080082c107001142020740c03c10f511340c04032003015440c0404c0600d0458050380103110106111440013629075560304101854461200003402035842d4000107400b528101e0b011045040c0b1400d00420544000700100345010400c81442010a4002c8100000c0410b10f118801400c0c00031103451f211041290081810101500080d07420898009015022280a908402da0b0000d018049070360203800e500450006215803448140 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 26997173 1250 26995923 26995933
    0xb060d050115140307051c0501060f08160207030201080a090b0c040f060311040902130305032107030c1d0d08070b01030501050105060307090510030906050405011d01020c03070b1314030903 83
    0xb8503900c5200e20600b240116554a803464403540c0b001d4134660031400503a50050850300c9915555502406818020502522000f03802c1e4810000900401c40040400ea00004010b0718a1b03c60340d800a04403048a80a01b006c4009880d03904603000a090541d202401110040e401c0c00351b80707205000108115001710381400506a00d4070b00071415034280264080f0010820b020900a044859000304000440d069112400941c0c1c0c0e9541070454000342c20742004201300b9582000d03122039080400303a1042441c502041640c007143d002a15007228a0040c9403038022189580603151074030036044a203145c105181e03c1e12041a4074140321190000d000071035595080400001d501d06042d4280c900401b00c07030300c804c40f1070f80c1402c06001c160382200c4603e90402d80c0340e01c400808940b840c480c10b8010790148002107500100564072052401010840074181ea2040100c040906004001e5a04059102058108544440780d501c856490f080e1009040582030300a14054480c0002c01403903100c10a9040e90 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 26998423 1250 26997173 26997209
    0x106030f090c05060a030213060e0307050907120b040b0307080c0a0503010b010207060c0602090d03110d0e1c02040f020c0703060506010503013012030e06100f030b04060b060d0501 79
    0x110946148840081c4621070005043c000e41c070705500a81020001c516005090104902610701150019440030b008201c41c100d8006850a051041740b000c0d09050318078040390304081c54010212029920a2800d10f43d89028121040e519030304079581240c001401c03210340e542c80b583c1c2a502d4886c1081c220344503507031042c00002c0b079003018040c1d01604107050700038115640c0340c21010780c0d2900c0b016400b1513019508000d41c11065441c11500c0080e28000c0c8d8801111820750170641d4904031a006429051040189001d4055a1048024091000e00036803a1811a030700d072012031301400b5040300c1c40c4903890000c207403416080000031350302c4200c2e80103120a01c100c0c0c40b00001924144020300070f04079500702c070b8031860010041c00b40002c0c0180d00e1469460183d201551108520400251013800000c1d8030381081e00d41c00d03d82040502d401905248200090610341080d039414003205110003442c5000c40c00003d414000d0b1a400254044409400c41d40e858220044040007410300740201458045580001 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 26999673 1250 26998423 26998451
    0x8040507081b040e070b03061009080d0e0102010e0c090a02090a05030307030e0315010302011b03020f0607110c0307080c010f20030a0f050a120b060702040204080106060f050a020604120c02030114010603 89
    0x1750403030310b80e040017a1458640b00d082c046c40454540700ca0741400320303503007002a015000f005198a40c2046aa41449201481c4002802c0da0701859021050307a101c480c00d03440300d960f513023001500300700541d500503522410030300410740c00003581e880941c1c5404003040a1043c5900000301c007103880e804070203840d59000125822840300f81d0a001c040e0015912414821201c1c000d005103e140c107020f8012180741c1c0e01da0a880501d046002c44400c0005103001d1401c0d20391743d20420480c0380040d8102c000e4003809040c151601ea9030b995444c0c3c010304005051003102d1003070740a141c90142060f8401c0890030b89954038085c803690395000c40402000100090b807a40b400761301c40c3c0c050b81c070311444e01ea0310043c02c0442101c2050190a00c40c11041d4044010007003000140c7d0340b8401032000b44602400400d186150800c00b0b4420300c0f80401580602504210300c0103060390100360684d119500120112080041a100322103103410018000d41661030503c44915104080c0e4a00d812100c1c00e5405001030b01c085a28 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 27000923 1250 26999673 26999683
    0x1060f0e01060804060603080c100e07060e04111201060903110103050717090c1804061503080307030f02040306020412020307050a050f040905010f090c15030204030b01050108040507081b040e 84
    0x1a8000c0010355801840030a100d02c11613600300307001d000c02040c0d2070340701d4032001d106074000b80034042d0719404000d00c0b0f03d0340581d600841c1c400a03c910040c00311145010b2003c2c0c2030794841e80c7d4083c822548c0f0240c07072403803615000546414156102034010250386880c000340087c44140402e6440d08100c000c400d46940c400d01500e4481c1c0720720368440260503204031441c01119005400103140780910348408249031503502400c28020700009804000d402c0c5810203004644e0304150701e0f0164a130080c002e0000c00c0a1108882d0400040e1600050703c0410b20440c6000303010350b410050420b400004d0019400910300a00221140200d007602c9040d43d80c4d108014042d00700d841404d40068120700d500c16146040e034040040039018400118021403000440c01c21507030224021601d0303c000700c505210110b038101800b0152070b41c3d070404500d02419a191420021014030070703181008540300002c2c0130400284040c0c0c001b4000402226220039070040c00d02c0c0d414100c10b4010b8042c5207481c44007001c8050000e0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 27002173 1250 27000923 27000929
    0x9100507092c070c1509020d030503040c0f0303030c0e011e0c02030102070c080d0f05120a0509210c0c0402090a060302070c08164e08040806010801060f 67
    0x1607400d600c0303140c6000b03100c0080c903101c100900b03401c603404401e400100c040c0c6114030407940c654803070700406110f03e82244800c0e50451003200561070b180f00c40780103869040075008000d826040c255100d40d128a000880003134283c000b4890b800d5208000800c141d0075810844050645849000300c58440307000440d0044e1408002d8801009a80e222120b0240541900c080d81c5001030005880e250194a524481c414a41d10403242980f00001001c0101e500c8040e4508201007450708030b20f840c0a243c0300c000c40c0500540341c0307103800743e881012494090040080141d03403031001308001c040e40d00c24a1f50360001d4000321001c84103405146111710040c42c141c82100c00941004120260503810300d4022402508440400c0350180d4801401040c0b02c1410000402505103000500c00810304200f075000744401d0082001101810b031a0301d41090340c581d100c04032001c8400b024160003003031200d500200720b0700051001818525001a0104000001003015416941c1440007401160356490b030f140c21100581c4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 27003423 1250 27002173 27002177
    0x50a080c030d2912030906030408040501020114130803070903060c020a02040608030405131a030f06010302041404080a03050705130e040218071707050706020313020406050a0f06050f0d0e030309100507 88
    0x21004160718207210310b00b801c0c44c0100d00b22410240b00c14040fa602d5401614240c40700e40380803504000d290b81c24041c25041e0024490080700608210030441480c4141d410000c10302d44001c00010303451445102080300441d040603090010500c18500a9181c1c1000303101640214117240c0081580d40300041101d007210b40103861201c1c444980d104100091401c24400d031807100c100391204000359010002c01f4840c12021002c0d0856501d5031041004484000005642d01c0e03001404000100340f061096459420783c1e41000305a40c1e40b42082190a80f1070f4001400c3c08601c00c440119000403410003e0b8803451080d90610541040c14500003203240f03040328103c0c0051a04018201d01581c10401c181d001046030900074240340040d80c542d0240d8004940784031120414504040540c60a070099100500081e256032107194200007204051040d540522018000009052490400180304513551401d08030700030411304108100907038032544146c46200301e51140002010f01c118040c03251a02500c129 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 27004673 1250 27003423 27003491
    0x607020c01200601150305090105160f03091704030c05060f0301030f050f1516030608030405011803020411030103051606020606010807020a050607090f06031103040807050a080c030d 80
    0x40380115182100a030540c85040c040049400364074008200d418060902c40d80c101414500c561700c0201282c2c0024241c0c00141c3c101401c0c000d4190b402d14941846400d00e02d03009014950400f07082c1d02400c402d0f40c0c010040c20709a2505820705c2448000740003644e200701c20340b00415a440c401c128650240c2da04041740b404c41080108000b4541e180c280d4891031184003540c1c2c034100c141c103800e418551507070680c051100541e0300f0042d614001002000100310355003401c101007410404565564055809110306003ea007442620140c04052012001540d0003002404003140b440302c0f58465400a10084030300c2d00c5110704810300041e0004818003500c209500400003070b600c12004480c00c09000e48101c0540c0103030b0400d030001c110140f1a6612401c03c0b40c503005240b502d0040130310b9402503154403400c109464003955504c3d446400086940154118400719156840c50501da07043c4003180301c0090040301d002900140000002c8003501e113609a4090400402c0301c181d8500c07007060840300d943c400a40351 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 27005923 1250 27004673 27004693
    0x11031b10050f040b070212030c010212010b03040309090506010c0501020d02070b060a0b0307050a0c050a03030902010207080f060a0207050f070905011415070212010204090c171f060f030f0501030305070b01050102060702 96
    0x30000608000c600007007d20886884103202581182d0102d10b91903066500055424000d00442003914014014820414610f140c02e0701c0050100340c1c140140c0d00290389440c04500668070641040c1821078000b4021940e90389564201c4c0002e5005c050221026206800002c1d081e1a180140f00100c519180710a851655280001c590b0b80d806541b034001440380d20b800c7d1340d0100c0c04c108050203e16200340c4000684280701d000291410b803003076100d90510b41c050780c09001501004200182c005520394001b5031641c0c0689401e5003016446510311109104201000919400070b8202c64102c4441250003e541484482404200a01e00c8200741303103100c1c1040030400606003e0341d801c00c2e001810000505054803503898400380e03920a40c1e4400069140913000f60300c00d11181030725401002c0e04013002e1458005d42c0801c1c100500c207100f180c043c04101101466203900039000f800c41e110349188100150340c3c5901d0301920a41190605030341c64210080040b4095000151300c60180b0812f400814444035 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 27007173 1250 27005923 27005939
    0x501020709050606070c0e100e060609010c110d0c091a0a050603071715011103040302030a120504180903030b04060303020303061201060e0106080702060a09080a050711031b10050f04 80
    0x20003e00229002501005030201141c61011418082e000781e100031034607400e1494108103014503d030003048014035a8003e1089581d50041140d44225003820050b041c0704060070b1001c0c46081d403c100640140b01450407400f04650480b0300400d86410200420020740f40d5009048010440c02400f50408060282070005240280196502401a00e00f4003011292212055800e08003a22540320891211540425542e00712035030106c400042c10096040c50700e10340001396035802c81d1780050080c41a149024840c0c81c45402150b0146c1b5000140d407c1620400030300138000c003141c080645c0002d281070041c00c0e00d072a044c080e607022640c141d1700441c10742e1964010042d0b00041c224038810599640c80002a0340310a45030310f05c0c002c00c0307243c8540a141c81c00a40107807c0c03090080c040c00c1c0e481e180c60110400508400306480c940380e0546403e94840915140841c0305036007000d1003c3d49882034159240c1c010b0700c0b080309603c0307824082c3c07078840c0210f59000040d02c032030192080302d0352104400d0105200f0b000c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 27008423 1250 27007173 27007181
    0x106080c0a0207031104150e1605030412030b0303070c080a110916030c0207051302031f03050304030b370c03060605030604020717040914130f02040e012315010201060501020709 78
    0x360000c10001d5047c0071541101101070403980665038075103140d8200030079000c100080403d0a052820014035501d0f00e5907424100490040081061540e100804030311518108203481c2c00e203034028561841d00d522a07412568403044a201162140340110701c01c8020304160504900035400d501030070b1207480c01d001003070300a46840d0b5044021413007450000103c5588105850510003011000182e030f90a28442d019420401c2c41d1441c09144648041000003e00000884003180e0704411000c4142d15084468140712034102941204528042004002c0c1900b10603802c441001800003000340702000a8246c09640d0180308510100c3d00c10320010f16141495001030003124410074003d0b0316010140d5401c0040d070460703040f11601c1030391280c042c0c40d40040c0440307803a00710100c00650802c40d2000c0d85c2e0100a070000c143c001b8021510b40c804130582940c01d410810441900080700f218015a90100c15074000301156040690b852002144d80c03554018481d800c20f55006a0141a038142007120160142c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 27009673 1250 27008423 27008453
    0x110a050d020108040b1b071a06011403040303090305120708070f0305090a030e0307030605090a030f0e130b0d02060a0201020a020606090c1909080304090902130510180204080a0303050106080c0a020703 88
    0x1e480e036904c10b400c0480820000d10b500c80c800d0b003a07048100d44088c4c0f05413071044010115814802041c1060580c10417007011385c5d61141c1d040c0b60208071035100381313400c58150040707440708044c0000e0841031040c1c094009180e40c3c82011641d5507407803088040740c4128107440c404c0d01c4485568000800c1040400d200d81c80032000090003400322030069540383e0b0390300100c400803980074140b6007120800c80100740c4c0c03042c10140c0160540c03074048940c4d030308030340001c604090382100c0c1c600d031603500d070504481e0b9110890507408540e0010704858a0710210320000c1d01030350203c40000014010f92000544506d80b20341494040c5130284482e6041403a800707152620700d1001841d11090108a040001c0c8680c41000100090f01e0310f02e40c0440d940b681481800780344801c5c0c5082228103410042003200543c08000e240d02100c1c8841c1c0d40d0a00211ba03000000001c0c4540c2d08425001c2c00385407054801d16406400c814102c48050b510013100e41c1c3e0b83d003004030340c60080c0e1030b6060060300840010008910301c3c040481403 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 27010923 1250 27009673 27009691
    0x803160201020c0609010c020601060c031e030f05011814010305060a0209120a0507090f0212280908120105010206010b48070b090609060706060e0103110a050d020108040b 75
    0x240008103d141440c144040b44c6421143e03443e0800c69000b1a41400a103005103040d0419107004140b07650060051003003503803060340d100401c1c05c440803001c1c8603812806000014a00c100813a503110b079400e03000b84034820144140326050003d4280030300a10b082c600d0480b5000702c0540301980329280d17080c02a40c04124400e601139128001501041003d21119240510585c0100401780c40d00f21280d060f2848101c0d803c0d801c61061001c0c080c4200c00c0001e16030300180301070801003400180003003225520080c240010681d85000d5002c010400a2030040a0105948442c18000e13a601c0d001241e88110900415003030200c2400041d5085d07410040c802400d106101c09610811520b50810745440d05020724090384201200c0c00c100c8000701407020f07101602482c0c2036549413044c803002080c0c40c0d1088804607805014009038070024401554812006410399049007212541d40b814405d01a10001740014842c42025600103207d00d040307200b0040d21581a190b0100c03660741d5031511b9144080003442c0c081 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 27012173 1250 27010923 27010927
    0x2030606040b03010906030528030f02071e0306140103170306031009030203090901050405060f09040507050402070309060801050a030f020d02011e0507050c0d1a090a0602120919080316020102 84
    0x42e414407501c01940c043c0542c002d0005401d451410198600480703848110b08484000b08006140944049144220354250400d564203660540c0c00f03d01d05805580710611441113000b03c00a0010b601036000120783c01850b0a024102c00c1d6031000c5001c180170300c03009041811020301d0b0b040c41d143e10b03005180e03c2000141035038001b000c02c955071000e86402c20380450050300006104490780ca0241f1041e4054081581c040025107480d0010501998441c112075200e411410000f4040000802400c809084050400d41d1540010301e00508001e001e40280b20216014400101c0e0780d0420558074022aa0855419600000039030280001000d19010a904100105c0f6600190b41251480d0440349261540c615607100d0f05420083e0900c4000303a003003441202109003034004210010301074100c18080c0018180c2680303810503031500e00a4101c0c0010700030f5001151300c030382c1a140c0f6824944542da0035015510101560b0b44641880071404200402c07021040c00410f485048410100a910354a400018 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 27013423 1250 27012173 27012179
    0x10c031e05121302130e070801110301030b25030902042408010b010203070f0b2503021b030702030a06020307021005152e0c030509090709080f1506040203060604 71
    0x3a0100c1100e1103628081a40011141c0e48600400405540002c2606020030054001e60000f403142c2da000c51004480c1d51110f010360380560b8140310440003040c030741008120994500e904100075170824032055400c0380b1154006880c140300102088000300e0321304500e0241e41c0415505400402c00c00c1c1c81070760080d41c1e440e401204070380f402142107960b401b45401000300c185812040d0b429130364102c00c994115001800341c0c40008000104100001e60f001040c1e035103540d2640035000d04942596042044180807505103181d40b40c041d4001c240001143c0d010038a03c5075104a41a540d10803401c0003509075000104820100d08941e004d10380008040c81650790082c04a941d0300280c0b90107a80111044503505c2820f15140382c81c003d070b00d504d007103003005d00086041c881000c0503854030240c1440c0b0074045001c007030b101014850300c110740076076074000c2c505417150a203810018a810120b006034a4240300d00e0303611071401400000d145c240903a608000705425a9a101484083d410203020a608441c0c280404 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 27014673 1250 27013423 27013457
    0x1f030b1306020a0201090215090105180d0507090b01121e050411030106031b0501030605061b0a021305060907020601050a06050903070801021b010c0302070804051c0203060a1508060c0405010c03 85
    0x1031910b0f501c10b600214543c039a031700401c10110020451000f1114040200b021180d070000291803101100903646c4400c0c00040001c03a800048620004005001c2c0d0980800e283d4520390001101450070b0340c0340d5601d24022200e41d030899110425000207200044a000490103482d00581c1d403040c899055070310740490034404030307017520742e550800c44200c04408014040300e210320138098001e000910741802814070300310114a1600c10130000d40304c200c99000c03500c0d01c3c80004002c4481003d5003d804048040c807401e200c24000c0c4001d641c540d2040c2c81c0c01c4080f4503950304c001105410b948004096a010500d007042c188c07000e44c06480c01e1130305401900e4000610050a2004d02220341c00280b20450030701030842000e0856000442c0e0006041c41170200c10302203200b04094805543c41600e1449040c004600c490181c000901002507061013007004200c1038411581241d1102e03400920892521501c405585446440440c2d5a01801109000402c12503100364000045540a8100070700c52488074215 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 27015923 1250 27014673 27014677
    0x3060b0a030b10030b0a02090d030c05120a1d090c09100e0a0305010213060906020a06020a0513090f180218100305010e010b010801050301091106090a050d0b0604051f030b130602 78
    0x3c0d0407a20785400304106004481034210792018808008518110324040010488401c3c039102400f0003006050360820803008008010f036480310f001d2540d031a0314045100500074032a500d6078100c3c203084c440c41810740f41032804030f5034041c2110703440c5641450228010b0001c540380200744a820032440a01c040826200c1e1485000954018800540ea0b1890100134000d40d01023903001c80c04000c81e03c0010080143d0125461012990041d030150b5108400b03082203810780120640059189590100000d401265a12a200300035071540c3c1440800e0704614427550b44200820044e4202036120b64440300c5030405030245038840c112040c1106001d03181d0712030301d003110f200002c0c1940316903407031090141e950781200d8460700524084000740488034080c0c0e1803948112840c81c4444c00742002051038402030761030080040140002410201e801510303070412009001e0103403030040c095031500c4081110b502c00c100f00d0170380c0400ca9107121005540707196541341d401078000f410485e02c036140441c07810001d900340c00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 27017173 1250 27015923 27015931
    0xa061703070c081b13020f0a0e030d0302040e04110102030c150105040605060405010f0e0103060b0a0201060e06090402060316030f0c23180603060d080a021e0303070903060b0a030b 79
    0x454440700d291401e4590718940d40c0041c1d0841d88001c002c03a0342e551200100900e004001e07158801400349451058001c0e001b00d0400a014400210310054030340d60142c1460100728080301140c101454a110660072407045000d040c0914008200050100381000365002a01c0010701c1264036000003012094109a6803603c3d0842c01d41c6150010801c43c0303002d0148201405084a0a518142c035000001c0c1c40000c0702c081303000900c40b164900741620707070281d03011b84002c04401c440305035180340c1e410780280240020b01800b40485103e1001c00c14600340f15141501c5940d000e803020b41345450788031080c00301000081c032200802d51180c00d41c244400f4240150b09091041e61212070900c02e94240b84807007040301c000704440b088170500c0303400034510100101001100e001e030303410365603030b103c030710200b00740300ca0042016140204c005031a00700c91750700007090001004d41440b0540e81002d8240456201d10041d5049000148888400c1c40446d241d075119914840c2c0082012021503074965036400200c400312 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 27018423 1250 27017173 27017219
    0x9010308031504060501050d0f0b09090a050f010c09031502160c0501020f0a03020705010c110411090a060e03030406081509040303020a0f02060412050705070b0d051503010513020402030a06 83
    0x20040c40910b80d0b02c0c0c0d5020003209000c60302882214100300009119010741d400750244541c40781042550107a0b590301c10008000d016000024502e400c8100a6607a203c200044a0521a00350340d40c602c842e0602c6841080a041d07620605a6451900c40c0d4003414241c05849014580c03c0054185909400c6510650315100d40303032141000d031a100001e81401c651050003281500810600d600080e80072138400251607003424142d003c40c003941042014981d17034408039502302e480d00140c42c1d42002e422001c1c0995010480d10000003e03254002200d400d0310425035290554070070700050000c6c40c081c0343c8055202800901040804014900080c400070056038290003090340041c5182c02d951340810401c80c0f41c00580000c104a040c00d0f43d4100c1e22034104807210040201c046804410002e00340000c500806041c061162544080e1001c0801060151840f016802600114502600741030107080e10460101450602d8180240c003403002a60004203510007040d51010003003031203602d094000ca5a54014 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 27019673 1250 27018423 27018427
    0xf0303040f02040b01050a080c0d0221060a06110604080a050c03070b061c08040b0a050f0a09060806220b04180501020301050a050303030c07030f0e0a030311070e01060e01030e070509010308 83
    0x42c01408102d440d60203145040040410100900039000f03406560010b1030400d580303944501e40c0103440001c2c0100c0c060808001c1500c100a620b0101c101026806000d040b910707881005d60f5460165072043d000035800340c2d103421510024020820000107041c0f42082070401520340348007284660705640c440b000c00c4400c2001001402240d0811035808010f9001140805110701c0c804e460fa03107440c4c003031032190341070f034210020701d1583c8980b08105850340c1000c0c08501c1d9172250780301c8030090134a0040d40101700005544078001202441d122421800030030044a618881600860f20b110181422080d60381e0401c0d141d00c0f00e4180601c07541041c50500c0c0c003900c00184c403941013100300044a8a1684054403e5009005010582c5000001c80300100d5050400d03100d100d00302070007507a000781c100d0407456200c1c1380c000001040c5604458850030021400c01603e100c9916200b05510030b140a006607400a5426296095294007070303030080100c8030004044500d002d0382d030000200500d40036042140c0f11400 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 27020923 1250 27019673 27019703
    0xa0c0b04030305100602030a02030702090a0906060b04080c0603060a2102030601080c01030b030304081c03140109020403140d0207140111030c012c152508090d030e06070f020f030304 80
    0x315420b40c4c050042440a50319041c2e03134000c001e583e4001c000e0080c0c4140d407090081084454982d20108107242d0042c010300896035107100095094105200b602c006000d2000d40220310300d02a401c50744100c0000380151905818800702c608c0445d03c40d2022061000080004000342e40c1c10402103009014440091004200600004059518050105001c1d500500c400d120110f008100a4a1030060f0184a0010b4040800c114041c1c403c03403102d106030b841c0c40c50000c41e10380041c3e0000c0c0305a80c041c0310b015416022031410680d9a240c0c86146600507041188140300d06150314515001341e600500d440c40a0111100410f0304540c08224101100da5441c06200381103c90480b040080910007086100c00c1c040c040441c580365034150503c240c54030002e40000790803d922044804000312180090108000c080d4400380640e18103803010b001a04c621030081e4022486400750342c03055101140a004030b80c0766a040bc0e81c51541482c1d204003507000700440d501301c0d01c104101031440786000b40034171100000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 27022173 1250 27020923 27020941
    0x2070203010e0105090c09161b12020601031e020904020f130f09170f19050d23090c0d0803040303140403120c030b060306010e0301020906041805130201080403050a0c0b04030305 78
    0x11b210800c05000d1a130311810000c102421040d462554031840c1800c1f04030301c0e100180751401886803032005000880003880508001d50000340c00d0b0603a8807590100c0c00802c00c94022200f000c0500800070350115130b860001d0014109441e10740140100509075150907100041c200742607551181c815540e280d03443c1481c00078064458928905c400380140c900d0714200d80031841160a11408000d4142c00030f007a0941d41d8030f60303c940704136442d680e0351407420825440403045040d03580810351a81e4049000c800c02140c80c01c80c011810304424100103040c1c00782120341c0e0340c50042c0307508020b000303400b40b42d0f64100d142440940304a0840c4241d10135a038512a0081c0e80c4110011158003c40ea602010b15181910081d521410708aa400c01000d0070030f2075000c81040700190280c40b40c40c1d4240e0b080032001ca0006498008441e841e40da11501450902851b980c0940341030800840f80c2000c0d00043e04840810f01281c0240010400c408942c03a201055001c56240c071041e481d026281107001a60f50300401032403207 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 27023423 1250 27022173 27022183
    0x5030319050f0f04050703060c120c02030405030a030804140307050f01050a09030918060807060306030c08010e0307080304170f0706050f04031e050903060103050c09090a0206041202010302070203010e010509 91
    0x184000c0410015410080320321006030310002d003800344100031040410b0a004042251100540d800002840018004d0400812200445c1c2a056140d4103029002e440c40e40003009030780a5601c09002004880c8640d101100e110401a2081d9000b00f0404040d522003042031008001040c050801070090408203845c0ea401c64000915108180341303031a0381e4400180d40079072070400b03c4038810f400c00f44050040394048002d2040380d00180c2c1c0d40c42000000500e2507010781002040380d02400b1110803043e601c0c850075090382c0c0317500d5030b0800741c1c0c004000c5440042c480b40061074100313010b6456425860420290400b80390700000307040100b4074000c0384280401c42c0c130b40244d82d844440d030b020b14962814903a602502d0f1b40866410700100b010700d000c1030400c0c0d034450300649150020041c12a82c5e00d596904143d80c440c2d550b000624024100c100000320404800a9441c11780303940500000e00d4245804d403080100c80c007502040b41015000c105800140e5402d000d0501043c4245000103020305106008520341 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 27024673 1250 27023423 27023461
    0x503090607050c0a02090601030b0d05010b01020f06010e0610090306050c0403290601030e010b030714010201060e0112080d0b030a06050f06120a02040c1404060f0807051c0b0303090607050303 84
    0xc2c0811031856000d83c04600b900c5440d0341907038120070a8407900c005070f01400f000780c815500805a006003409108054204000c0d402081e0203641000511007c260340311b4400340212072000d411100891300e00d052501c0c00c01c0e02c52007640340c00c3e00195100c0e40d82406035482a5050304040d2400306061003400801d1248042da6130600e201c141c45242c28090080390200003c00d454185a5155858a0110300039042244c1c002401801e45460070788941c00c144002c100c1d07410080c010b41c81d110307010800100f5510968161010802200240c44599440e045180d02280440e01d08544071100445161010061040000e125400114440c81c00c907002d2030203c80b00405c01d40c400d95009030301d00c101038000308031020855010398010941c61502041900c04036401005058000700005000800d035510500c060b003031440d140e03203245007515080e03000c654500805020b00d0100450803a000d612440725400610148000307000e40781131010340400038135903810884060b03400740c00000802c43c1d5800e501d0700345100c2b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 27025923 1250 27024673 27024677
    0xc07061107091b210f0f05060409031b0201020a0b0a021e090109030609080405150703020705041401050108090f0105090f0f07060c0209070201090b0c0c0c01090e0705091c030503090607 81
    0x800790110030300f83c0c1c08201400460040c01800400340d0241d4065000620303070b003224050706002c01400d44034060002d01d850340c0f03c008414507200205240d450306015985044d900742c3e030b412010410040b01c100c10044401c2d000ca05601c20400303403d000480d0340007030350b2103a4481c138801610351001e5020941c408001d805964020700301040312200316a00f10f004102980e8008030b0003c2c002e0028079102c00760303105680141c0d621416000701d00304181081c400038541c5a210b64251000c41c1d550f1001d200559190b600c3c5403810a41c0e290042c0030030b520455a50f80d118109404032071440401803600c1d030840e00d00751491465030700801e107180307132801003003050f40d0f1500c80c041d004020380c514060005200304003030764009118291000101300301910035008000090340002c102445030a1a01c0c01c2541a0300c4402041c07171a0107001c0ea00c444540c02008088216000c2c101c07101e4580e9074a81044486078844d03020954040b51081e110b030003039402880141c4406109484050341c03810142c80041c50240c0050107101 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 27027173 1250 27025923 27025931
    0xf030b0f0103050304060f090e041115030402090a0209180c0d0c0216090b12060a090605090f0d030e070f09020a020f0a12030c030b0d0b040201030b010c020a050d05030c0706110709 79
    0x100240f00082202c048400e0b510304903001860940d001c031005440307640416010200001400b0a004504072500d01002c000c5400d07094030009461291424001218080e500002040016800745d0040d0010b06100600a1138120b0305407070316401d00d0000e01c1c10b84071048030352000318880c802c2c030705607201d00030a03d00240014800a01e003c442001421041c1c0190a0015260301a0303021588503209211140d10070f0000751002ea1030311034204c4005020007001a907499003044085180c00b00085640840c1c2e100080c090520700a405006074040e0100d07401e80c3c080ca00c42c5140001c0d4840521103020007401e10740c00c01694908007060001d02d040303c40f04800d04503030050540840020340390f202140a40090342008504442100c50640007800380001c0e25800c52a285400c2040000417226640b1591013620208200102c1c03600440e008108440f00a400ca6040390041c400e0f880c2c082e0324412410300c2102128902640350030058100001c1c0d6003e1000300706480c1d021214450144499000303421a404e0400c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 27028423 1250 27027173 27027179
    0x60e120c0c060a02011d010507090b030403020604020d0213090303050423030301350c01090905060f040513050a0305030103030e030606010c0b060d05121201050f091605070203070f030b0f01 83
    0x19448103680441d40384601800140301444900030741003850b11a0b0465000c0f00e5402d9542c01d500c1c0a030204859510000b20400808070311500680190380c001d0360036600521540d07072640d00b445502e8950301403e80e4409908894803401400343d018440100348030f65004103e90401e40b8202420006030310303001130044420007120300001c20020035603045845100030100d801c0c41c002101c448048032501010b09030f0900d40800254581c2c000381210205400b0303a500d02c1ca07103942c4c100301000c072103056031107552003120302c145d04d003103460650091030b00180300b01040304e01a2035943da01d900d0a4100d00003140480e90110041045c10b4101c0642c11061005a01030140c030f241c0200028001c40062400400c0c0a14980202c0d07500c0c1c4408000d140450351100448000a43c0801c010b0700642207151030071503444a250000c2423a0419142c401031491001d002e0f86141c0e181c0d800e0301d400d181c2c3c03c854104100842808031300c02503502000703864010b000824402e030443c0d04500380380b449150020420800300c200a0010 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 27029673 1250 27028423 27028447
    0xa020307021525080702190e0912090d0c0f060908070803030f0402090414120c010c0201091205090d0f08090f011106060906010908030309011505100203070b06040e0604060e12 77
    0x40304400c003080f0000e10b900c01c0741d19009501d4000e4800280d00032410360901060100740411440070350b8150b0044035159a21600800c2c1d8886c107100e00c4106440c3c05100348002410440c0075018690321401400514548840d0300000c0d2450135440000064004513081002c8101480044080c12207d4003551851524000c40c002540c400362009020309a000c0026003130110a002d5032140300d45490030f40f111600c020070080000e40210f0840b201951a0a00c2e0201d0940141321b05104250f111081d812506103c4109637001d41001303107143c0e004010340c0c1040c40000c200c0d100000301c0134446e05805403502c0c1c4840620888049005245040c40f1840c070380f200a1138000586d0341c4c0e02101c03c1703880c0191580c0309001215103003c00c0d071107080c161001000b0301c54201010340140e2401030000c541c1110b071954820800c06c840101460100158104011180214078050347c101e50052010304003040300100b402060386000c1d0101d500b919440e540d800e64070307240081885008448108410b1041c14030b02c018050b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 27030923 1250 27029673 27029707
    0xb030901051008030423040f0c08040302100b01020a02040515030609031207141801021011040302100215070503070521070305010905100905060316030c060210050103080a0509040b03030a0203070215 87
    0x701c110b03284a51b100c400b190366250080241c009800c40144075615443c50050514441510300720058051007003100d203001400e210700111a40140d0040c10082d0490f001d00000b0280a01082c208002038134142c1440d0301c040003080e0181400394000c0d95038580c40e2460404071600507060408203c1e0300420401a030040c1425a1945480e800c911f1480d81c0000c5c0c0141d151070749125480f076046042c25080c115419100c400380040300c2c000d4801e070180548c0240c04031b844d5151070710401020348441e80401c00c0603100f68040c550260213400e00e1490800c901d24085448075031889110316034000034040000c05035141c0a66401401c2a4509010302e0508013219070803613045000d141c00065a98000400954042240140d003c48070080030f00315072b840e400d0014000743ca6000306409442144030b440501c0d0905d01c5418100c9070056115800d00c040194115900c2e030100080720b60186e22041c120b0329075a0140000c0c10900b140750000c542d620000d03c1031002c082c07807003800200340c100d06001e500121404003403 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 27032173 1250 27030923 27030959
    0x601050d02061309050106030e010b06030c0f031b070b1e2e0f0e060102060906040302060103020f2d010e01090302030c0d0305040801020a0804060e010509250b0309010510080304 78
    0x1031a10745511058088022110341548084413544c1060700010310190185c1c00403801e940140700910820f59504240040d0b8071040e681c40d0b40c444001c000010429a4100145801610103080001c0d108042040300c40141c00000c0c0940385001040c040c0101b11811401d03a154441207050841c655150800e41c00c212240e500705400320784032081046692440e211043c05015002503080385000e251180d401889106049030135502500c94500800d0200703400080301441b55615031700400941e03007180e0038411039031075802c43c180c1c2090903883c45100c0740804511119200b48840d40f91208030044400041c054140c81b10003d041c0840400d00b4400b43c2c070049200388858400b0ba601c10801000c5203812120380c4a19031203d01d0651010504260880e400390032503004da40507280a009a005080350740f07080312010f8030710544c154010f440c4060041002000c2c22050381d00e10074241ca00950b2000b403030320982c4c01140c0c0e2481c0c83e5074440400c4002101a00d90002409041d0011411725062400b8407015204000d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 27033423 1250 27032173 27032179
    0x8010c09060f0201020c0307051006120b010b1b01021204030e0f090c0306030a12020706090b0f160212010903080615030403090918020d050a02130e0705040203100f06050304140601050d02 82
    0x4074030b18003560003501100c64000405c0c01312965036410342050385d1114024000901024240700c400175101700800419500c1319000840840070303901e088000c0003140d00c0410524804101b00e00103e00c003510038400780a5061225569001ca86000e140040c4200c0280500c0c51080bc4a0318410641e51900540554440d140341003031079a1b500d462001916003885a0300040c40310420845000140ea40030518a0498015031a600c410540342d00140c4080e02910008802c01d010600014241c40c440c21085800140042c1c03c110800c80e030540d4190030341d080b00340d0a034085603804090105038200361601040c030204400d0790508500701690010f112130418451440455110032044066070b5001d0300d0802400c0d40108242100401c905e001616140555026031040d180c030030010320600c8180c011410403004035005402d004e410001000002d42028100307042c50f140360500402c07600c986070328a0002c3c10542d220302d6103c1c83c091810010041c0250802080d40e007207000104155150704c2d0021405075411 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 27034673 1250 27033423 27033437
    0x1203040606050d05030406030c0c11040906060506131a0c0c090403020c0d0b06030118110d0804090e030c1006292a010b010302070804030308060d05030a0f03050108010c0906 76
    0x250816030058641508802d5200410b14103507410400d0020003441150900e44061044440d03000c2c060754800c042c900b01405002040f600b0161610b0103501c029845440741c0c4001032519120000700c3c0054200201565410901c00030034071903100400c1544602000c0401600e10348003280e010705031951f800c5400503000c0e01c0410086000c25000f48144401a4006070020094807800c1c200194203c1c0700f0784986020b0751a20928000544c4c503032070365507442c6410000f400b4035004040d050054095942605903040d04050102051846075409005000040f0900a50300c920780801c4050402542144035555203151110803c540700e13a14201c000400d400c1d005070040f004105481b03160382e1184a00e800880400140c40c40d0701454901c281c1c01c206214200200a01810080194100c1c400e941e8054050841808100000b91291041a511202c050301d07110301c1035560ba49031891508514070010210b0401035000c074185a1510590740180b4129000340041401014003030507110541c000e2101301b0a603 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 27035923 1250 27034673 27034681
    0x5030708032a070801050403090311010c0b040803060303040b0c0313050d05060a0504060209100801060801230906010e15091309022427030106140303220515030402041d1203 76
    0xf070210400400d40310300284401e00c0c013460001d00300480340c0011038140c00c03c44031021455104035407010f6084c0c2e110781100f5243d00c0da80c0300c0300a6500003c1c40d00381c0c103200c104801b04403800f614024107058400b00005584503440c50310203181c5441150032040c0150214504203000c20702c009a000c0e002000d00c400010303680c40701d0504034068420401c07510340026500381c91209895000c01c0136412516266203c140598072081c500303842c8912601041c0000c84501c0140340145802e640c100c0d00a10f0506102903641682404585e48069105403104030320008504c249440c24034168050340c5600700d082c1000048016400a880000000310303880303482441d05001829201010200c1e60356200030307280b1a1440001da01c2048881028440360f80c040d500b07110002428500c11044005450801400b640c100200148104103080052088100f822001000094180c8400d00300f0b2600300d07803d80307503076541349401c0c0144030030345415a019040419100082c42d45003a0085504003409030b030b04940960301c0e15 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 27037173 1250 27035923 27036007
    0x15031005090c09010e09070f21090b070e030703030815011403131401060609030b0c0f0d060602010c17070e18070201020a1709060601050c16060203040503070803 71
    0x2650099030308900380070140401d01012801409410320b007603888290350041c02003403041c41c08060358040c020400041805074054052104c52581c00c901800800760030049803210b105a441c455805d5039151038004c01d000a40c4c3c0e02100101c1d4600c01a0000c0074a0ba02d580e034001d000f958000d0800e00d07000729007001c15085078440c0002400340030312000103940f241007140300f04101c800c0707042d0f0858812881403000c44418a06004e81822620f40c0d44501140314a107403100452140c00400e8441038540c20041c00d0520108500640110594410001400e505090307020b400c403a00d01039040e0501c400352403e00800310f60304c002c1c1d40e440b032084d2505c207020340318070008206100c041052805540010100f006082c03136055016040844140d5564686c040550140c0c2225030001c0d1130421681d0400e0300041c15a500400041c03c0f407566400c11110041c01c44205d0004400858000f20010782000400300700c0c0e45400c0280001a010800c0510704e86020b0895940400c800c070301c1e5110340302c4119094803040f14 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 27038423 1250 27037173 27037201
    0x309020a0609081f150e010504060617070c14060f0f070c11010f020c0901080a1a09030720040c0905090106030204180902060f03100302090c0f0a0c170d050108060601020c1503 77
    0x1008a44540826154206c810004100f4007804d4006e900c0c0c4040003524a201e11501c0041203403410b00310001da1102001200e014146d10010395103a40445030b1010012020841644104030707000050340c20707090030f101380b811381d6102a1000080013a80410800411910003d203075401d003003400c00010000e5a02016030504500d5503006901010000001614a20108130b0080c018130480c0480c403060f440725a130300e10503a001e03945904664414000c040004413010082c03c081e899170300c00e46044030700c03c1c00002c0540b28047c95800004080e03080820943c207010483c2c601512140c2810b505040c102a01c180507503007118102d0068071749903108503083d925440102c44405d00d404442c00d40c0c81c0782501c1c010300c20100c0e46c4400c9004102c120000742070745000c2000c3d03420050081a003a0318111003050110f5022080400c16110304909896151404801d100102080d015022002c40c4a41c9400c40a60034004010280c6055401c0036546400980c0c421404000490310458240d85903224030f81c00034800 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 27039673 1250 27038423 27038441
    0xb030709020c0f070501050a050f0306010924020f060105030a0b10030c0f1505030613090237080601080309060c01060e01030f020306070c08041401050903010c0309020a0609081f 78
    0x180703200107840441e140d004508603d04114000c11110741c540d454004440314800c080c0c40e9000100c00307000e0044801030480085400003030503d0900d030721075252842002d81c000f4420003242d454072101d0840300010f4040c00000141c2a14801519040d131510020030744441c1c6c2c2d1440107000b01c840c03100180c2c0650001405002558205013202061500c41e100032040e05824000d0480d000e00c284171650703480f0b2281044910a54004d1b103e40741c06095000e61070003070056000201d078801951103040602910703100b000c5080300401c921141c2d04588031100e1070a1290305e9001212103410240041c040320300e0010484a00d170b201038415030307500e402820000d4010301c4180c00c01d2a028202c40000024842215905000e0600031015202292260705007500c4e0300302190b2006100400c00d000030130900c00030381c60448002d10181001031a000007080040c2c2110180c0c450071001c60303902d01d60f00055007090b6458030003030300c0715041c444403181c00c0c1500ca071340d180947c0c0d8281c544011446403003c0d40d0341c0c1680052500f = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 27040923 1250 27039673 27039689
    0x510030906090c06230703020712050c03010c03050a0f1a01050f0409090c0611060f041202010b040f050a0b03060705090609040b1801090f20030702150c0403020907030b03060a0b0307 80
    0xb60703121131006204c2c0409900c407004808024004030000701c178403400c4605443d170680081c001145403502e05c59030140b100c802600c0e40e01800307804042640742030055400180e00c075980080c0c030345070002070707403084071703c0c1d0301080b01c0c128070b4000c103582e0814142021910491007428895103401e02c400102c64603200c0e41d040703c58814180ba81c2c120411129002240c00d0b58000e4843da807a030001010f41a036100000c03180d0000714410503001c10045020f681440b0080c01452001141c0c0104400100f0f082d41e1116404001040c1d0ba441000074640f900c0c41000c044050860140100c0c4c140702200500c54001c2a80142c800e41000500e105169502c0e0b000c4400c501c800b802040074040b800c4166501e1600910440a0050502d801d10310052024400c060001d01581d407660202c41c003040c0d010b00190001000744041d407041000340c0554402c1000c50030302c5411600702c000e50300da0451040c00440140905a4824103090240014260344e000c10705540c844400800012500c40700700000380340c6035481d0b00c2104 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 27042173 1250 27040923 27040943
    0xf0302010b040b040203071b03140c0303040c05030705090406050a0f060b18030f0a0311030909100f050a05010905101e02010903030617031e09030712020103050f01051003090609 78
    0x10150190040949014222810000c40c1031400c140401d9100884064001030340302c0700c080e0f28100c0382003c3c84542a020385080b90500e0101c00c0d05c4095584008146c0b11142d001004100400521300c1008010f014180c010707000b40e52400ac0031078218000a0401071403079032100c0000b895410158400300c554410100113019a079903e844154266000b00303c00480f056101c0d00c0c012039410000f8682ca0140c01d10390040106515945045030300282002c41e01c44540010000340545a441c4001680501c040d2000443c42c1c40c501160030240c50798580c0321a010740c100680402160380c10180c0c2d00216003080d12030580300074205600b02c65071001d06011030041c1c07584001128402d54150311401d010b80c440e0f03d0801403141c58540c2c0842d20401c80c00710003999402000030b40d26140b64222006400003c21030014144011100000e00b011456000340118000404030b180656902d0701a558028a079070f009801d46504103000704010b200d10148034070506844182207410884a0f6200071101608621070034 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 27043423 1250 27042173 27042203
    0x1104051c050d0f08060307030c1a090a030317010609080d140c070b0405030c04050906180f030703021609090f030f050405090103050c0109060807050901180801050906070807090f0e060409 82
    0x83c02c07210080c0000030000e0007200c0010080e00b0002181e4081c0e90300325940900e060319010b103d40d9403050303403c50703049056000c3c00701342c80c141c803162880070145110341c44056400c010304a890044900c160300500c200300300400c08000d5100c010448100e00c5000d8944000740316001c3c0d401428520806008811380c7c4140040050000c0000029101b91801107050300c2400707100508100a0b210207444816142e0040b801140d008180c241100901c440c608080c0e03016166681001411741c0c109038001d40158001e9000f244684200d0041d00028090741c07141005091181e89410010307001001005040c401004110000a40640240d81c0181002003e4100940c0c4a240ca19240c0b4962440617010800d03d40c404502c06009041c0c0714440e413441c0d1341d00341c20201d00034011154031490024000d02410030400102c0c19500a00910b4842e00b003501c000c00c01d60500c0c40004040d031200074101010000c080320188882011a0200e0341100d035140101c4903d615008001001400040401881d6150690444e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 27044673 1250 27043423 27043427
    0x50f0c030106060908280b0114040b0d03080a0905011b1107050603010513020f1209030309070503030a0c060b210a1b050d020904061b1d041104051c050d 67
    0x48008404198024008030303a5500007a2501c032003a00507109140c1001c0d91101604800c01c00c000c01040c00031409180070340032074950f1882c1c49404c7e00071411141404400344203034240380c000c05c0d280340c83c107443d1700e00c607010591001481c1d00d0018242040d1740c0c3e2103122400c01d001d4250008655030070082c1407041e1031041c070400a8440c4407040341484171802410b8000503140382034000d49048800c0031708145501d00040c0e443c40009d600500b0510381e006000c0c17160150060986401da4402c1d1480d03c0103655a05050208074a00703200c40e80680c0c4294801c2007120300290340050b06683c5260300c0580403611480c5640060f807280f20ac0740c00d11034162600310800e460344900244925040740110f90414001e0200c40250b40200c41ca030048540004010b40c00781d0040c20a80d800700e6105016100001d41c15214003054000b020b042c11128000a40300026100a104501c01d1680015001c40d401c0085949450406105000d01c0c0310b1a4405c01c40c54141c0310004407100b00c5003000712351001c1a50046407a0641c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 27045923 1250 27044673 27044683
    0x70e04051303080906060906150f04060e030f0a0203101a030f06040308090303061f0507020a091d06061c0201110708010c0306080118060b010e04050408040302010f1b0803060607050f 80
    0xa40006200e00013040d81c1082c0402c6107030043c0d9001d40140050b03038950050146d080d492800800310484200000042d0800e54000351000d09500c0d60350a04080401040604d8000345030042a540e800138910383c4016035000910245c0f1403c032500c04940700c40c00a14002d0050300040c5069014087e20040400b142d1001c07031001d106070300c2900c0b134107a281c41e0b0034403281e030f2408116141e80d04003c40403c9000320300b091080040c003040007490000d00c0d00c603031580802d07030055960344101c42c1315072101e1004c0c400c0300449401d2030303610251300020302140c0740c6200010340c0419150098402180609502019a44111500300054648504507075032203544045c041e000301421100c560001c1d140000200d5070200600900e00c0100103a0000720003012a81c58241c02400000c046d079040c040c01060940090711036016542c8610b01559102d6100c920310700001d842e1035803d01c49401040011400c10424a07182001a0f190f036130805295034481d40d401011408a00c51a0320150003403180200201d100d41c17001039 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 27047173 1250 27045923 27045961
    0x705150604050708070206011a0c010c0306140f060715020f070503030a060b070302061501091206020301050a06080f0a02070602090604030f0203070501181a040302040501060206070809070308030708070e0405 91
    0x1d020000b42d600c0800c1120b034100c00350784080040e0080f800420044003564411046940d5003c211441c008440102c1400c444d07141d000761010a89544041200c5000484000c60801c0e05a840c00e5034410f4150004015100f0b6603401801100010f00704405c000241c0d043d00d00e47c1140307180302ea0340c4038481d0a0140d81c0c2e401c1201c904007090304002c0f01051880010055403c6a60700da0010111030701d40d0343c425041c0c0421200c1c1d650400950000003d104440c1420030f080072401600010303920350521050001500040d00f1190a010b86081400b003c1d07060007043e55801034510700f00513169102460010041c2c441d18003060ba00c60400309000c41032204144039015018402c07011501d42aa880c401952003807213002049480c040151820800b220881c0440900d506811202c00e18054032a40000c0403a40c080c2c000500590181c42001601900000c0d443d400c121402d004003900352440c0e403849035070300c8000c0002c41045440d40100e140940030f4a03031a045070704020002d00c4103203007005d800352001d00c00d02 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 27048423 1250 27047173 27047179
    0x31a0306040b010e06180a05040201020109050723060a0203121f03060c17060a05040c110d0320040305030405040b01050c010c020607030b0901050a1401121a040f0209010e0909010207051506 83
    0x404070745c1e00c3c903116000070306002501c900c5c811640d503140010001490010000c5e4195502c64603110001081440300ca030181c102c6040b03466130308401e0400c05101080440919014070410813800191f01d40000a4541500d2586a01e0301c0355590100304400302035548190802c8800c80080c007104100d440e4016160b40c940d141d8a1003a80552162008100002540c86a03002a014042841a03003800e801000081c0114100020704c81c42d8416001e1520b5800700300500041c1c1d4030803405245500240c503100071101a010414100380c2591140c0307840c0d120714401c141c07050341e940040c030110f039000313405540007218900002c00080c7c4120b100a5140c41085404a001a18040b100c070b01c03600d441c1e00b0050507100060b0105c2c004c9800c051618403038032921441c4605001030b004c8404040b42042c01440e0058524803000740d4003400540c00c3c0000d43d40c0c01d80d40450361500512200440c1d90b40440c1c2d541d4100002c0302c007520240c884040070b500900c2010405030182c01140488039680d01e04100641c041c0500b9 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 27049673 1250 27048423 27048449
    0x4030302031903090308041112060405011401060906080c180d120306050409050c04020309010e0d0c030207150206060f0105091503040c0b03220c090e16090b030706031a0306040b01 79
    0x80c07241242240e280c090001d0215403003001187c0841c403000348034107030001c01404a1007850300c0788d201203180200c101c80443d403036074460300a1240b048030090b243d40101000c1c107209401905003a4080c2002000810340b6220300c4003c00c81142e00c0d000b540c40c400786081d015100e803030b80f0b0314641840b80c02d02d82070703644a4021900f0a03000140f5810948a10300e0702f0354200000d0080881c027082000082c0d40003404490b00c641d207880704581414020b00c1105520080c036100c02ca9503440602d00a42420b00a5000d000c0c032629032200242c0391a008109254000005c0b078140000044c51401a40c0b00d01802460359040751050070f81031a68140500258000d0303000e05960450282c0e00d0703503840e01d11301c0222114140140221000c80c0c04e40e03a5405043c400f00e1090360892069519140b003c0115101c907007a004e203613444050700940403c40d4580d0400034101221041c030401e100500402d60307074405407050307104041c0d8170b840e81411070149884100d580000107058a04a0503c0d003001c240025081c0101154a40c01e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 27050923 1250 27049673 27049717
    0x30901051e06060901030906060b0408030403030e010201050c042d0b0405011805060405060319020711010f0c05060106050a0903050d0531140f0907021b01080415050c0c01020403030203 81
    0x2039804502ca030034020407041c42c040c202e4004402918400000b02e44480c0c48550124401106001a05c0504591001180c546145040040c495403102107440c1c156407500c1c0134040c8007082d0780c00300d6003a03071700c64a0058007440718a208400c2c522000a5160f0b00d501d60050003042d03c0400f00010001c665099a812164240307140c1c0c422203040f61841081e5028100300b0080003d030410300c0c080c2d6440204161921148104010601c0503a403001174200c0d44c0e0312010021801540e00034200710905540ea15100c811100f40366942643d0f107606025200038480e0102c0c1d441c00151185200c24040c590180035551002803d200141c15504024040100c2444440000d1100301c11400d0f641146445440ca22240601d08414003003050152024560005c20a01131503002d07440b80280c40380200500c0c0d0040581002c50420304d040d401402c031207075040164950505c404200082d20042c00000295000100c54a980030010000c1c85000e042807440c0d40085000014140c004c409070960098079070035070380c103110 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 27052173 1250 27050923 27050971
    0x7030f0b0105090901170a0f0c0303090905060310050a090609060b030d050a080f06040615020a0c08030c0304030b071e0f02060721110c030409090203070609051c03021203090105 78
    0x1402103c50f04080c10f50010404004000ca1800440d403191013510400042a2600710319084a85402e8031483c2c0741020400030581d100094030024400c0c00010000b40c20b182001a444208031b641020070651600085407600c0e2031079206101040e0b0200301004103000c1840c106c00505924504544a0700070003908005071800344040740c02900d002c2d1f4802007130381e1b620000005a004050007442d041a40c903c0e0104071880c0c403850f140c04422490f0000c002008103413504004203155070300000e089401c01c0c402010b1100c0004103407815240d200c1003482003640c580e00c088500e103841034180a1503c48082440301442c0d00881e4003004100c49074282c0c0c424bc0d0f1090f5042e20490140785000006c602c40645201c420f0366541d02040e004c0c84c0740c071500c03440e200700e14192078615002600403800880c0c2d0703034003d0000c51a081010320000c00244c20100485440c000000b074110801d1240c104c80f114024080d401011302c00d00400d8450240e0b5081c19885c0c2c240200200d000302021a0f81c40b081e18502c129030119a0707 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 27053423 1250 27052173 27052177
    0x50106211203050405031605010e0105010801020405060421020303030106051209010b09280204060921030215040503040902070f02100c08091003020409020409140a0603080702060906090907030f0b0105 88
    0x41e8000201035074101141008078020800104103884500061000401d441101c90200034550b014500218051199640c03a5086440c103030711060160388100020000d5840701000d4504403408016101c0c11382150810480d0450749400c03000390306010000c00814110740140180141806400c0c4006280e507810340c00d40d0072542601603060f0300500703810005420800118401d140c1402d8501c1c11181401c1c40c03140741c4160f8015402c40f5000c0b540700c50b4240142c00403880408150703c000d14a442e403c5079940c801a4843c24804c01e0074000c140d800c00041c003840810800c0340c0c000c0c1a03512046640d401d05041100701403000050492281e031102504031544c9124101d0780070305603041011680b50040c0181040089568215040c0604d43c09001c0020f485a0758070161004001c43d82e8046840f00c400b00c040d40b1a400000c0148501900d003040a0021903090000d60745440e5055610a03614900400003506901030914803d0f8454041d030108030032168145c201c00f82c035500440080c041c00940400541e914 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 27054673 1250 27053423 27053489
    0x11e050d020403081215030c040b01051201060f0215040c0e0601020f100504020a0b070308060907090509040f0204050f010e07120605060315030706050403080315150c01020415090b2b0603050106 85
    0x190311588c1c20540c1c13464180d00010001c2014103046190000b40d2480e22001c041c2648888082175002c81e07882c1c40c01e80c040c000203070070081110800d5043c0ca42a40c1e105150119802890f002c034440348001071031382e402048000d0300d00d5018001c48034034107104501c64020304800c85049000f208030b840c000a11240318000e4a006030f80c56100c002c25550f0303180611071401b20003800041000341490340012140c4039aa8114000d50003142c10f01001c00181c01484190750015060074100d5201c10300420400c90121002c54209140d450310082c1492400400e2000d486603411242e4424000020b1002075003501c4001101c984043c0d0030f4410540d6a042c0a40c1d890207180710242c00c1d1341d01080061001482102401c80001d0300822050341100001744002581c1c0040450074802c2c2c0d8000b500740a030701309805820007508090f01d441c000c041d0600400c102180038810304001812100781019010785003203603080b90307601040307101009042d650341450383c06044180304207151150f540c0c03d290103041c06e0048210b08 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 27055923 1250 27054673 27054679
    0x902090f010c030e120a0611190e0103020d02161103030f090f060403050d1101050114010c030f140d0b04050c0307051e04030501020304080c0606030c011e050d020403081215 76
    0x121114090054601e1500550700f20100301190901103d40d170340b9050f5840b402d5030b80300300403d460950707454894211004020041d803000014070841020304040b01c208180e5000500e407844ca0a960303000180d002c1d00604007100c2c086800030641e044800712248204c400d40c0d0246084c0c40d24106110149a228460002c3c43d640b0a5030030400168903040044a400113010050046031a0030740c1e0780c490b5800c14200c1c5130b00c00d0028142001601108509009841c05408500080d041c481340b1900080d1010520700c4009042c012425000d9007018001c440300b1012249200c2a141d90702c081c0c0311340e14000c11f0184076030352040345403e0101d40c4803205442900d00c41d018a880b0030389480c903420510550460901d044282100c1c0401011000031002c1c005180030f03d103d602c45a4998150180b40c07400e010000f41058007992000b00da021304d680e400b00c16107102d80e8120250004c080c1403038504039454454400d60541c280d00006002040142c3c1400800300c3e403151038010301550301e603480040d20f1040e200c4c80040e4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 27057173 1250 27055923 27055939
    0x31407080f070309020105040315050402130501050d03080601050702040c0801060f0206090d0c0c030507030b0a0e06060114160f141509070504020a17040506010e09030708031305030405030709050709090209 90
    0x494000e5200006a070b005040448c10180d036940e40da01c1c40307880c004440f541da5071128140f02c2141816440c00c002110208002d101b107604040200d114540804005800c1004401c080380159005904a807841a00504144082d520000c00600b4010082c449c0c3c2000544038010703046251720200711a070152865001030030340404240b0701151034080c81d45098413071003990040000014401c0000c02c0c01140708841400d80d524008084800310f9061201c0d9040b16044003040107666a40484d01903030340303403106501a8031035404100117400c400e13000720f00405900021003418180310b49140d481041903030364400c4a44414180400701801d0720203031034134080d980c4200350078811441c00c4d070050b100351222031601102d500f44404207203241e1603050b07d043c2ea1a8011000501109004460031640b0517542001145000c13100e5460000c0c0c2d1000030b21142186c1e4444450718108030080c42201c008107001801c89001ea40c0380e9001030000c0900365110030202b02a070900083c00c00440c001e507807040d480140004 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 27058423 1250 27057173 27057181
    0x403050717030f04090c020106050a150804110a0905040c140627040204031110140f03040f020306100608060102060403050711030a021306050f0f03121b070303031407080f 75
    0x41071041894541909000c244000c00950400c20040d000a00c40c4120114066150003000b1382166103582180c1c0c00b071291844244000356600090600b00d0030705140001060342e035824003100e0901d441000540c0010045800200342c0210340100e8043c80c01100480791842e42d420700c2d13020400300a005190002130500004250100440074501880310003d408003810b00c1010016040342e0081d0400c030740c264000341d5a20f00a06007130201403031200d41401e00e980009009890080103015130194003012040c0003001a0810440701000345280313a010b0204c50f10340c00c2034140e03021007601501441b0009071041001404a601c0028111b0183c1c3e01a110140340407515114010040b030380283c1640c051056481d5007005840e452a0390a0050f61003400007000350030316041000f00684030070700c00d204507000007034080309503408120040c08960020b0843d65840000040381c0e1020000d5000c06098000c9505c00001c0c150150408160810025022001962040b10a8074003000540703108101d00c541c40002 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 27059673 1250 27058423 27058439
    0x604060e0603040602160f1202010624030e0706050334031a090c0a1106100b07020a03080705100e03030f041103070806160207080d02060f060d0203010c0f1404030507 73
    0x110381050144e8400b6140503880e1503000301031100208112090040c81031010180059040b841503008101d100a0102904c1c011030004244030b0228031050301c80c4584040c6010724000c6e40210440d50f500e070141c40d007080da58680a403168008031007242e0001c079403042c0560032601020301103144000281c0582e400b5001d0710021001405500418280c041242c0c41450b680c3c0d0b42d80302c4080c89035100c040416541c09103404000c00c2003854206644c11940300b00180a0383d40c040041740b10580320301c64078503038031840c40e4000603141c406150b00c05003198100060140901c84040b400344284132040d041840b11070035200c88a6602c0c4412201130300381038807510215000031200e114886141d000281200d203916215004582040d405940840f4082c1100c00940e0301650144440c0004000e840003424600d030307140b48040e445980c014181a20146030400058543d96003640c0081c00d45d4020b0000c00202c5546034000e840e4811003503c14010400c003101c3d8403228090390003210140c981c0311010f040341614108034 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 27060923 1250 27059673 27059677
    0x150f060a1a0a0e0d0b04061b1403010e0403170703060302040606050301060509040c02011b02070915030b0103030e1507030503070305060f030316020d08070b0115020303010e0705070302010e01110909060604060e06 93
    0x3e552204160044001003844021098001c138011580000c9041006e0410800c3d582601d0000003444240c0000b00100501d40d4240c0781103803920740c800e4005a50b05d1030304455051100042e0144190200309101029a00d0b80c08441a24800c0e40e00b08800ea44501054480e80024800c00000420810680046003411340180c0e002140d54000452007183c041e00c7c8445401e4452810340040e400700504010351f51642c051400610307000c9209451440c115190200082c205000c05070910150000c412815143c042c1e00e4054418510b070070540b200241d24005002da801a210760002a060101048440c980301c1c4c00d840a03660000d00541c584920400c0d0b0114116550f023050303901009003002c100109070000e0042102a10035101d001182d0704003000350f2251024044500d045600c1403005000a40c480d405c0103821111034206940c40703200d0742c98228090301ca8402a19402d5082c01c030300506041540002d09580e2500f02c0304a078007036a4507020300607140070b544241300028864004903a41d50600f540 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 27062173 1250 27060923 27060947
    0xe010b13021602150d0f02070210080709050a0605040305060f0601020706030b0301110301120b0f06060315060c0d090603060603020f03160c050601030804090f020705070e09150f060a1a0a 82
    0x808000382d40b0103500041c0b100c401150704100e070300c100010a062240650b1003070303d1a4035a00d081c00c600307000440e000700b0b03004464004441c0620042c0030102d8540c2e40641c1c480d40c02880020200d40c881a15450000d02c0c0d900a4031003111244101008181480b680c2c0000522440040c2e004144040c9804030850145c02110401601956150307101c2c0300310803458000750301814842868003423203481494500c13101000101101403955090040c130400c0d81d14241141c1c2c001c152007050b5840c05039291300280390340c46220140c2942d03100d01c2e03c0c1d00310101d81285184040300c0c2d6079102000b0581e47d82606400b41c0c86003d00074029440d0810002e6450180031011131581240761802081400d10f6a032410720b8544203800580d1424004102001300e100c0038021410a005810010b5080480c156512950b0304001e0280e0740e00faa1100380020311400d020071000e2030103a0311413546c0406040c00d0038006001441500d1043c010709548202040000c8001011408010010704561810306021021108450044 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 27063423 1250 27062173 27062197
    0x3120e030d081603020d02040815010b0a080406020d0e0102030411010f020c030709020c0c030d111605030d0e0301020c03070f110315070302070602120103030302120a0b100c060204081501090e010b1302 88
    0x70080210026007440640050249e10009104e80516881030011500052313100307032411107041090303012485c0c1c080d00342c680007a84607402507252400c9a10300780260031691443d407100d62000c420070081c0a4940781c48002d541d420b80318241c0420780f15070120b031a4824400084e0309944103000400100083c4d600404900d0400d01c103507070130101c404001a04040b80710042a0000e14204100c4410000074850801c54203008000342c4011880d00000c07946569100e40d100c003e10280201e2040e1603102034049421042084064030f80c0d8000500e04a00303120060441525141d0001c05007044030301b400030700f140764000500d060a0305942d6042d001c40c060340c0f02c60422a240c80d020b0001303115403d108001c1c40d001c1d501c25100035884020f2200154071001c80102484200c0382005030700840c5840c5d40e034100c182d1205501d1302003002c3c80d1505214029118a038066822031061105e1400c031400d000607418103a58002c1418480700303c051592500fa11840d0b194181e0008080c3d41a880d900019070051840e05000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 27064673 1250 27063423 27063427
    0x9030702090a06150908100902011d030111040807030515040c1a0702040203010608150f090121050601030302010518010c0e100c050d030b030706080c030a0207080f0403120e030d08160302 82
    0x9a4584819080e0019000e01003001c5c450103010019042c840c43d011000c0d28130041100040070340000b4129542000c1307103119144802c5000c2c4480d00d082d000b00500c0f00648901a60716961401190b075210402c1c4002d8903903004001d903100c8100b043c41c01840c010303a08040100c87d40c0f8207008038030740c155882c403082c00c040904c20010600142c6490010350300038061902c1f00300d1203140031014000010f0403210190b104619042c080380721a503982c0e860505480c0b5400c04a001d03455014041c41560898000c040c2451180100000400d6070542156104007003000000410714285d42245083e03aa1048107100442d12110f0b440115082c12800008070403c64502040b1441e9183c41700c1e4104400400401d00081c0c0302ccc03c03140c83d030703042c1006024020405440c040c0500e16000c42d00d4203141c040031300b01c1c0004540010350a000c2c8504203085e80e501c40c40400784640d9076556841c20100b040088550314001c21310701c01603081c50745000324101d01c0e24201c5403510b00c460b682d0211b40381e601003012000341301410342c2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 27065923 1250 27064673 27064679
    0x712120c0b07020c0108010b090102120c101e0b01090b04061d0405070306140a0812070f050d050a0e09060904030309031101060807180c0203160f0b15120609030702090a06 75
    0x702070501030009034024200b6000307544001021004140c000d030b201c3d09410019211070740d0740044c2ca410801d82000c461615031760a01d050720b00b0244071800c1c10503036505007407142d40b81c0c2c403460301d502d052949691000c00003060b04000640c0c1603452441941c2c600384d000d100800c0201d01584004000d8001c081c0300d41141c403c107000140c1219070036140b08000075961003017440300c6503a410342140048030890f40c140c5010b292a1195a4400000703100d51802c900200d094801c01078102c030a040a2503010095504e034448580c4000c0042d0407401c1b07400b0000e80901602c0009082500006014032000b4104404594641d02c055001d801001c00850400c0800c0c0f2107081104020710412008d00219405001d41c0e030701e04070300e10020340c0449038030340c60b01858140c2c100e0000743c00004a4400203500c28584803c00c07064200204a002ca041028104002c0d110401c40c18035200c0d4250100300604544400d801d41c0300c1003409a40d00340c03c9078080c04c0c40c2e0082200e0409460200300095014100c65400b00720561 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 27067173 1250 27065923 27065933
    0x1401022e02070605040c060e060d2003010e092e02130b040801060501110610180207080a0306090c02060105030c040e0703020301090f02010f020c09010b030901020909150a06020712120c 81
    0x10182e503064445650751303403c1c0410041180c03515070040c4185d01e40b004545101c9000203030144101100002e1582d40e40314a02c400b10803107121520018260700d410b584a40e9030340b200e054180b40c2241c20b04228080e031207101120b400c036400c1403000603100c20110103200c0201038041c0300944c0500320080301e0150f00d0f00001108005c0741c0080000e000d442001160f26440d110024202c0454a298504a50000e0003007040e0a00f0f120000b40845843c46d00c8070703151418006000c402441504405000c03810001000e0200c01c0d0550040f40071900da06504015004c0d80030b90403615010280074596054001400c40004c5203860f030010500c00c84000240d03601e20780c1d25800242150002c1404881125007000001c0a540c0c000c000403c0d90807150002d0941d07054241d00003241c2240500420a4055001c40840c01030070095068422554014011075410704100d908180b848040d000428498880031202142c0d061003c6200c5e001c0310000301c01e100340d260a50303032080180111482c0340e804000405405002182e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 27068423 1250 27067173 27067177
    0x90b0607060c020c010f0302030408031b070602030f0103140a030e0103050a020c01020705061f081c030603050a0506040b0109060810020906160b0a060f06020a020f0109050d0317011401022e02 84
    0x803642e500203000752070202002404c2000300c1d1004000385803042c01040041120401226400404001c008645901003001d00315180159400584424800b00407c01040713181507089045c1c90081d0a4140c4482e0742c0c081c0f11380e4880a400000300000d0250302c0482030341d401783e002650410004c001c054185506020482c1c220380050405650b182e00c41c20074494010740221003c01d24500c40c061028015050041e40b56460b06261108004000409600c40c10030b88654071101c0919404400c0e15803610305402e002e03980e07010a03681581c0c0b000c04d8a00025080740c003441000d0807240e071003001d031461072002003442d4029002048069040801004100aa10854500b4005461040044c03803205d0030f152407000100c407095001190020120701040c00f01c1500054500841e81d030444d040e4000c0d02186004a0310302c005580500d0304440182800340030180c0011151050400490703003b051607aa03014500340040e404030b00180035801405041004025943c1e028140744004254640b600060100c608126 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 27069673 1250 27068423 27068441
    0x111190606050a0f230103020715050403032a0804141608010e031309020903010e010c020c03060609012105010b0607030f110105010f12051207060209090916090b060706 74
    0xd240c0c1ca00d03040c051450b1088540002e005041c0d00d110686082c01c00d920648541d00c002e40c4c00c0c209000100714282e038800e804440b409607000030440032400164803141d001e41000d95040707020a00781300c13200a9410440d160801c0e4824000032580e50000c200c48190303140200980242d61364040402403110300a010051380795152158a12001e01a00c0d0280c071300c0c2181c1004d0901a402d400400090306841c031010245025140c04000040c6d459601c803000034014285846503c28035400c0c4010104000c1d0003081341503010009809540044c0d80345820000c1c5000c4c240100c1e0741d0062400c0122031f94080c2c0303603070100c6040c0c801c0000290b010782120024807035130042641240080c1c02201d018924950209042070504440402408103504040e03a4900e0f04400d8001c0c442591901440c40003404401c112031840032103007408041d983e500c6400d004000c0e40c404c11210340200c0c003030008214000f00018528070740000f0b02d003c0d43d104500b0209400c024121004c00d01d54410000e01c000808103029100d80c100c5 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 27070923 1250 27069673 27069683
    0x1020a05010c0f090905010f05040c12060305060a0f110f070309030c0806010302040c020102090d2d06020702150406020309010e0a05032505060403020604030b040309120503030402030601090e0c011119 88
    0x100f6025140e00800704900c68002140c031070700b000010410740145680e0b0400751030040390081034040010740111f445030800310ba01c01c25907040a0000042c48004070300c550041e8800c100512205540821301030554080d641902950b080c20442080074880c401c0150408038800c2c600451480d0341c035210310140404540116210b034001100400442c071b0079104217840c440c0180025820402d0f100700040c002c102d500c0300501803071100e4000010070201401e6500d40b5001c0c401081c9016501c41c203000f4000d400800e422030045604030400ea203c000e82909641c11185641e00035480e0400c0d90004485040001c1d011a0300721840311000700d1030380e038107000d07007000003082210340c1486900d076910810012903d030744014042c3da020081480940c580400311000d40b80c001111900c5071b11541b138200c803410702c80d0788541103000201100d442040701c003100a42c0100c3c0220b04480070341c1d072280c55030000c0700c14075200200c403079004001c0e074910355009400c3d244044003000c0075a01d81b83c0051501003084181c540003103903 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 27072173 1250 27070923 27070937
    0x301031e151b08090c0108040510060609090b01030e030301060509030c04020304031706010e0109030201050c190c060f02060106080103020f04200c061302010c0813051e130b060a050901020a05010c 86
    0x811041800c5100800000e1502a207513050000040b0380390180311034103a0400000310005800e10008000b0302403400d042d8201040740380d0b51800010a00f0802d4050340840b281000700b0642150f1003802907403000800e1101442c61640b800100b510b4071762200a1440c1c02d40282d5280000c2a030b50751002d1407080b4001d449100840102e003407442c40141004000038140110b00300781d00d20590f0f00c08540425aa820f0800c165a0503030000018907103000180380c070740c505941c12601020000452031034011902981c4031214041c0300080240d855072401d02424002a03002401000540340540201264440c05000041e00344542c2014801d201d25040390300c09034580000b40290000c4040001c103500a0202c0c2e0780960380d001c66030008041040b504001703840320744041040301c020f40884048000a0100901100342d1a40d84071750809522128074410b4400c1060540c050000c1030940642003032658010300307680c50300700c0000f81920603800c00e0300e6142c1103208000410001610900c125640031601d5201d400c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 27073423 1250 27072173 27072191
    0x312090b0406050618010501110307020d0c05131404080a0507020a0905060a0e0411090702151009050a090302070b1305150409050c070302100b010c12030606021b01050301031e15 78
    0x82d090340c1d0f0280031580500100c04004400416410040f815100c09103012088840480d00d140e20b18003841d540a544070440c080400d0401105205100032a03005075841001e00001c078200d1001c8819800070b00300080341e4200060000341c8403500410b0008082d08240e400c0c400d607a001728019002c00e4012280c01550341c018032219103000003500d4014640700ca86c14031280791556625500f00e40c480262402903070b40001040c0528000d0040113604000c0d01000a03c170f10b4100c0e80e4000c0410301744950215a481c1c000850312001803401044030f01d50300b5800801c64149454282c54050b440120030b03602c181400e003004601591080d04548036042031607201d07520703a400c3c102c00800f140c002800800b85060f081000c200001c3d00440e1014001c0c03011341001454020b0200180c4903423000c08001080303070143d416511040d980540c4500309031a919401c41350b0700c940c50540500444000881c20b40402c409000410010320954400c41c20150300c080490000c6105503a03c1005400040e031001c82252104284 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 27074673 1250 27073423 27073433
    0x9050703050a060b0901090b0d0b0303030403020a021806030c1005040503010e070305010605010c0c090c0c02040507020f0c0f011d040603053003040b0105130e0d030c1202030705160312090b04 84
    0x5200641011303041c1d90716280d82407001819294031449505030380e11000c5011203000d880e503400041d8001d00a42071b03d50701c0c941480c0c029152504000d040344504100112000c040355442d0080b4408c0f0360182c01001c040180004100c840b98140d10138100700102000040f91035282801891070b0541140300404c0c1441c2189030032400d480850300182e0400c045242d40c10b0210310b808c0d0858085441c251000110380c0a03102c41100c00060350000a50000e0800e014400c1c1c05600007025200030300311078140c8002e242801c00b046868044200d510b80000e8002c410145240520401c046000034020f00000d00c05550780da074641003140005d81d240410b4010812182405142951141e86d03d4175090007a2540c6005c1d0344095040c030f0180030711400b40100300030010709401c1582c001d801460200c0c080340c40418003030b600180542000001440020401c7c5081c00030155107000b5a409500aa1201400c22003c45004071084000c1c2c0340940801c140c01e0554254245580b0807a1015070054029100500c3c09043c1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 27075923 1250 27074673 27074681
    0xe0a17040f090b0a0302010f0905041103040510050c091207080706020307050d050a1b02040f060e07030b041505010f0912030509100c020a030303020a050c03030a06030b060d0c050d060609050703050a 87
    0xc03441c1c50505103003a80c141907681300410002d83c0da09090030a240301400c0070450780d103607070340c2c0120b078000d440d00c201c04000002c014081c40c8640d22030022111003289919110303007628000e80d02151214014000c441c00d621300400c18080000b103045c2241c50155440d069030303262070701d540e01c4440960400110360041c0042032110400c580c541d410300510b80080c0f040020301d4030200301803440003280c40304540003c5559270f81141c0c40c10410b550741440351640b9045001100103066840c0c50109140c901c18242c54103180c080d00840e80185164400040c0c540303001910b01e50503220b001c20412842c0c0e58081a448c0103014074a205500075619192220440402e00503030582c0511a1400d0200100c0d01c080140c2d18210310600703407a4103103400360315005440f03002c3e40d45000c2c1045609060001104220b484001c036803101c4c2c108e84c01011504955240c4209000000080e544040c0540d000d464040c0540c0c1811451010600d100f040c000503010344d134000400848500703a550800103600d0700700344180502c280c01 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 27077173 1250 27075923 27075929
    0x7020114010b03011a04080105090c04060504090809040e12030915060a0b1801020118030309020301050f06030304060809030f030106030912080106050919050303030f0703050c0a090501030e0a17040f 87
    0x3603800d5410500c0689140c0814426210038001402c0c081c801c0381050700c02c1e14014507490b030091046080a14a40e5200c1d411406c415004e6440c2c18400510b80c80d02d4042d1990540e0803120f1980f8004807501800050301120320318094500c14401143c040c481c400004600c1801d0000c054003c9505600c1c20560940c0054019803150407403000500020304810220b03007401c0c0080003061601440040107071f000d014a800000d0826810310425014590142c1102000318402c50003040141d480c10151f806643c000d50b91f054259000348001e0103d28001d0031455045518642101d0420520b81c8000304580d000360044000282c07101800c90400c10310000140300300915041c5140c45604125004009000b18800389100b10440142034214540c0114100b01801000d000e0303c2c3e0740d1801d121039944480301a554500080d107082c0002d00c0445160341a120301480c00e0b40d074205018500f000440103887c0704068200c20f401990b80842c00240c5041744910300b241540142e60700c541c030305486118501e40c00d85c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 27078423 1250 27077173 27077201
    0x60807060804170f0904090501090203061f080703030f08070c0b0c0703080604090825020301110c0706030605090123040606111219230301080304031104090210110309060d05070201 79
    0x104c4035020142002c41030307031400c00e41a100005d03180c4d12420302c607002d02100c100282d0140107400a121ba09036282c1860203076904101e00d0040c43d607682c0d50040340d07160141d100140000c1c018844490200e446807041e10303044803803464061070314001500c0383c0091b09400d81e139040c1503074000101d440403d074112400c240c2c04602240c0400c0181d0b00742d2285a044d00c100350010400d00e010380b40084c41c03604040d0454010940190080010159042c04004590701031590b15041d80304440000420314400c4c00b60105541010742622035030391a204060305066180c1a02c40864400c00941d400ca0fa01d461050100400360782e511040c5612888060a00780005100592001603080258a0f1032051041c2d032101c00d02c41c180340c0141c6103d10341180c074804003c07802c402040b6136000400054218030001c05030040d00e0048064903002e00654040108688040000035084000f01100c0000e0030b019038800355010441d04280c034a0203c0784400600c0e240d00c9003035044030f840d9907141840b414660901c01c07072040340074003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 27079673 1250 27078423 27078427
    0xc070b0d020a17040b0a050601021905030310050604030804180902030102210a02070b13050a020a0f030203100606170c0412030201020d050105030309010207090b030304090608030a1211040501050d06080706080417 93
    0x5e45540b01c2c0c03648020481d640990311000442c41a0740f00708800c0e201401c1e511840c2e2820380e00c0b0310345079031a507209680d0340003c40140c50010803a40341080c101c80441c0e50001005182901c0c00500341c11852020300c00200107a510700d02403026890a0004010a62050000300030b01d0400011807860b8910250a8110480c07062102c280091800d0780c00940140e01812600d658003018030b481481c04610031300081d000a0b00450001e0040d10f101001c038103803407084003503071290741140380044201d48151081c10001201e0400003200e51009510503034002920a10b00352074951182c141103400d0360200030860041c1e40c0050049001901c1d07103d80d6001d400110003561034804c0c00c000007540c400541c02402c00666035980c050b109582c0410444006200c203800c2800203aa40e405900d032650440c4003080d01003078064400c00c403191203522445a580741c065004070309090070319004403100e41081340890700d141c3d940c0b400403c1884040040a0060403141c6d40c6203a585840d1030015002d00c0685401483c1c1902 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 27080923 1250 27079673 27079681
    0xa08010609080a170403020a08060a0509010c09052202030709050a05030a050a03050f0412030906021509120714160f06050a0f03090609020409140705090115050c070b0d020a17 77
    0xb18001c00c1c461340104114055400c1e03031904061510582d07100a41c820550340000440c4880410680c1c400c841455082000741d0f10100b0f041d00340d41d500300c4a000003a8418205021501d401441d9a000d6100d0f4202c4002d04040c001801e0100da00c251500c102050040204000030710300a952003014050030760142180b40c096642d02503607011100e03070003000d002020030042541400c090a44009240601094448590a08001e0a40d15090103510300602844542079030702034001501c580681c5d120402040c1d02d00c11031035a8041e82d00899001c903020124034040c1c400302902007040044990002d90148055440d011011000c1000d90f84890140101030004c0030100d13411034554240301c60175080104440ca40740c60010f0041c01d8140000754007502c1c05c5123141c2403007500e000ca48840c1080b4800c8803d156111410000d2030030003403160b1810001c00c41c4064000c0d07449007004d01003100070303001224101610f680f4010107a400800c84942141c1e404914603144c3d40c0c1c4050064403000001140c4240c1e820 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 27082173 1250 27080923 27080939
    0x5030f03030708060303070f0f1101050304020f010809030d02070605010501090f030803060f0d060c0e010306050f0307031205070209010e0712020a05090d03020f0a0b0406060f0b0a1b02090c0a08010609 88
    0x4100e0001d2003a83c000003195900c050044503c10b42d442407100c0c1d454011458800c600442082040d50f85000c034128801c207035401801141d000f550010505602980a80f004541889000f821507040703000a001040c20b24010340003070301c6100d01c900b2000c07980d50f05041c001001c04080340e010241c0441c14120410100d10b40a003100e42003e802c1d100003180c410035801040401e00d020764000d000c0c500e400518000305510001203c0da0030802d0760140f0003981e4030f00c204241881e03062601940354011480c1080040d0342d201034035100c11400d04080d800c103905a00040d8400e41c00b603004c09080c0170043c080144207540200ea20043c0c0040000c21402d01da41043c008065010364101603010302d43c480300a8052500800c800b210702100350088400102e9280381101c4000b0b403d9404444007402c004000c68803c00d24032220701940c1c4020b00d15802c0180f0004122603856148010018004845940700702503164424042d103d500e0b010b08090b0340b0f00c04030600810b47d031b00590250b01005650501840004 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 27083423 1250 27082173 27082177
    0xc04050c120601091802030603010605010e13020d0f09030906030b04051605070c1809050f06160513050409120e120705010c0602040e15010914010903060519051f05030f03 75
    0x202001030500c141da80c81a0050f29550704075000803110420b083d84800e404100f5400452284109400034070216a603100191804083e00031030030b40c0003044526600d280b0b00320b07601400116101000116540d0b46a41d109001c8039040d1005400184170444240601d030781500501400c032500f910108071900d4442e080c1440448083c40071030804c10b000600000307029100c120403001d0503030241e00707070103155104013004001c1803003a20880d81401400d070350280b5540d0220328544540d242030080b18150a058008503015440300246500405100c0310209460310350344503102d840b078850300c0110000c008180014101c400160131a9101d510350190301242c40d00d0200d4484200c0c0c1c001e081801d4003060231301c1e01c500640955081190b03180000720801002c030700d241c41d0001c8082401e882e01032901d0b484190b80341032030680c80c1d030080c00308501001c20000030300c0c203603c5258801c5030035011080b2400d4000c2c0c1c00043c0c0e00c050715851045034182c5049401e04802d405264000d000803801443c16000e1500003030303224 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 27084673 1250 27083423 27083437
    0x31b030408030c03040f052b020a050705060c07081f0506060304050a03120209041803080f090d0f0e0301020307030b04060b09010c08090a030f0507080106140d061104120803090c04050c 81
    0x1d00c07000300102d0200082014581e040541c04401e80e111442d03145583d10034204030003030300790b4143c03c0c40403201c80150001c50343ca00142cbc0c001c1c024054150400050100c260b1000da4080007601c140c040025503002e0600c46040d452807604a601c001b1000c102103201a111301812080c480c0340204144000aa000100b40544030740c5414501080244950301000a0003039140083c0c116003010b150300001e0610b400d0161119100752200c07001511440810032051a08032281c1400358040f42203510054064280d000c9198039605d00100d0f00c5400001103400d980046c2d407440c011036241c0b0480c080c6450f160003900090b08012104608244c0c0100c00200301d841c06000c080c02c8420005040001520b801194101441e041582902c030340c0080d240072503a81a40e13101c0c080d21542392800203c1c00e81482040c2014640b0020007020203004140c56402c0109114034054411581c100320001d07201500002144040d40181c84450301c17807800d030728010b0070312034a942c201d0710507450300c01041040e003440000e450f04 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 27085923 1250 27084673 27084691
    0x8040308071b060203040209090a1703130c0b07020a05060310090f11030108060f0907030206040e070207180c03150e190605040f0501061106010302090a020c03070611031b03040803 79
    0x32945441c00180c40c0004034442d03144401d0081030690041c420550000e50041e882610111042e54600910b96140c0a480000400301940440b00c08aa20700d0380300613503003060861401044021250707444400d07070f045a510178008040042240d6040d031500801c0308005203015205180782d0301c0e03d000800307000c54803070203212200f96403109200781d40310740c580c4951070100120000c40c2d600e5840c2c4000c036940723400c11180781d008000c0c082c0000e4034001c4040fa50302c080701d038040c21090401d414135801a071b800c20b00030814000c520030610f0000f460701060708503824405e8080c41c002054030106800a060791501440001d41c030550705410441c0b405d812444980c40380c44200032842190400325503001500344e65011590203401d02402006403500d9070301040c12904e4540b80c16842c030040d00c04071a200c180920010b50301151000c001035801a254008122540c009001c2c0e9160034029520282261101c241500700880c01004022000d0a40c0d071b0103080b0f061180c1100c90452400782d844101c6440000c0c00644c0e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 27087173 1250 27085923 27085937
    0xe01030507020d030e0a0f0308060a0b07030203270904030827100903022406090105040b01080c09010908030417010e0f0d030902010921030806010518090405070e01030303050f0601090501080403 85
    0x5c00103800780409805a80c0c030130000f9008a030b183c10000c114540aa90701841000d8480d000520350700480203c030901036041c3c01031230078500d400c0020050500d0026a48894140d08011395a555903001c0c0c10b188214440d0b1246c00c541d0821807000c0070381040b05d22400d29440601011204102e000080c4000307400c91010300880d00b4040c0d0b00c1c04901b04000f8210f40500013081d41e401542c5502c0d1103440ba07101d41010780300e010460781c1e079004210550303404000701808642d030080840c592561901c020032803450181401a01c041d510807225246500c140d00c4040401800e20806122040a001c0c0a02040360240102801d1840c180070701e13210300798444842d003415514001a011a4026880c03880105401c8000d8403401c0007a0b018001401e480082c214005424100020083d601903402d46401107241c203160984c0d05441003e101001c14040e1043c0c0b618400c510340000c2d409078040401e8041c0d40700317550118070707828814102c0b41c4c240809081e4506000b4050018401030b684001511340c417a8051400b08 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 27088423 1250 27087173 27087191
    0x90102120a02010e0303090606011b0f060e030906040305031201141f09090507050c0c0105030c1b0f060c04090501050a050d08030a090c0602031c020310030f0512070b06010e01030507020d03 83
    0x43d005141113003e10866002c00300c01c00c45102ca0200b0080e1090100fa200c0c2c0c0d19001e61510449484600c3e810010503080c024205100440c407d54080c1440050031000caa14260348107002450a0b00300358000c447c240d00016820a80107489c0d41180d0041890045c0c02040d450641700044040b08480d400481104d078032441600c0c102d1107500d00800400000303004101604000300010003590200e604a1078611a03ca401c108552140f01140c1c86030901d420450b0a0889600705548410505400d202c820710820001d02060402402010300582040c0c640035603652400b2420810348405a108a12170100100208400c0d21800c03841701c841a030140d6000c1c2d603943c1300b49a91004059450019100c1110484041400b17a0000020981c40010219141039000e050020030305911003140c24080c2c070003549404100096412801100d420712030300c02d441d410750395610190301c2a0007001c0140c941c490400107018455070404981c7d00204400e18080c0000c2c039000f42c019650b4040a41c25500b0140d03908650 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 27089673 1250 27088423 27088427
    0x20306060a050310050a06050a021608100e0102071703010510020606180703140f010807050402030108070501140f0c010b090a0b090708060a0f080d030606020f0c060304060902030a0b0405010b0105090102120a 91
    0x80c00140c0340003820106d0b44da803640c400900c03940042c030b8080c000d071040e030003280c0c290b001c082d900d01c2c200c0b0801001040d4007401096000c010349000c800c101d150399000e0100700c0001d100400c80044c2916034100301600d070f6151804002c0d0301c0014088540540d004142801059218000d0f41c0e64044038030482d079061034803a404110001d0110700101e00d510f010401c01d22410304c40740d4146074102e0315020300b10303000f9035141c070108012403000384241c4a441e40b0401003080554002c44101d204099000d5600e824450552508d140951100030009583d95403001012202e1405551007030b00700e010588104000d14400010174007001014104109120b405d1000555668503404c0c1da002510304000079000c2142c0d980421513840d0003c03031203440404d092507404603515200054000728154940001c0c010b0305000c00601031268009001510042e03180c00c007190150710100544e262032403045100c04441e29050a20382e086943e16582c2c1410003004100310380d000d03a400215491508444099681d0b550350130501 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 27090923 1250 27089673 27089701
    0xb0f06030106083705040201031b0203030a1d1002070308010b0a0c060b0a08011e050906040b07030203060102030915030603010f0b0609040b0409120c03110102070803150d06050c041701020306060a0503 88
    0x400074220b40821040c4d2030f0800c1d002607006910070307201807000c0518800c0203031000c1c42448141c80140c0c014070004141c5005a040900a003010800900441c403003c0c1d405420041150280d40d4050340001d400360800d60300040d0b0900510042011509100384150000d1040400f0480a070407a078590b0242d401d1030741c03101c075820010301c80c1c8402000040141413541c00210000000032101d1860000001c0504c540032800da48560f5112025400e16038425205400039080540000d045200c227010941054580800b020304428508030303842e451b440c00e07504040c00d440d2030000e6000158209240300056072a80c0f416601500e00807500407400200c24400308009200c21600680122143c1c0320240b074054020141c98403c50196039075601e48085081e5141c01d07441900b000a0800000f000018424100301d410005203900060100c05054129141e00c1c003691000d40d40c444a20b60000b60400101c12002d2011131101c2070f00000754103601e040300c0000e5080c01795040c0403090203000000152100d03c540f030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 27092173 1250 27090923 27090991
    0x15060702040e030a120624050307020c0306010308030405010b010f020c010e030c130501030209130507060c020d05060f0702070501020703020a2117030604050c03090c1005040801050a0b0f0603010608 87
    0x22281c0711240440f00a0130640020f41e0f56217101d00e00318000c52408642c3c8240c640b100c7c10021a038890030b0340843c08a80075032004100801318003074100c0140b03155505006084c000c2d03006000c10b90302d905003400e2580c21a000e401c0f1540c1404071001c1448181030f000300d20354a214609080c48004070000201280c20880000d031040d50121440704c000d40b9581059100e0f5042e28002d0700e4116113a541d1440f003003851814105e01170101d60004c1c00c00c01055100d0031000941034406040c4e021081c407140c0d552483c000f0b083e0703807140598480c48204074045d541009510010082407004041442c55500412014203003805000440d0f071100101110202c2040e840f105804e0740102da1030b02c10000e000c8100c1258009880c3c2520903401c02011072884414402074034010b044c0c040281100301d000030100074074111a21082c90502070305000020b01c0320300c28401c8501c40ca40f00300c0702042010706201080884941031440500ca50000e0005103c402c0d03201c800150310501240c510310005102565190308062019 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 27093423 1250 27092173 27092201
    0x2091806090a0318030312090f0807050601030b0702030f07060203090703050709090302060604060503030901030506030c0604080a0506070305040b01060f05070204020307050d060906060c02061b0601120b0a02031506070204 97
    0x103100a85800103290b0980c0e80c041d540e401e818050403c5801d120380070b00d20001e0002103031000548114022030b803008408030700c40e509a1440c41402d5503041082e801141007501c0c65009000100140308800300840e40c009a00c7c400795280c03900e02c10909407640035000000d0701c07079a1302100103408404100104805541c118084402007030f07880d038510001e0170001600724018040c1201140403420b050041c1e00a80d007008020b0f606000c18240110010308006203015814031644044005540301d02c00180301510246029100411850601c140b40c824098688401c0500d01010400070903c0c140c0300b6030542c0c0440c5011203500c6d80082003102c180c010540065449840002030001c0b40781c001c0000c2051076100c40d4284a0b09a9a4203950100e503550b100790343c00700c0d42000c0400e006240c0034004004070450103045807142002c450443d840c00c4400d8000104000701a001d00d824080c00c00641a4064503428066103503183ca040c0c40802001d03a00c04450140c03e010a81400b150340d10307044043d40039407075 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 27094673 1250 27093423 27093433
    0xd23010308040303020c06031006080601090f08010c091406090d050a08030109060918080a0302091f0c140304061704060905010e030315150a08040213020406030b10110a020918 77
    0x41c1c00c01c50010b03802880100c0c05403144440c615120700b018011b8034405e0100020404040d890024280c6080400400c01410400107043c08209000342e00d0740b01c00507128100000030222813096010745000c0c1503410180c4c1001c403c8041400c00c0e91a44112107001905523061aa03002c01c0e0704d01580b030b20200540003401300303034040004207406038281e0040341121404a0184a80c0c144600660030041d0b05100c042c20041c81007141c5a20140030f81c00404034440c0182c10781c8520314503078144641110220070f40c80000f44094610324213100520740d90512541d81c0c44055458030f49450000381034251f5000c041e01c000d0a4030f90028040c080d41da400b030700e40d45400200038400d1890402a65869600c00c441d44030a2512515500410f802d20150140c070180c04100480e10b0000c0092080d00d40f1040100308070707130007129154180c40021060000d04001c003171030348010070f54418030010046220550400c040400c8904441d4518900c0e00041900060f50151754110041d2141c182d001d542c4060f01e44044090710030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 27095923 1250 27094673 27094679
    0x206070f0b040b06010e010512010b0307090801020f0d15240507081210060201060810090501020f0706050118020a0e010c0c05030717070e0108071502032703061008030d2301 76
    0x922254544030309000d036281ca100790740a50041d100341c0278800300107032010094070051102251001c0103682107903132414030203100c0f80d40311a000d0076a0700841d00c4030a56880454001031882180c09094285c1840c2a280b4080904010761041c0b0134100c0070440c2d00c44259440e81800803805101211000703504500d60b5640e032011403603500329800f810785e10388400018541002641c0c6106105a206648049000c1c01da203c0040000c00040c2c071003850f050761155070802078201c0040120004001107445000003140961510008900c3c141d004ea07001d4860900400214400952007590028550401d0903c0c80e20080780c0e00342411841d4403a00720a03010b02c12400d000c0345003c07086040c007401c016400c0440341c03a20f4481010081900d030a00c00e0411641c400502409140c901c0042005562003c0c03044034200006610700b140e60304820724000d0469000310400743d038a403c042c003070258040200050a01600e28003030345c0725a20310802e00c04043130341a40d404076004216601c1e0b60300016801d050140004550b1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 27097173 1250 27095923 27095933
    0x1030305192607080702010225021f09180605010f180312050c010513030f12110301060503090c040519020c07090509060f070e01020703060f140702071e030206070206070f0b04 77
    0x8030640d43e01011400880c0002c0e5424414000c40e2079500d0010082144950345e044180d03c00c0e90580c0b01281d02c403048005c02c1260080c070400c0080050119901c5040035403400c00042540041980040c0c201c3d8207155040c0f00c9660400f1010041102a1a0500c0e20003220302c0ca03c90042203940008002c1001803040c0ca02081d030000241c112003044800800c20b9448400070062807420551008000c240105841d005013400780e011540c0f13080341074101007041441520082c800d50300980106000c10404014000d00301000c200c0d044800e0010ba604016500300401e8820b82001f40b064604107843c0c00086d50b0015a005120b0000140341407030701400b0504058008031303200c100c103d55000320030464000040c82188103003074401f281c20040e0081c0c00b0090031500d0b00ca010308110f0712450300c82e9488070314075401f0116901d00d051140e10f49501402041e030801d0340003c0e0700c103071454507404d0001c2168030034801344e501d00c0200c541306541100d4040d0b0701c0788140380c41d00030030801e0715010380343c0d015076420001404 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 27098423 1250 27097173 27097247
    0x30f030309011505030601060c0515090106060f0f02120307090f1d0c030c0703030504020406030209070c0b0123120106050a030309030c0b03010608060f0312040b1e030103030519 78
    0x468120028001c01503001400010010148a070744d616502080c010881c5078024010501c4060140c0d04be80c40008a00004070380c2020705a6081c13000369540c40d020092180e1145050200c90114584102400741c10007000750349803210700440004079400404110313801c1c01380300100d0040c00820032080c0030690702c5085000001406158480f03442070752002800d0060340d40e08a92041d0807854a0302d04001c41d94404030010100140200e8102c0d540c0d14000c0003503039500c10b42c40d1142c8515621426510028600f0794220141a8040c02c00710b0b07001d42003204070381407107400780c0304c0061705442ca83c0c200c0700051415805850361303500c4280c001c0c41000700801807680c003201c00c070142ca000d0b40303110701242d43d0b07840c0c00c02040c80301f44510000074100b60b021503003130700c1c006666560800d001000c89050948034242e4602e40d60007a400324003c1e90002659200c40345040c540001c103101d0b086019400e4ad8516100680719111f8504614144100c0e103c25a440901130002c42d1607488140414182118110b06001c1801d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 27099673 1250 27098423 27098431
    0xc030209040513020a03030c0606030b0112060c03050105010903080304081b1b0904020f01030207060b04020318010605030703050613081e040302040f11160201050408030a021c0c0201020a0b060d02030f0303 90
    0x34504102c002111806410202800319a01610700c41030f0710b103191422103811154900403a2140e8031040004049043d22a019018006c0c03001004500002441c083d0101e90310502e08106150810f8010011a0780013800c00c422030f508499502e42d40d94481c034240049208080548a80d01030801701405c9400300001c0702111f5100042c042441404890704000d0201021600290701c510741320141d040652080e00132703221503841a0404101c140280c000101a6081110400b82110203800c464003108000d01400004010540c080c10042c0d0075629985d841d494000c05105a5502c2c6a03580d00411014030222401080d000d4a9500d83c0c02e030b40e04440116510030320050b0300c10b5080c5091050200007903c211070110240414051810f03039410001491140300031002d0303041c004103010000c1c042c03d0600040c070f10702e40c1c00d80c0642220202d04140005800102907241d00b000b13000b000341c40050342c000844403210381e000600d405442c1d5580c1c0014011002081c00250507002e06080026180300c000302075401 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 27100923 1250 27099673 27099679
    0x10c0206010e160302071506080303100e13030509120106030807200f010e0d0206030f3c1b1201030c05010e0102150603030f040806010503011407020a060506010e03010c030209 77
    0x840c0d82c1d5001600d100d04041e1a0408590b46030488541658000c2c0c0c01011140d01c168a01c41014858501c20301c1100e400d5400441150400010060009002c0c8078082c0509182503034042d440c2020001e880024040c214010103100b4002002c1400b83d5524011424040601000340310041d00c0e803415298030740042000300ca0004d0010320750f86209128221000880390302400030100900b4070001110400742101c145500300391480d0310600980c0b80e4000a5200f82c40c0300360420034604000c084003800d2204108010303401100c00303240c3d60064810310603101000c0c0d0110902441d58903840d04245020400c1c542c0c0e0003191400065014035548001281412640950240030b10b01d40c0d10001911910001408a07005800c18040040403802d060010340c2c0080d4003400312400c101d420701e04040140d0068102c0640c0380d0100c0010096031500340614204405440c41c20101810f2040e006540c41a0750f40c001061a81c0f2000025201d0344150300a50041400600a1104040008010b00258010008140 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 27102173 1250 27100923 27100933
    0x304060209211f02042301030e010c0806030c030102030c04091109130903020c120a0303051f06090e010605070b1302010201090803070c170a020a14010204180606020d0e0306010513021209010c02 85
    0x802011501c240c0d411030340c8020074080c03031648170790720340b81e10300700306c0c840c1905040c0c2c1d45200d800051800d10488040209540b00c1601605081d0209460107500c0307039109204e40c7c01001001303420380d59481600e04a40d082640402c040c8c02410005006000b000c40150b0400401309403040d801d0b00d07c1d00480a8030b4000d03000d484402002a047c40611602d1134a021183d900c030b00d40c101e0010b486540510352081e40c50b14014060b412180c20f400d8140c120b6801040055a0a54103001038500350440174010209800c00c549031030340355a65403c40480003044030280300c00a00003003007564003c2d041040b203107611140d0719a6900c0c1150b4090710365030201606903035207114012407400c40d021010440365000c01540041841c4100c2d5620542c151040356402d0b401550240400030f12800d0301c0c03e03450700103034810401103589030a012009180548010407d81085401902a240b5407400310310b5a065540550b0405036a41080382c6000c043c1c8580d4818a03682551a420800d4543c3c042d8800c01440d6400c0c0c0c259030b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 27103423 1250 27102173 27102223
    0x50106210b0f070509060c070909080a0f0201060e0105060a020a020d080309070801020405091609030503040e1509270102090603100305060c0711011b080c0601170d05030406020921 79
    0x22200041c11503c0c1c0022810401580340e561520502810120881208648441c0d0701d51545900366032400750100d030035000c00310b803004a882d0084103019520020344020000245070503094a90300f00c042c0b00c0c540c003c071000100200003a100b84142182a500544100d4000b403591900115a03071045a00f4207880c01b0320100460307480b0041c000c036021140c004258465589565540380c100d5400750f5000d40a100c0440740010000d1000e00250008080030000c1c03a10918000404059400003071401e50301c50752440d020050210b560040b003110141c11003485d00034800040420034024482d40e800f03980e2040011042060420320318400c0400e0780e12440a4940c661250300c4405058007640000074140100c084c0c820255521952800c4424441120140016603150729103600c181d101105040c03a54004030f006012800700c0128011300400c0703070350081c100d02010100080c1203000240c401005c0c10380002d0b03984c1d641c1c0d80380d10300740000a5030041382013040342e0f8114410382d0700e105040c56245040b500c0c030700c40 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 27104673 1250 27103423 27103441
    0x30106050111120309010216050609070906030213110d090c1a040b04090213120609060e07080a0305090303040504060e0403030c170601121b0f08010e07090e04050106210b 75
    0x10348501c0105038010700a183c5000c1c07003d845604010009a40ca40d428460501180b28084800070501e0103030300500700c2c9050950050f410310040d600510066404c0c060204016100e01045402c0c2121a510014199424000c8404a0b20401011021103402c00324403a062104919a80e01140d40503d407003048842c1c03c0520104034050ba1080e200e8800d01403001f0800070845800809441c1103500491410f55220124403059200440054410030399881e9480100b2215105072411024100014484949455a5280d4030041040010100040419190181d8404005940c054400200207014068983c10146a042c0e421034094000034100780c0d400d03800c68010300c2e0084c0b22290036584141581d580600555103081d1004050100c26564001542c8500030b1484942c8807003080d44c2c0701d1400c3d0b0800308000303041c4481a0807240f01d104000c41030024464100742031804498003407403a80140e5aa909000d40103000e1035101c0850101c0001d400013140e00001156981c0306d110b0000302019485005032 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 27105923 1250 27104673 27104687
    0x608011a0a080c010503060d1403040b0c0c0409080904090609020306041b0f08070306090f14010615110a0303090c03080c2107050d1803020a0e0106110a03020a030e06040e150301060501 81
    0x10742c0401c02c00c01c086a00c6023000462900200e009040a540070701085040324990707801507000a6040f80040303001008210144406051618116803d02032650b440d2641091441100701759403040e0354501403d00ac00250f0342024850350740050686606103804e04141610110a02c02003ca050565902240e50701d25480c022050712181c20042440d2800c55039100010076542d0700a50b13060795800516000903c101c1f032001c1d010714440c0000f1903d2450310426040e01c821300480c003003d000c4070030400040e1142c0022210201d035003501d40410504da4a0a00c20307115041500007400501c0e0010742d060425070002400001020711107200c007038070b2039a141c2c450542c0c041c001e001005a0040d98a9800b154407070707030407943c01e10308040a0011080e80c960008000e5640d640c84020081e030a50010441c0d1604525114015541e40c005040030085696000303482e00240b03900107003848034070f408080171034039404160f40180c000041845654141108120324114420030348610030b40c00e00f080895194801c0e10 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 27107173 1250 27105923 27105943
    0x15080f0d18030b07030f020a0908010506040618151203020102030f0f061f0e0a0314010c030b031c0512070e031041101806030209060402070203010608011a0a08 70
    0x51005555007103664080841c3d001400e08010140c541d00d40140b0403155100400c3d418507a901c0c3e503e41141340030885429510014542c9c2e119911b40030041040d10912111480c1ca80c8013a80001044e0b400300d05000503500194000d40381054400c3e90900c03c15805600030b40c01905070801c9410580d99001ba0b440350000e045528035040700c402e4051111100c40d03003d203601d000716141000d10491100b000410010003e41c1d00503540c4000700005240700690a108032140070050b85000d202a680660201c6d41ea10360503030b031604140208200300030045d13200d0b405852207900002440e65107420400001050000007a030010300ca802001089005a80320f44a424030740540d11076052401d501e500080c1164000d0103c101c1d5007a14008039800611042d682c03142d104050b4140d44411503810101003142c01c0344001380700d008052900a0500140e9038a02c4101d03885142110050780c0d6082e0391011074003501d030a51103034030258201321110085051400c04810f1078001990b942d03a95507500ca121503a9080024 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 27108423 1250 27107173 27107207
    0x105030d0507140c13091103070f030b0405030d0501090609142505070503070606080f0106060c0b0414010c0908010b0105030402101407170405040b04090515090115080f0d 75
    0x554000401609070070601040d100c2c00e0356a280c2401c008100d1701007043c0c40b8403c1e91a0b480c0321241c20000302d000803801c543e1701a00200407a50800c2d802074158005400040c4c0b410421000240400030300f001203a508581881781480036595982034000641407501500b1521070414a408ca400030b80c05200c284100954840e80340e8054100c07a6500340041d290011108201e010800017020441c20401440460300c1018000340c014580410113050031408250074070a64105230040141a03401810700c90025007089208005131202d2070548004000110b4080e030950074000250001e50704290801e045402200003407100600c140c00441b468441104d000354004040c03032000c0d403450721a82403458403420407524145000d10a46803040c074003940130070072022114009028460780c202405400310303180c002d031018005414155155615201a1030042110b00d600d40c0006a554409411401c140380070b046219042c80d403281034035030700d802e1024189643c504c02c0e00705000901c0d20504421905503001 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 27109673 1250 27108423 27108427
    0x206060d020f040902030102180a0602060f070e0f040e010504060f0b0a030f03110a05010501060905040603080307120b13090c0e0106080408090a0e0f0f07080903041202180c030a050105030d05 84
    0x1070360800810100003045203402c5640c6880c0040162401d00c0146000d42c0350030403010b82131500758108408245941c000e03d0440d0400410310503048004901c2075008101d0342003180250b0041c8005c41c1c4400c5908140b140e21505040080120020643c80ba50049020f1001405689400700c81c01040d1346514a500303801a0403142c0800120f5a000c2010500368403c2c5481c800c1048d504031768910f44614103030b0980355a555040100303c0e0980004601d4018001510300f400f1052441c2c5495602d800000d00c0c02d800c0c0400741a2420800c0d1245e80200ca0404004046030424000040c03840024044082c0849103082445800f1a0f08415482c4685c12940183d4410b005a42d0301e80d03865030940c01a10040360880001c91002c0b070450210401288128060781c0b800d16140b03003103515072841c880080c1040c0c007031041d06428051079113030220032182905d54456099990203d5840411025015068107178241d41b0410144041070030a44011401007040310014826071740c0717840400d501d0f4980340210002117601 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 27110923 1250 27109673 27109699
    0x30e0a1403070803010b040f1e14010e0301050c040801060909050a170f0403121d010e0616060216021005040819020f0411030a060905010e06090405030d0207030c0c06020606 76
    0x421101008040100300a880c14841c9607503c0340c01940003a00003210107800400e0606c841900c1880000041c010303403242c2403055400c100b02d03200d080c00b01c1c000c1c455828191400000d10743d000b0b803003940c41150060001c0000745031290391f2031182d400074010751501d542020000034070701210340905d2503115040b42c094800b00680d561901d004004901d4917103000001030140310200100300016000031402498204600201c6e541d00400d1802311401e40109961892405200d43e41e00c050103803440036043c3d501c15541c19580521030504102c12500510b15070001503003c210858000300110014801c5c0d40a2044c801e0b620f1007a079081c01280a0322225500c00d001c03281c0411100d003032000b400c500160504005041d40300109090396802e0f240314100c414000180000e1302e410344250f6000f03080180c010007041d41000202106071001501840c481e5910001207400d00c43d0500499000842c580c1e021035030b4210524020b0200710f4041c2c81076601c910040d40004d5658004901c22b071007104001d1080f051908 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 27112173 1250 27110923 27110933
    0x61b020310150f030b01060f05031306050a0e0105040f11031f0207030e0907080105090a0605090105040b0303040f030c0501030f0c0804170c160503061303120e0a020901150305010501030e0a 83
    0x101c0460344220b084800d50000904071084164a4061070041c20128120740c100500035048a4016030803108124003001009002d00100e542e0202455120b440071541da116155148060207043c43c14100075440c10f01030000b00910b003501c0000f410710540c1c0c1c640441041c5402c154607403d00190079044d52000c00100034080055900501c115842070034103041c042c2d00e08010401000d4119040c0000c95107400050025103001100317141c3c0100302c100148501170514002c0f5842500600ca5640226195009261103580c140190780280090850f114240e5950b42011402c00e8202e11a82d40800d20300215105da0154500072802c00d1007041d15140c10303a0710340766281c510305c0020b555803000191042c00240d090383d0080c000a80da2208405450203220304000c201401c3c040098000c00920814418810005e80c0001d402c0d00703502c02c8008002084680d6190450030310321041002503001c8a030900215544807014400c480c801020340e000c005580c0c070351006504076480680020360036400440c407500060 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 27113423 1250 27112173 27112181
    0x606050703020d0807021207110f031b150702060f040303030507030204050a0b0c0106030501110d060806280209150d050907030b180705030d0201060312030c1d030a0f030306061b020310 81
    0x5081d0784121580140903081c00d2049802c803c1c01184c002403190b5584107270340f90022051800c11012805010862a031030100d10b14940d45084403401602000445081241d83d6030079500f483e0380141c00700d40d0302c0b4000301d1111400c1d4010300044001c80c0c40d14010583c000d00c02e1081d40c0607070b60f000e000170040c030f0f05144544409402c4010000d190750b40354000400003030000e0087c1805000c0e441200e0b51a04990080034080e41c2ca2508420360641c845c1003085541502401c1c070402e0004144200d40032213801c058004007038411072842c140c11150001544085094140091040902d03a1000b00302036101c0398452030321265284006091403040c0408100c49450b803441c83d81d021500003044404c400e5031480420b090080b0000c41c080540d55840040090103031501400d055400340b13140402c6124200400076001c03200c490b141401d0341e07020210350070071074501704080803040707402900b00706c04850245001000380c030f81c5008100004401082031001e503015030003001a400d038020080d064a8016050740c030010 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 27114673 1250 27113423 27113431
    0x303010302010e041d0609070519051512010f0e0f130206090111010510031214030a090204093203070305030408030402040908040605130f0803160204060519090606050703020d08 78
    0x1160359140650110241c2c1700685000207074000c054005490f04001560512090b944400d004048a500c0000031003400e0243c3c1e07081c1e80d0112501440c40071005c0039103d480c01044c45407030988804600100340b03282804c0369182150388028410480d0758442c00e81800707120040c0c5880c115a0b4840410800500d07006010307114101043c50031605010041801900307582d0151004902c00a00040c00e1082c803004503c840b0002e00c50b82070101480340020b080501600c401440e5095881e42c0340782c428110341c0c03581c0002c21420b0b0002104a4815802900880d9841c1c800407461084a1403609910300444040305448a480d0962a50350560b036980d180c482050f0700040040b41d219503070300c0e03888000511490190018001c16a607140d103170300f092400400d901d8096008060b8504a0310400c001e00c07680001103d905400900300703244801c0e05880030034050061600825071003040c075040d096a901c911a0040101d03564150148030310303940c90a007500ea61040386c60140068008551b1204010302440003140c01c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 27115923 1250 27114673 27114679
    0x30804030509130603150b0d0803040201030f1406180105010203070213020d140405190b01090c02010e01060612050112020f0d0302120d02040302030606030d09060e19080a02090a0e0303010302010e 86
    0x2a04002600091003460f0000140d40d256035288024070900001305070403006046109420820b1900580004031b120361a0700e401440d0000007c001400c69100ea04110a00d2034000400e2111180c078560842002100300c03007250140381041c080f004c032859445907240c100c03803040e000380d49002c03103540a01040d01861607021f20f0185c0c08008030300b22a0401e10541340840c0f81220050940d04062911908041c00e0004082011400581d03800115030b485400504417002e40c0000200d1645900313082e80944200c180560280d480c00c9400243c05400480c0c90600b0381811404000c1c0d40c0e25440a11560600800041d41210202403100c0c1c0a0400e40b40b40784442e8040d0040740d17001a002d058500880d0b1211020444081c1c01060800442c1420400c0302e8000034118044c020070031049100030800c1100d44915020008942401e00c41c45d2241c0c4090322208007882d0440d030400c0c1d11040031030b54038084540f04034001c0000303500081480c101841010f00c00381d07c010255155904c0c1d0740046800c01d0003012503d42c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 27117173 1250 27115923 27115927
    0x806040207140607081b0309030a0302070f050706050901030e1c0e06040902040f1503090506160311120103260a03150e040b0106020c030a02130513050d03020d0b10020a0308040305 79
    0x1814980820030303d07200e02070b20354a003410703031a0029054070141c1c0c00c0c0c0405040c0001c14006d0010005010003990910380380c0303180044c0c131408a42018020500c840e5005041e60088000109400d64070078000c0c00325031400e88007400380c0002a10300030394400011104101030352410703140c04007d6210710301c42e1084010042405083c2920b03060103004a03403007a44079030f2494006c410300f000009a8903a020001040b2400c1c108001c3c0804e494041d02e401000b0087d0144102645031a01103500035844025045101d1301010b445140f00000120100401e0005541f00700c0060991b0210041d100c0c0a030100400c4181070504104c2c0f800016400b80c110388001d802d50f0904040c01182084112440c0703131040303000386443d403c03552600f90b01a040120f13800c80903000f90000340000380543c076401080c04000044000001d01907650f0504038106069901c40108a40074044e001c40c10154181c002d0301d403d29181004103d590340103410442d170243d0f11149103015070404025140428052101c0507032041c00790402c68 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 27118423 1250 27117173 27117203
    0xe030c01050c12030424050916030201020a02040b0312040902070b060406150f0302040e041101110106050105070803040503040302040207050601030c0e010302090f130203070603021e0301080334060c1e0806040207 93
    0x41c40001b2846030040c003a034500411034030070401c000c45882d900c2c00f601c40c40302e0907045800003515a00c031650301074095502d8107902102d5032010007080c50048000c1c601c50fa00e03207456010940c003039030214500b524203020a1001c14030619052194400b1501060964900c4000c40301c1c0a039280c0504451200c140b542c24000040c8001100801c03030320a81c41540b030f400d00500002c002400880707007180d0100c4280e00d003010030300c80f99810404540c00d103900300700059120f41d95480c1443c40c5204682009400c10300218015082220025010b41680e01c00c4640e440515224002c01e4000342c002d2101940c8405000c0c0403070000e981c550301c0c0c41e40248418038503a0412640d070b00840c0c6498469445000002c0d8002a818582840841c1d04500007924542891855141c0401d10307980e401120490312003884031008400b95880f42c60b090300d00040caa60180d80c242c2034203050042c010301c0d5401a5002050b1034060300b15204904210070b000d81c019603103070b03020b40341c0759901840000d41000f141165446041c900c0c41c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 27119673 1250 27118423 27118463
    0xf15160f02030604080702100f120b060c150907060201050402031e0a020a030308270706050a09091e05010b0c060106030b010e041a030c0607081903060504020a0e030c01050c120304 79
    0x160704ca5030060311010380d642031600c1401448141030f01c01d0802c00c0702c06255034141e2a842203134841d03001c02102001c1014451240011000e1140c018031399064440c2d20b14503a100040ca0000da0f00c02c1c0c0000c4c0c15170b8101c90756102d045c0e098580c102d90082d415000361012005030301c18550b620b0050000c820441d41e80422550100d50310320280d41042c1d011840c00c10030001d80401609040d21000402c4c4204d1f007010f010280388596a0f045030090100388200424960680c51007092001c005045c0da040500c140d040481e4504140645100790000d41e40c1007130b0011031001d6126040702c42004444000b03010b00e0b0b182c01d07000c9000782400d01d5807604005001c540100c040d03036075004040c068044407000701c500000b030404042c54185000d210342d00400c400d1081c44041409041903038501c1d5404c8003500c50008040700100d008083c16003081d80d005202180c01c0708001d82c03018003a05412415002c482c02d4280b014010740d4207008070700c041d00c02a84038801d00340d03810340340f04003840c1c1041c400d0501802c01a42481c030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 27120923 1250 27119673 27119683
    0x40c050d060b040e0604050d0212030f0703020f04090606031826090303070515070804020102030a080604061205060412082404020f1b0c0607080d09050a12020304050f15160f0203 78
    0x155000c01c1c1c5c444401d0105101c030038800c1d40c0303a884050005040e00c13019089110300c9400018801c80c986800c0100003901c0c64060780440d1020082051070542d100d4440d0303007402c010b00b1140904c0d00040d1902915080810120a14062003034100960742c1d0b1507408000c1d580100c0060224190b014032082c44400c4040d2000c10190840c584110080d11410441c000b000400c2d000080040c030401ca500000c1c000540d0300070013140d0b81120285001882d581da00004200505010f900070800050225084c0050103004281c80340190f00c6400c1c102041000c0280c12200401c3c00e031a10105030982e80c007132101090381d01e00320100100c0c0c0a400907042c6a03c0c4505200c581d0400f41034560640c100802c3d482901320140610114801c007100e1040c10200642c49000340f900030303501d404c154955502100030130b10900304001e0001c0c03640810b0018800041210081d120342261091502a01c510002542c039031620645107510020b01070300d40c80c18031a1039103107000c1032018040b0940e04014104015000f507142440 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 27122173 1250 27120923 27120941
    0x106051309060b030109030f180f03080703020f06012709060f0203090708030c0304050f03030d0c0908071205030d09290402091f0303080a0e06090c030d0503040c050d060b04 76
    0x54009500703078403030400c00300f500c00c60000c1c648240d02d80314001c00040e40044215041c282c15240c408840c00c4e01d81341003460882e0a811881c5c0a010300da1000041044800081002510035030a69008a0b00180c0180d940c00080c0900085504480004000d5080500d4006803031008014041000220380d00d41c0d604552030010741450a540010401000c000c0c1013203900020715040008515100c41c480c5842c3e124090b501a141c8100050207000d2a03503076080041d40c1c10508402d10810101c0400440903160302442d2289c45004d001e1820001060640e00e0740c800322403a00f15004e140b51030f1501d0386030001003510540440e211807000764504001007a0590a8060b07a507401158201030805004000d500d000043c900242000d40340d032420347c4103c4521965046941c5400c1c00e030000d0326400e08140142c030f403501c0b003180a88100c00811481c0b442c0040d04044072041941610380b80340100f03030200c484d48011a00a03121003400720701000141007110b05285441d0041d0070001d850030210000506582d0190317 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 27123423 1250 27122173 27122209
    0xf0402091b0714060105060301030c0e0402040b03010f0c030605010f14090d0f060603030207090203041203051b13030b01050405100b07020f090115090510020c0f0f040c0c0c0e010605031503010605 86
    0xf46401000c1c2003044164050401140d03a0f03402c540c510b40c0d400d0044125070041c00c0c801c07280358000c5411034696400c640e9440324010000d10040c2980c0c94003000a242460a14000a04042001519500540c0c020100030300642d03d220f00c08160907480f12507680a81942c0350090100054040030500c900c00d1542024803507032000c123240d0300d1420000c0c5000741d590014413100d072040040c0b10000340922883d43c4206d0842c10082403540c4c41c1c2c80c0e11030545004000994586000041c0711040301c240301010000d07241b0845950301c0d940d072503400344400c0303c0017114505004100154107001c0704031004064141a80700405941b66043c0d80004244110300a0b07100d0b00b01d840b4218007203480c0a0700145010050201903800001811084030300a45e1105900301d03032401015141481c40c856141c0000785440740b0009882408856105400104102c81028003070740c0d02c0c80e1061012884100c000034007030403a0340c41e650b45815a107614401082100010b50f01690540d0b0f2540300140c00e0319802100294030b0100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 27124673 1250 27123423 27123443
    0x30302071d161b020402030c07050f0109020a0302090c0408070303090503100e030a050a030906050405030c060708010323100f0209040b0a0f0b0c0a1703070909050f0402091b07 77
    0x448515510141e0726086000764009036010010070014840521140d1411841c24a000c485145000b002402c8402c0b40603401900001c01c1210351080d4000500045100707404544070f0b00300c601c0600f8200c4503818002075021503014020005460117106180e0130490200006190030340e50312038103142c180c0662049000c101420010802c600e0140142c604413880098188810403001440a0f180d00c6849040c03824413a01003051102c05109500c540c1031070b44d00c0071040000d405d10b030400969907000500340c0b80c0c0070300c07504002594152142c1d8181d8126680310120b4a0710803043c0101860380e1070020040b540a101c1d20680041049180c040e4862282460307500590b10030043c400c1c4820303102050400c1c1d00594190344100320003000d40d42c0210446103410032003921005401492424500b07500c4003e0124202140030546500340540114012a40c0d034407180f44240c3e0703414078079059860446844100b503070388200013030150800290641d84181900742c81c0d0214018000c00a5407500101c000751800106 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 27125923 1250 27124673 27124679
    0x150c0903100f050609090c0112020a03020f07062c0a0b04080702030a060903020f0106060207120f0c08010b0f04090503032707060e0306010609080d05070804030206040b030a0b010e030316170403030207 88
    0x4103100c060b801c00c0e1b400018005500b40e000002c0c22450a0404502c10140c0c001225160648280e041d11502da0060801c1d50b9500d8107805c041001c0c8c00032143d9141c0310340c6c03503035544120200322803c60501c8035003100c042c2c45406c00c96107554000741e40041083d0703804502000410010394090280e811554460440080d62811a080c02440c000d46c8948a00183e898210203004158000480c038040743e5a104e4a4000d11106282c4541c00c84104000100700e90000c0c000403a1083e019000820504001d4401000940c0c280c800c01058800f02007015009810400202d052a0341000801c2d065106500e58162250301d01d45202d440e104082d8400000901c1c50300c1200c88078174040c04901d0050441e890010442c504005100e03803900381c1800920280140020050f0800c41c00005640045030000c001e039480d155a0000160b4036802180e010714524604240741700113600549880d01e403684043e0040d07013008082003107000030610050701998032004080807040008103600051016511981c050945d4520b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 27127173 1250 27125923 27125929
    0x2010210060915050303030618060609090c0415090e0a02070201090b0307050705060a15060f171006020d02151906030204050403050901090807080a2003071e0503150c0903100f0506 79
    0x885504924070a8000300240586580d551611844403071144200c40ba40d901c030500090800e2094ce600e00b604010039204002c51a12002c0207081100c2604842c1104112134800c1190003602c0e50003550900700010f00400c00e2034055a016101151060615184d0310381c5450140328030340c1084030b100300065400101c031001c1090500c81d01d03401c49143c83d000e210000c65100800f42e42115030203a81c040040d4078420954503403040d0405604640d2a19907004c1c1c60601c5010704030744403454003a400251050310100c214117480043d50203000c1c801c0384444001900c0d1581c11441c402090211000c5081e185d801c0803015036603a10500d03000364030030340302c1503030f10840030001604170342d0305a0002d1850307000241f01b00207070b40c004100b40325219404480081001401c1841e000d004040000f080e405204071a00803969044550742c520707031281080c5000c9105a41c40040682c2c0e40d10000d007071303507242400303034080f07148045918090003440c0002415280a01040d07c0c0002c02c84084800c13045c000342d1a2000e00072282 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 27128423 1250 27127173 27127211
    0x7031d0f0c0103020304021305070210020a0201050f09060f1611190b1003030c02040c0302161115040609090914060f010e010605030903070201180b040b030109050c030402031207020102100609 84
    0x1d2800e0809500314682900015503000000c0324000c01c43c0d0b21040010fa085100b445158040007038540c04640700d44500d54000e00901c0100e07807600300c0c0d0243e00041355141380009034252003611456645602035858070200500002040c0d00d03402481041d0f140762000e441c0501100c01c0c1d0044403030043d4800a200d040941590001504246680c1c041030b4045c80401d80c0022100340307290b0155000300340c202803c04201d000788200c04403200b828401c69444070402100d0341d0410945030303048502c0c014010484140d500603110380c4c850040480c162003c00c000c803541e00c0d0059210540142c1c807002c580000010f1780380c281a41110340c06243c55180d00140484102501064090100c515209040d4038046200301e559118540010303042c02202d01010003c020152103500c090072500480b1500e80d95201d00d115580d400c01c0c02101c11071401c19000030603202659041d03c1c4100d070014000c01c00c29500c15110078850b480b03900180d045000740310a107142000c1e1405840014514203400003100c0010b815102850 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 27129673 1250 27128423 27128443
    0x20102030615090904030804020d0f050a0203011b0f0804050f16060f020a03050a051303170a030f050402030d11030405090106090612110306060f07060903030509060108120304030807031d0f 83
    0x194020f0140300259202e6184050340107525041440280d2034600024901c901880002000c4240034207401c0100000030030b1164449100790024040130a030922004000480000b5100000d40440c0700e42260500c1052620f8001d40039505885089880c001c0980c14421803000650320000181e03010400280d000585160042961005d054060700c2d55500400f1b074440c0c0300500c003c100c00030680b070451a0700d10a00200543e03100d1a070300490765490182c155641c20005c440d0000c02c2c5040c03d80380c80c110082c00303000d00c070703903070050151001340480e410a4500c05801c42d41c141c0a4402400b020440b0380f12480e42d0f80c00380c41c81e610b8502402c1d1030210f0081405540c4c00001c0206410607008008042000c2d060300e070460411501a50bc03031075040003400d018014004050401d03410031400506054255000ca80656082400d03126160b032280b16182c0e0b240034140f40e89440341001c00000340403a00c6103030071940002d410301d40481d0841400500d1081c0c650a4030150725203420049620b42800c80c05c100724400 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 27130923 1250 27129673 27129709
    0x50114010807020f030a03020a02030904050108060106090b0c07090c1211120717010b091201020304080408120406080a0b01090302030a0506190903020c0405070c0218061804110118150201020306 85
    0x81030081c864411703124001c0100308814990045076803102c444c000c0c000e0b102d0000c03001d40100515a583d0240d2503136280284208004500011400b18011103510210b07080103c48038001c00e02c0b04d2130801541d006010344c01048040060b0000f00c045d001d4518010a0000d05120b8842c0f44c9410303000d07280d00f0603080c014005030140070b011242c14210210000d5558111180710012a443e1194140801e00070461503507034500075440041007100704120b590160090329070680454001030254581125036100724021103001c00d90200005e221140c440c0c128140340c0c0810316000998030b80d41c1d4086403911003456400c440c1500a8410082114040c141c01460a180008107014203541500d0181d06e502400c00c000d801140c46034001842540100302c40c61b822a405072001041450351841e00c44080300071394425201c1c0209202d100d01c1e060a5800380350141d60030079030700d80b45003201d1070042d110900382008051100e01200c000190340302500d00501108051500091ba0724030746074041000344d4014132a9052 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 27132173 1250 27130923 27130933
    0xe0a0303021c09080d1806050301030206040909080409090b0601030c0305010f0e090f0f0d02010b06070308060904030903060219090f0f0b0c0c0d08040e060405280b030105011401080702 81
    0x40800c0d40018410200c034820503001e011224240310880d00b40f80c25400c8100580b144072030742c03d41e0390360100b02e80c5031014220480e001d620fa1650000c580520080c440698801000d100500ca12141a80039481d00e910510082c0d1a0540c2e030100c101c2902e40e190029a006005a01000620750701400341d030100f82c0552408100c00d6041114551107444070b4028810700301c21400000e00020b20130045a984c80b114041240d21000c2d80710400303070342c91103945590401942000ca0300801070602009a6405580c5a220220169504418000d1015004005a003000b440640010100d10188000d20400c078500238440c06c842c01c5010080c000031115409501c40200041c1c0c1042010302117050001500c2074061143d550700c149110782464420050481c513844036a0a5088003041000e000400c102d42c10702442c15220b80d40c141c2040f0488200315580e60b200c80e0b078103032602d2200d4074070360400301032001200c40011041c4102001c682101c0302604a000100c000d10801c1e8015030700a003505a2244080c0f004003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 27133423 1250 27132173 27132179
    0x3030504060309020102010f0603110a08060906010306020a0c0c0e0a200a23040816050306070210020c03120108030903060609040305070219050d03030f0e03090117060a1d0105010e0a 80
    0x10640e205512446041507a10b543d10f50071a8400e4011b450004001e420a016054403401c2c400e501d01c0300e0038000b900c5001a500006a0110007080b41403280068038060076007a032843d2181c41c041d50000c000841040349540e00e80300040d050b524268007a0078400902000c610300400e20000301c404a52141c3c01c1111000c4a090300c0c0c2e940102240e50851051404403c0c811a4200c01103078000c47c000e000c6a01d41011030007260640380001e5080c9a884860540090940d42c0c4040c1500c80030240c440f000140c000c802c02d0800303402c05400030010f545800e81201c0c60b00b01459203818110340280c02030f40242c0c0000445240c1480d040100c1900108211401c640300c0c1011799015215218a03c2c1c001c1c0106c10150340c1d040c03481050078914005000280401079000c0481c07800600900e903004030074031010701c0d007401150210310000580c4e240500c107840e07418007011442d2001540c070000416456004900070b034040340da5815200e4039a0300c2c0e400c181c882c4d5010350510002400c117840c0c500b0b0b85402091004410 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 27134673 1250 27133423 27133427
    0x30311120402060c010e0604050105040b0105010e01020a170c030c030409050109061217071703060102121e13050301111306051201030b0601020114010f05030705041406090c1909090e06010303 84
    0x1d410a41c1107072116510b81d00114580d01522100d10304882c04d00400c0c081106010040d009030b13208030301c03e1185650580c2c0b035000650704100702880050041e0b102040c89000108580c0490b0500c040c1d4240503400c00b5040901545503900140c6540329030380000c941044205202e009440c09000422001d101017403e111105d0300c6200103c0b0013411810410880308401c4054800326500c03607400c0030703449a0b010250805417907540d00680d82c03940103104220703618084032200c0f400e0300c0703225a804880242001138074600c1c80c02070704501ca980301811280300c000541a0f800344929001c1069004406441e249140404107001c2e0b46c590010040c410300b08811140350b1012400d4030b05481e8020180700c056202c07000101d00400c0c0c0e01c00070084000d204000420490540c0c20b201e02107030422812036100d140c603074090109680502940510445a410104805140914070558450601c0c4140e038103000f64260800f01e008a00e15150001c5041e0017028000c801660140240345101000280741c554590f91b40 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 27135923 1250 27134673 27134707
    0x70f14010f09081207021003060e150f060d0504170403151806050c040812270312070b060a0506090d120e040510080c181f0e070903030311 61
    0x40c10072160100c0c0707061160184010401030300846044400c03000d6000d10804080c0d1000da800d07841078110402d02c40e099842402030500b030316400d1038002070b291201a4842d0300c024074040100da00c11002d16508001c1d8442102409440e000b801c0049124146400d15801c9030f000540c80c170070940d00400040c030208003440c6451b03a4800350700d00b0003e4150f502c05100021b010812030000c000900380428031006c10503090140c030589078420705035040c400d000d490b200544d108003d40c0e824000402c40441804044201500943c5c0001606503010743c90003001141980e4807206003115009a61030904c80181014900080501002c0e60f40307a00c0c081043c000a0407110301440004c01d641910400491083c0c820032188180305009003043c405400c05a44580013402a0300550380360744078004d2060340c9454001c41e000410841c24903a80300301e4540c00000c03915032420403003900e000700034080c0028061161070501d41c4141d640d503680c58001070840c60000c0c10f60b0a4454440e0305440280700780c041040762000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 27137173 1250 27135923 27135959
    0xb090a05060a060c03080601120209060a17070507110f0a05090705030403020714090a110d0903030204050301051e0112030302070c0305160902030c041403070f06020604060e0102030714090a030b0c0c070f 89
    0xa101e2601540c41e1840c02c080c0c40381c03014194100354007183c040002500a001084945023b0002499695603510104d803280a01500500100329501a075000c900704143c0324030018001402c0c44411580355008641c003400240e86140004100000304020302d03038113003c40c1c0040d0005442c95003051a44500040c8a800090000c0240fa130b900c004100a02c9801030441e2186c8090810520ad005070b42e08002d40290440d11800c4d0280d400d10300000c1e8920040007c54450300c0302951845000d03402c01501070085074400200310b0601d6801c1100201180341402c202000314820001408072080003091004610140c1e03101442481c018024080041c1400f4151415200720700900c246204a13140020b00d080780c5580010036224904401080f025404a40310740700f04e020b050306020044c10444650f080340320807102200010540c504030701c1c2c0c4030300301401003600c1e60004200d00e8010346c403621000780050342a076058160001c0058800b10112080c41620014203440003800c0348107180944040c2291a00b034 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 27138423 1250 27137173 27137177
    0x60603060108100302030f070305060a020304050a080a030b060310050f040b0105041a070218090d05040b09040906021207020c0310020702090112050319030603031416150b090a05060a060c03080601 86
    0x200007103001c4104000f2400554004044602440c00d8506480c0c440c180c40c00283ca5030700603000011000c440500171a07010b1039001008003004440b58a8000745030300814011410161038a0400702c1c0d60f40c5001c013070750142410034901d102d014608010010603882480c06540130303a04241c5071407801ea0308074040da01140e1010f0300601012400c0f50f40014030f84640300000307602c04c0c1c21880c1101900c90200c69944500e18202c1102c55040e01c40070103940710300603481034040340e0a003040074251500345030300100880b621801c805420044507a90806c2401c9040300c40d240141d0240c400702040d46030070007100145d90381340c5a0451401c00c5a80202e591600305001d484868072006400c0f50030400700700226003140c0100203141d0154020043e00a01411081c0b00540000b8038000300c950b01c5440ca5000ca40c0034501000003036407a003100740d07504410a00c42541c0031302490360b90442003000307854007240580300d101e40c0000020640b43c204208125845141c21035020004444000d0740042d402030070542c0c11032424 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 27139673 1250 27138423 27138437
    0x140615031306020705061006090803030a0b0418030e1c020310020901020a020a030302010e10020415030b031f021209010509070b030402030c0d03020a0201080a02030c0403080d0e0601060c0c0b030606030601 90
    0x4000800c10040801e0020407041c0f00264000600c000402d50750b008a14592880c80d0361691001c04480ea08164003801e1070a800c100041910050b03298444400322030094400310301610100f4003002000340015047e0b02141881d000040b040ca0003420301140c0152100007124400c210750003090f03940140b0401d1900d02039000a800411340c1c0204602400c0c55802800100c140d900c0c2d140c024040d00081200107900d10484c040c102100c40ba034002e58013585d40795030f160315040700343c514124041e00c1d011086ca601401202c0b0700104121222002200301f08003a4405a580e011a203591910380c540140800c10390392400f03040c00b01401c1d0200300c0c0800c40c0c0c0c0b111245510b0ba1501c1c000a41130140e030241d40c80e400300c41d40c5040420107401242d400345050003605e0b0340c0340a0361480c1c4c2010030b07480111410740081008210900000d910240507201455010900049881c2071000071490440283c00c00f00214580c01c11410800c441050b000c400390041c00c490508504210010402900005c0c01a0341030120f6 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 27140923 1250 27139673 27139681
    0x1218030d05090c1207030507210204150902030a15150f080c0c010609050109150302010e011b060203010801060512010902060a0503130609060507020d080103051e0f010c0203040914061503 82
    0x801c5403d8021600400903e411801041e01039500c00d071521040380c031401a10000140d00c00a4000c01c601201c06002e505142c1800b90b08001c0184400c00860740f021700702c0b13003011492144600c00356104005441000030b032104c804400c4544944140e0041c00207e011101038060aa80804800c03018050390420500c19140c1ea041e5240314051580c07004643d40c0381000c0010000a070b500316034100c0e43d048000304490003040306185040310083c000a80850583e580c141000d5214104480820442c00743c0c2d00c051644950311901603074404e82c1f101c01d00c0c0c1e440d4002400249480319001140d005104001c0190f051030b5400324001d13004d04d94401c010f0280202c0090420400075030a0b4604a6011904116407041c51030310703800400041d10801c3c010303c0343c20588000b40d4020b0181e141601d4028006000c1040364100703540480000ca11600354a0040380b580d0300c1c2d190403d00a506108010f03801942e191418451440d080b03c40300c104010a56038501d0070303c94a62200c1420030840f180c000802c9130f403562 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 27142173 1250 27140923 27140941
    0x6190305030414011101020f03070f0c1703090a0b041a060303030f060409020a0806161202070309050f06070b0c190e091501140a0503060411030105100c050a1202031218030d05 77
    0x20754045822178950000418628480820004610400064403962a80c600c0c00104882d81c1c00014001070144102c1120b03d40814060000765a01c50220011510172403030994034420344900c2500c0469001d200d0541c0c5203401c0400203600e55205205600950840c41c0c02655040136071000f400349409940d03210b0901d030554445840107000341000c88120703016410071488207000400300104007000940401c42204c1c01000c0d078000c607813140e42c06558070603c00c1c3c10b01c000c04c207410100f000410790145003082010002413004401030701c134500c1c00401c1902e80e0506689180c00e0400a803218003000700141c14070b9126921010a1070308a5144402e0500c40b0f403001005035404004050141108840030840c410130690000007103201d21415182440b0003000c0c41a0702d0070500080c0629a44020081003562405108103c0c801c160b5005d0b104854040801e61a18002e01c60318903100c4006800008490341c280707000030402c0d078115040c0c1c0e040100b03034110045500d0b01c038003403564031040c0b5030f1b140c40100300004 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 27143423 1250 27142173 27142187
    0xb040807060c050a0305180a021c020d05061501020a0f1104200a0908010e07120c0e070c0605060a030b010b07050f070f0612020909010302100c0605070203030619030503041401 77
    0x181d2004081148904410380982150488462440080d04103400035281e4441e8031503445a812242000305529aa95800c100c0315400d2103d19000b01483c6404400c0565541003081e48694007501c00b510660a0150001c580040764203480780c1558041080c003000103408010140e0703544d40001c02d004d010041e074000a0040e1206600c04800d545070354407807000c1101460001d054409850b1900c02801b80c2c0c0c4c6480c6401c0c2c1c1c40008154280e07411690b0304000001c4d150401c00100381c440c044581c640c0d911110408883c0300e0035254440002c0e1080b03003010810005106040e0081d40032a00c2070443c82c503640d41c13460300f02c2c0140181403030303c0008038048040010801a80c100c54904c001900c000e540c44140c400c00d03208451107500d0018005015180814085108440c00414080c08210075a821034090103041c02c1e5542c07582080125400418000c641507215a030702407251a130107140e4a04081e4104010031456002080031072240000030000184000205d904440101018045104007580161821 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 27144673 1250 27143423 27143437
    0x3040302010207120905010224071407050a0f021503040f1101020304052101050c0c0703031d0402070303050a06140315150303030106111203011d0a06050d080d060501080c04030b0408 80
    0xc42c41018004e00140c1008990041c0d403005c1c0c0c00c4540d0448506080c001e000040b1107844140b28071a0041904988501d04110304440805001c2e8586000742e070780c0906e8110300b04400d03510002060300d180214503081c4081c1e0140c3c0404540c582c01c42c14561540101d18000704001007140700c0303102c40024164000d0040d0360091100034460340c00c080422103601e1a100d8044464692940fa01000802616440041c0d4035106080c00090080900b9541e00b40c41c26441c50000c4003441c01941d00f0241e0b141e0791307400207209841c82580c5c08142070405e802183d0554203d03400c01c0d40002c00000c00302c42c0303035280000c58030910050701d03c1d4100c5030388030b443c0e0326501b04000000c1c064060000000100c3c505400a6012071200e40c0041141c40c4100c0700c030301c2c8003410300007801030100d00300340500c281250810000a8540001020030000f414035691b030002130703030323103001d400102d500800200e40b240c0400001d11421000348002c2c01d102105103003841300b618840c89240401800301010001040c2804035813000d0b2114 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 27145923 1250 27144673 27144683
    0x3030b0a080a02030c0102070303140702060706020c010c0e01050301060f120908040b1b0607170a0e0303010909060506030105070c0816021909050912030106030b0609060a0504031e050307030503040302010207 91
    0x192030711400e07010380751200200164040d20800b000500e1652000602404803609a84d4540b050269035a0694403540442e406030703408801401900045201440148400c1d10044000100e64108060161410740c0301e107482c5061100a10041010702c0c0c00c19602801c150b12450080c40d080c102080000051092040180c003201001c02e001c180b0405203001080001c1e500741c03810140d4050b0001c0c00da0340700800c40e4050006802021900c0010b05000f0f02c0c80d4002203411004a0913003000d001091a6070400d03031005400b00d0322141400140715192046130307000f95058000744003e00e404103000d421000c2e0b011000307000b4940007034417030180e46065199058442d401420307405205610858074541070f206000d00d0340350324501400300720340d04000640d04c216169803010090640c0c0c070b07050050307004000000d4081c0c1c0108003041841800e035620f4009104404c44c41d1162511039086080c400e2000580f9201104881c9031480200c0c041000001510202c3e42c3c0340c503080390703a65140d20f41203000e03000307030180204 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 27147173 1250 27145923 27145939
    0x4080a0b0106080109050915190c09060f1407032102070303090b010504021c0b0307080a060203010e060d0309030609020409151e0b0105040e0c0c030c03090112020403050607080403030b 81
    0x10000812080380c100e5100703544640c940e07601c44050f4800c031082960b400c4441d0780b0201d525203079040c1704101c00343c3c0303c400084180c03518549900000e06440c0c240c0300013800541c112409001044d0406209100c188040c07826212000b4103203140151441480809800e0190306160f520300c02003a0302c0ca040380c0700502c0c0300664544e072132460054040d260415048684003003000020550f42030500c00d413040d01c1c4071402e0f82c5c20191400c2130030400400d0768202003074050050b82004106a0410002c14003501d1007240c005a8941c0741c10300104c401c201c05083d0300e100741c0b400040000460313409030742601526041040019103000307a20006004024102009200d40040e01810815210550044001d40c0c4815001c1510740d4110000314100da0a45400ca40800c0c418030060041001800d000c42d03110340300010203890880c0040b003007455a040940c0d6891542d100090740c0c0055684080c5104072031191410550801e41940d03039544c0c8802d0010004002c10138010001070606110760072179400103201038092a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 27148423 1250 27147173 27147193
    0x70806150d05030d0b10050906072409050f10050601050a050307020106050d050109030f0e011d030106080a1202010c02030a12020c011d0f01050112020a05010c0302031306090e0a0507080105040e030408 88
    0x9004c0c001740c45e41203206696078010704c404c01b801581141e2440c074009240510b481c4c25992000881d41740003c140000034850039440c450707086544103101c0ba042c0200e00410b0f2141c88a030025240c54030300a805684070742081d0502090740d802c901640d180c0707200d03400e11944982c0c07403002c100e0040c6102d0b0300035940022900540c5c02031010640c000002d16000c0d0381c0c0c0c060208000041640d85480d041c0515000400340001a07230040801907402a95110040021a1103680c0c2d14003c2d10303006984a0503038403401e1840e4100e00300343c1c0920030480c00e038080340051800d00410101c042c00d5200c8804c844840c65800103a40c505020080d8000e0843d90b42a6802507201d0904d1091079544c1c802036140013135076610b0702c00041282c4141100070b01c201640101444a450b003004011203144021a0b021401c1d0b100038072004500703400304401c40014201a942c0c0c0c45906160080000f00520090419001c080c900340c14480307030783d0f071224090b03040d02e9040d40c021494181e1190410700d140300380d81c01030100c0c0c054030f40c8c40 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 27149673 1250 27148423 27148447
    0x60606090501180510050d0b0402030a0b1f0e040b01030b03100c0f020c03030a1103040e01180c08060d17040305070b040501030501080d0203090d060204090e0105010303020f070806150d0503 83
    0xda400c0c0c80d400c0c0e858820046181e02e034a800f00c441c41c00344592000346401d500900b50b1054004121034159051701080001e1001d0104003a80c200f560166a160340301d11401281d800c1c03601205000900c0c22100e00e000d83c0d0812806424000c1c01c01c180c5016544600390003205900a03003206103103080140466481104644a80000303007000d0092000203200301440002407403001a210f080c400c1c00502443c6041e440c0c0406886c54603071716082c5807050005002c002992070411403068020308a8080520420000e482c441c01181c0c1c490078044244080103040c85240d032070b44660b8038400c1c1d86c03001c0e8501c1520201003001c034882c0030340d42c801810751180d01d001140789081400a042290400e8800740140e03621200c5e0251a4078019001400503401403140c2c62052500781d440c0c5c0780c1c041c001c0400602d460740f5001e550003500c200c901c24048682d10751004004155040040c184052001e03c0507200079800d01c0101c5864001c06020220b100c0c20300008241280e40300e00c5400189644a400c482d1384007605504 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 27150923 1250 27149673 27149687
    0x20708030406090b060406031e0c0503070b0a020712110d080c0d09080f030a0f03050a02071208100f0503030d0b031e1608070308030a020a020f010618060b0f0306060a0c060606 77
    0x49804c3c4100d040810080c4c10a40514401d880d401b206503800b8103003034034000c0c0780019902c100b03403051100751000003100c2d181032108501a0401c1d5600d55a2640c0b8604082c0c504181680440c4c4031070142084180442d0716420b0240511008a5172220f5031401403c25018a005401071710741c00f4060b0b083c001c01902d4008200070f04980f40082520347c2501d01c43e4065440380150207005000c0b80360034010400f1288694400380d40600b00040060510442d501d0700c61401713100310340c0c0d04045046038040c041c0c40541139001c03000070100c89080c0307000c0340e08180c04a610707401441c0403282070039201c0500c007401d60340c1444050302c882c060000342c5c0c50242204005aa88081c9905581c4d01240034060101d081000402e02c41c007a2034100e8081855a01d40051010013948080042c40450141c0d50710104000400e024840080140140c903048040340c2960640440310550f0011601e410f04014071400000c0410569500a004031000d50f1140d85050064a2014000c80001d0055141c0314010450b6900586 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 27152173 1250 27150923 27150941
    0x60f090b0a090803040210110a2906030c04020f041a040609091407080402010c0506040309081207021806010c050106030b042109050907050c03041401030c021c030f020708030406 78
    0x311a14041d115452220100c542001c006400382c00100005005410580c1c03450064002a00d03042c900509661106402c00d00030a904545218002603004140040d510483c20b07502100c070000700f0b003401e041c00080e64038400c0303018050159030046918004c00180383c1c00d0320018818164109803c020000403410384c1d40c05402000003040f014440499000c07040d00c580e124007410844040d0b056155504250b03501c40c07004204904010b142440321000890510086001c1c40c070039160840d425040102d5181080480308020303c003088280048000b607030b02e484000900d01009030007000543c031950012504201c15001c06072107903003840000010400101101c1d441580980d8854480321440c0b0403000c01e10007124100340028403a15001d02c52840c0416506410251504100d850040481c50403420754104d60300041d50a60040340c2c0c46503950709400b40c020b4001441c4084c2c80b5010441404500c01c210041204081565456089100241c964102c3c1d0845401c80c1c0036580720300c0d29180003405442100 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 27153423 1250 27152173 27152183
    0x705070605030106090302041a101707050705060c0a0c0807081306090518060111070909020a05030105040b0a0903030b060403080306012a02011b1a1608060109050f010c060f09 77
    0x8400000c0207072152050303c3c1070398002d9070b55121052440d000c0001030104010348013012001d00c40c1464242d070300c09080802001b1240c4034a45182c04580380c0302c2c84a4401450f504c280041000103000280c400316856502100700b0140d151110030302201241c40218500b8001c0c0840d400264400c02e02030060302410b201003203959440c0860780c6605040b00c840c0600d11809401840e1181310106039442060241e134400c2e0103140090b103907508a041c0d1858a2061360080800f5541c40300920b0070341c20150601400f07404254024002070810380c0e00c1c00010540100482c10441c0d0f601015004c0604c01d4004100c0100300810841d1640d8490411190343d51060315024041509001d4842c0283c03105010010000c00088081e54002040d400550f000240d249643e960b40450710010b200084100d003106618400401104030907142011448904c03604e00100d8800344600c1100f08000c9aa02100e10015140c0940302c0b000a0440680180c50070b54240100504250400b1707085886502154031903540c940c050 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 27154673 1250 27153423 27153433
    0x14060106080405060108031306030911090a0204031103010506010f08100504090c08010509010c08070f110a0501050f1005030c0f060d0507030507090f0317090604030515040308060111060403140405040203040501020705 95
    0xd206c020740d00c0c4620301c2440004454103201708000c60082c0d21444030700c0e0054060182d0100081c00088a1000446500b0300c0b003a4081014028001e403010300350030154060340200418102100080d000c480301c00c05040401201d40c0c00505d4020640c0c0403000204000341040c0084200c0c0d150a091110060240d202250328007030010b0b440b40014000c0211030310964581583c15290303410b040790080004801c41d024040040c899220804080040c029190300a07000041c660801010460b03a43d031000d440c044a0103034481d014412035402203102050300c00d0032143c0c0b201011514001c40c50f039008401c0f40d44023044c9807100300b019182d01a0041c91007100a56103541c07000e501e582c01041d0720091800007038900061b1040714400b5000c040c00800d540a070003844c9504090340c4c2d9481a1600451400c0d810301000c2c62020300080540191a13903402000900340780741e080050940c210f0f5542c1d0010301c05001c00550156142c0e039866848111806081c0140044d03651346058180326020754021902120b45100ea = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 27155923 1250 27154673 27154679
    0x100207150e0a0b011406071502030a0c090803030a0903030e06090718090804050616081903230f0a0e07030b01082e0e03040b030109090506010b09010c060207140601060804050601 78
    0x2021803a40750b040e070301001c40c02c0240d0030302209071020034004c034006410900402448001c036400a10071170400112540c05070382c910700000e004040d61003c94842003805014002401141c4022041c0e95101f40a00343c00500e014a90408a000d081103031b0b030f016a240100010300c040c1d08030109281080e211401c42e000402440500a6000c40d0184031010f081c402050100f0700c01c61500400400103c50000301c0c12022418545403001158011180659080741c4038402a41550305801020342c1c5081c500324460400340301b640c131990100d9008140300030000303000d030019200317980c940e2108066050340000c0300c0466440b4680030b1086030f428002e03020f07580304003200310090f48821440450a205074920b00311040c11171100590290015841050f031500081c400400c03a140c0c040041c600802c402440403510502c0b0741840ca08101044e04030014200c0e04000040850760890746885070f1035407003030005036030360358504080a86007400c41d00407459008060001407481d6000000c0d50140780140282e400c1c0381d0f0303 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 27157173 1250 27155923 27155951
    0xe01020115080c180601020d030509030903030c0313060302040b030609040c090501080102040602060f0103050c1c1505041109010305071406040e04110a0e0403020d03110919090b0f15030910020715 86
    0x513080f2116030040e0b100500c0d2000151007504031030b0700904210101c1c0e061080714000203081d5000440c100941d580089546611008602100e1004010700d06086103014245501c000007448003d00e65401441008081010010a400480700400800704104075550b11645298041c0d80640b040c1c200520030200441d024840c00d1090034101ca03413100c000c000c04150a024010760844643c08500711104681d12a40460218940384121004aa90000f803e00d001e20341044041c0f1986505070040c2586030043c4002000010320340240c941c0f0800800c0015400e500140541c811030b00017000b460104020b000c00c1042c101042e200d000c0c41104c4c6a6070007621111800050b103c02c4a0240c0168400d50501442c1e074001d500c00c5a2094280c00c040c0e241c0040c10000c10410b00f40742007640c440940d001d404114000e114031804841100c2161002d1000520400040010180d0300400a071080004003240c07582004000e8011110a444010354940da12410f20f038941105003120080f0041c104144e6050502c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 27158279 1106 27157173 27157219
    0x30501060302090903031e0603030906070f0606051504050108060103020705010e060a05093405030a08031b0403030f080907050604030c0807060306080d0e01020115080c 74
    0x303803451060140072a00100f560740701e80c209005020789551001da41da0350740314562901c003845807039110000c0c1c2036126402000c1d500c850b00242c0c1c0340400012010204c00303140211ba0800015503503405000608540c003000400c003d10401041c000ca6014483e001e400c01810314006060010555960782129005450100741d039100c07008124218460b4010181d0060310302020304842810418414500c0d40b031540d151103c0003420307c50100501107543c03100d00910000b01181c4800110b400c100d89a60710545100c8401c241c0e07103610440500500048030116549569044012514114100c40244020300404003a010754080000d03280d54010103000594020341e152a00186040081031911030b07241e01c02c0040c1400c00000b0000c03a4070210b03284903a015642403070044608944d0042340104485040c82040210200c400306c2d020b0f4002400340c5000601360342019800c1c81006030030f0115 = true := by decide +kernel

theorem cover : BRFrame.Cov 26978423 27158279 := by
  have h0 := BRFrame.cov_init 26978423
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26978423 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 26978423 ≤ n) (h2 : n < 27158279) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
