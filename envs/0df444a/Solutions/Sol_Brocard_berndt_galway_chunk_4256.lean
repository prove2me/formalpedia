-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4256
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:01:44.706554+00:00
-- url     : https://prove2.me/submissions/9f764c16-98c6-4858-9514-d98485347726

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 765287769 ≤ n < 765467625 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 765289019 1250 765287769 765287797
    0x2060f0a0b06120f0910060f140a08010203040302100f02031014030f1c0f1103120604020408030a170a0c0e063403030b0a2409050d050609060921 64
    0x10007120049500c205504c142d91010f00c08040c0d1805840480c01c1040d04038a007001c541c60b0030400d01c010b07010301c58108281c925409070142d00307086910004003555182c0c0e0141c61198000020401056404108024081c541c848248404085074110300143e00040380d00c401040d80009003040315540c01c201c0b44c1003508010b005c1d208101441e509003400c000040c00fa0354550420684100400380d4800020346845440d0b02e4000d0300c8807222050307030b0f46074070403081d61944901200300810a1503a460781240c2c01051300074101d81d540d0340306c0900541450241411513000150000c0000c1240c81c0d140504100b030320700390307581d62004140d08041081036000a00d0004105807128044814881a000e850440a006400a14006100b40f4006094441c900070142c0075980c0300034200542440c4184140705220807940c5015146100a0111030f841c0007a0301c05079001c0c10034a07059050240100701940030380e82070710580b80c2907a11282300903907414180c010700c2d2842011502c0000c0c0040c200005c2c003010001412 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 765290269 1250 765289019 765289027
    0x60b090f1302041202150f0a0c06150305010f060e0c090915221512150b090c0d0b1206160c120906021005061302070302031b060f0702060f0a0b06 64
    0x1080d040341c100d41c1107244039000902e10b05041d441d006660f000024080301d03500d850640010603006540c0238030b881e02414801010101c10802c1082c1c0c0080e101084045a01c400711035407030a10a0203004e02a0303541000c0343c600310300401e2030508822414810300c0795402942ca024061402e010000000134050b0050006922900c0c1403961817a41c0b41c40d12101c090f04080340c0c0c803501e0981e401180c0d98890f00c0a46d951101c6c0e001c108020455070315000d805e4008111100a0041015503030262215804a961102e2804108280d000f0500c0140000c0c00011208004d82d0412400340650f04081041c440160750255002403d10100817407520b5158069140c00012000c1c1a80da101481c041c200e0600c02040c43c8071418810720354100118464020005d2040c01f190030484082000400840d54054460740c0009041c0180750003002240c043c03464105a5521a04003242c2c4292105429590940c04000360004039195510010781140100c407140641c840719242c802c0484000d1071600801a0880350603c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 765291519 1250 765290269 765290299
    0x414040e03070f1217041202010219121103011206090c0f06080a0b09330a080109020f090708151302070b0105271602010216080705060a060b090f 64
    0x10014208052140c0704610f0458000c0c90104da0903410807004104005041c0c0c2190908150005055000340c3c00c8007a40100310701c041c0c41240039100d491502d841490402c0c050210b080c1e4010b00382075a1000180c020458441e40c0c40000003144420300c02d890000c4040349299010844550201d821544202001c0e14503964800d8442c1c000419940002c01143e051407c00c00c0342241030040c2045106c04444078809071a001c207400300b800300072004d10101e11b0b040e403c03a101c418007520303110701c3e085000811141c10381d51b030303410024042c0c00c000008a005820800c415080c505000204a000c0c0d0701c580c1b5451169641c50030f0384002146490318483d80060416040ea011800f1480141603103401340341c42c0b100c01c3d8101814055260340b18600348080c04540300170410421b050030b84858200029412400100310b80650803406030090000c0403040000100080c6e00300031401d402080543c0c85101a03441d02c0d038801601c0350480300c030f85c0b0600d202603601300070f4124103146c5200d040500110007054152990000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 765292769 1250 765291519 765291523
    0x306060909010f060305011202010f030b01030e250b030c030a090f0f06020304050d09081f06050a0f0905010603020a1b0c031e03080603010516082e05010e040606050414040e 76
    0x1c1c3d00c014901d0188040c2030060382e5150183c0c50241c442d10740312100803e2640e000070503800030140410201603407801082c071540c0c420f4000701c1c000e0306032008076032911030b80300503064040c1d0f101d40d0544180d07225140001542c8440e0000d603071080465062035402d55403200c68402c06409240c0b021200d9004407284440001c509049510440f4014000181c4038a450728000d40b40032040030030b51050114060782000350120014684407a4400c000c000740c4050103980d140030181907076802595010101d95800b1403800e81000d0050115620440c00780310701e9036160815012440744181c0c00c00007803e40b00040008030000c141441c0068402d46105102d6130340c3c3d44908414100e1651040d003070300c41d0f04030a038003890b9010040d15040a0102c008101c1c49c146444440308481ca0241407a00b8043e1901c0010822500341245030380e00203203180c050618007400d03034074140301044030701902e40401c000e44214046410a032041e076043c0d07156512068600f80c20600140d02881103400c0056001352142c2195503c10b0701 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 765294019 1250 765292769 765292771
    0x14211819300c17010905030301091a0108010503070b07080405060d051014010c020618030d0e0307060e0d1b030b0c0d1a09010b090d0807050c01030b12120f0c0d0c030e060c120306060909 81
    0x82e5040001d208000c24442c510bc006003003082c181081230361001400b490740c0203e60501140c9a08286642d01c0c0350900c0c00a45a00495201660180021a80c070b8460046600400d100b48032070320742c80d02501d81701c40a074445614103d074414002200c1014940040c24801c000348180400d0600ca01e0300400e880000174501102040c500000502201c40301a0a0074200314000141c07289003040c10000000401040c42070a00071809404280440e4004c00d2205580c2c4e80344d030146400030f096503410b07d8010819901c66000401b81040f1505e840d24030718401103200403e013400e0b04001c1000d40700d646080300f141d800c1d400c07045003549d11021881c0305900207400e001c010414248140043e2490326517001c00941290a4070800a0140408480c108a40c12000c1022280802001c00040d251840851040070b9805140c04070406071207500308140d881078002c00102500342c840e9880700410111070b418000c8a0107005e8000302d49a0110080e05030a10405001c3e40e8000700c050046401c14650030001a00884 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 765295269 1250 765294019 765294029
    0x3f0213050717010b09130207061e052d1503011508010e062805070c0602070609020a09020a0207060804140a14211819300c17010905030301 61
    0x4100c05291001400520b5260041c035042c040035082400301d0003ca0040c403d0441c0b4a001154009003070010403040e035225902c083d1a41c10b140c40301580220313082004000596240080d8084486000844120b42c0182240281000650840da858406d02154002c00400c4d80c0ca90554079850a03400c0c5000000e2000010106007001190318070001000b41e00b01a40070305110300300300900303000415103240742c2c0420603c014643c1d00090300d0303030f40c0c0c031000c031382a4604802c0100741a000003407007410700a150f001109058002c4801084e81507544941e00101d20400e000e050140c0c0140008110712405286041d030b125028401042d01d0541000c8418148110098200c680018249221400120412825500383c400b001280c0c8440452400200c440c01003900c8105000c0668081413008d884d41a16101c0d00300b604100620043e45a4644480c0381d000170204805d80010804181d40c10b5803d0010000e01542100c2c180309010b08006420820721945000d0495039901d030200000045c0c020001580204 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 765296519 1250 765295269 765295277
    0xb0402031504050604091703040311100b010810031e0609170a1b08120a0207050d0e0f010c0b040224300f190e07030c3f02130507 57
    0x1e18200e0030041203900c0034000a0296103081c400c000044d42040100300700f121080c1c912a200d540328034040794184a0380c2c2c1c10b0004c40c0248482c19041c52006c0d00312015a6030241c0354041a40da500a9141d090380321403201030545850380f850300e04079000b810294070b603440c001c0e4000f0405900ea5140e60b0300100103807400c010401000981020500e034042da8030811008900c00707858081017542c5031220940119902031850030102400310b0a51411541140e960651140548404081e40b09000d4240644845c40034050403861624406661282846084487d800300504c1d80e503407216024410348460085059000d42070003507102e200c0d1140b4501410445048000000361000141709969950211649065038440c4031801e014641c010f030024240e20086c1120741e480c1c02202d0040c0b00c0c01401d02d2600a80342402410000310901110f4482c074029140c4443c4510440c0c106485003583d003101e054030400010303610041004041c418101040740c071500003008888282801c0b940341d802c48800b95042c1e4081 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 765297769 1250 765296519 765296551
    0xe2a06040b070f06060f0e0604020a09170d02250902032d04050706170f190c02060105150405010206150d021f11210306060d02040b030a200f0d0b040203 67
    0x200d003900500c4050b11205402040080c038061541f506d6500180a240c40341d40c02003490f03c80340e880307080781300010301a1842480000b00d1502c2e00e1516918000c082c0d0307005000da043c0c003110404028040380700102941c0d900e855041d00d005001c0000b0341001d13004401c8907880701c0ea48009050840c4159101007110341031206181804c1c0f8259183c581107500c01c2c0d061214900e2007421803103007000d01c0d50303100c02100f00b41c803020740d55500030042d80c12a440301d00481600e000356080d180341e40010030b14180d0700d05848990070000d0194412100340a54414a07006a1111002031168001154441811000900355039081c418503030008000d00b40d10400a454150a441a400c1080d40702c0c00140b0040c40400281c1b1490662190080920f4120341c00800040b10000124005403154030440d190391150f26400c540300d6440c2e100c0048281d1058540c0c818031030a10051a0300c01d0a44a0301010200002c11b031145000045e0720031406c0381e00710386034401d1001d6403800106c0d0252100d00085100d180c0c005d141e0405 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 765299019 1250 765297769 765297773
    0x11190c06030c08040816060b04180308090601121401020f0a03020304030810030b0c2101030506060a090606050a080c09030106030c05040e2a060c01090302030301090e2a06040b070f 79
    0x4a5002c000b01204210205040c04041041a4111105021000c4410031841c01c5e0342840b901030701d11982959001881d05860440030500d084440c1040f900c650389844590300c0e40700c20250754000c00e000ba050a00700420010000074002d041c40c00300205800300150a052681d280d803400c03a00a4600320b00401d80001c104410036602c010069400b80221503c6e268150960319400307543d030700040c80040803c0e000202c4902d03009020700d0200032882003040103c02c541e1640303065611038400b5604070340030b01c0700d8040105514a43e40100b205540207170303440700d04204240100f114220b030040c0003415400010084008240c500b8000e480c00b840c050340d185510345d860081400110b586000007410141c0102491140d220000c019094001104481d150720b01c1c408900002c1041c8101c8140c0420341d860a100031042580210146040710b410701401c2041245925026840314280c1414028441d5007012810f90100750045481c4182e1003c7d00b82400c0640b0340303401c00c415a200e8081601e0614240044200b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 765300269 1250 765299019 765299021
    0x3010c030b1525060617010911090a062606090a11010f121a0109060306030f02100e1207030506060d02030c010818010c03020d06050612041115180f090105030d11190c0603 75
    0xb81b20000740c0204031022050716500070180c4d118a104e485103402c000402d503080443e8100e2000b5154200d0446c0ca0140194004d0400c0d074540181180d59011b45000900c4c010400f084112060b41c20600007401c48036400011104000084542418800c0004617107400708a140f0800100c0d45913a8020301c0700c40384400001d45a400d80e0b078000800c00d406e040c0284005402c0c0118000041e5069900035030302e8460b00b400355070240340c03001d41d036402203511412104481000a201c0044a0103503040c0c0f0001d444103814440c000e118410701070341503440b08540c2e0f84594031a070805030f80f151450100100d95500c0042e501c1c00e488510701c0050000740c01241c1141052a00c1c071401c07004000031503080380b40c40b01416030800307954030090000d0002007003a103060301151240c0c01d83c4a046901b10074041d507a4402c00c211302c0e40d61050348600d0780c000c00d68090100020305200c1c04a030705a070700c018014503503403a000d4002c41d40b640c11006555501e00510035000202608e1002c86c08059125242d80c03041c680c20520020 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 765301519 1250 765300269 765300299
    0xf0e07021f091a060a0b0319110a0801060306050d0209062116080109031407050a080d0f0b09090303013804080f070501080c07051c030b03010c030b15250606 69
    0x2151941408091004c2907442030801c0089802c00c034841b039240d9845402c44940030111110040a060502c411041681a200001c00d0780102d181c1300c15601e41d807650021811a0198050590051211942d14015241c5480e50540c01003000381074500c80e00c80083d4040310a0600d408c803520592203040402c0c0d418201410480180074444020044400c1c1503c1c010f0a214038000a051043d00000302d14050240910506040d0340d041f006d0300c2e56407418450418000d2015281c00240c0a1030003129800d035141050340940202003100080d030441c1d09041d0444c035001c1448403e019900e900a0504104400c0002e91112089080030103a442d9458540e0050810b0b105c0c00041001c0d40100a0910403680c04c100ca668210000800280d1101881c1c50542d15141e001c0a1030f030110040c1c40b01460540380c2c503400460f2a110154000d0120fa000c2c9042034064038204c81d1560750040442035007907030410b4101d01030000040d070140056184c40344c0130320b0b82c40d030030409460a44000340c03540014002d0944138030560b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 765302769 1250 765301519 765301553
    0x90b010207090b180619140f1002061909020324090a050a03180806090c040c050702090c031b160c2c0a0f020c100b01020105010f0e07021f09 62
    0xa01069100c0e034000b980b01d40c911003900405a81a2000c10065110900746030a400d6029410240c501d456001c4011100c90060509208004001c8e507010703207041a100c8210b0708213068000303000e10344031320400e01d01890040d41112802d568603070144000d07a030204102600c640000100451071907921940b80000e00004014a50a502248420b030006d4400200030300699010f10b013038402c0c0c4010200c065000709080c2d1200106100c1d100603c0f4000c00e02069610703480d1070131136040041e4400351f901618a4041d800700a58004030ba50001111035107100e00450348000340354203440e51b0300c402c0041d840c0349400c44101c2c2c260b81155207020000308004070180f000039200704046652001e40000604130381e48400300268003120726940120b098165550055549100030460a6440e400b0511400b503480d078000c508004c0c140d06240361a501d42d4010b00c100d0307041e1000705010502107800c11401024200014202c2d9003180315410700500c1c43e40b04614a498540e1002401080a001900340150540301c88290 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 765304019 1250 765302769 765302771
    0x411090411071e0317180705041b0302031911040f0e060618042909100b0a0f0203120c0304060f0c0e0d0f1202030307080a0207020616020303090a090b01020709 70
    0x1c0c8010414140000f850310b070b0454000c0c01502603074030f0700312040c52118142040f011010402c0c05484007403607801d01c04110074041100c06465580040000343c52400e00c4d20b03000c0d0404a420600718a1294009642c0034801c0d0004048040d40400d41508490343e40c403107681e0007000030a00340a100b213003503118001800251007000807400d00e02c001440ea8800c0301c100c0c0d4400f100d181ca010003030780c41d6a00304006200b1906c1e8a180d0400c0319429041c20035400b001020300c150103240c000307400e40200d194002c0944422992a905101c4a1002600c00c01540ca000e1015031006000235503000610411300c0d48142c01c0b01000e19141c1c10b1a2505009440f910200d0500460411841c42c14855008909200c0400c0403559441103620b0b070f00b0030a2400310301c0c8601800d9002d81d54400d42903240c002000b14011202a030fa0380390702d5681c01407408100e00401c0390095004100300081100c8d2104581c10100107800101601d26061003100011854056a40254003850f190314911b0344960701030200100515040c88 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 765305269 1250 765304019 765304027
    0x19080610090213271401090c18031b09020307090302120a0b1b2104021206011503110c01020309010614062506060e040506010806071106160e0411090411 67
    0x10944020742050180090228809072248400d11113801c0708403007500c01c0d0204200f00004103002091800c424041d03024217074289800e80b002c15200c0d80280c02045062100043c41c0340c2182d90300307121100c002089111103c80d03c103002c0381c0418640b0055000d1200b688503548090b01d1072040c8140c240d05400020010340150240c0c0005c0350f94001200ea0003004038044100340c0c2040c2001400c07901a80c1c1860900d0182c030300000e030f0340c0b2031340940d06401035000325007441c642030581d0a00f564074002401600860101c10140300096406500099a442d9170b01580311300b8141f05040081c2213800c100da42c207209a445440070000b51060440038484400c054485034039040b4039200941e904141d04502c0103041c000001103500f0b00600380d100c903002d860000e01d00c0306e060600e420700e183d0300c1000780259102c9000750404280710a0091f140f10000c0145c10004e0591584c030141d215400207903610001c01407091303266031107880d07540c0d9201e4030b40e0307078628014031a0711050494140800c42d28000c10003407a800c0104 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 765306519 1250 765305269 765305287
    0x10b010e04060e1503070f03060f060503030906190302091002150702060903090d02030309030304181104031a0604060e0c07060b0a060e2214091504031d190806100902 73
    0x11003e0b4000d0b4040408040700711240e005c24a0600c685e40021003c02c403441c0d0100400c040d0390091818110010f405101182c1c40c1c4042580b0b038812962115400f40c000c00078880d0344d2118089102502080d0f08006090140400119025605102c010700040c0c20805d48015000340c0c40014541143c103500c011703c0c20785804c1415507924892558241e00c561800d0300050215601002100c2c2000c0010307058945503503032040000c98800603600d0a9020905000b11040f10200310700c00e0b2402c4940000f1207400c0e100440084800707004000d070200350400d4480034041190081c0820807405000c030250341e16591211414071b20104c60620601d544290f44400c41003100c031358000c0c0d01c0600c01c14101d0751080340f170201001e4900038203801010f0229181c14040020125007440e1a010300c038041c1c007000c1c0e502c2d2030803241a642e070b01402210b0080200c2d5407032001c0d041024801c04045400000070303191a1f507203400a00781d4440340490740d102c94143e034060020058001103400d0b400c801040c000c030313065061044130 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 765307769 1250 765306519 765306539
    0x320907140607230a1203020304032c0405090c0a0e01080319110715030f180b070302040308030c030601090b13030615030212010501090b0d020d020405090309060c010b010e0406 77
    0x150308040c85110081210014801420310800c529080400521502c105400354251601e048103030554021042d040b000114902038000c1b80c1c4907550582d00d1854410f50000d01d00071a01b42031812444034800e0301d48152032915540b0680e4095003034180140340d020b41c80410440c01c40d0300d5401c050a03842d5208010417914600200b074a1307a1010000045080031140b080842d503004506400103204d01c10071200080710a03524098065000d055a81400030340350314640481034442000480746044807100810740803911040d04640c100500e40307800b40c50503030760b6149e8540540040c3d4001c100c2c1e6030f000060280560b08224140700400c0000110b0b0b06040d400900105018010b21001e4801511000680300d420144e10700030000c0c543c0149403030500001820868000c104c01d01981540038038200500803540340c1010100d62070741c0e00800c040e4648607240e007030101501016100d40712a1206104400480e500e410144c100c17040d040d8000100d40c20b0050005100000e4003425600940c0b4210042c0109164 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 765309019 1250 765307769 765307799
    0x19060b030f16050f09060411160c05010201110a0c06090212120903060a0c1407061b080430120f091406011a0930070503010506150a080a320907 63
    0x1c1140c0000b041c0028020001251180380309d03900d02c9644107003107801009503208070101911000e0f8000c100c03c411a00b121100c80c0306005a40e004640c010341030720001a6141c10200125201504104600e04840340b0549016218000e142070020080f44004ca03a003401c10145a12442001c0c0074082140c400c034024120200d50340d03203248a0000003914609200c1c540d006138881c20002c007602c400316120800020070780c41058074100c82c1c98101200c5840e0401c40310060900c0480030103050b259280f500d8000360394007218418034118003521102c2401c04803400e44102195540a940300c120300a00d80c4030030a0820805030042d200c0d0b0701c000070418400b80e042400ba1000c400c410780e103c481d030f82c2d0524408602d2100305507103030317407803035a03004020300e26070008a4030004a52058000703000544440c01009401400740580c8248104d003404140c80d05481594104e8010300342a60015861303a410866511003481120782c405e000c2403050402c6032a141038801151302c0609a409049410b00f0100a0508015 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 765310269 1250 765309019 765309031
    0xc0c051213052b0b041e02090c13050303190f090f03060504211e170c03060d1209050f0405060f010509011101060f030b06060a0219060b030f16050f09 66
    0x2800760154906400b0800303039008840c1540e102a48000b032921301440030070f9084804841285d144244110710032000005031442e20760040913108039070f541c10200c0c0b8068100200c3c090304e11704000070002e2552000e10041c40c54080311016201c00c110a80005014580400941c40c200128290100040800342100e0010350b81d00403804112900e490415404020101c0440d111812600401110070358200041c2580200003a032004601c000da020151001c24504c001c0d01e10904808001074600e038806001954000d1009000305e103204180e440390050151440520008900758000500851520507805061035108031004d02c220703c0c003400890070b241402c1048030b0510101141524040c5c7c0244920a40040898001c09c038407036403482400c20b0180903202c20f44025060340d000c5465800c081081380d0400006400408102c03c8242029210000080d8240c4905030345590403041d030340d020301280500c1003040b8010200030304241d50031005110241c0c01584512002850118191a8207010a80c882 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 765311519 1250 765310269 765310279
    0x4140f10210609061e150b070b040f050303010914060a0821040b0c1014220302071a0d062c0402040222090b030304030b01050d0201120c0c05121305 65
    0xea80b850540003420504000800c850304200d101d544c80b448000001c1c0d6440d0720000140f041603a40d060314420b0616a00603820091010005032003c00c14071036880d40c00030b2003a00740381c14040c216140d0324290f030801c2e0043e000054840c0c2c0d0882254103070100b82c80d00200112840d510051600800c155141103126004080c0403214036003154034014142583e0043c400c0c030603900c1e960320303643c07034602c1d100c0340c00c5419280d20915020f0003070b05210300000c159225290b5100d0360518984112200781c005011004218114410900c000c41c199105084800e52041c00c4d461041e100c2d10300e20303c034005440464000015000703e540b0014282e0302c25002d400700c1e280c40800e800000740c9480c00824060310403c1c00c66260b01044c00c025a5140b101c80700761404541181c9420001041c1d03100805851307100c4d5200180c2a040f43c03600500081c82d140b028605918414140007a102088001800030354000d515150042118904420103002041c001414107c6503020314601c4d014811940074044030701801103e000b0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 765312769 1250 765311519 765311579
    0x30d05040803071d0108012c01090b030f060c2b0906050405010b1f0f110a0b01050306071806121821020328090f151106040c1401020c04140f10 63
    0x4034100800f0b0b168038159105c2a0a00c8c1d603119050f40c400b615170101458001e22070b07101503401c6141e011407441d0007891022122441d042045516035007490000140600540220314180e680724054481c3c0002c0900c161408103079403074141002400c4503d80c000701801040d4030440c801000c900c022580030003900c00e0821500d00c011202c0c3c200c070100f00b0800034007420b1142031414814050030b40345250485508404484844d07503404021200070218400700040c55074100c9003440704e103000b4403101c4101d107100c0c0c07030001b000800840100d802e0f803044681500d00b464030040902d001c902c0352440518807541c60000f1890b01900a000180c00c1840320441c07002c08070078013681c2c0a140d00c070300500401406408001e41449071200041001c03996504403030740c00f00d850280c0c1540d1805000c55914896038200142000103840c241880755035030f401034030207811406400c1011020b6551b61050030050900c1c0407000c403451400c0c1e81d944002841c064101c452080c012041008208404160a0020700702d1003940030070 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 765314019 1250 765312769 765312809
    0xa050a0b0418060e1501170d02161406091e010f031103062b031205060a0501020307030827100f05040b130303060f0603023105040b03030d05040803071d010801 70
    0x80a110054200d01c01c0120340c000a001c0c006002000c60002d047d00903a40310b0a5440c1c420303030392210050702c3c103150000e03601010031211070176000700f6503111f20142ca0ba614014264000911501482c070b0b004c1c0c101c010100d041c001950b88515210403d01d0b00f42001c000700080000302c21103c0c080145000c2c4070b01208100c0c40c00441000174480d0780c044c0070401601411a0500d40903041d12000900e016001e460b100015030300780741106000701143c0068018500d4000f40e0b031002c907034224008122841401040c0b09201802290800b201c00c0c0c0c030f0f1100054081003600c0d02d656401e5034155012121401d081005000201e10402c5a0642103001c03117405080030039041c80c2c10b90107408268400c2107104481040010000d4154001f45801d0003005a511a1101094040005140c020011300c184641c404400e0040307040c26031000c1540b0710020103ca040c100d0f9141c0760300903142c045804891020303004c0144042541c01070307181c40c480140301140302031072164400000c20211051103826240f5115000d0510 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 765315269 1250 765314019 765314023
    0xf03020c0f0d0b0c0d231012060218030f0708060a020301030506011203120c110d210c0e0411041a0a0503160c0215271e03030408060a050a0b0418060e 66
    0x16507a05610014040102500c07881c2c48240c8149481d103090900c1b40000514403940040d020055454074450814584100d845180094100c590802c0280e090006201b03840c1e582001354039110340140c802482d081d03080c40e03d8141040c00140a0071000350040c801400020000309800d41510300b80a0200400e0381e040c03c0464070b8144d03076a6080c905521b80309403203003603c0d442074a42840354400811500d20741a0b5036000c82d581f2081c0212215800549101d550a030b28003500b04070780101003440c0c0051840c2c0c00100150440e1404c0c0e4414070070b1740000404105503204d05803001c001c5004100b0141c00c00c070100300c01901c0e5100092017001c501e540180d03480e52550142518a1107641c0103805000914086104c0d207101c0e920551602003265260381c40c5811008083c07409840e4010060260000354032140c26101070340100340e4585030b041c0000e00c00032076208410000c9520a82490b1404a55400c100c030008044030b8a6103480d50041e82400b2221602d028000420b6210540c4140000385155542000034 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 765316519 1250 765315269 765315277
    0xd051e0708011e1e020304050d08090a0b150111030c0105010608280f0f0e0a050111131703071707031b02010807120204180b0a12030c0602130b0301030f03020c0f0d0b0c 74
    0xc4c010610200911040c8980001c92101268064488040079203600201c0382d46d43c0c4c18224018484055200050307266400c00325005903603001810640b0303502c03028502c800d0954200c056183d610380c0d500c40041220690000300550401d21150b103422401440f20181d04000c281985405116510303004e50303c81803000c0382d00c17480d01080c07451020488042070b044c8490f15a0904481034070300b0b40c00c001c013a06110340c15404440000c1c00b0307107100701d12091500406400d01c40b050780d00352181e80000c4c48040b000c10511103d103111030381480705c0c01d655240185000f074800030040c0f200034603030201c20700007d006036000040e0541100b41c5081020502c1c8085911030040d01c9180c11005a4a801102080803902150040300441c14101c0700700300340a0b1a103280d02c1e084000300388040c000940c0d0003403c00201e601c541c01000d4807400107100e80c03180c60f11400c03940c446074400e030300440c8d6041001007030170141541402000401c8000704d81c10049045880000760036a842c03c1c402403c4101c400010800030034900b0126 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 765317769 1250 765316519 765316571
    0x30f020a0c032901050630090a2117090721061103091c020102090d12180e01060509040902310504030c0602090d051e0708011e 56
    0x101d18040e202c0c43d1003600700d0182c24402c0c054902e01d50307000c0b441c0e4032103081e400c1c1a00e2000e41a281001034503960101c58802d4074640313205c200d401280258603202e040789290b02c07c1e84580001e1000c044240307041101440da0700724000c42621900c0d00040c01c142e11104400951405004820082d191018070509000752540700c200400800314403489420011011801802d024032001c001400141000e09620f100c2190394081c0b541000702901c00711221110798040440c001c0c8001800d004010001c00e0a07020303038000507a00d0910441128200a501000c140d4031101c1e011821600c42d807518044c442104c0c5e0600594041c01408181064651950360104600c40d400821b031070382c101200160a80704800002c410717100c405425004a1030b00e80540210303401550701d580e690010b0300d6503403a00d00094114000c00390b4003084c1c440700c2d140030590030400303960119402c4035080c4001b295840550301c4d00708030b0742c4184075603414803e200780c0d40701f07603505900c604000340034000c1905800900301d40700e405000901 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 765319019 1250 765317769 765317783
    0x32318060708091014042402030a0f2f0306010c150f0c0207030804060810030203010e0105180705060f0307030213121e0206161e03120605011b030f020a 67
    0x40101e01680036040601880080003501c803144540020360065501120f5000300d00d036161404100064556240380040c8140b2074a944601003001005406aa00540300068001d4030b800e80c42101c03803840e21512034011120203e281c03e01c3c0c584441c9016000201030314030003424020001584690090507900c0c0510341c4a030182280300d10225a01004000c110002c0c0b010526009198508a00000c0c000f0b0a40c0d03000140d003424a4500b01088480c500000d281c900c0300c501255001005803000d000311001082414008107451070110320859000800740d540e40001d90040c01c0400c020303240c2400b246c4028005002d035075600da075030000540281c031400602d10a0720101d11000601000c44000030541107200c0c06406d0100c40c40301c1d6250103410490803010b903201508112483da1011405140140c191007a01114024a403202417414170414a4001b0b40c0410b80c21082d02c400c0e0343c2139104140245c002428001820481a4280c488a03a000d200080a0110402c09029424002c00606d00e4060744610703 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 765320269 1250 765319019 765319021
    0x60e1603200403031106161b0201020312010e2514030405010207020306040f0510050714130302130902090c04300c090903030506040b0121140108031903231806 70
    0x9402828444e032a50a0005d500031030003c6881e40c40d0740b1007883d0301a00c16030784101c1b000060346540104c1400e4207400324190701c4100030701e5481c0064000c507603009000e01d040d012901d140030002c01c0e9107142617401900c0c500082808001e601c5411900400c00ca4a89540c003030340f243d0700c038545540244034580000e0341c10b109850400c0100030103600d103448200d100e4001d0baa10700c10203078a02015604165551000f0030305400c00e000b5007580f140058030720700340400081e00711036030780382c001c00d140f5603800003c0c08029854160034425400c0c4041340c103800c0300c40580703000d2034203291500715010f0a00810100214400d800000c131a0030b200001a0034138907811541111811340e803251a01c00520b108481100803a09000004120745050300c42c0e244002010f0311b0780c03040c0850302c00881e5030002041044409407650b0740c080481100e81040c08074084c00310200116074405689c4014465103000000d008105410092030140e01c0314185036000c0400d441c0c0848400d16140c54280420368020a60f6590052040344 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 765321519 1250 765320269 765320273
    0x18030a050c010216060f0c0317010e010512060105060d0b060f040806180f0c090712021c050c130e1008030d090204060f0803190e0307031104060e1603200403 69
    0x100700180308100076001c0303c0710048082914036009002c4d10408006c02c0c000c03000031103501d000318414608607100b03140005260800100002c4801403c0e00310035070752000302005001a090021810203141c1d4030320010451036140c4000680948240010720030182d45505c022a10741d200c05042d6128000754050b070544581d111207507550b442c102160101850a140201d0103071101021440d800040040400352040c03100001c11b01200a0000c5d0003441080183d21003420180030f0391002d001654502d103040300d02d0310404204001036403806030400f05008020003807031086c0d695202d2a40119030030041100e509039a100407121103800d81e83d00c110b0050000049808403442103074041800e49100321006c0200030b0719103081d0100c40b00c0c40c5c0589503042e441081040302c000c0ca01d208040c10b130b51072441c1990125414201103070a22070b6681c0101c40c0301c45644494040c9103030500410020f0014000205441d280800c6800300040c08501004289a45c0f1120641c0900d8042c449a030440400b018055030f031a035034 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 765322769 1250 765321519 765321523
    0x15080105061f0e040e10060f150f02030a0c0609020618040f021e03100807030c0905131a0411060f0a110c010e10051c051504140c18030a05 61
    0x201c0c1c0c900e1080444445070102d035844142c0e4181c4811103662500e20301102401031000901d104403c000e182d03c110300c602c4c2e90b0705145000f407801034520700b0321000105141c14540c0900c2ea110540315410b20083c4011044050340c0041030322185407040c0340441e841e9265050807401040300403c040d40019002544070b00e001d000300902c0d000c0070b0707060710100407000f8054030b000e00728000c60303e0f8500c0040300c0d55451a01c040c1c1c0e2001840e0403024541e00303416071583d21051103180807059801141c400d92001c50801c41350080e8407a496203c20800082400040e466403005030189000c00148125405040414107102c05019424900000070303040d15541d006001643c00240c002203c2e10700041c400d902d80718070307180c07004c00d80031020203040e1942c504188194040192417441e0003840f42c1000014040c4024021072860260402c1900f20000103083c200329440c0030003011406586401942001c000709407030264100c0302c5900000c0181015282c4c13807503414031003101c099002c1c060382c0351090500030810b104d00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 765324019 1250 765322769 765322771
    0x20c03030a062102091513091109011a0403060207140d0207081209091308120c04030201170403093006020301060e090c04030201033207080705120c0d15080105 70
    0xd400f0300410a00fa8200240c801c3c110341c0003009400424050100d40e010645450000d41010000c010101c00f0203400c04400c21108040300c03d90b0301c02001072000d012420550002805050719a0017901521a0000d0480c80d81c411440000c00140c2c0c001042801d2003080c2901104128456058030480d08040d00c009581d10034074051201315008079900c1c00c0b103c901c440c089612055000d010010a5910070004010710209404d0613110711341c0402c4581340103900c10b6201c610905255804640b11b43c298000180324400b4003810b002c1d004500028080400d4008100e00c0440d802c1075100c041180b04040c240603010a0031141544a540013139078141000b5207a0060b5041e10030035a5688502c000c03280402155900a481010180604020030310155102c0c1e000014070a90400040c1c41c044c3d5210100e41c400a10707042201d100c0384c0300d6018000c0003688454a19003000c441c0c0b81040c2172a002c040240da03140c5000c3e00c20300000c02c0024040010b5421038101485d010301d03da1021051030b07555110207000e090 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 765325269 1250 765324019 765324029
    0x10c06150626010519032f0402030403080f0711031c1404020604120221011a0909071e0b0703180b070f0308190f0b040e2b03020c03030a06 61
    0x228081c003502c02e24103080b200380080b0000d02d0036102da4a00002d010420316913079451141c3c580100000720220703059801c00300c90340c5402c0c000d40b141002907144c40c400c194520601d2510403401041400b020907408000340340c01000c65504814aa11400d600390b4100400c2c00101c5418003000c00c0c0701050303800e0340792044100640f014050103000295805480148000c480c001d500510512049c45a000c00c10030717404451744007415150000026960210f4490261045144169194031402500314680001c1950000080d02c070000503060000700541c8802d80c3e03011345407030014000344041d941100b0301100300080c40c07040c1030760f50b03588598280144040c0701200d61408181c0c589070000317000501c520440d5032840d04101401196000c5941c104c07842540a400d980b0040d0100c40800e0100c5807070300c070700d0b2842c0d84458000550b00c51410180400e030740141e84842c0c0b49800540307003400006000b40312941111904100d035220400160402c0d8000d01440b0050b1005120100801050540c241e1080d0242c81c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 765326519 1250 765325269 765325277
    0x150d11010302222d0b0a18180e010b030706140a0215131a041703190e01020c1e060403050307111617010c0f0e0406031401090c1205031602010c061506 66
    0x204c1888100d400ba03082849045060380c010072070801c2c0d880c8504801e0740c0074602d08100c54003041e95407080143c1000200d0685065a507a40c20b040100d1f2801d00c1340c1c845a010650107400682d1070003001510050442e40301d031f54005000518404154400d004890010f1682c048040050410b06078201031030540e018101c3d210780e46a40001c852032403c5080e070388205d61001618000100d1503400c050035400203011369500c0c1502c03412040489106014900c41030103030b44c0005848003014421140342c528410003d21042440b1000d80c0000c03d0301160142c1d1054141c1801d45e03580d107030101d00301c1e403117402074046056500400100d162015020310814040301c0c10200341210358503403c0292400c9404c0c0c07c0260011807030707582c07100b41c0440c051140ba07002007100500000b14640d80b0f8507040e280507000302c0105040c0e5541d098020070080c82041e581c01420004018100304040d0340e032800c3c1c0e40e02c82c4030140d0030085082c080c0791045a109004e00b104403507001c4002e121001100c00803047c1c1d11424020f11000c2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 765327769 1250 765326519 765326579
    0x501261503070e1b070204110d0c020601060e0315090312010308090109090506010c0b04150e100e03040e2a0a020c1302091c02150a08150d1101030222 66
    0x40d16054280501411204c41c0c200c520610395101044103a0000104903049500c1d8000e22004c11070100203003680045994000c5501401030000a06102e016046081032001c1c42c611034030f294800180104e00d07850741e8040e55002e40c8540b8255407440c015906407080d070840c0e0a00120401c141d0102801c0d21610070b881f01c9031201d4459a00c4000d545044403002e0010b60a20101d4001c101c1d003084141d080b03802101e1841882c850303100404190388041310f0302030741d079408030b1408100c810091080c100f030008244c0107181020300b80444c2c4c5009100103441901003030880210030003901107040a0301c5030b51850f008080d80d201c1c80d28001a4a8411141c90940706048140c030354420302c041d41c02100c800443c01442101e601c0003140c0e041c8601c0c100001c050740c10040c00100100a9030000c402081100884d4803a0f1480c0d00c1c108414625605040c0210b50080444692920015a43e0301248588100c01d080241e182c08a0401180c2c0f1048588840e4842000301c1c2c4001604400100d1040c01c403078503580c003034642 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 765329019 1250 765327769 765327779
    0x21010603021215040e010c09050a0e0402031213050301020412030206181e010f0608150a09050c150d06060504090612050706030c0c0b10090608010b0a050126150307 72
    0x1203008a014a2560024050001d4580b1550301c60fa41c2041c40020030006151340868101d60840307069107001d4010488070391041c031003480c2c07070404440241504920b02150b8541035000c66140c5c0060081c41d030000901040d0f0000c0f0402d28481d000107007102030021921540e032183e113210110034130442a0050300900d03000c11040c950503003c0b401c12801450052600c44441418a0700315002252420495503032140750214000301405180020440701d0000e040c1d20003030341941d0105140140c00119040e00d0300c116100040c00104e90304403101c0040f10880418241801e0070a5140b2501c4005046140340840218504d5005400b400980d15400b100f003210715240c06030302e5150f01000401905039800702d001005210711941200d07141c0941e510384800008059611410399010a07103c0052014000c002807202c0780542c8140d80080c048c0100034800104580003281c0c02458900642d410003440b0071282e510706903440301781c415050800c040c9854515200007403040b54403000300500c0c0300f4041d916000071 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 765330269 1250 765329019 765329021
    0x302070b0705031e27010c020414060319051b2808071203050f03280203040318140d060618050108150709062307080901120606050417070b21010603 65
    0xc050f0141c0c291074001c0d400702c0a04040178203105000341082000100c0c0780c01a1a5802454400200b401c026001c80c18610704250030800e0041c030758400e0720400c01e501001314a0000340c1c00e141041904281486001d102c01040b80ca003081d02418401c00d080b080203110002c4100484400c885080095070f00c02070701d81c1200201141030344c0000d000544144141c111034000c010081da04a1754000b800b401561011017604003159050381c078080030302ea0200801c030906410520100e6107400e40c0e80c464080743d04090091702e0441c0c4000c2c085010b611800c004130108001039000c000589004885150080c81120f246400b8140c240500f08990080c3c002d404007a003052a000b50060029440304000c0d1b03410424200d41070344505480c0c2c02449164070020907600b010308010b080d964000c8540079541e102100001d000800440c0c0f0303c0725064039081040105039801415241516500e407850300320a030940385005d2a200480e044541d1000c1c0000320003c840c4c0c1c0c44225145043d205640c07414040c2c0c0d880405070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 765331519 1250 765330269 765330277
    0x314040f030e0616030e031912020705040203132603131502030c0f0a0509090f040308091b011103250201021515060d090b07030509010e0a0807030c0302070b0705031e 73
    0x800d0203016680c2040020b806800241c1c00506c000c0e0031110004507500d2080711800b4000016030319807240d00910315201d94148001005803005540039807540c1040301c0f00d0000c500180e05c003e4244908510761000d5104084524055410b00d500c919449040c4001c4886042220880c1294000c040034203e028642c042d0081d2881a1104c0c0744a9007001e0580d5420740d013507400104c040e070420904200582c000c2d03a4492031540034805c24044e1000b0b40c503051030050714500f002380070342000303903c00598500c144405c0005007548407001c1c0390181110504558181c50340c0030340b00101d203e221503e131010900500720400b2001c00c0b4000d038201e50071030178100c0c0c8510840205807100b40307000c4070101214415040100041500b004485000a0030000035228030f03000d0b1a003941c2c080002600c0b54240325480c142401811010090039000e04100d8440d540c035a4000d101e04071005003408165601c103010305009102c03110040c0600b941469856106280464590388009804909d1244c080e05074094580428151 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 765332769 1250 765331519 765331537
    0x1103061017130314040e0f150915010908060c09102607050f1902010e15060909010b0306010801090c0f03110411040f0603091406100311010314040f030e06 68
    0x80d4150b500d42d400701e41c05100c01c404055092000a88042c0c013000309110080000f82080c8591607024145141c51201c1940042e250721040134508104280c01d1b0390701c0d0f0039281c004000d115041d192080000045e03a6020260b80103010a0060608021084c07a204005002e911400c8400c550703441c921000566007241561003030004003c2c184024407406404001042e003001e59400e26600b0700c04a01030310f1207540c1c8030420301c0c0b0102811009039441e1503024040c10b402c0c00c200d04083c2c85030004160819030307200300042000c0e102d0340400010400303da00c01e5005007030000700601a16010f6031540245400380a9010381280c2c03018051200058001c41100900e068a42c070124400010740c8540800002d440480c03c5181110000c1000181600103207c07000020481914040f442403605d0034000c48480c01c1000d2012290007110421042145480040f401e8039440070f541c510300020000120b00500821000d113814403516404e01052086c02c0720440c00710751003aa58508040c8180c410701c68103000d01481 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 765334019 1250 765332769 765332807
    0xa0f0204030b0703020f0910020109030207060831060603030801171204182a2c19030501150302120c03031803010b0a0608010f0608011a0304050c0411030610 69
    0x204203c40d12903001071240032108041d05083c5003100c0700160440011116102c00340c0e6440078190205901801100c004060380d080041c01c0303141a000700c2e017040d07805071b000c05c10020300d441c03c03851611024401c8105031908028200142e035202d28020300003007402c0c0074440c016180585803408042c400210f01e0b0807901c81d01c5415040500e000d4903140b8042000c0701010342d06032180003441c4241a10240b020f0b920021044080031400e01e82405005684d09110803038481e129110a508034208040484c82d01c50004d8581402d030b9a28582e408000f18140d410040c8070394200143c91022101040070803098a000300c610307618925100b0076940d56102c681c16040d40503042440300190a0540b040d200700081809000402e13503564240001c1c846c45665007184021442c0ca800502c9421000040c0101800311414200d01e0b650500340b079400c03280c2614806007110640080040c0030040b040c026000f4000f80035201f4042c0c00076075030344a841e6030400c40b03860303002c1c842c01101c480380548a081c404082c0c0d100c40103 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 765335269 1250 765334019 765334021
    0x602010e070906032001031b0504051c0203061308070c081006060503190506040212180142050405072a0f0b0c041208120609241c0302060a0f0204030b 66
    0x1031080e150100d805e40c550505a82c2c4c49050b2140b0b400c006040c21000710740ea6003507607880c108401c001c40b0030079070340d009084c00041c4214103005880000d1480d80080c40003a0556600a01d4079110101d4400c5840040c2541200d46001510304c10000b0f2201c103a00c00d030002440a261581402c42e803a010444908200c2410503040c44241034a030752003190407a0001d0809494600e07145c41d1241d03151004e545006000301d101255003005142881050f22904184e0450322880e01644c694190041541c2e1000c1100d000b0617884d09400c0b00310481a20043c58080c10901440c50207010152040f21200fa0841c25022408000c001d42100b0405100300298082554840f051070360f25a594200c20081000352090020000412604110024404250b01c214407455a41a454081c89000341d00039000a008800b04800d028110081d500c1c0084c03034240c96040401c110b0b007105c1c0040c955050342c404403855805800c90f54020700d5408a241e501c074603041e800c00e004c000c03c2d200d502012841140300244c03a00080710 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 765336519 1250 765335269 765335303
    0x70809060a020a3c03020c0406081e01090308041506030b01060806100801050303041406120f01080c2b0302150117010b091501120f0f02091003050601020d0c1403040602010e07090603 80
    0x14070640d04c0781d010307204507000080100e003c90119442500603926aa10500c010785a0208521580001c080850003d010707030000350b6805800c07684054001018000c2075502d4102c2042c459200800843c1c026803208619650303803501030010203040e200c1d58022481211143ca0722030007108141e0480354094000d40c9010702e88100d100040900e00385003907004500b0850351032a0024030781c1d0703603020f1058044420120351521140900d8503412030119401044a000c188107031a0441410b0b0311052620b40c074104080349035140417030526503001c0c13410800d590350100200b4104004894080e07a400000b00802800f0302c02c90070050100000c9800c0050a020310a0741b13191035200e2058460310b180107541c081240c1480e0071120b0180c4203181542200154049a1243d1a00d461825403021100d9800e04010301d08060b40000d413210004c4898005010103255000100000d8001041080a03000f05803922a80c0710100207000c0d2104003e06c96032442126000305401d0385a01c190b0303088a0780600b1a41d140049a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 765337769 1250 765336519 765336623
    0x2060106140d0207060606030507121104060302070609050a150f050c0a05071406191a0a09020c030714060604060503190b1b0712081515070809060a020a 67
    0x442007a0b5441a000d01c110703c0060b07518002c0101401050700d0104140c41e0100c0000d10f2003e050b4040716039a810b108038548403c1c0038400300d600b651103500c0e000d0b030359280342d007051070290800703441c02071451040740f40400600a00f01d9460200c0c0402c0e078000d000d144402c80860040d0b81c41078440070b9408200f00100340082d070040d001841041e100784030b60104050103901244c10100c088540c08034111540c0010071030703407105c1c1c89150701c01e5641c1012204610307601c4001c6081c00f101b50040568036980040e845914800c00c009803900b4543c0640d001a00100b400c00241e2030701d1007a182940a1401e0100200e070914000c22100340b1030040e85004403c190050304c50f804694409020002c0407503101e8080d500044154004000550154800003113190303d86500400410004045508d60075041c00f05032065a18100702050070084400803e0321030926003000c1c9250321485a0890b17001c1d01c00118071240f0354000c1600d00482c0c2c00f50b858010410704200f50041b0151900c103000000130301010014106107a4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 765339019 1250 765337769 765337777
    0x7030909020d0921140c0d0e030c0316030b0708010503060f07030902121b01022404020a05090f0a05090606010c03031a0306070e091602070303141201090509010c0206010614 76
    0x1540c0420403609036121a000c07042e880130030015002100700500042e075080045e03050100c00155030a0300d4819009000d5403035640c110790813020002c444040418982d42009040c1e24404002d090343d024440103030010115401c1032104440034014940000c0c416402810168100c807409000f42003c0d6540c0c02d15061440360080100047c5550f6107010740251b02c0c0c081c010021640f50000500300340e4a0388120100305008034100380c2c110b40c01301401580a0b0900e60a0901c4050030211b505e4994645200290003e411a08003e0b0461001d004021100080240c001e0188145007001c06c1692502c014003520b03050102d50f41303408240c10445080000e071007036010441a0f400742c00da030483d001c00f100001c0c0c1407900958174100014407140c61410140783c01d51034150042c02e5076418002c2034181c0107010303468110510000d400d0101b8140304e202056400422540350310b400003d0041c0ca581c4501d8034030300805003134505095661a000604807007500002c3c215040c1c03030058aa4000000c0404600141580 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 765340269 1250 765339019 765339037
    0x21b150702060606071e08030a140408220503010e0c0a090b220f0e030a26041b030507080105100b07150e030d02040f08060906221a0a051b0703090902 66
    0x210181c1603509104505082c2c821f01c40d441c0241c2d2424000c00d0b0406aa8a500c0115407071202d54050000095851044400441d1002c10314621907410420600038940580c1c4141d405508200c005c0101c00b90100c0c410034002030450b055190562943c021404a507043c240141e0400c1007404110070604403040c01d160380c5142110045100c0c4800c402c18410784400301c50300c1c91668004180d0f5002c1c95040407a07000b00c2110030b880c4242084514081e0240420094405040401001d50b00400d030b60709c860884011315004001c45030f00c07558502569000740b00807100780306100b10200000c1100709509084903600c6e6044181c1c101c6910345000c3d0100203000f0f1005410003848100720040400200c2d0014000600392401c4036220545800d010f6414200000c1113480d03560080e070100480156038100d100b44983e02d1040d8048968024944204000c107210000c3e076a099021081040166440c2c000d14414020301d543c011a400980740407420740d0240c140000d002c640070000a200118090b409008850 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 765341519 1250 765340269 765340283
    0x1917030912130503010f090231020a0212070b010905060d080904050c130f052107120c030c240f020a1e0204050408040320010e0f010210021b15070206060607 69
    0x143c0d4440010f03084614800c034200a490b2030f003d4000a516241042c1035110602c03000a106003407011079040103413101410701c80482a0b01064500c1068401c0002c0d11540190201041e6111414186102059400d11031000403078100800110141041300c881400d41b5440f6040e142042202c07400c00024080092004a08100901640007812420401d403001462070248032200300e41850b040c0140d0300821507403c020140d104a14442009000410400302c03646030f000c60030600303000d25100f11038881a40c405001d410601e000030604410380a283c6440e01c0c121400030703030b640240800a6490240303017446203001d40c0001c4040030108070340304018200440c4c0c000c0124a80a00780d4006012990103032400c0d500d100000c24280100304036000044080d920310250f80d1420680307140001c0244c078480c4141401520881e0340c08646134020800c01c510a40224400d54440d1001c00c504101e205500000c02024810030320011a441c2c0300030b0030180590060b038003820032945e6400a03c0b00c51f40c00f10034101e40c0c1d0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 765342769 1250 765341519 765341557
    0x6090405101104090b0f0607080d0207120807031d1c0e03100b0a120c0501110f011d0c01050f040b09030703080703032012071805031917030912 63
    0x18103568812030035078400c1040160384950030116030008071442c0c6803441b4021a03034032855079010380d204815215281d601580103031783c0c0d40c5c90340e889030080e000b9400000c3c140c5503421801e055403038001e010944903401680d8200000e1103035414070384035200603803610340e00d50700141440c6a00c450120a408841036180c24049002802040841d18141040018484141d6250305800c403902e01080b0090050924803211032255500e5111241d0b00302c2c1038400c10703040c00302484607081543c02c00d0240c2c2043d244000001c2006011040c00f01413502582008007100e40282180300c8500c1d80248255050b00000c059424146810b014211020364007901c1d01940c144a0f110000000030681c9000b01000c3d4840d0b40d021031540f82c070742d0b86088c1080d010301118299400922810f0401d000c1d0984543e4004000c1c5080daa0a203004800791048841c0342d0016a014020040f015603040c0c01c0144410196102d032440702c0706201e1401c400c518a002c10303580d071001c98000219800c4102444400707426a2400d480c070700468 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 765344019 1250 765342769 765342793
    0x6062d27030b0901020403031e0509190e0a0f05060d0f0f02120f01020c1006030308191d0a170903071a210709050301020301080d0c0606050a060518030106030b06090405 74
    0x841c820446800f00c031a900002e0a10815500c800044d0400c20b125820031240d6840d464007070254083c1e074401d14018011780040c40d0341c0081c1e0001110081840d64003410f5141009941000034140e46c8812006070b03414a404640b00b8105041e0000300d461b0815042c800003d5155942c0c00303600c01c0840103a911000f083c4844a03080401c0c00f00b0142903100000041e907400e1515103941c200b001c025500c8014a14050003000400c3c0c000001d6540081e0680c0c1c141700103039480d1000e5000f02068500c44600300c42d44901c0c1c090701c041c0011480c454600904c5550212074140c00c00310076a100d8080626007640010301d00300b12505600e0401c0504c0186804010706014507a03d202c0203070320b1100c00345041d00303da00f4140240280c000210102030681a002076285604000205540e8501c121602c410070034601040003d00a82e42d000001820009002c404216960403006040d80c10001d01c1641c410f40c0400108458601407180d04100c1e948904101082d56440c1d08102d074102c40140107075014015400c0080c4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 765345269 1250 765344019 765344033
    0x9090f030a0513050d0c090c120606020d080f06100c052a0f030703030504060e1306030302031315020604020f0102211b06060307050d0206070606062d2703 68
    0x4041641c0d5800352a4160b03d100c0002e1403070203900982c081da00301d1109001058652400e5001d03506402d4001c280d20051400c1210762034558840f031070340c01e441c00c1004580640e01060b90450709905986000c041d4030b6070380c1084850710007a030351968410300e00c1880c0305065005000c3c1c41070341030250b819210202c0c0001c500c60382d200c0c900d8100b520415600c2e84241d449217848442c3c40301d6104250000d0003c02d05555001d0803e1180340125418805010002c0ca001d42d00c103903d19200c0e0140210901c6202d6403490065a0f0340c00c0b0b031081c40b903948085600403031002d0030061080c0300300002d9401420640c0312a024008040704d1801c030141140100300810f024803908540709030704030f141c600545070b136101094030182a5442089070320640d40c0020041c002a5503000a483c415250200c4180744015403e100140f514450588000d052a007004000900c498100341c021031940100036007120150328105002e210000a00e0180001c11030701c281d090500510100350220501d02e813407041d0042d45c0c40342c071041 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 765346519 1250 765345269 765345277
    0x2714030609330f0601201e0a0f0602180d050d120e03031008010b0402040305151e0906090d1e0305100f030f210903080304060b062d090f09090f03 64
    0x70f02a1040d00082c8089568040c02c1c2d0509400d440518041191512000c0394460740d101e6030300c0203898040207000010350000d001c040b41e001e034041a4803816007446c1c42e148010f908022000c5030002030200e001d10141c10140710000c01940c0c010f001e0442408203007016541086c51403502c0c5406030380c80f0691500701104000450082c92074a2964203514030b011000c0e401c4d5800c0441c140c1c012401440204009003000800820a20217038100302501d5882c10340c0620f541403441d8455909062100502088800c003140f218050a4607800350b0b020088a84026036220f02200c90121039515010240058240f1a6001039040198200d40d00161940d030301040880400c290000d0302c0003056030020108006000701c0d894154200c24181c0c40c1208a09a00600300c4004e030b20025050701c0c0000300060820400f0307402041400c00007400c0a481c0e500145036020001d407100403285081d08010801c00090010f0f80580d1102000140b500c21550754040601a030181e0282040b040d03486599130540b0101780a202038 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 765347769 1250 765346519 765346531
    0x50c03131202150f0d02031306050f0403090503060c0a080405120f130f0807030b090309030106060e01081f06260f0405070e1306020703271403060933 66
    0x20491a80303482c01003025000035080c0944200310104502e1200304018019a203600c200180300503125940c180f02c4040d00350040d00b0003400c2910749420810040c2039140c506002d507001c1e9407140c030606d4862041c9035490f032054801c03105421703052026000c010300c1a50f42c40c0d80b1500c160141c545a01c070124403008550041380b0a20380b44a00410090b0090b225010a8002080310040000383d41e0301c0e102c040d40d200c001500001d0800000e200000e075804c042001200c2190700702500800c481d65581d44000c140c510744100460009101d0030101d40da80b03115240e0608650b00b2040c100525034988070040d00c1010f0803000034144507424184031003542817041e00191046071402000c09607850300f864107a0620782d03131b5003102e00e003214240244440780016110351402c4d80d500c81d50060361101c1605098420320300540c1040f0110050891320081c01e10520a5101101c07101e10800c0d000c00409002c00d926180111418909544601600c00805081e000c4103d141a02c083e0f0060444003500540183c0c003108940c4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 765349019 1250 765347769 765347789
    0xf050a0f120f1803030305220f0614160e0a0e0f07030b0d0b010302010c110616050f0c090a1508030d0c090605181210090f0204110405030d050c0313 65
    0x880e03040e50081ca24030480b1403245004011410020019100550540405420103544000192816a110b02005854258041c800800080310304e812070300d820007150100d40d070f2801c182d100031045200d117064500030550754990032030185281034101d6a00d040c6c070f032103a903004003800c10004a0306d50742c4500314000c1c0441c40c000c030881c0c038200002401755403600340060301886400300d0b94004907030040070b0581541e609180c9641460000d0800d1801c00d008a080035074020b90018081410340751400c0c408550324070400903142c0c4e809100e00d080c1c0e05c4010725944070350400030341d5000070000c1c0e14551180740382c01d0a200756643c40c80d446000882c85c1d60021a41204850340d12180e0b40400c54101d0303007801c0100520b00d0424a803000000399400c510580d004100d00500703180800059850050286860401c18000f0070802a10b0a040c01d11001d000c41c0c006a00a80c075003a035000241028008603800e80d8405402050100344480c130888a9920006508020340014085921900940d0640700020210101 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 765350269 1250 765349019 765349043
    0x61504080c10020f070902030a0b0405090c0f0f060906160f0b041406070915030912051c02030108030a0c030306120b1e01050a15090905040c030b07020f0303040f050a0f 74
    0x1081c490780030800100d01043d9402025603a034001000600700d010741d200e41501584030740700e00c806240686203045066520600f400d040241c01031000031003c6041c10100c940105c591000801d10450f00402012603802c18030401508445040070303002031554000b8802c040c006002c86896405a481d007024048801d40280c0052000b48021090b0404903c0750080191009043c0b00d4401f4190072130b0703441000c0c4c0e17121041d11821020f070701035440b1980580d007016542d441d40c3e40701f0b080205030340d216a0311202a0034500b500c5480f080e510344252810f07207007190011443c000c030109055801c2048271108400701034035404003107170b1040b8816801000e00c0c03141403424064104646044d56019100c0c1d409601980100010005070707641c1c80c0c5180480c0c0810b0b148850080c0c150101f03c410040c21303007280403040c2c10842407100b040000e240e0403040341e001d0300c80789800e41c031010310482e11900d0511000e2066401407000c6030104501000d001070032407198040320b0030255155600103120500707050546070441403030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 765351519 1250 765350269 765350293
    0x10b0a02060c040e280c09080d0e1305090307050d08040b0f070e01050a030605061605060615120c04031a0a051003050a1b05060f0d060e010b090906150408 68
    0x900790081020b807207190500c0c0c140200180310040041250201c002e201111a402141c00311060768100000300c020b016081c51004043d00ca040a8030801841c7e20802c500041011b20402c0301d04e800c080001d201d0101d00d5101c000d02c00244c000a031018503140400c004140014800300000400d034203d80c1c40b603480300d142504224002042c000c20052502d8000400c2020301a03004000c12400002400e0154540000b444100d00034000d5820a42e0010400151051000314034061040d03000d2081c42120801c0d55080140298201c140100188090b002e0041111074801034800e50340c885030503c0c810b810b160390b0362164803948540c0400407980341e58072014445644010700800d030b400b210702c01141d0000ca10b956240c40d5a000758900180600d4000f040c01c94076500c0c0b0110040c02424001c3c80c680d1629102c2140917800d41c04600703180c080b203240c110b0004458818540d80e078101c6100070582400e1940900520042c507400800055001c1c072a081c00400300d00d50f20025001070590300d002411003510070 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 765352769 1250 765351519 765351523
    0x102090607060b090a061d090c190e0c1309020d0b06030a02070b0702030c030d02090a050904030f0306060c020f060d0902060408010b24041a040801060e0f0a090c060f17010b0a02 78
    0x2421480d196810140700b403001040003147c5110388001c509141c145660341c402c0e0182041c01c2000c9141d409112400204004400b112044040d2224902401161f40314032644413031503c00c85208210803401e2250401407031403584c1c050328002543c80c3d000308641041c03800040951f88202d4000740404d5010030400240142c0110156001f095030004515150900001554034061040d405d1192600010500c2d1540c80f0541e0030002000040e0a1085a051514000d000003101c04800c40c0020301d08200010302c1d40c4699072005103540c01401441d4803040b41c40520805912291510070469240c50503440144c6400e801007000380032843c000644420403600700508221905003003c0b1a03903d5107000b00c2c442c81c109040324201d4002d84071030030b50160581c1c440e510078048e0303500c203d100d546050000152420704018103841000d5040d01000c60365200c0350000c040710031072039024040202100b000e0240d0b80c020440c03001c0c1d03541c031420720f03044040d075450112040b0385c801d8111602c40040411410034007901 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 765354019 1250 765352769 765352771
    0x40e09010b03060c1c0b0301110a1106010302010509010305071e0e0a0f1a0c2506080f040b010b09060f040b0a0917031606090219060e010201022502030102090607060b09 74
    0x4030b020b000c00342000c00691403d405240f9400a00d91a4040d030100c09620715804420f80c000007a000780320150103d0003001d095009000140e0210b08041010840305c0404600f642c140e036416110309007040b6401004400400000308104140803819548070402110725401c800000c80070b6640c009500c42c100140301081c01c19900460340901c1b031120a2003198034059250a00c40c015040c078540b1440d111402d10b281502c000303881e41031200c0c018003584800c2c000b24181c0c020349440d0380301c14a494491019500d80d00c102224003030564034a010043c010031511000a1501000c001d201c1c2d402c040f070240a0456951003680440320b5204005650340580c1c0d0024890001030080c40d05680003104e4051511381c90748606103c21540101401090007044007a0b400803840300c1e000340070990500d050180068a1400501861011031500f44020040d50310500031124040d000324540302c42d2900314050f92003c9080d01c1c0c822070317140d5000d20200c02c141e100c40c00541100390280341c0124401e9461780c01d006403800 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 765355269 1250 765354019 765354041
    0x18030f1814061c0605041401122010030509010b03030412060b3601081b010c020609121c05132d09020c0f06010305070e0703090602040e0901 62
    0x4155042561a20440d0102241c1001d0810401c600c14000050034030f102e4090b8201680d510525240c004000a900c2401074031001d8900704520241c00000044011007403152a15020125188600048940e01c100c404c100304061290207211075000007401e0041c3c80c005410003e950345e010400140d00034042c0408044050b000b943c070702750924443d500d0081d00380e64090802910b07403c03035003099160040302c200081110000d2031502c41031508004803485660402d4155030b485240082019100030801c8002c039481d502c071411141005600544031407840c10030a0381c2c4503d0501c034400440d200c0142010f1286c034101c001d40440000c0101940f903a18001160804001c1c0a0140b084240e420010300400c0d1000d813080c1d09098402c18290f03403440e0200d00b1042d40350036280d500010301c000c11500513020510140003501c0d1951401200f181d55000244406800ea9005420400881d1010b030b120a42007500307880d000c07071800d035540c4920741139a0181e40140702c804401742c20010f24040c28172a5119500e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 765356519 1250 765355269 765355277
    0x204021603170c0f0c1203010906090b01080712180b0f060a2c0a0b0d06020405011b050312060310050115081f0501030209060c01090501060f080a2004020d18030f 71
    0xc1400498610b41d80540340c28605944d6000074142100c40b030400900042483c400f030100e80d07a6844541410103403030381d841102c05041c1881101500c070f40c0602d240d20701c1114565200c1e4a84108000780c42e0251101101e00000040c0403c24600820560443c3c14800c41d0461000c2d00346090072001e201c0a100c0c541e1007038080c107020600d40000d84003081c040302c80324075522000c0c600c0390315500701100c0203041a84070b05a010304003c11041c2001040e0700a48201d0350709807506800000040100c00b807210203907400526a4104110030071a91040c0c04465401c04401380440e10f00102c2c1075503803011603000381c02c0b1409070721a41d0741c81c00902d07034042c070460341c04044a6103924841382039034498140e8101c00d000d460306160300031a005401d503d030b50381541e00440c1594002c0c0941445410603a000708000d0003005010507044001140344c900004820030a140d0040702c140020b41840d440761120040050b80383d90003502002a90700010f0f180c011032540c4103403102003440b0303c5502c6c40c02030520641d00704a00144 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 765357769 1250 765356519 765356521
    0x30f090a080306011808061f1e03060203040c170c0f100e120f010606080609060102010204031e02010e060409020a0e030c010c0311030403060c1107050301180f02030703020402160317 80
    0x9460300c1c241c0350007642c20b00f80909000a4174032000d09150003030700011000d1050004020445200041e0003030488000144801c20b2034480c003e110048000c1c0c4190004521012010000181d60794011350b131042c05004641c2c0d5650311110645111603001c1c02002c0d1950250101d1101443c00340c010403490f4070205c1304811040c500100182c0f00003081080c00307214800c203042c00c80e03869000340541d00780300f40103400811003103403200741c060600c84041c1c4105020b4803501c00003a04a50051003100c041c4d80c0c00141c200082d001019804404d11304c1c04004a0410510800c4442e00d529050090720140030100780c050384503d12540c00034206012500c03200c3c4a41d001c1c1407150100d9030403000d51410190146021510b409040720081e02d140300d5980018600b45c85c00f11104415584107180303a0440058209841680350b8078003c1500340c03200c4580e1952150000424100052070015452220394400343c15141c4c1d80c1d560303400040490708488010303c54041d2824082d000c0640c8110004c4c511140329000701d0700c07 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 765359019 1250 765357769 765357773
    0xa210b010806100c080c01020a0834090302210c04090215070206090d05071502030a17060409060f15090e0d0f020f0109050703060518061b07060501030602030f090a 72
    0x2405010302080e008506900341018161301ca4010101d21940080d4000e5840d40c026100ca4000d6005007544c0000468403070101d050348080311181403d0000c1e003010350b03245402e661020706000740403480310414424100c8001005886002c20f40c02d0859080f40208010303034100c134140d8100700030080c94030700c42c0c0c4c40d0007010380040e502c180800010303015151000d910303a036052011404520448449980c800ea40641c011304020000940c1000c0d6000030504181042001c003080c0c1c2d490140740e20032030110b88898000340d50140e14842107035002c5401400810705821580b901000c8445c0400c003400011703121300345188c1d40744c01c2500b040010184624100417080384400d682e07031107402d092851005c00c5101003440840a100300282816800e200008015003c0d035480c019036101d5507480102e40060400c0000307a80300a0101d124030790308440f1005041d09a4030413801020400000b01071a21050003440300b5000f00d8410702c10580038522803080144d0f02d0420302c9146119141c01440100c09178841103090340 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 765360269 1250 765359019 765359027
    0x90603060b0f010243171219170a0606020f07051e0a15020d082401080603070b130314010603030f050c0c120c01110c010906081b0a210b01 61
    0x100c4140c0c90140c101a040c05000036014608082002140c4165106921041d0102c0c880342517088841000e00700d1345042d00d207041c590300c9601d14640d400c1910300034005002250502c400326448290b25141c51081c80c064014501e5690a094400c40082c0c0d035a002d09002c003980400c1130507102500300008003901803078034002909008128021a20f000703040300d40b0040640b02c1881410203440032000d0a01d100c230f1400c02c000e41d0b0b00008113040000a0a620205030b408800441c8050411004103810201c8100305006580c6d83e100034040c00e41600c00c08000290400c101c0c2e010f41003182d0b40c800c1303180009156040c4450051102041d501e4540d01d0700c00304000094201024001a60150800c0c039240c40182042c07500740700e56864000c0d04145040c03400883c03e40b01103148030007144240c8540d16603e01c031603560340c0d503252591802400700300421014082ea034064690a944144c07a01c0c510800140359132041c81c01038000480d02008990041c030b0f02c5000103514800c00001000b0000c08104001000000034 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 765361519 1250 765360269 765360283
    0x3060a0314010b030109050d080a02040e071b0606080a02030f010509060105101b0b012103140f211b0a02030a03020a051204150b04060b0316090e01090603060b0f0102 73
    0x81c1910041010400034540a420061406400400801000029007882a2240101c00180b000100580000f501e03a040b0341c42603500707803000360b070384107485a07182ca0069070b00c22440c1e081000c042d00101d0004c0009441409000c000c1c200080182003010602e2050500d4403503191212522a410042045003035074002551904503101246c4004611003001c03411740d600181c4003001c20000c0c40c1c4107800d00500c042c21b0f01081c101d81c0c6a1510748101d219420f06114050540d200040c005030902d921100000c10381c002502910302e00c44641b602d010103005030913890007260100c0070f00308803120080261220000407010882c6c84000039091a01c4455003009480c0c6c814640030909240c0d003c10062121442203064030550030345009003880d54203050401c0003050034000b4000b81801d0404003840341034180390180008682c032800d0b0752800c6440d41c08644854414003500c502c01c000c0f80f40c9000501030840303840c140c000c14145800203605401e605010040d204000a210300a220540380400141d900050407 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 765362769 1250 765361519 765361523
    0x160320100621030c081306030c110c0f01030522140d050301060816120c020105010305210f0d0b06070b0708100803071202010e0f07080705010f0c110a05060706020c0c0603060a03 78
    0x1031090403180f4504010a40070b500080b12900c0c3c010f08007c03030313842e4056020281d280030640790003a01400e2140c0d201e40e0f40e0000c507685074110610410304003841d406508806d0b0814444810440c94403076050f078180c0307076002428064504400c001e0403049085000d224800720b0300341c28600f092071503041a1000e450500b002d0f0108080d54045c03110b003071a0038880c003c101403c4415401c180002a44910028060b000a00068070301d07000c0d2404484015050406540300c40d4200150541007140c01c440068054004c50412110182c581c0070100d1103030390304401810110700c501d541c4219030030905002014580001d1030102ca45c00c1203107080c0204500042501d0520f64400b000d5030800064010890243c03480400d01c0303c5030700c5001e00c0c40000d224080340c40300a0b02d50380b200300c0d01d850f50f07a8030044510400c6013035a40003080003242d625002c00e11520980e0800100544034502055a481c00705d401c0341e00c03240c03003502c100b580469183c0140909020080410700102e45540c203605250000402c84148c83c800 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 765364019 1250 765362769 765362777
    0x209011205010f02041e150e0909010e01110307090915030b06120115030213051b1b031305120f03030a180506070309170a020316032010062103 63
    0x20000c100301c0c09410150303000316441d80941d05c555680d102120a059209100c007504000a400803c8103414030421380c1010074990b4848a080104200780400803074040e000b0907841d501c409515088103001d01442d2481e0001d540003550780e02d4030a43c01040c122498201d409451300741080c0000c0809070740c03070000a4075004000030311300391070704400689511181c10b81c80e00c480d42000c050800440c014265801141d00a4820003007031030031015050103c80c0b080722480d606181da504d0303a0640c240420040c0000c5030f0081030403075486091441c441d2458000300400301441c1d07078080062145091201003082c515210000503d00a06440884c42e100c0c040204042a1240d440c1c000300d0103c0074507508488080c0d0800c00b6075415081166000f4041d083c850300c181d8000702c0031009548082c2c82c0704104e0340c000c03071258040c60400802086d45000d10701d4000c0c06a0811400150701c2e9103607d90094140740051905006100b400844a400019211a540940640b03461034052826045c0444002e00714250b240c58 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 765365269 1250 765364019 765364049
    0x91b040608060d201003020705060112080d0608010f1107020102070302060306031005040b040204060e091207030e062a2b020106080307291315021e0421020901 70
    0xf01d40000019000130b040791420000380d4261001281c0101001d880c00e071034951000d4140304080c0d059108034900100320b0b82c81070380100260054641100946032150018a2074402040510416201d49803c049400d0f5036501d1080c0c8172141620880361000e890000d91030405410b500041e440708000d11000e07010b08000000200b056800344030403040c0c400704003400c000350308007420032250141003201d04a01662400c0c0001c100c400018403081c0c407407095400100345980c520140465544c102403400c4043c886044500c08507036540c0303000740c42e0006058401c440c000c01200108150809407a00e4681d0b9034000c40c0e010b61410380d2969004008909140760203c20409950040340100420391094850f03000200d403d80401588003020449e103080c14502c0790886415118604101d0000d4880d4202084a0400030300020788201c102c06003441010380060501443c04820f05c680146080208070640e00058103102014161014001040d8034040d101c58600d0154041142104c040c0210071030510400 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 765366519 1250 765365269 765365281
    0x1091d091f090b0919170717030f0c090109091107061514060412020d0302210a02010e0606030d140f0d0f0f140a0e0a050f0c091b040608 60
    0x10010440350303800250740500c0081d90300250010076400304101d840440c6031010481c81c000011300000c81c000c03c42000d6500d092266101c0042c01c59220038201242d80500950003c108820105121030001c410001c2c1d40b4a08945070000c5404000c040244589090100b02400c0c0d80c410012410340745202d1380000e4030081082442c4080c043c40c2c1e0300400e02400c0250b00b481600003580180212030101e810440c603a0300380020403400340100d010320288441000700c0040540303040c2e540e0248190003401903410700c05084161901c80820816000c0c0c0240b40000c0c0b400b41c0603824494070628001a102070659801c0030b01c00039445d0750384030044d00100440c0e44200100005984111003030310814400c46540c42403900311030310140c1285500b0500352803901d00a001800e290b4020100c02c0c51000e011103005903600c800000082440f8144074645104000ca0300002440801c0103000710b024001c001e000700d048510800403000c00c0145001e40f07003a4204600c042803403600e016502905e0705402c0c5059076560b10 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 765367769 1250 765366519 765366523
    0x512151815090a1707030c150207051e0d0207080304031704170106320405070c0b1003020f1c0303050c07050a0b040303060524030403030207080a030b0f01091d09 71
    0x21103460700341d060107182440181e11000810001d0544a9250303040c96000d102d040703207964040e294010340450040c1c40c00ca40003803081d10201200c40e4030001e006080035116100c4510700403454203400541e01722000c1c203080628040055180307040143c402000003030f0030440c0d40c035124090391000038001c4982c0940070040340541c0042da0050031420005204100f0100071142c043c0580b031003014011140c0039614100341a003c04940d04002c1121740707070b442c64000041444014000203004d0070400c1100c24814000074070b400ca2282c080e18801c40c901e170044d41540100484802e40b060f1452003440b0002e0310b14502094008500c40c610b401d810000b88030380e2074009224462040794002001400380000040c1000101d42d81c040c040c9009036420030041e5110024418180403c0401c000c101500fa510f290018a481c8003c50b0b12a21919003d41007002564880103560403034050300c000301e0340b11907080c0250306028000c0523a4007030901c0c241d41c00300c0c0750030220b4640508001500f8a800d10183c001601d9401c1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 765369019 1250 765367769 765367783
    0x201021603050405101d010e0301060f0b041e0305100b010c15020c0f030406050f13090633080609060a0312230708040b0310050406030c05121518 64
    0x200026154100302149401042c41d841801600c3c40392044c2c44491146500c40c030340e50807000d00701d4050311070100b200a0054484006502c1b00035410343d22504040340342da00d00c8403070f0402040340769003880d1568240002502d1410110005110f0303004080f03800c0022442c00602001159003141001038200000d4004a50080c600c0302c003d0701250b05072102038800d50702a4014920010380b042030f43d0314482450121512441540304000009006001c03140010040000624000c00180c070041615999802e40100fa1410359112401c2450840d02c80c0c0d01030710451801c0c10401c0c144283c0311112021503500603010041c007030300041c0101d82c0c220000c0d001c1d482d40300f04c100c007460300b200310201401d41e182d80081001081d400c00303e20305494180c0007002810100e0540380501d034807050707150800341000002c40741a04020102c1c8407102c5030400020359900e0f24860f541c040c500642c000314a290500d814001492a203001202d01c030b13840044000c509040d22005950042d6809068003010b482c00075600c2c0c98040 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 765370269 1250 765369019 765369037
    0x1080f1f14010e03061b0c12041410020105040203030a11030423100504030b0a020c150414070e100b130f090902012c010f0c02040e0d08060105030108030d02090d0b130c05030c0105090f01020102 85
    0x10b000034042b440c090918840f642d00b030000c90313041050050018080342a600140c0d002901517005000d40791080d809101c00c2c9980b041c2020441c3d003881d5807544058035640000100100000f001e00032406242880096011406c4881c02d16514062031669400301c9080020405000c95501085170220200d04cc1b002000c070a004180310503003030500d4103061342e003104182000c1260307100728036000800201f0717920070b94401d02291500e10151450b00300d01c0074143d4060201c090345424542400304501d000c45040c81e0203800d40030300c009076101c0d440c40094880081025031229a500201d804da140c8020440680303c100020302e00501100300c140400d885c1031440341c03002503105040c00102204400005203101c00d0701d4450340c42e10000d4a4420064440744400e025034503041d0030801a600c610701c103e030010140e145015081032255507240c0c54402c8400800d441040540100e10240b00501031115807000151004038007800031559880000b0740b407840b494a0f003500540d440e9141402d00e030700071740c1600c10030300c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 765371519 1250 765370269 765370303
    0x11030a0806041d0d09240203030f090a02060f04030c1212120b0406120b0703020903060417040e0411012c01031d1c080901060501080f1f14010e03061b0c 67
    0x11640220141c100c01726402212102e0008600c4c821071003d510520711150000394001e1072440d1210700780700c4500c24008100020600c15a1203181c016201e21005090009592040a84950462400460f080e1644d888446a51400c040e500c000c10348041a620480c2180c0c1400c0960701101c00c08440038192241005900a107031400c00038041c61480e030048031040c440ca162101541d12442c090b800ca0250111190300343d40210000fa000940c685c04020041405400180c20a6500d40008881d01c0c800c5608503005024003201d5049560082c1d03168060100d0000d159909a490500c600ca0383e01e4801d11480c101500d87d0f411034100022a2641d280b0001080d00341c85955111030464141e80300c600da20800007a41c040002221440184190000e80d40141d5462440341c446540310b00ba00c0401400c00c0b601c000552044840c000d50120324140144511150fa0400721101400074000c0002004280e0081e00710310304100840c0b074546911a590f40394030039884c0e00c9480343d01c51903141c2040c195400c800e02e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 765372769 1250 765371519 765371533
    0x905100606050a090b07080403081e031302090f010605030a020d0e070308091003050903070201030506011e110f06010b091210110d0e010c020c15131511030a0806041d 73
    0x72540c0000103000250f05030f101c04510b0741d582c2e406038800d8072480320094100c0100780414000210928010000c3c000452201c040c8001005080801540140c903054452940c800704007086060030b00005901c090f010300350344440d6260500c00f50151100402c0058034950014192a5044259101580000c0c4403400c462a541d100d1801c80615030200f03131240d01c568020402c02001c01d1281c001d0f24070030201c0c0b0001d142014065030064000d003402910890502c0260121070940c104ca0524020390400386c1e40d1040411540c03801078500f0080040c1d61203c00c0d4000c0c10061096241150441d24941d6040d5030310254801c4814180d401c1c000c07083c044919290500040444806c00c641c05003194240a01041001c66002d0030801d0881c2d2640b1114400358100f006884401d1815494105030340d0511802c091034844083d000c426815600e403c01c0e03541e034810321040101395030f20036900d4551540e00e0000f580b500c444c0c04400740c0310040050103a4803d0f5115200c01412000b4605c4a55031482c01c08111743c20 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 765374019 1250 765372769 765372779
    0x110406120614090a0f0321020d051501020a05030711010e09010303090602161202090403200303041b05150c030f0a11010e0607052a1e010513110409051006 68
    0x2605076000100008a24000803c0b075800d004940800c0b4540d128071220f2140089690607180c0b00c5030b0b0740300070041808074806810300000d180014004404d500c1400146407821080804003034140c220451b0440d803016203080700059000007121202c80c1c02c4415164400101d0004076510000740c0d555a030003d40d0680000704050b000b8529074142c60007502540c4400740600100700001c0325500c41c00180c9800c48442c0340250402c00500c50b0081e000c0d00d401d030710304002898a001d626034900e060049590000080100380600c80040c1c0481040f19080e04400501d840e0000d40f804100b01540a582080050708070403032017040084030035540c0d1002d201d0352548481440a00701d9140c1c0d4007500902d509004210442138400300c0d8880c40303040940c40383c50404c80000503c20b10040c2d804400c0021283e01c501d0345031030203c01c200c12a841d0328240107c4020040c500451801d59002920412071901e11096000001e41045c03c02598400207640c002190710041c1040d0b482c180780c42c0f20944401740341000c0412 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 765375269 1250 765374019 765374021
    0x3080d0906111306050304081b01110a0215010f080d110c0a1d0703050c030c07020f0604080a15090f0b060d0f12090602032503120f0b12030901020a1104061206 70
    0x41240d4038181c0b04070184c0d0307a41402c1c2c07202c0c8400ca5000789201000c00c00108580b0380341c00101b80989645000064000000c910107525500c480101c0c00035a1100e0074403000700700f810040d14050300c0a400d01c895058613001d03010396101c0808014000744034030141c0f95001900100044286844010a828146a510410010b03064002066020080800000a400c0c0e038080d000d11401021405071180c5142e0329910080c240350040c1c44226803007404031145c40c1c560350343c681c090300203006c103030015200c504100d15040c09222907007110810490b00300701c1c0d09004541c010703540c2482103801c41400d4040d41e8503080040d00c5411402c60040400d420000c001d0305005a20082d00000350154a440c1040340c1c41e502c0a81e0b46e4000c010300e02000c81407884c141142c00700d103080344100da01c1c40b07418a00c102c030a070442d049007030b16481303070f00c100d00c441d501c80041d20300d45401c0d11850250038200b0007441c0750007540b80000b502e43e40b408402034003141d0b4001c14107000307441d03940c0403000030b150082c60022542000d1610300 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 765376519 1250 765375269 765375277
    0x20a120f0c080f0f0726010b0d06081c1b080309010501030311010b1e01111e1227030304080a0305091f050a0f18031113020a0903080d090611 62
    0x2000403011000103140600c03032501a401031400c0c200c4210307035541c0d6002c00c9400e4840e40803030710704038485150006c51152650b1099400b91032a40f500a46070101b02941d50300300c0701907603c2940154000000300310010415550401e50384172902d411807050008100111851100c4032004016000000402580900650200341079a209540d296162045100200d0990b000f500304150f10805403040e0383d00c02d00660110a1034107c04ac14003c0c800f065401019041c145000c1110b00d04074203411003640c20400901524404548101d1200c0c01c10648a40b80090070701c41d00070010b9070745140d4105d00c5c419501041034400501c1e5802c1181d00d0030140b03103070041890700700314940c41c00340c00718010701055124000c4070002c45919951b24103003440300b2042e08a40c41b007203180c0780d0018410380320001402150b90080110140d07003c1d146190138010b0401c14001e19802003014982c03d42c1c814807082c40c220750b0184004088a4000011079141d65442c49464000e01e10407030000c080e586031078540c40d03079940014050 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 765377769 1250 765376519 765376541
    0xa15050901090830013c080a1122020c0a0b070504061407080f070c0e01060801060807110705060705010e030a260f07050307020c10030509010e011509020a120f 70
    0x142d41003544581e070785404c440c400e010b1001007101e82c090264110504243c10000c40036983d05512451b03240b0002002c0c035500940181d44075401c190402000d1101807110503901003800d544010000841100c01140d000048220381400b80e00080c0c401002e0000b0007943c8941ea400050002084c00c16000140840c1d206209002c0031400940d1900c45506601d0241c8500e980c01440703892808035820401c410a034401c40d0100e8030801d0071038010030022084003070366010304420389580c0440e506103900075009000040c100c000308141c2498000c00032802241c2c0307404071403060f01c2d800e880b1455071912074058075046048084034440440d0200843da0700c041000c86888040122907103840f803034403000c001084112611640351107400c000c076104a1003640119031262080c03040d6405e1481140c001100b1007102c00b20030340040c0e140c40500c074141d0740c00c0c030603c8150384c4120001c01100008600e82c00f40107a1910580220079404140c10079008d00036101c100c45480b0503801082807490604600c00209904901 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 765379019 1250 765377769 765377827
    0xf0c03060501030207020a0509040f1a07030b120d180b030c130e04030503041b03060504050a0c050a080715030209030708030705010c320405030a05060a05090a150509010908 76
    0x31154044d01c200d81e015500a0b082c3c40c111403c003030030f200c0c07610809003045a64503012181e20b0082030003169480c944282203c4070078407074249040014207868100f03d401d07214040d0002c1d03035010b400e030004101504d0246400c0140c0b943d050703014003134030b00c401c1d0358011004c05c0ba0000401140c46a0f55004040214681c0c01d0006101d4584400e5640d00000702c41c0280400e074100003003008910718010602c01700d400c140113445075507201e036580c1d000c4e280c003a282200d4035444103110b0020000b0b06010000070380000d4404100d030701c1c41c00c8950782e560480341c86401b140e0349119a210610901c81c0e012108114000782c02c0700e540179a0f0783c120b1a9070350701402e0180d0700d0394a45070305a41158411404480103803d100c1111a2103201d100c02c2007080403e080e003540600408010007d2651400d0200e40200390195010f44034501d00202007605540009250300705035000350500380005001c01c001d0041110088070002019075940d424035004100c10f40e0090f000d030201058555216907501d0b940c100c54100007070 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 765380269 1250 765379019 765379031
    0x306040c140406360909020a0909030e04110c0a02010309020303041a0403030906090b0405040c0c05060a1a030a0b0f0901150f031a090c12010209091006090605070c030b060f040f0c03 80
    0x3d9904440300d1413030348004002d04403e0308016100150b0020441180010b000d00030a90307036258280111460740c98101d0200d00d03440f0182046180610407c0c9800f600040b150746015405003105071030708038020000f0f0506988084801c02c0d914100b0541e0054060320080340c60f81c0745800c4919043c0c0c0c00a2100310001026250003040f501d10a80d4107008623505817a0040c20642440d04000140c0900183d1104001e4100040c0000c65020044c00d03000d0050504c00048118000c1d015540500c640003074140070358400c1d900300000418613070010358015040b0020b00c1094845803d080d00ad016080d585c40d008151101c0d001c030f001000101401d045a00c00c020751038110711403000c600002ca00803581d02083d83c000d0340000007603040c140c5500038a00000d90005262030075080025400030025107203c2c051403404881880015004521140904000d00b0620305102040d910701004080700d01008045c10030381e401085e182e80314218140481c0c40000c00130310988541d1b085040040c1041100c5600190a001c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 765381519 1250 765380269 765380327
    0x1b02010e0a230607050a02010605090c030a0203040f0b04050c100c0b01172509050f10090903121a010318020d06020c03090307031a15060306040c140406 67
    0x11040c5040025418041c003296500c40d02e4000800701d0102004003031054840d4071000704901071007a54842c4101d600c90f41d888014446009003100c80710740046000d41c000c001842403149903201501c0d4800e101c99409030348c03517a0706d1030100b1801c86070703c1008003015101800e1004000c0c02240b01151030801b40d0f00d0202c0d42603030344012181240c204101414504410740140403030003803002c4070b003940001e80c402c0b151806041ca805180200c00c42e050642d07011100c0505000303101d654002c0b107030003c800021003103160a0080c44207c9002e96441404d10032a5100c1e0300c3c1c03040601402c8080c0e05030081038001c1100c14a480d076074080111001040c240003034a4591a00751075003400d00b680345a80c0d001340405080000660318400254000e011074546440144030b8490141d5003003026401a5200d14a0200f07070003001d510340c142d4100041c2c400c0c4d80c0319114440504081c0c80744010b0b032760b000314204c4003c13545402d00c0b10140d03061140103140040214000801040709500004984900f4589000610500f0042c03 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 765382769 1250 765381519 765381521
    0x301060314060f0118051c060c0327020d080a050c0d02010515090a0b0306070507050609070308070305130504021321050316030e1f02160509061003020903030a031b0201 74
    0x1200d40903803040e90303e280714610f940b01c2c0103801078071910056105445921030000500360900d4800d60794031111100d8049080060358061b0342e040c2e82c800d041c140100352400d008c5030000b4803512101e0a0054154914500b559641880c5056564005090750780c0c45603540310007042c0d03522600b44c124943c400c0d1200a0700443c81407103114807520048501c80b03010300054042288021000d048420a1a12007960b0760056070117010803030090134261601d59a45543d85082400c2240c000c0060ba20764000c00401c001048a1000701e0350102d5052814a03568041c01c941d41c4400b0100d900300c2504207102107900801c40d50040c91a809540000e98400d2400081d05032054420051131303002001a08207004090503481040200f041041c42030406015400c188004612200050710794071000c1d0360080540c0040315010b0105c3c4031450009050030014034140004a05030300c9000d4000d5004001c401781d1400b1140c03090741540c031003041c001c080d20764484901c840100071700000c08041c11410555040c1020940c01 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 765384019 1250 765382769 765382771
    0x210309050123060103020d150e07081008100509030d0603060c0e0f0f040207020d0605040305122a0906041701060602070e010315321906030b0a0905160306020301060314 74
    0x407036811810b0740e941d09801180030350820a45101001e0315500402014209600000d01078040d03d0740c000f50610380004000c201d40005489500c01c0079a04205100d8080d010401895038510f4071404201c40d1280079500c1d103584502c841c0d00180a1809030003008120071600221840501541c6062440c10704400700a01188030508555200483c1582100642826006005d04c280001c0040410071843d444000684104903801c034005000090f0b01c1840c807030709203140ca0b045680184c050541c92121450344040300c00958a1001d0488042950543c9030740341800c440140031080f08900a031074070b550555022b000540210405402045d10200350000c1d040c8105040f42e80201c0ca00040d1009558080018445501c00c0600b484c5410821645200060117590703a0b0100680000003519158000d0780c117550030018034203d002d041c108100081140e0000c0260003980e00a0002103030581890721074034085112800007440c0e240d240000041c052980d01860488050752030902001c8041412540d03d000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 765385269 1250 765384019 765384071
    0xc1a0417091c0c12080c071205060f22080c06090d02120c03071a0f0a180b1012030f03050a0b0604090f060f08030d0b0d02100c2103090501 61
    0x60002d01c0c0d00d0800011601c010301c424010403000341203d8950012601d800c2451000707407004040091151462482000070314002c0a29161002c821f20582c0c1d2500d40b50000503203010301490b40c2002280e03043c2865a0100c420400b1000701350842e50712484d090a49030040c00b2010028054000080c070038150124000404c01c0e540da02400c42c403040c1c411a0380c080e401c80003002c0090f11050110b0390015460803018a00c82d041c0800840b90f81c90a030700020024400244640c0e0710b0350800400e10030010704214482c10701540410301c0509541c1e81c49402a182020340e20000181360f6032481003090640140002e40c0199840d0303400d0003503507104880041981d40107445540c021b00200401c10180d41164800c290817060720001060f829a94401c56009030a160082d80c50307900001071801745c0c0c80e01481200203820003541ca1002c0755049400040c002010030426405100700344003803104000355002c0c0c242c0e00c0a8290083d0044d580c030114001c00418150303100312011341c608160503030740b41c04c00d03480084851 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 765386519 1250 765385269 765385279
    0x1e1b02060402150d050403030b090901090816060f02030f0f01080601031a060105090d0b220c0b030c0c0304030b010609080604210201020d020319060e0f070f0c1a041709 74
    0x28946a0074440050b80000c071043e0141410301c014461080b4902074107020b24001d80c2d000c21075005901c10031960b03c00240c0940c00ca680741c044000c2c00104040180c071145003074182c0d1100042d5041c1458000382501c0e10042c54104e10000070001e46044200000b8004e80c450325020302d8603038a41498944d07801d401e0001416240d54074003070031345003610b0145050b07100c4018034155007400c411a0100f405000350b884100d0303038111100304111a1080d04221415007d0009800600355070380c13520307440400e800a02a0000420340000003614404141d421980703981241c1c411a5030380c5641c2d0420680f00c0c0b0080c051040002c2c200a400079442e030000072558025504406505c2c051903040c041206a03140004c80c0c082995000d101b4080307c6010380c40030314803d0040e19034001c1620400c292a9040700d005401002c9c424010106000381440d0080121398000d0b400d08003403c088000c02c009541283c060742c0010522041d038070301c503203990a2131031000380104d03c540c40c007000c40c3e00003030380c01021801a910500c0e001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 765387769 1250 765386519 765386521
    0x2040e0a0c020318090a0e100e1011040308090d021201060609050603090607030b0f0d05033703180b0c0a030507050c15130c120c050103060302060306040203040c091e1b0206 76
    0x13030f02d040b0200d01e8015080b4040014910b0201d000d450816090001c03294005940d225580710854042c00640500824807004105040030040b0380708850042e0b010141180c080884c10305003503141c1164650300305030028403400d180d100044d9480d019002e035004040009000900c002990300b03181c402d80c2e01030341000001d03040c10794983c603080303004042000700c15270b010311900c070202815212821154081070140b030185954804100108020b4a11038440711002d900920320880004040b118051003480e0340d19011500070101400b08950a03108600074200740c3e0303890240000c2000d0034006001c00e40b07143e10280860380d1246000c0da1680920000180140c000380d070491003c3e001c1759000d6502c405c804a046c0711217011901c401800f031807550050780c000c40401c4002018031202502c044018482407a06002090660f030211b0f00e94000503100c40e000716000303c080707070404c20b46ca071903a00a03007100d49007000980055100c0c07001d03001c82040c50600442c640700341c1c0d1801c9802c42c07101c40818140354004181d2 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 765389019 1250 765387769 765387817
    0x9060603090807021917030c0105100f0e09010f1103010503061812070515090c090903040b0a1214040b1008120406180e0c04030b0702030306130c050d02040e0a0c0203 73
    0x5011213200603c0300b107072560317100841c0301d0780e10005682501c0046002140c8440d401b444203401c481000e4101c262015104100304080d42c5010403030002c0d2042c2d40b4210700d864032205000340c05404620400540282003100007000e140c00d1002940c12204220129451a12164010703640030103c54114192600800a4600d503a003150008040d2244100100e450300501148a91002013055501480e0768210098849961826240d03554000543c40050742c0b600c1d261400880c0709102c1c80000c203040c40700c070000d0380070054101e5000c0003105a01003408046880c1500c1c121868402c02c503906d003140500b142d408036030b151001550450607010001524a4942800416034122010f100c104910708861040412910301d40d100c018050089294101d8540d825440c1203456141d00500d000f00719070041c0104402640c5403003858400d000d10b1a80011160f08220086886100300003003450000e000040000d00c401301c80240c05d01c18441801c0402880111036012a00d0380300d01d0b00702841c00b072024001d2400c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 765390269 1250 765389019 765389029
    0x32703020a030806012705040506010f050403030f0c0807120315080a0b06120d02061b0a17040c1e080d05090a21060c11060604061208030a20040906060309080702 71
    0x600084141000a00d0894528950824101b01c0011589400261004201c01c0c10316002c0d4030341045003420460364021203480000e04034026488050b00304402c00398451079040c0940314400303c0b1394010200d6503880e03085080950100342c01d1043c5d000003900d44074291101c20321008a6030141d42c4110040c0122101c2910350001400d005400e066004050307080e10200c1c1e08081014054042050700984054645010035104501086410009004c010800328581c2513214031003100340842000c0c511000c1e243d03030030180c0b05891240c00c2440780c0d5200f806802c1c0361140005c0c004044820715000c07201e2407400e00d40121014000c0e0201c3e00d0304101101030034001caa45400804894003111110903002000a80f10003003500d1580d0803690104020703401210315880288000ca500100503a4103006032460180d08521014410201070259500800031884001440d04041c0c14207034814008990003a4468070410164414802c1c1c1440e18503143c00056553f009000303040d00b05400020103070a024264003885 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 765391519 1250 765390269 765390271
    0xa0f0603020309161706010b041503020c0a05030c0124030b19020c0d091404060305120c070f1517010807050d050307121e020c0904020f010c12032703020a0308 70
    0x50094000c041d413440c50001480241c0c070050040c022030f02c1911154544d0582031541c1030708501d00c0c6000800050002480c0002c800d80380071614903005a54003480030340d01d410207440c13403401040c03408000b541da04401015049001c582000807880940030711903803d01da405103039034030008243c00d58440000311107030a80c6140f40c0801c02403c3d40036103820400604a410700c440c1200701000310320728030018000781e02c52400c4010000d00039a810000103046846641d510035102101c84203861000904c0d024812050043c1401030210f51108440c583c2c8940d9181c042d104030f0f038524800a64121001d245c0c061b8902c0186040f60100009444410b082800380040c481107103100755903610007004001d0000302c039000c41d02448c5c0b030269190394070303940304803008815202c12180040031940401d560481668504600c03540165040741c0b004d43e00c600e00c0b00169041a4400c0028204040a0007000c0300140c0682011103d4084070348201c0c52403124142000c48000c1d110b8001c2d005038003101a000c00203000380070306 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 765392769 1250 765391519 765391531
    0xc030b130c02160905070801151d0f13020301031b030f0f06141510020a0203070902090a0b07150f0e1009030504080a06060504230c0306010e0405041406060a0f06030203 74
    0x1580783d5422107420501141d08540c003d0340340d281e03944104100b80340e101842e10701402d603400343c148072424240300060070741c981410b000d030003401c00701e81c0c80119544000ba502d454034005444a81ca141c10403882c600290030911090700c100800748102100541d80d01c011100b5698020010300901855480e003600088042008580c0f55941c1c04140422000c2003151a200b1001c0350b003046810b958410500c64098008000c00c01554081c581c03007801a0780120b8100709441411600680b5050301400181d1814120b40c000549070300000748507800d014805441c6072034400010000c2c002c000e101c103501800c80300250381009481e0054108001010703a6504100600e038084e191103030509403611b68036428180c8100003152226944d603002c0000381814020f05100300c41551400405030302c0750f00c1d00d44400c000200300d801d0000b00000018400d17070086541d020b11400c0a8801c00040c941440c0c4502001c1c040710341703640e80d84103c0300014110300c0c101044400391130722103024a04d814030300345054000e5080030b404 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 765394019 1250 765392769 765392773
    0x6071e050309010f050a0c020d180b030903040b070302161a0d0902030705120c01090b0406050304260f03041b061d04270c0e0408040510120e030408010c030b130c02 72
    0x40d0110780707034282c041d17240504038001c0c00040905140c84080c1c40d01d0302045000040c80002070700407240c400881140022200b0903081c4542d030343d6440c1c0c80070342544610341162100000221744c001c141540040d0b0701c2c9859a00c80e04000030991100024060161101200000400208040002c02a40b5003144640c648040c0440e03101d81e448400042d2440103001c846243c0764050010800d0759070b8401c00315002003048580f1a45410304003080100144401403024200c90740700440240c14204821707010000061074031086031241e11040d03180c03407036500540d410390b5510301802e4403210030f0411514102c112682c54440e080d03511074150100074100329021600d0f50080e40c403030344440103005160700d4100300101c120305c2e044801d60310302e403114182c161900b0034040108200108000039070040100c030207941d421140807000010320300044074460200e49103010054100091454016000400fa00c1500c001d00001d0003c803c0c0404c0c228201e038503445419500850b0380b048000f200c01d050340700c1e0045415501c1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 765395269 1250 765394019 765394031
    0xe060a0b03060a1d062404060302033a050703090e07020705011d09040503070606080a0f080f09060a0207140409030c0b0709051806091605071104060f030501020301030506071e05030901 81
    0x51060300b4184100c40111240f00c4081c0e441810741a82400901c480303e0487d4100309140c02e68012a9451049200c1404601202045194094000302031170280f02c140e00e10200c0020040c0794010010b8006481c00c030f0200708482e0021844d2035008006501c03441c000e0307004109841c50500112200e00d2800c0d5441d450444000c2c0c030010903212031903818070484c02840150703a130304c225140c00000c81d100b0b940603036540d07085180e07804000f80301c6100401036a078006640c1034840d00d00741000c12040c86011103607544108005081c004460f004200c0c0b00880700c076451464564151f10080c0801e4070549940200000c400d88110800528901c4415801000d14a0800421600c900200b4052100903020024080c000020402c8a141c22082c0c0e0784e20103403a440c6084600840a0054141e00414800400c008032381c0f02c6402498456500104c020b000700210038403025600c2c14858001d500a000a45090090341c00141016016081800d0100c0c24a071244c05003510204e011a07030344d04082c0407041a5525a4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 765396519 1250 765395269 765395321
    0x7080a09140a03022103010303020a060905030d0501081c03050714070f021c120c08030a0504111f08090c0a06180e0a0e01140c0d09110a03060e060a0b03060a 69
    0x1000b03003034500c02d4006019282141d1094001022041c141250321202000103200080e070100c2c05181c0c1d25071040020620346221324101d0304601a09604820092503c0c00010307007210009060407600040c1c0540c030038100300d140d1003101620001c6410401042c01e80c0d121658900495000f060568020b1400e00200c80f4503034001603164100c039943c42c52020303010351204188502401804150070315030600100388500759448800078040200043c1d941940e07040042d080c41034403800300c412214010300e07110380d0a15403c0b50408500c10910b0303600002d04490001340900350002044460050020480b0400ba89407040c1202c0c3d10b40c100900801c1c0d00c81c203a8002400d2a13032210b81e5401005444030215407541050319241c2161000700700c041c441240c042c10b210b0300d040350300104d0720f40202c83c11000c20310088508000c01c248200c0c0328a150081c1440d1800000c0c000d450740103240c0280d0a0094502585441c50000c00355401002110b500d0b81203030011602d0944036901004030f03008004140c802022441d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 765397769 1250 765396519 765396523
    0x501080c0d090c120302122b15150e010e06030f040c1205010f0f0b010905040f021e120f1e070e040911040528050402040212130213020307080a0914 65
    0x1a0b02510b00c4e040c010218504154040c44040c1e0030406100030181420010803000c00641845040d100040210600c003150725502a04840a0045e0000548260310b076105890071040c0d80c00c0d003412000421044071400c140d031003050f01c072014210080419056485500301e05158010141c000c5800100400c40014081d41c24144101c03c0d50140d030000488040c21901140ad4500070f03081450005d140c811003220300c0e03802c4004803041d1841600c00248141c0c40060036002031042c100b84c10342c3c09642000c08031009040000070b0000030850311030402c440e12556092034803003106440f60410185681100c00200c100c417011264000c4913803030b00e10b0582e004480810202e640f102ca044d15409441c0d07500d541076003024002c690300a0b00040d0140940320504a490108a29030242c075100700751581c020400f55681c9406803035200003c11680d038210f061001c808041d1980300c4104078068503108100c0104404d50b80b080e684121a0750b194111140d41c1d6010580040850500444a0100800341082c0c61002 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 765399019 1250 765397769 765397793
    0x3070623130309270c05040f0306020405040c020303011d1015020109031701060c080304020303070c08070810090305040302120708010e03040f05100203070b10030b1005040e01060501080c0d09 84
    0x45a01c0700601c54003600b402008002c0c0d50b04640200c008450790003404069038248102441e8100d04000b5000d00d4690040b180c5103e0b550207001000580640401030107101d80c0200b085917400c83e410000300c05050340c140d8807400b003403003200d500300b482c1540c00c19403a222030100c5500254280301540f989072a00f91205a119110190400603903456041f90201900b0900e24601c0c20ba4800c0041980c3d89404c00042640c0740450004001c240c0100c003140854804009458950780d01c0240c41c10202c1e12201c034541e88102a01c40c28103584501c202690f100681d42c815208440e0305555071529050840c0c00748803c4c240d00a41d170741c00520450000141001080c443c0c0c4089a81200145694618100f1601500f20082e0081803103a4020b42007512510f4001084441c50b40d44000b8990b410b598088002005440b00da00103070400c4040c000b080340e003200d440090429980200c40030030a071000c00c038907a42258400d019480c046511040462100d507904009004d031081c0004c80880d80b1080b90345c4091009407 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 765400269 1250 765399019 765399031
    0x9030f0c0b031302031504050c040207030302120c250b15031f1d03040e16110f060406180b15060c0a0501051b0f0405010531030b01150203070623 64
    0x70f40c500e2503108624042c00540f1507070b5440c1c4411a45420039807625a102d10468140e1440366a000405004040c00794050303500c24881004400040c1c83c0c100c0d690102c0350b01146090b204204429405104c0c26000c4440d604001d4103c62072041a90b620071310100d400385026851540340c070540c1a60840002d0b904140c2d0388054a0500c0804c941c44000000f005440c0b418901b80007a40041c4418407840b001c60500c0d95209001441c2e07003980702d04012042d6486828100c09003001c1c040d05408140c103450010700280940c0c03041104000801e0011a40d405521044c40c00501550941000c00da004100844c0032000900040c040c40c5400c84150002e8588280c103d01180c01381d459108002082104001481e0704008000030a4035181000d414401c807485240192418040045402c0458500014042ea15034030782a20021005035010f001000f20389881c40212a03043d554800031881c5207100c07490140d0b001150700118100340c07840d52040b000d020040e400c070180b01c03051084040542402d04038180540 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 765401519 1250 765400269 765400291
    0x20a150e0f0402090117060406030215040f140d02040f0f0e0f07090b01080103060c02071a120703061401081b070b09060c040f0608040203150702010209011205060109030f0c0b03 78
    0x40600081c030805402001d0414440e034814030469046907048810ba42c8141c00318411245140c0d114400500101159000a508110401303940c1c840110700000400c181c40880000242d0583c0e40c0313000b0311509182b1840d00313820280d244981340050070181c0020301d01e81e040c00d00108001d481500702c50b0803102c5020720b0307500542c080004803440c0003051000c0405050405001d21420000380c0000e44401d20602c002800e030355807440c404040078420b03c81c140280800a4005600d00091810342c1800c1d0008075100a0a0441c03070089040b55000c1d2080b402120103204d609a1140040790066800c8030005104c004a11803584566402004110042020f05d1098039810309906049000303d11f003010041c80300c00c1603c400c00c401e02603e41403002120482e06c0300c1c5000c0841c0d0f5210b1000c02c0c10040c2e1403824204801100c0709200a03a43c064001e0240e91000b81c6c0c3d00e1000d04640791f81e2405440d1f084d00c2890105000e40c10500100f07960880c45010140580c644a003082e50728410b00060b54000c0382c40040c06 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 765402769 1250 765401519 765401537
    0x210020f0316020a09022a010605030303070801091a01200703080d0203040c0e240f0d620a080609090102120c0307020a0f080403030201140f040807020a15 68
    0x185800e4400c20080d1058441c118149441c1f03480d000ca02048032400c9034048400351a2000800f1070940019000d031038080d0a0342d840c0d080c64440a4100c0c60203000b5900b070181007012503100e01549001401104005a54078013000005824220540d2a0510724003814041c041012020814403402001c0c811108a001030b40ca1420381002c00801c80c4076003000d03445110840c20701205006035042200388440d000c00000c070320620b0800140c001100600500d80000725485458180444207450341c0300d1000000601c0010b5023010300f00c241c44412010074401c9a003101d82140021983c00070000402601000303044180c15000c3d07032103019a086541c8180000300c400080040b10304144c880e40d904400b99400a5041202040701e0031641c41c4010303c4400703040070100c005241c2d00d20070044001040e40020403580009500e0a20305e8495125000960256082c8090800c2d502c901c0b260706449608044010406078a40c1d6480307a4043c2d11601050740d00c400c0700540801c5a01e107091042100085580b40c1c0041 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 765404019 1250 765402769 765402773
    0x5090a03050f160f031a0a020409050405010b03011d101d061807060e100c0309090911120a12110703140d0201061a090913061b1b08070210020f0316 65
    0x1042856082074591581000c81040000e820242580a010807134000c00e0030350b1f0322841c00500a01455229480171420311081c131050140661114101c0407007a40280841085010341c40b60000780010010700c19881100c803401c0e210055844040035078014141e18040000c518240c6241c5001503030f00c42100304d100048144001c00030030501006001600700101c00303000f00c10000d156040074050150611400c002000d081520400b024400703002030720303001c100c004840d050100705400d61502071401021600c042c0880c00d000046c003c90583d501c00100705256207281c60440b1141e4203280910141d100f8142e0100000d000c1003125902c4803c42802084420715202d4000d003900e0059000d010459492100c9108084600742114500001501e21400d1a292009100c01149001c2d0000e040c1c9450052220f00d004248100015480865610885c085422150118420300c60440040422804001000c018101034046905910710743c015141c580c4200c0316460700f540c2c805143c3c16038880e002d1640b001 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 765405269 1250 765404019 765404053
    0x3191506090f0605461407020a030212010b100e030c0103060f060e060705030315130615081306111c0212010311060f0703080105040e010c080705090a03050f 69
    0x1030141d0030303569240b1450030074003921038840c2c0b000150551000d5090b500f90401c640c035140c01c030005120300c15468201c00300d8080b514400e02c051145d000a0110103403000160700c000c00e807052250001c010025880c51a07007081200d80d4000709a08641d501da1201084998172091341181413840703911590b602ca0650410541007814240301e80307060610f8504148000c442e0486100b0075568681000d2415415600000d44140aa00d100070030710301c0000700708259400000b9140e1030350306090b51150a142c402c800c008042d070f20180142160504401d070f82041071442100c7c0a5017080d01100320001722001911080280e40043c0c66007a00702c03200003044820701c0210a0341440c3d608048030114180390100d101c0364249181840040d05482d1107100e03243e5160f455004541803401d0407440555940c0c500e00e0081d06001003486500e125600e07002c030340e0076a03c0060040c1248003904d80d03554901c9035a2014183c1382c1d030300488000b580220b0b0950020002800401140b030b51300d140d2000402c0402c01c0030311806 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 765406519 1250 765405269 765405287
    0x3c1b1b0f09050f0a0c0c0f08190207060f050901110d0e0f03190b06040e0706032003010b09012703030201050f060102070303090303080702030d090311250b03191506 72
    0x2440d09880d00042107400018580301d00c4e0080100c100c0031442451407141191440c40c0307040090050082c6002c0c20040241c5107000b4001824044c03000001c40002c0c00085c0e0300d4a000d0701c258000319484015010714944600c005100142d030505090b0048400d9200e507a1404180e01a003601140031414030284038500b00703030b5601017030200320018900221442115000442060001041200070f000855110303585d41c3c000000380a079141c02c87d01e5641d074841d0024040d00c50100b140095002401c821882c80401c2c1d42180d0684480070b03525840e00d00310b200112a8940d000c83c0c1a42004100b40c41e04031b44190b011242002103004e035001144174101002045003160001e400207056610000042001030381041c104411650142401c10751079a80400a07402d40c4551500c01070001d2a0001ca0020140c218048401071302d000b0007201c00e84005045241107440752080242d0508013951020403602ea071071030003194005c2c3c03105036468406460384a55029680003054210422020400034061300e54010041c07 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 765407769 1250 765406519 765406529
    0x30a120b0f060711030109050a0308010504152c0c130506070314130f03240e060610020f010203040c150c080702210d3c1b1b0f 56
    0x41011145020020710004984038409000362408205802807000041c8808040c0202034024006412585801c94803031380c84900880100303450400104840c1882c0c800c0342c80d00c28445640215060038152403010168401d0303c0070242c4100c90703802c440c50550010f6000d0003482182c1aa603201c011b00b1000c1403000d12150080d5001c2d0409128180229510481800b8814007014100c3d96a2280005a00c40000b00c6c1e08441c19041c648000002007050200b2900103100307040f5481d403500c000425456090f0360240191010313540c00032300410024540303005401c0d440110f074011581000040d201035426a001260107581c0080f0a000070041e01819055064801003985005001c419403592200d42d2030040d0f04011b400b0302e460002808484040c40c1c00c40340441e0505049401034044440c009000c1b10006c0e2036a4050010844000070001c042072030103122540f600c1c03140c698803450100441e00c6408074003000301080082082100810003900b00c02d000300b45001c280e000041c0c01d0007003400e02d4004641c46 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 765409019 1250 765407769 765407771
    0x801060207120b0606361314010303050f040f0e011d010627051309200a150314010303020102130e13201203031f030302060f0601021e030a12 62
    0x4070500189040e6415a0304c51003c40320307180c031442e21001d258842c440c1315602c000c10300e41c01609140e8000211502c600100c02c225404003044140e0020134041d141710940700416060031303000520000e4014006040c000300d4100a450429a84440e1045401e070254042c0c1c01c92440280188111040d403841d41001560b90300e1442015490a800188041e8800180300141d0f0b0040101f80800007000800c1d000824000740010706540d101c852280080500341c004603107050501c2c201910540c8c40b68010782e100d400080c61292410318140360f551100e01070051355000c265039031000034030099151412034061402a0f00041e251050382e094040030000a4104a00c009101420414076509115041c45000d91112100c560003442c003403950000840c0d10701c180d5001822055089054800002440c0718075508208141150b5103441c42c045010120300000d070060b00450002130350744038100300c425002613062041f40d0350b05210a0751250201400740400240b60000244090700946c001184010040c00340c0d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 765410269 1250 765409019 765409049
    0x1209032406090e10091106161202120a08060604181e050114130902091812040b0f13080601060c0c05092e0806012301110705040e120c0303041e0b071b0c060801060207 73
    0x6100c2f03240181806601000800d000252a0741c0b20034098400501c0010311142980400d400c0260280a48a00840c4144c071102102d214088039030040314102c54044c00c010040301419000e0011a214226080b145952501e48050040e00e035059140d01c03035028400304219000b40221000d062005c0042131440350741c2c0a0105000d0384480340202e031200003800c0407495a43c891a100000b4a50340c0f03502003441400390400015a0581080004030007500c15865003152545500c00c02084640641d0003030305650b45182c10106607211040c10159010a9805c00c0300c030240e41c3d10710685400c0c5c0c26003041055103400902c40141c852506c1148804600909005400101d0501403d6070344407203221303091141d5110400042c1c5d042d018422100361540020308141c0c0c42000072034a0396a035000b40e90031240704c00b060380c1c10008048014030382140c031540840001e000c1e85031284100e405803140c201a454401c0c0b010030350000580d12207844801801c8540356940107600d8000040d09000f0150700451031440984 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 765411519 1250 765410269 765410293
    0x30213121a0709120311070e060111030304050c010503090a0b0c0a121a10032414030703110904170a02250e041209032406090e10091106161202 63
    0x1030400070554007184d00d100c640303a07000e05040b141c61242400c1c0d0040c0d40115070b00031480310b4103840c96034840d41c020b80700d0b9500d030702c00604d50035a00e200c00c44010740306030440c04011800e58800c07001150000355010480343e5060540c1c554184240068513600101000029109102500010503c884403240b403010001d42c140e14401d0040300e55981c1300d161098001d80c41c8010001d00039440b00841c2100781d2010322aa103201501c200004005000b40e0f01201100326024a86280000d04502034960150b14240d03501003460500145d510060802c5402c43e02103220a407040c0007100162010507200c0c3e004101c1d84444501460080900098501525001d51800d21800300b4000510f90800e40c0b100103005e03410130743c041c01c0b24282c07000e0700020440350070680c90256207600e08411841c0e07a04c0c52602085800e2b521900d090450b54410340d0a11150085000000f11980a602007283e540c081c8213550414021a00086d6503030744005503489440c10f580c4400303018051190040d030080021380c00201882c2141c1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 765412769 1250 765411519 765411527
    0x30423060405030a020f040f140105090a0b1f121a04110f09012708030d0e1c0509151308071401090314070305010501030804050108061806010c0201030213121a07 71
    0x88900640191b01412045882d5140c4c0d60040c0013419002c1020041c00c0c01104000190307203400c2c441c56124884035801b00c5c5202c0d40070701c034041641030000d110519807400300e05003040303109055004906008012803d0000e45489010342c0f403000e035509610414403940c8104200464420201403200180300b401301c1c480d1000c1500803034281640034200911039052088212080a0300041260360444500c0310009000000201a01844454513400c0c01880e2a0f2b540042d55400c00d0000c0440e490501002d03204806d000398014900e80341c016000b0100f0b1049a280d00380c803648903140c080078404c0e801d0340c00c1052100c140101f00c0038280c40100da103140a181c0000130071a480a00010742100c203001525101524204100401182d100c0c00900880d130303407800d0a141c95000351081c2d0f03005c40e0740c80300054017a24140c0601c014142040a1181035a214040110350f0441c0b0502d04074103066007045560802000000040010032164810074a07804092519888001007040741308903107078040040c48903103500 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 765414019 1250 765412769 765412783
    0x302120c0109050618060d0509060a1803030e10091b0f050f10020312090a030e060a080103120212070c080c01110c130207120c021002070602030d051803042306040503 73
    0x412203c140d142e80e070005c05884207000d603803091640f0410005603a072a03810703c0e8021505ca11801c80581c0c2541e0780d248101e10540303d40881c0d0040c99403925502e0740009000c0e501190b4038403000300444a9107552901460112111a80c00380e40c86011501c1d400d0248810030340030742c080d04108030b0340c0c03903414900380c04150190070120000f0702c90101141c1c0020380368030030401e581002140c2d503403012403414051459502c400407101c05800142000c265500036041c28012240920507554814117561310b503403902c4078002c100001c2e041c2180107c041091a11b01028041c0c10070070301440e020030a903490140807920742940200001e051061050701613603080b00201d411405043c0aa9145811407540684a4001e2040c0d581c0100081031120114400350303800030000c0d506900c25950044c100800704000e036550407092141c0c500682c000c004181c4401d8480d0040364000790440d5148500220880702182940c01981018907130310b01c1e50481050b10000710310300101e45001a14640c5c5014100804a601c1b284 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 765415269 1250 765414019 765414029
    0x90c081b09010b0c340e0105010507060506150c01060f06090501090e090a0b0f04200604120f0204050c1315080703090f020a0605490e12040302120c0109 67
    0x6400315500f00f4283c01408400c4402141481c2440c108a2026a00c06004441440f010007100800701c04942d00f00c0c1c50f40c021f410f03034805849041c1851107942c0c0700f00241c0720003080150840c00e0410401e1020b2a10030180c4180004c0c4000807804c242080000e807003041e52540103004112542d4001c000b0f07a6040107000007951001010480d6030b59852001c41e280510050700101640c08840412172000c640082b03150241c0d00c00d48403218a045a00510724107500d918207401d61004c0d08000c10004520085501c6605074400c00030f024640f4516000641218002c4980d412440c3e0001414002c01e010200c040b0051314044000a8003545012802003240300b00400d0704050654906248007400406c45007020000d60003444814806d0316180014480d804c29180c0d0300440241c1114040c41408003003203500d5280c0c0c000d203c500044500483ca81e84145808074010f60580d030360005000e03051b01400a84104d880ca40303821982c1d14514414000907112408801d603654101e410601c64580e401070546045034 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 765416519 1250 765415269 765415289
    0xb0c1230012d08030d0204091b39030306063c0309020d0809040f0e0d052b06063f060e130212030f070201051606090c081b0901 56
    0x100c44010115402c4000e90849801444003050010120b032480d0004c2064a401e040244840681d4081046a44150803403c50118900c5199001103049141103080e5050215002001c503810030440f80d000304404610a030002525081c00340103690704100d600395484210000748405070244541e911100e102c51a50520b0b007d45500031190031807180d081802c1c03c6800414440101c101850710040c80e90051101c0340c09542015442000703a0307014400c0007820b14010000d0a031190311002c044030645d10000f09100f1341c00f82c07900a061142000c201e0b022032520101c80020f855800c00300c0c00b0300140d0f01d0310240302e051411413040903100c0e07614108503100c90124161100d00584505107120240400307800c40c52a42003030104101c50308980c5910798000a00079508204a02a6103428586911528601d1803184104000d00801548214001c007a00713445440f00ca00c152069640c0c200c02d4401103002502d8108010b9414004c1d18818009051010840c1c4010b2800030841c9001c246000d10522880c4900 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 765417769 1250 765416519 765416579
    0xb0411010c0b0a05100b031e010b070c0b070620070507091a040903020c1e27070c1505070210050a0b0a0e0a02130806090c040203040c0b0c123001 64
    0x300030300346171030400b030b10584c001d05450340b404000781200c113074095450f0102502100c000040e00380c400341c11200d070f10350016000381c1c1040c104801d0a41d140d0010108030380c026555560141c0b007074000342c007403014880c10203040ca54414881c14113034980101074000f00c19462078000da401004178103c548000c10441600c5c0030400b4501400c09a0400341080b003215004206030440031a0a09200d943c5200300104030b52101558a8850041900802c40a45040c40c0c40b400303000708020724014080340c4d900c507100701008259484401c1c12001550400d5550001681c00075000540e03c2c00103002c0d0726404500a00f08200c800c01200000c1e8941019100c6c0c03001c40403040c80802c00e070481ca90111100228001004a1001c0d6980e4505640340011a01c648c128012039184940c186418000c03a4080c1b0707040000d4048090902c0705800c10f95100454181c9244504040d585001d660a4060700700c110581e4001d135030b071a03415034510201c6504100c50500f440d40090042c05410404440d103280c85204a090501c4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 765419019 1250 765417769 765417781
    0x120b01020a05032208060c1b0f030d0b0f0108040c05010e0f0406081c02210901021c030b0a050303070507121407030c0f0905060f1909090b0411010c0b0a05 68
    0x4151201d10003a11a0100007100c81e203010308240d41603103506488a07485159541c139200e0710303190b01c01550b2506013100104400e01c11004801e000030f0b075504c01201039458488039918150320315402428a01c3d02942c48911a00c000e00d007a1034a40000c41c420700380307a0b0741443c142e075801d80c000409018641c180f085400364500540c031410704800c07080001500c10003100f910758000076590040f0b40a5a070722001e21b1190709203214804603618134400b82c5400c20503002d1041008541003900030303801490440c401c00d5004260141c40401400c02c602103600c0000d4035407403800c240580c01000f600410b0180c2d10400200b030004400066070b000711003020103802400c075814a0b10ba80c0080008101070a14070440d000442884008500141103d900c088031a940d80c0d41c1d4080d0b802036440444100794080055030545549003000e00788407c0e050004180411200d881d05015000c07035024500507a4007002c207a04000400c01d6008500c08505424284408158416500c0c6083d15400030120b03141503071500d020a02c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 765420269 1250 765419019 765419023
    0x30c150f030e071d0603010501171911030d08103f020306040c050f0409021011030408011a04060609030f17070b090f060601080903071709060304030504060305090d120b0102 76
    0x40544482e00b18a001300110040d103c2070000c00ba507200780f09500e094000034200007400c06600000850802a1011f69003030060700014003205a000e903084048401e0209190740c0034001c54440941b00d4680400e142840c0d4409060880700e604501038084c1d80181c1c2c401048101202c8541d0b19000c40e420040076488529808681a407030f0400a4043c440e42c0d046c00b00b0001d00c042d000c410385a00707443c0e00229680d03d034104015075802d038a020b9000208d90340c048820f82d02c1100d01c444c281501c03008413031505944032149801c4a4254400b61a01c5e0711040f440c031100d02c1d1074000d86004000c0d901d800725200342161609006201d183c0c2d00180710503100c1c02240b140405000a40740407542000aa01061a04603101ca0316803031500242901c0c2c0c0602d80000f12190b00880a01c4e0255003034000840c10180c080e510b0b407403406590800d0248101052040840580e1440002e5104d207110782d540544892070702030094207680001d019240c194000d141000341c5603a01c0891911001103d810201f0050320f0080103034 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 765421519 1250 765420269 765420283
    0x501170a06080706090311010302031923151314280c08040b090f07050f210304050112180609060b030a060e0d0801120f020a080f0601030c150f030e 65
    0xe21400b403c10300003442d40d0069031100450340603a600c02e4038407110800460481c40201d584010000d454040a1644002a40610065554100c0d00c40010245005030a068207045604026105011281e9202130520741c40c1e4849140320f101081c45031904e503203885164090010280c52071228500c0c4614034560032201010b26044d40d14408010088025000a01c82d40c4100d0701500c07580c40007000314424640019850391007022000c00350886904200c200420116410340480d4008244d0384040e5070035405101d01c0c03007440b00c0c65000b1684c2d80e28180000d81081180148180514a822116440d8941d5005e0b500e020681c0040c0008904220b440d044004201c000f9006416200c0c504101c8204032044e40030f88585440f007001c0301d41e0b0900030700088401d101d09004d081d07601d1504411010001b04160b00f9550014030040c103409100e51118a40c92825a14000345280e551081c001081441011181180503005400c0d2501804140c44ea018011010411100d4205a550b681000c09210240810 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 765422769 1250 765421519 765421529
    0x3030c04060323331005090a03080c0307050c010c051f14090604061d030f0702240310060c023f010912030507090b030a0212040b0702160501170a06 65
    0x10035407424801c10400c102072100b0144030302244100703180004542d8000381985130240050081d5140a009101164103400a0704115001200c011022000170740c110b000e458592043c500450301c07000e01d4181a45010b400c482001d0501820780302890201d44d000c07446860300d02c098611011a016074006d0000104211103898203240040c0f42405810580400c40d14080d40c01840240054100c18941c00c03459482100c00d1410742c0c0c4100801031070415070170050904180010300b4500b6071817241050411071810540d140c03401d48000010400105401e66400c2e002d066689044802d040701503010400d04c10708481803480101c000e02e0b12681c0c28600080310f05c0c5000b20700301d100700520303074100640303018180ca940300701c0c2c40d1901c261049105a21a2142c2c40c070840c61683d508000e00e1400301000041e0780003078007124915408000d00c040c08007145032140d0040348a6200c140a500e09004002e042c40b624404840604001d620200800e07a07111041000c070100b001c2c030200c41a103515121030010705080e0304c4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 765424019 1250 765422769 765422831
    0x50304030c1a0702120a120e0c1819021903051f08030705120a080c070609020436020f04270503121003150b1c06020406030e03030c040603 61
    0xc440c04942d1104154043d202c0b64084607000d40d200c02d4a03a00d6400780d45898000104410780701043c5080705e4101007a80321822054918110150011490841700990b0100380c01030610103100c102900c0c458811032a01541804506004055440b1201903000e100072008050301c0d4004104a031414001542c910784031400e9284c407696035205002c3d1207810603070707007030b07985024401d070407804100a40110743c6103064a0362801d00a42d1681051800c58100e848195001d555444806006880c1e5214141c182165000c3c00051502c0280f08802e00090009550740d11000c2c00d248a801611030a5260840d12021100031492403845407400010701c1500b403040c109940c0442c011002d1050100c01050030f4591004051000c0d41d0380250035503413100310700c801015a0441c05c06a110591903910650741400c00400c00c0c0f07040c3c5240c0c1c07003156400034100d5090340c14a81c00101040140c2d0188580c6442c880b00390065800d600e17081e03038481c00174021132069406140d114002e054403050411812200141740d40c203 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 765425269 1250 765424019 765424043
    0x509100c1d130e010c0f09030b071b060507020303220201121d030d02130510090302060f0408060a06081618050411100305070e0a08060712020c030f0903060a14010303050304030c 78
    0x8103441c040d01e0007a000c5e60104400c9102e41080d03501c541080d80036642c201c45403201c01d490340d440032a2080180d0400c20404007150034403600151850068501403540d45d40151384a00f00480f04e40302814160b0025407801c0700100f01400140d8000c0e03400784c50720125400000d0f00041491207489038402121003aa140d000000b880d00000c030b45a806410180840c0c4160303442541c640c0180300641540080407400320b203542000304018a0204000c0aa041e00a0320745400c0c50f903a0703070020b4505001510f205601a407640710502501d0404c1060051040182042c8110700b460158801c82d1005501784000e00c3c546c54a0005080c8140a00c401880c0230000c1e20401088220100090040c50150790480000b881560780800a2a0200c495400d03070340f5030809411980c80d030420a580700030300080600314564003402075030480e20040c0080d000382d010f00300d145591402d60204050809000811181805207403800903032906900f100100d06407a4103090699881d00ca44c1003e03151060784180041c88400196 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 765426519 1250 765425269 765425291
    0x90c09040224040e15061b030d0603050d080a02340b01030308090601080c1f170106020f01050a0606020a08180901150807080402030c011d0a0303030509100c1d13 71
    0x240c014400c40700d10030b02c4e1011546941d0818130400d01032112a560124081c0180a1a5580958045180c1c0f01c12000c4904d0510001c0c00407040c0c442591007600d064101c0717030a80880a810106466004080301c074110f10701085148040309101c0b0900d2800100c032044641c1c046811613110180e0843e54001402001c0d660b5289002405031030201c5440044c3c0c000d80000141d41a4001000c101d081c6004001c20300d82240d040703c03030451540f4002c00f03030300304010082c0001d5101c0c003400815018098940c0508900d480703c005203402d680000d0941164545002c500b0041b182d404280c4170911503104401c942d840480240d00540d030041c05440716840300808000007141c0c043c884004a0b4043c03a80c407410b0650707884200c11303103050070b080b180a50140c00241c6614603542c411400e0804480342000c0d480045508030000c141c82c10a1a04100c2c04259224144040d01c0030421600201302c41000b0140401e03820200010030410000d1204c1c4c000c00842c1140d4481a40c802c008101202140e10742006040402 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 765427769 1250 765426519 765426589
    0x101b051b07170f0d050f030c3105180601050a090803190f020102070c03060f0612080406080f09070303080c1902010f11040b0412050a0f0b1e090c090402 67
    0x142c11000d00921400c14403291040c8089560000e0f880c40751501c07410440c0d20001d228480d40018500d503091801000346400080c1610b00704484616500d0540300c0c01e00c2d480c68010342200c2c03103030400340c0300c4c0000d2481340e034490303c00c07800b01c0d0b0740500207107016511083c0a5100361840106031f004418103000100700403000110340802a11a0885a9945600000e00400581c00c034421200082d141d449811420b00c086019a0005c0c020200c001c40c000480f5580c40c10700c8060b181e4910030403158010001001c0100561001c00960005a4080245100e040201110760303580e00c14440102400303803140000d204030790310707006482c0c2036512642d402102d4203500134024002c1c03410107407100b0481d00d0036a800c509250440c0660b405e90f0f104618242c50b050400c480010b24116503d4100c540384109903c1000007494040300352404c0b8410111040e040c20084100f2800c01d0084000c041c4003c0410104102160002082c00201c82e041c4c40c540b1264a03203001240003025910f00c0b001401d641c08580b1031150b826 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 765429019 1250 765427769 765427799
    0xf020a03050703030806031c1209020f03011e1a03250b0703050c010f020f0d0911121608060f01060e03070519060908030c0c090a020405100801030203101b051b07 71
    0x850959241440c0c0d00c8e5110466041103500c1c40c00035061001e031525104d900d5002882c214001400700c2c20a4624000180c00d40d0b1240545082c0b142a410a80988170740d580141c03102042c4c40007070007010781e1a040100b6550500c5111140f140c1e0214801c141c0c0501e00d120803030024029150466030380b902d040c100a801e6500030000035001350301e0081003035030120136031081d503024946160318549400745040d0001d0141c18051800d644455203655000c9081e41ca010002e5990f44008001e8201110f0301503005000086607448880701d5001071007044103800c020600d00f4151100c5080029003442d4640200f80781000780d400250b0002c3c1120301819410041008910403180150369408840740c80d0030b88140c5030300540d002c000700d03a0700002c181202460130941480d070107007030070100500b8603a407440003a020207420750b000800305024a00502c258202030145000c58644d02409211007400c3c4d401c0300448040c4000e040040250204030003010301515650800c6480d0010229800359849803071603083c1c0c1d08 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 765430269 1250 765429019 765429031
    0x222c1f0e041515150905030604050106030b070e0d02061c0f05090c0a0b0d0b12071d070c02030d0f0302120a0b2d010e0103060510180906030c030f020a030507030308 72
    0x40c40c4861000d0201c0c06000f488140502066803000c03070303441d104003825240c0c100601c007004c4c00821080480d258408015503442240a040041031080c03650405401c00703e4064120300821240d01414403890300c503541ca4003131599040d181666105500016846843d4813846036203007035400c02d040c0004407000e40d00a00e0250400302d05031010202c0708820043c0040b43d5125030619410140302295901441c0d0f4840e4001c1503001e80080703102c119112405040440c0c680140d00401840f42e07842e5074600041c41080d50101c15402c0440c07010902ea00020b40c2c5007035598010041000c20a5450304040c8240c066a001890303040c4e4214090a2042c101001391881e10112030003400100e8203c0152800c01801180b00013070b85030300c1070002c54410011105114041c00950515840f4100041e0a45071041d0103076045e80d06e41e980c0c00b10040b00750a01503d0780426401000054149030040c00480c000840d19012681d102606641c41800c030310100d00001d2003640040d240307006003440042850380000c0c038a03104038 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 765431519 1250 765430269 765430283
    0x80a031709070e06192c0109020301080a1103070b13030203060702030f03010e070e10030b09060415060518060301080d0f0203070c121403222c1f0e04 66
    0x15480c0514665030b4040741c0305489075a42103201080e0142406030a48944032043c0038208800341e02c2e06500207a03c05800a075200100100c3c00f4403445a010196940c050130020509510319490800c5441e6a41d2801501406403c3ca680c0c00c40c0d42c41d40c0030062180181103000300343e611001c0385a0308002e80c0b19980300503802801010001a84644040202c8242080d0210000e0440e420b1651188251030020903800a11081001c00c0d151961550069044060070b03503004601c1e1201c42060000881e8040c000034000c40c1040c04030085401c1034118841641c082d890460348400500440e0060445148203550f0400b000000100da008404111000b6401180d20341d115000940942245d803845000c0b00a0700d0689a181c00307200c0060456017030410035006200b0032046110910055003140c3c0f04140001290074454005640346486549040090640f0603001c0c410b1004030503030003d603c5446030011500310145d000115500d2101c0180118482219145000c054450b000c1d503924a0060728152900 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 765432769 1250 765431519 765431521
    0x1006090b120a0f290f070318080409022b060305070f030507060c1a07090503101a0f0a0803030a02032e0603022d03103c080a0317 57
    0x280d440011031500700d507400f000540c0d0a8240b074840c1011313650780c1c40400440203a19074840c9020300340000114050009140042e48038144107001400306d82003c013049610006ca281001d0100300340c00d041d00c0c1264190300700580d561100040d03105461401410800005041c0d140301c0d041085030b80d1200c4e040e244200c0c00c480d552603c41e00f869034180b203a84402001940514010f100d014421000c0401d003e01c0b64141101440c41040030404400049400500140504101f0825480c0c01c101c840c0b18a1201102000100c4100c11070700d1810b070595a80e240074210060382e04446880707c40054005207440c8082d41d44904210760f01c01c0c065442500c0032000c01c0800c800452210b098030f1100500c02014820310b5041c41c0c94000144c010b90422150300f464081390310507019040031540c00301102521000c0d01c0300ea903440c04101c80c0c0b02c2c100c0036400c503139000c1c40ea0b00c00400082c3e404442074030300030085940100b10b440494800b020807101c81c0d003040400e40680c411440c100b5070040c3d80003500e403a4800140d081 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 765434019 1250 765432769 765432799
    0x11030c04080c06030c0703050d0914010e061b030112051c090e0c0a0e09060f100503011814011806180506011211090f040204091103040614070e121006090b 68
    0x3d980800c0d9000500500200f06010000b40110000c0c043c0400b002404100e211440d02c034146400440189840d5070b03510f40131011907081d814426903920241a40305002c910340303a000c1c01091404140510340c2c1e10718140d2060701c10b10104000010510b01c04921007550302810b81001010f1901030300c01c3d80840f800d8800415801c420200c103490b0004000c3d0341e403d002418440412007080409841650060300d900380c1d9200d07507102d400407030400d40150b403100e84da69454034007100c0c040f43ca13241546440d6442d004100303e1500091a646044422540419840740e00001e1424024038a0780d020302d0003401901c4802510041030b40000b48100826240d1041210000600c07030700307483d50601c414018130010003450110f880c0801d946190968003a10040c2043d40324060002112200d1060014211011081004104060140e03030190001300c0500320b494104110054408240c1f407502510400c95009000001f1404000d80040c546605c2c90034891a03a036901680014840402124010303881d4140c0010 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 765435269 1250 765434019 765434029
    0xb0c04080d08040305072316080c0402040b03072007030c0501121416020705450c03040f021009080d140711031f02040512060906180111030c04080c 65
    0xb11030f075015120603280c50080e9440401103000c048801000d0542c0f9522201116020000c00b00385009031103802c10a281405040c518207000425040d118500411052100d201030f0700503613030007411506050782c1c440c20003140580c028200840b100e5040c840c1940000a100c855911041240c1083e240c0c0302c681d51021510a0641d04581c80290490260314085a14500702d43c1001c0003c1d03d0a1054072101d036251400100111100da12203828581d203c020b8900341c2c6c48905544003000034103410b40c000f0380c4041d02403546100340140410380442d8040001010302c41c1003a05444803d90041061070030341c4400c400a4403180d40c9019015880c821131203003101c1d1502071501c03080003200110303110b400d0490613681d464501115020281e018042c40640d40d03188040ca45051902d024040d40160b1074901300790902241d0754805807a00c000d903104c0c40612a8124021030604c0d0095007801a011400b03044110050141508010303402c0c240300c00000300701d1614141c40140090700c4814080e0b0340702403440c40403c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 765436519 1250 765435269 765435271
    0x3030e031015030b3603070206070b010603050903040608010b25060e061e010510050f0d020301090c0503010e06011d03120909060102240a0f06030f020a0e010b0d02090d0b0c04080d08 80
    0x1c4900503003600981000c1c0c2d07608203061705080b60b14101c0e0702d00720b040c1c3e010038510b40085100b19024660000144001501809140c3c4e0041c2044000c40c1058548200181303407100620800f000b170b010005481e5070300254a14001c211440044002030b03040c0280c5450301c01060246079816442c01084085851700c181f090f250002c5000a0760044d040e83d0030803040140d5400c21481040c1031040130001101401c3d00d41c4050710150410503030052b2250700d0011006e069a50150301c2c00e0400000300018080f181e91600015003002c02032a0504101d901140050366481d001c40079294103101e052102400510101c00030404c07202c041c0c480c070020b07445800c016603036401d48458039540c61034007842340410780d000a40702a50010060302c001c28410346940d00403023101c16542054920500c0010400150704040001100070720000b14502820743c5000c140000e039005401c6404407541e00041c10800c250340e41178032400c042d60480340d00c03400360428000b1001c10340e02510401100d400b600144070604ea000300d40369 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 765437769 1250 765436519 765436561
    0x21110913030e0d0506040c0303020708070e010905070c060612140d021203040f06051009200409181e05070f050612062101020a090905010f03030e031015030b 69
    0x200d4aa6641640d609401c201e00541040a09842101140c0200030460181e802441c0c01608a411400d00038240310564001e01642e41c000d510402000340c0e80b00202d4112501c040700043c0540364070000321850000608054111070401c100411000303820088003070407078400e00b500084240d03c07804840e2a030030b001d00d0b030802607081407443c403520303004110007190300a2048210310222646d9a6030307481250404e603141424915141014040d0345ca6030312a80c001341ca180d18041082520310050319096100b01d004c1c60726001d444503008000b03034840c07000a480096100c54118040d070480758180741f00600e8014191420310034600b0000320020381a0400c810750f00041c000f00c2c40d0406054404526050240c4a15040078240c5804056811541000c1c81d00b10a49000942c0d54061000000c0100c1016005240010310f46401000744841e10443c0c0c00071250b041c10304d0f80c0c05c0d00303448001a0500c403543d4405c0060504100f2040070308140907c03000243c078401c142d21041a220304000d0843d0505031140 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 765439019 1250 765437769 765437791
    0xe0d0e1c031b06020f030f090f300c06100b07050304050d0c0503060711061008031b150103050d020106231504080d0e040e061b03060604211109 63
    0x50500400d106084030b414207901a1500b0805000c1640c9860072a84600c50207034503060041706004178640c07620ba185030450b4007480200016400c540e8020b444849500d03503807403411040c10300701860320750b5400c0400e04603100c4c0310f409071105405030450751590800c03640d140070300924a202203228801c0d0003d42da00c1540000c001c60503c0c2c01c0a00b8004030042c1d110007915000c084400008640c0c0e000c008180c403840550703403000c140d03c034044c46503840c080c4054004400302c50016418090707002c0000c195600302d0243c91049c070300c01060114090a08081c2d0008030300c0381d41c0c00000807060120008034020042c400d9802040744541c0c4100c8000c02c400241030b4103043e01c009400141701468540c1140c091904100083c6240c240d0b0b481e8210300e41124103142401084052550714920310702803081503100e4403d8006031505280402300c1c14205800702410b011544808800b00300c45846000949000e01204903002620038481022a04101c1c4a541c003220700c482280d085070420308185600314028040482 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 765440269 1250 765439019 765439069
    0x8071b0b150a080327100201090c0b0307022d0a0506090d0203040605090d051018020415031e0309031e060b030c011b0302160b1c0203090c040509030d0e0d0e 69
    0x380485d48001034001d034429609020340c40c2c0b01e5036074484642c0f14503595103400015141c0941c0c034000c00681d4640d070201c2c41510301801040059500403a00e10032001c00c919110202c20a000c0489031b0307000c50070601e41070b107200e5510380c84100200084c0c50750203a6060821544910085002280c0da8826401800300140c1d00b800030b441c0390308040c0340f511901031180040d035000000101c10802180d000844111300d0707010341c0d40c8400a5003003510031207002e9a03022000d10003035400c1d5110000051102e504007110b8440307201d841003c3c18403030f031481400340d540400800048010030a072245e118603599010341d2110f00d01990080075140000b068903c20106840350f090080e908d440036140d40403100810b80c01c0d40540b803103115507042d0761880030015100b0041119143d15044405030065545880369188091040061010b642800108181e2041003101c0100d00c0d90344103000b45043d4000c11140d19030050030203002159402c404510100000c2050b40c404001099490801144040259122075a82e1441e4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 765441519 1250 765440269 765440287
    0x80907050a0e070215160f110712020d080703030b1c021809010204091d01050c0a0806061c0905011d15041e080406030504030f0302120708071b0b150a0803 68
    0x5115038402c0813030066410200e04070480b204e985800b1188000400200d41710764400340d40160021071644054070b010f81006000045c416a101c0840c047e81c000070440400d414215941d03070702092101c40e8410005a204c202c03a1601034081c00c0170700310852050f0401403015161500a4000030400c03600104800e40c10303240e81c409034190803409084205176540802002c2018401c502401a1061000c0001c014400c078440045086400140045184001c1040ba122203181e020716000c2d049482150318664a00901d412103807200c1d5001426441c85050140b45814400194041c46000104560504500e1100c4141c0d5448080000300b240105a00b8000b2401143e07040c08803862485001010300050001c0b5156808103401c940e0201c00003a0f00c0c0c80c200020103a000c0c044503410501800e0a50a211f4600d00c5480f003810000c010408110000e800181180e10940078944010044003010b4500196402c01e00c0002d0310403601c1000043c05507198080078204041d1450448560002840c2085802 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 765442769 1250 765441519 765441539
    0x80f061c03050c07031b08120f09040204030204060e04111203070618021c0314130320060d020711150406080c070506071707030c09120311100606080907050a 69
    0x9034000350100072041c0000c942032401000b00d03002860140b418000181c03103105107400148410b40100203190800340407005884d516000759180b4081090b10f0f1364a9082d030b080441d000307010301d41c80a944035080150000c2d941400c0100d242c016400780000310605000c6809120540d0780d0001c3d010815801042400c0100312603900099441148480072a401000c41d00016804e80c4607503200e41d180840c11410004040d00204400400c20348507a081c1c1c101030004030140c400d56031611015140304180c08030711300c1500729043c20040408004203d00d488884001240d0001e410151044556111152564083d49420002d43c0055900810074034601070824108442882c009003a10241900c1032144000058007400082e21030f06196850007100e84d040803442c10303001406005401414035008001034119800203401058900540c0c0e0845801d606140407034450401d121032241c40d0007100c1d0394000449150300010110b80744d5583e4070070300c0e0b00c1d02803038140c40f071140303229050b4000103c0d00b003000140c0314 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 765444019 1250 765442769 765442819
    0x1a011d13090803061e0604060c051e01021c060e0a0e0f0f0c011707080718170309010206010e0f040b041401020304050a050708011a0409060e0a080703080f06 69
    0x10103003440014412215516094511810003101c119802004010f41c42c1406001c9511458108070f0003c3c038501c030740c0e021589070300c10303401201c00300100071f41050240001000441d0220b6001d1440106e1840d008030024002d4000400400207100310100c5504045003600801c0181c2d0080440842349803518900c00380140129030040383d5a000355202e00c510385a0500000181c12a448090002891000001000c1c40c00d12006840d481440780c0c14400e8043d03221040a902c4545810410b2662421190b14240142154400d9410003411461603509401c0800940042d0600380c0864081e83d03291000d40803032207002c41d0680c1807115403000190100e9a0500016000360080c00700c0003203410008011400d90344211000d40d2203134000d0504d101002010082d0000a08181c3c0081248694400c01d54a50103002910309100c2c5444194650070f1010950128500e01d50300011191400068500700c00f080e042440190046941803000441d148150a2401d1050300c004101303803d0f80125100c10344601c2700c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 765445269 1250 765444019 765444077
    0x3091406060a080334080307080a2703030c091205070816032409020607060203060a081617070b070b01170a0b1303110106080106030b06060c0a29070903061a01 70
    0x10a8a09801055004001f9805040305070741e561901e20308a01c801d029150342c800c0d01c440314074500301e4030341ca000140c4464007a110740c1450041410200b142d01107410400d503420145054802009035802c000000405204949000c019500c90701851800b00c001c45000344805064007007005080140000da1041c4101d481c00d0301000080c824140340c000c60307480c0d0000041213030060341c00410321005290070300b10080189031500003018100007400c9440c070307456441c1c070176a85a00c1d0030741500034201300c00340011400340c15052440c80d150941414070500c03001b02886000083e0315101a017444c1040081058599283c0262081000b41c94000c0a01170b842c07060001602003000c2030554002c080e4082c09540001c003480000811040c1c21401c1005000c20080c004520900040003605941c2401043c491180c81d0040c107008080310204040c5901c202400404e02503103c0554100244030790800740d1034041c1c80c0912420055084240c81460080c0c000c0d5500740c0c0455602400b0003c85c8a00d4042162400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 765446519 1250 765445269 765445357
    0x721051b03042a0501030b03010504110d050709051006090f0b04031103010e010f0509010606030e07030b0606070f0f0b060105120c09030a0b0c1209030418050703091406060a0803 78
    0x1030308054602c0c11521000001c83c402c02d08494104241e69060044070080c590840081040342040e81c7d400840c240440300c5a802042821008820300c502840868006c002c080d100340b0691800110f0b404084501c0d00406000c07512510010031300c0007103003021400340d0300003c8100b440c003410758031410b00b942c800e4021140c6c9076480b55000070700f0000038020300c00564003840c8045001d04095000741d00b0b603001a0040400c0514000d180342500d100060014200c9401ca00d241a01e80ca5040210b4094866803038040c0c034840210600900300a4002101101103000e59003a480030349600b0b004460700d102e1922103c19071421207012070f1064000c00000c0c102c42c000242112100421076503040d9200504548000015a0103e254010414400c04555020150101230742c6490306007c5080c0820942c84030301d105881d95100000c009501940c0900d03540741c0c0011000918007282e4010941c0e807041211150b0054141010000d005031002042d9100c204a003030780309a00c00d01529603d01010100b5907401140 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 765447769 1250 765446519 765446543
    0x7020a0620070f060605060c1c051b030c2b1419020309090c041206021303060207050f1b0f0d0218070f0f0c020108040818090721051b0304 61
    0x21401c0000141449407144901051000242c14550111241740e40700d68011501002200510940031860404405602c80600305204814604540300d00580643c2281d21298052103000d1601c000081c16002d01440300303c43c0345881c03a0105411071002103030803100031461b040e01601814054078072401c100001026160601050304a00790160304101c4650001d07801c00124490b080c10500503095001d8600c902c0d81e40380c10b0be02280c02042e44208000544000c0e8085814101141d202d1031080003540c0001d010b5440385010704240351a1a42c00340e0011240c412240003107409585170a03103070540d000080242501c1d519a609000250b81144012648800e00f110a00d54000c81c000021740541415900c500c03070035208503405800c1c81c58250004040c000880201401030380c1c4207080c90f510681c00342d8420b4441011a64a1310111610718030564410601001c02c11803c1d4413000c0400070a403921081420350352912528022110250740020350f1440c40040305c903400c3c40190007076411500c6440c1c0b03c02c00b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 765449019 1250 765447769 765447821
    0x30f220506040b09041413170703050403080d0e01091202011d191104090317090303010807090209010c060e030306010e06070b130201110f0c0405090d0c110f0a09021b0607020a06 78
    0x5040b4100d41e41c81c030302060080307c10280501d40c8280c840c1c1030300128201d0714000e6503840281283c0110302c0000c4c03d075a400601000c0e0000f460b040b45610402c0700c002841010b265141c01840311a001e0340340401986861701d1804642d00c01007601441c821408041e01d281113900328075150000c40c804c4180c43c00781c051810b95803035840d144a00c4400d980a556a41d540e4000c003d14829031a002070040d6001d58030900042c0b0050078040752031412501c44000c0165150019401a11000f0000c4000b0b001140f918905c060600f0000c4000d6108150982c0e984028040403030402149001c2c1c040701070054030040000a9820205110b03010081d8014102440301c0c10502c01406e00d40103085001c1d0029800c0030701e001c00d160604c1e01546130812580809402c1c22001010000c203030405004004d81300403130900000e02c558580922021200902a00e00c00310700e9103500d01c810180d031007071040708082d01c4d0380500c030610310314042402800f4030703019400f03004407654a4482402804001841041680d120050340c02c03 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 765450269 1250 765449019 765449051
    0x20a0c02091501021c02070608040c09050f01050a12030c06020d020708070501090b10080d0f03060b04090203090f190605150402070b09070501020c06090108090f030f220506040b0904 80
    0xc0701d4211800101400e0480b040024144003008000701d140b1421003040d1854244c010568606680c6186055030580d626070500c0c2c0454413081d4080600341d841c003000d01c80b05054808006040c0c0e00309a46030240030307541d03060400b811703082c102001c0d00003100341003081e0005e10241c00030055088540000350404606da1584065540105401c4510ba9900c01102c02008410450150f010f205010b102100c03d00c3d14006607190034038001c0d0402000a20365882e82242c2c0641c0c48007015014a860003502e850715044a80020350090311403038130b0340c820b00c041c031f1410403400904050203a03400c1c40441c114100c40d64811014141c040c101c0c3c0400320f600c9400d10600d413201d102900c503040c040e0f03901d0302050800d441d000d0304280107608080d0464012107000180c0d038580c40c0898001300000c2c41d202009030354018042d41040546401140740c0d0100180d2544500c1009016064041c004044102e01980e88902c2c80350000c2d20b4820b194010700140070070026005004003511181384050720101c0c0c00d00340749040d01 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 765451519 1250 765450269 765450271
    0x6040c210e0304152105010b07030e04090606060f021c0e01120204031712090c03190809100503040b01170607050c0f0d08011502240403021f02030f091b04020a0c0209 73
    0x700045c10482401140c0181d040d40700c3c04202d400b2030802c195410580503810314410713010040c040c8074510103120100e440e10b920600342c036074104108004880d21042c0060070701001c05d039480010b2160750070004420001d0f02d180d0001ca1010303100c0c189401c40d4003005642150000140301040c0da428040000450301c1e4130b14010b00303c02401030080d510343c034008640d11040c0e0060140d4807141d210705540a40b40d2070001d403850308a0420141070140c0000751a141d030036031290781c071f1031034029802580d07018129030010702640c0501d00c07030002610340340c0c0c80c0d00c0290310051807a00e00300c5e600d5000c24041000b460150300106270740e1841c4002d441030701014070503551030300120405480004a07080010071100050b02c01d04401e0384003038406481a5600040e8030020429841490f6214840150100302014003c000c2a1801d501702038030740c40b029018000c450020740048400b600f018804800268a484002c21280d280c00500300324202e00c41404e106000083d00010003210034448a5500440513070b544074061 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 765452769 1250 765451519 765451559
    0x703050f010c03051e040822030c0812070f170c190606120221031207050306010912051c030e030426010504021e151206040c210e0304 59
    0x812482d215120003011160002c021650005145030b2008140d141c0303441d4660410340081c0c0d11602d440079146800c0f403100e200c03000c07821074a01c0040008100000742c01c1c814101d031264000e840c0003445a0404842500c1a01c130004c1c02481d00191180006400080c9411002640700c140c03030828803260409841c0400084165040700b680c642018100b011a004000203003a281c1040103a000842e4045040d514481201506900300c424801020360310810a5030301c100c0848845c1440e03400e00d028007070700c0d035403051b84c2541c001181c0800c003188070104240e5030301030a64000002c210f03414821180341084c041c1c18000200701900c410000c184088108090005002080c0002414040c0380748840d80d1000e182c12080e4507641803d08200c0917980e508000700d0b2001c0281400316400f44000000707100349800310815000030740081086000c40390a0f81240e03128801c00d0f80d00b0001140007040540d1100320041c4151801c00340c040388687c0440d82d82d00105400ca07141003c807400c290716810150404284480300b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 765454019 1250 765452769 765452771
    0xf020414041110090b0325120e0d050919030b0c040e0108070501020c060a1b0b1e01180b04060b12070f050f0415050d090b01050a080609070509090703050f01 69
    0x520081c80880e29451050300c0c0111842680720f02c1490000d00b07010854482c0e050100d0380840044c00e00c01405100321600042c0700008a16848183c10140c02031420403003001380d072498015020720381480000c1114036a4156225541081084020000e2741c50700324505840fa00088039000000800d0500d140340079822001c8200c0d02d0328201318800b240c02c20160f001c102d6550018204204590300401d05041000040e42c55039514100c840301030352205d034044501c0c500d005d0801d01c00d40c2404403044d08c4c0c60107103111551542c54100c03d15032460301c80c80c00b8080d002c21003001d58560000c80421358001c17000d10001401c086101c90380c071203510072560000701740d1181181f036410410a4565102d504901901624280141004004030764459036006900071007032a4035480c01408a07050080003515030440318800103020000da6490a017a940d002803040300c0c006c244064010601a0b0085011849100d4200c01400b042d4949420014501c00113003040501d03005820011012500511000c0604203034400 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 765455269 1250 765454019 765454021
    0x150c3207060c030e2a01021504020d081e190e03070e1f3c1a04080d09050307080a0f0803130206030f01030b160c1b09090605060a0b030912070f020414 66
    0x4e40503180003410f1782681190040010107449010700c40b002c40c2c10540580c0c5080d001e01082c0707412041841450400340c00d0040b482811040e40c10343c4030040c28082107591010500c1118544180da8403000b40c07000541c503070001031060048051100c111503000000c035203125030b0100d503c3c224501d003c1e0645c000c040c0f03424800004c185000c0c0d021034290440c00072884000350821240ca80050402c4290082920222180c82043c9030102c140c02950040c000d10005c1c0c030556803542501800e09611840f41900902460714001903c5c100842c0140f074503070300400400181e8403c1d036608000c41d40010300d190200d00c01580d01d400544c603000c000d50301c100c0c50513407440d1155055017001c5030282c000070003107075100e03420128103c0301591202840a9160b484051034140060588401c40400481e82003103607114600041c04040c045d03142c00c0381c0e00810050300c08811003030304e510b140b0243d4842101c034600558410400316050a5110006240076070141100e0000880103500040c02d8441c04d6170380f03e0421110304 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 765456519 1250 765455269 765455323
    0x3110f180406051c08090a05121608010204060f03021b0d1d0f012f030a0f1211121515120601021f09150c3207060c030e 53
    0x220411001d8074040740d80c603000c03140900803c0796004c0c400c0001407018a01044410540d115090f814015240040200c9030940311149425551a969907205054900001001a400c041071003110b06588240d5582080684200300c207401175030000101c1c0071503503038020401100440501c03c40302e015480d40e0b680482d80c0384080c081d1020909910000b0321488140c0c005a0441c0c0e0002a40045541015180c001d8136426a90901070202c043d03a412001d030200046461a0315840520040c4540f02c540310381042040003100c22084070152512103901d03600070481a00c82d0800b9141c407660240816086525958008010444003a0241400c14203400041a2000607004900703403913901041c2840140140e40a0700001c0a4a2046400f1014040d81c0c1c2c012940c10301c401800305c03289000300341400f800804445080201606070744044030b2060401c248106030450424030601e200030410100140c2411165218100284541c10280090550314003804000c1c0c6020701c1003880019014540c003081701c0d015 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 765457769 1250 765456519 765456521
    0x2030c0d031b110601210606030318060206101a040807030305071101020c0f0603071115060102191713030f150b0103020f071104020f0c01060f090207030f03110f1804 73
    0x407602d110b05200c42c1070400c0c110854000b882078110f0f410040003000302c8901d04030083c0d40002c918001317841d55060503c08424140c0201840c1743c000000e800003606c1c984d0300c10b000c03030312500c1c00d45051700740383c0d44000108802d01040385c0c441800344410400915003039542c00c445140c09400c1d403003100401d0022507080244032080390300b412844170a001030041c03000010005881c0000011516220345001310218060340d11402d00000c00400040c210b807200d10000240001480301190380c5401171042d66411821451070000c0340310317004d41c0400d04265083c1d0704a0f04d40f29030303001020b0b18004c442100b80004046a20005a8140103000c0c51111b200c81e0b44284c05070007611000703514241807500406c1499030111884044501468211024407501d6180100042c0030780300380c00b000a88260003103602500c010066124104a820012221003610340e80c010380340580c055544003030003154a8030008240940240c100601c06c0c070700041c4040c50820380300d11000180c0c00158081e9402d04040d582c400c00c43c242 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 765459019 1250 765457769 765457811
    0x706120605060702010c1b1202040605030a12320d11030105030304050105030405120309060f07140702010807090f0b0c06100e010527040807020f0a060e1002030c0d03 73
    0x8a180140492800d21002c240a4403070000004c0c1040503040c4044180000d515580c00300ca00403004400010307540d16001c44d40000c17840401d900c51440c00750001000d16001507032944103607001043c020300d82e0410b1001d645c1003280c00c6114240002d002c1101d04800650b41544000d07001640d42d40340c0300d02004c0d0340a021240d1341d802508a040017000140b1031983d0010988007142c20910340507940750390707500d03020341092007480d1023031494140030040c00000704e0042022846229a1100360803199510b4004440d92803e004400c503054a003080301c2d00c09548190180c940c0280c030707070400d4000c0589e44ca400781d441e405c0541c0705220083e808a001c0d21031050910410f50050240c045002c140c40c145481180d44010601c121481480d20364480b0502c550050b010044402d440171088403030f440c040c03c082007243e00c24a4124440d6407100a02c1a50345004001ca5080e10016558081000340701c80038440f40040190000f025403100348840291034508118006010040b6034011420a0007101c2d407441440c4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 765460269 1250 765459019 765459047
    0x3050f0706060e2e17071806081002032203030902030619060f05061902072c1e010b0906090406092703050a18080d092408010b070602090904050706 65
    0x41000540c00c034010100c84d594041e240c079036000668030841809810315018080d03100000c1140c41c800e2883d00c4c1901a0702c8502103442440684d050b80c00300c000003200300d100032122202d2200030ac5c00102020381c42e403000c00c400c0398480d007000240c8000070b07000030f4603001c3c085a205008411400d29003590701001d0040f40010071401c2e994070801030070000041c8241c09140d0710030b420700030890020407480c2d01c2046440c00612611002212140b140f0742624580380340e0243c940700a00301c0c2c001048001c1d9680f03042c40d007000c03422804c202441e428504c3c54503641c0d001400c441d91110007403110b0b048a96a030300c074920040c241c00d20f0008034401100d8240406140260480d00d80070b458041a1000c680c0000c204e444d07080c80b600d01413507070503054684024228070b950002c14551255500c840005c580145102054507031503100c61019500d58400c458038104210400740008245c00c0c01041111400d1001d0050fa51090f040075007008280c0c0041070200b642101d003600e45900139801001080d40003103610040d20 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 765461519 1250 765460269 765460321
    0x50d0c052b2012060d02090703020a0f090506121b0c280206070b07090e01030803100f0f05040207080409090c09150e040305030a06030b0a0207020a050f03070303050f0706060e 77
    0x420b03280a0491405504940120303101050000392065896482059901d6030080c07050303465017007a01c0014001e4100801e0840400d080d0441c001155004403082422514010f00e42c6140c5426052301010248020b41071100301028180147c014907045001b40c25040301c1c40c0020503180003800d076103a140c000501c3c480b024607182400b090f4096107400341103e08054202e450040c0c5500c90340710841d2890220341c0401d204c003402100100402649600a6008905e00d210749040152200c0c0f902c0c5860300e05124642e1040600310080000303051a0b0054500d8074043c0368224140759071800d440058a0b01034408441c2c110f40100700780851151886865500c9c40b122003c401d04a06040d00b69840c0c0c90040c2000d0140000800040c04850254103c40d01031a0320901001740707410070500c0b60700030b50040402284146100d007404038950919020000000740020020070840745952015210b590014001045402e0100300d418003066880c01018020700c21110640d455117000c8800d00d299a4900e4000030b240 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 765462769 1250 765461519 765461561
    0x18140c1e0301030b0f04030c0f060f0515090711100e0a0209070903120309110a06020d0210090b0c0c070308040e0109050603030a0906031508070807061e050d0c052b 72
    0xc141c0c0e419000f0303800142c0305a01710315926076040a0b50b42d480005401090f02101c01c40c0380b8100700c8103401a80c03560000744c0c0203002d103803140d00b2078001071840d200c03071550045031482c0098030083c440c4014408001910040d510344140e0681100705580d00346c040500150f0290150300c0c00c5040082c0c1c1c00e07a01c0f0000d0301e442e015807415a40c40c0054900440c00003000c00d81c490064000340302d900c0706400c0203084000e0440d038a00790342e000069140c003a030101c000c026000300b01029424030554022150b0311680b142c41d20306266142c4076103410790f801119001d1aa4420b9940100005164100070809032039409044005503140c406003005440004115502a07041440036284050304055184240c80c41030402003044c080c11680e0300f0704040b5035400031740a44540100010617100c0425004299205982c0d002c1c0c03200d43c040c0c40083c98144415040c4006582080381e01e00c444016031000b6001621450482e00c0c0c032281382210005803911f04404d0b101c109102c0c0c40c01c04118000d21071401c80300600c4210441f1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 765464019 1250 765462769 765462773
    0x60608010e1005061e13030303050108010902090f1b0c010501080d11060a05040206190e030c1c0f06110c011a01080903040909080c03160b0a0902060418140c1e030103 73
    0x1e005624482d2a0050780e012a2000d0110044440400385d0320240301d0054031042a501100d1204a15100a4000ca03240000204e2480300c1030041400081c1c000d400384001f601d6603606000111801404011a070090084c190304845900e0020040128000e0020595504002e003413803c014030384801348184090605800504440801c590703a000d046a42e001980e41c5d61030000c54514071a0894140e0522880858017400c65005000e6011540040c1c040740d0f01c8600340c0080c400f110902e11610300c0c408000103201d00000b8500d400411041c0d02c0b500303000c10a0285c0c00c5106815411115840c070041e5143c040b05120b5026030768030b9800294091a046105090074881180c4a100358000d0711038043d222088079040c05440c9084940c621000d008aa03581c410048401401507150a001c490049118002c0303440180580100b00c0856001040c1900e482d10f032045484080d4406920513580c0c41d00c503808a420880d0300b80c00b40384181a0b031311450b41e40c1d28201e07045070041c103590714106442c01028401400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 765465269 1250 765464019 765464041
    0x2160e1003060b0102010608120706060f08031209030706020304111f0516021512060109120c180e070b0901030f05090319110105010b0d050115080604230a060608010e 73
    0x3040340c0d00080b00290500341800102d0250090f500030022911a003200000c10b09800c60040494a0023800100b010b9615824040102c5045228001d00d82e8410311988098244003c2004d070028030700390071a464807a80c0d580d80c1c0281c0c2c00885007a28050303540524817107a8203241200180030079688514083c441c000c01c00c00791140c06002c081061000c0342d5140c120440d100c8501d42e46c15280980b07800342e10380c10b8a40c0705016030b0340d084a103e800101d85030380002c0c2c0750700010440445642c1c80110040e241d81000105d03040e5020030007040c5030340d5403036101c242c1100740c2c1400108003400c1c0408205595441201c00501500e40b001c1e074134000c051614040102c2100d021003a01c84403421440440110104c10000310381c03884d0f00c46041c903210f510349000040d07815201c10060034801000300b0107012aa90341c42142540c07185007100c17407001c1400c2e0400165945010313400b00e06c0301440001d4a00c403d5164114582c240d50b000c03131b01c41110039620002401501c2c0c00c950040c0c0108062401454546446c0e0b0b4105 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 765466519 1250 765465269 765465301
    0x61401050303070c030308100b030f1815130303091a0906060604030c0e040204020c10090c06050301060c02090c19020604050c09012d0b0d0c030b0f060708090301180302160e 76
    0xd02081880f0000c00c0c903402e84021b23550001d00760341c03900a4490420100e9a1842c4400780c4000419104d0f0282c0c4200004000c01c0004640701006003055507076998481e28400301c11001400c600b0140d442540d400061001c0e80300041d103462600f81c084c41d91511101840c500702c4041c0c0842d20a02042c001000000e550340d07850401c0e07a094000b02c541d50740319840400c0c0030b8090010032107414003502c2115601c503240b981c094810310740241d0700e80c60000d60f52101a01c0500c02070140358005074507001800054280307400354580080c0c40200c242d20b031200c041d43e000200d50800c1c1c04000160011414841031003810022082c0d0001e08031000030f155454001a20480c0100c481c806d05800c800c0e4000e856540c49940d0790314010417080d4807099a84802a2120000703020450a160209151000c0c2e03075068100b0300d107920103010307001d0451407a1688644603403509422254900d5410340d2102000c11b20001074115500380f06100c0e4000740060b83c121080c24041c12480c2c0c1100c0a00150601000702080315104a0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 765467625 1106 765466519 765466523
    0xb070f0903030f0e030705032e060b04150507020409080c2a01110f071202090a0e0d0c030c02360c0d020a1b061401050303070c03 57
    0x6465610860001030002455150a8075030706010341d41844c50000300400311100203075904c0c0068034104510b10041c409000e480700c0c07008a0740400008000700b0004c22010b12406080102a80b400c2c0500d1080303224000c80100c1c01c0095901070412101802c5d0050010300c8052020300340307070490381d0100d04200100d104400243d000b80e540c0780c80e40490400c440c040c03c810308201c10011554840c0d29242500d0343d0041c0206210203400411220005104102c41c0070507000c21801040040c9000070b10400b011750502140d0005050b001c528102600030f58200614621303164101100c1410510b50000e410103074096080451540040030032405d0b10104c00e80f0701011440140021450303c0940d04409002804d1081e00004150740d0040d025400f600c1c0b610307480f0059000e580005811910005035003ea0303035079050000194842030918090a810340c000d5242c942e81d0f5603032600902d414440 = true := by decide +kernel

theorem cover : BRFrame.Cov 765287769 765467625 := by
  have h0 := BRFrame.cov_init 765287769
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765287769 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 765287769 ≤ n) (h2 : n < 765467625) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
