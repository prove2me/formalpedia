-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4205
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:52:07.378424+00:00
-- url     : https://prove2.me/submissions/0ab26b16-fbf7-4a3c-a69a-13d3665a89db

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 756115107 ≤ n < 756294964 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 756116357 1250 756115107 756115111
    0x3171303120206150a050d050f0d1e1803020d0807170405030c040b0d1113050112140d080c0c0709050c0a0e0114070605041e03022b0903060c03110c010203 68
    0x1006100f4280010f080d0302010000900c6001c2c0100441259440c0204021030b46041402c240d900b070040710206489004100030400c45000c0f15118070100105a02141491007900c580c15024003003040e81060000a92241c101e064035030444610260758842d05005400e801001b000512040e19980a00c0c0101180009402298801c81c200c842004008003400242c0352107414641d04083c1d40040b42d00021041031203901d54030360182244a086103c21055010b0301c03c20b0384042c160842e0700d1b000d00103024000c8007400e4550b40c01d1005080c40d140b4450010316131800180701000000c4003240c0c04007068024070050006002e0326209018500348511038100715888440d08401055051040d540194020300d0300d0442136a5401401e8200101c9403100400b4000041080705c0d03121400b03e205c14101030f55941150304a000394000e01902c1803442075112070341110001200741100b0034106100343ca034028012019282d12800c080b840341c5012005402500b04c80a142d1030131a8080b511403040c0e681580070394 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 756117607 1250 756116357 756116393
    0x4061515021605040204030c180902030a03030b0f0d120f3f06050a06050304022b05010e19030509030106050406030b31021002070e07031a0a0f03171303 67
    0xc0003250f882e003c00c4101d00c101d20004040000f2101d04225130007003440d034528090342d00342d800309081d441640000c1c2441d12700d03442240030030355580004101e42400d2861500102090759040c028100c0307512401850089140c441d000c220814181c1065507115890302c5045403c811801d0010b0200342601918101222485510b00d030351002c210b2800d030201c0c3c0079040031140c000d03040c41089810040c044030a580018000e981002c003402d00c1c0703100b032081e040640c0f4031000c1d007405480c44c82406140050075141c0320381140310660700890503074180120b0801d54007075091b450f0622590712000702000c6030140c03001c5d43c03101d648a03103001000402e10040d008603510490005a0b0207427003017242c104000c400c0d40b048422030030700c10161504100600302404000c24910704c500448160300ea550501a00020b0200d803503500085d22602e2a02c103841c03414078203170a044400c445641416041c83d8084035003040360b20014144105145040c0f140c1421101192423002081c2c81040100d9101c1c100000ca40050361256 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 756118857 1250 756117607 756117643
    0x60901020c01180b0402010c08041203030e0d090e07050918090c12030304030504120204021c151a030c070c0e0c04052d0609040b19060f0c0b0406151502 67
    0x50188020001c914803c03041e440119070005889503001103801c10704280d02201c844404100c00f0035422160200c516080703200b036a000c84c000201e0000182402c0311504000107121401006004040c0046001c582c0440e091038080e031503100301000030300205940200c0c0c0f100c2c0501c0d6030510070152000b11b00c9000100d020b03100f446c44040c5d25054584e81c3d2004031005400603100348410f00440c035030000f07400a0700380000d1025003060700d6107008245000c1e5007036104602a0f42e8000c05812040c19040410061444030174042c20348244a0500314107200040100240a01c0045c60300108254900c445001d4008030f51208050314202841641c1d0703a00a0080c01e03c90b5213054100c041810090083d031240c100360468400b092003289081c4003198001c1c0c0140c5070301903240c80401540e84c45070b0881065a108054503400312628241c009055021282400005c1010380201017020031132101c095604598441c4000039048441d0340342e80d42d23001c49600112072220354404000c100550000700345514031105010 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 756120107 1250 756118857 756118871
    0x1502090d0c06021204030b130f0b100303030b030109030c06111908060301050109050106020d0e0a091806050c0f160c12051e0106150e0604030804030803040c1a09090711060901020c01 80
    0x550314130b90140c5d10000b84809071200000d0030592034002c00c60540b9114000c14400c5e40b0081d506c0542c2a402181c485241586c90002002419418042c20801c26410740c000c00291505440047c6483c10301c550103803d140d11140f1040085099508980c640d142140304000700d1404108020700143c2d064420901c01d41c01c000010a21680c9845510704882c861b03002800310750f00c4684162006101883c0c2c0e607603c000c0381c07000081e450060307005143d42002600c428a01034002c40c50f000301211009060306c5035603002480000411024001110503800e04810f039a6042d104c5880d00003900704140d0080130b0003400100903e420408001000d111040400c0034114001d00c00200540c200c1e01144600c1240d205140c05103e2181d000e400c604041501c05414249015101d0321401d80540c401d52080790701003000030801c4207110707825610794003800369a101071482010509180a442c010312807018804ca0403000800c117100d011308194103080101c2d40c151203031031a00981080c000e40150b00c841d080c950030101 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 756121357 1250 756120107 756120133
    0xc05120714030105060a0302100207030803090d02010f1104050120370c171c02070302011206050a2c0703230c0406110321071704050a1502090d0c0602 66
    0xc00c0d206100c0582545006ea00d95002c00c012420142c00e4881075010301107020020a848030f006511800c4d184d4002c02c0110700526000342110340d10002c5007030452900c61802c944a5880c001c44040b43c209180081e00d21448404400b00c1d14039194494046100340d41090000c0c030484826010413440600303c02d0300c3d840b801d424440460884920003800100049024040b0603040a64149040206002c80b600343e0b40e160010300d811010004928003682c0000407c104560740030301b4031220004168001c0c0b2601e85001301154002c21240100e41b4a010704800c5114015000840b0052080c010610002e1900706050050028101c1d4043e8003000003071030130303080124410516003038082c8081c074400e5031400345041c0c8121409185440804c034280000c000103503150024100c40041600c00351907240c1d29080c2000c001d082c080080c0400c1035044003407400c22020510108651544035040454015800300a01140009110b100392165105100402d00030a0102544e0103905540540d0222010418440 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 756122607 1250 756121357 756121361
    0x10219120806120a081b010e0703050105100b09010e12010f150801090201020a0803130803011d0615070b070e040609050604060e09062e0305030a0806150f03040c051207140301 77
    0x8020f0b410340e41c442021240080e4504c5e004040810803406001c1d030840000d00441e09581c2046051107203a0301c0450180140318080c820103070080b03580407044420601c1e001048084d40030341d07600c913070500c8902d01a40802e5100ca9100b0703412601041c0003000800b0f42c90202c0802000c0321000b075056403804210101340298144144108143c0580080181074525500c5d00501c0d40000e1404081110901d4194005080304010b140a0030702b140e2406030003102d0b40100da850034001440305c0e1040e5140d00341410740c850620301301d400c3e140c0c0001b241c00c403c2e615000140c41807100c030415a48c220303242040028040704154402e6000310011501401500e5407803400e0205090140c522044d507400c0500852040044103807408880002c802e8800c1041e40f00e500744010904056001b541c0c1ca8000007404400b482e0301011050340b1181c201e410802d03003400c00c01864081e000e00103905c1000540080441d0034055090503100003044010074030507a02d00e410320640e4031045940704000034606c030703110036941c18035042c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 756123857 1250 756122607 756122629
    0xc0612010b16120c05071a04030809060405090705070501051e0a0f0b03030408010b0f030d051207030b0d0b090d090b0301060f0207080a0c23060915090406140109061404060e010219120806 82
    0x1c01907e904207402c0d80c951070660340c4427084007a0f00103070810001544d44c950706805407055400d5161036131140c00a041880c296800200700b8003102d40c04003110120300800c414020b4214a025070001454410008400010003502c0d000c00d070b051002003000540312005400c820340c211f1094444c02d601a8030a4245940c07030000540c5140415414000000169007041455078001500d29012942d2540000402d4901c0260716003035401072000300c00c010505c4030401004211000c2c0b03103804a0440e250503001d0a0901041c0035240c10480200001d4101030320070040c03100a081500c2c00d0b20032090366881c6c07026045070a071154245c0c88051504841c1e05215240305c040c081c64001d0b002501d0144020108218800d00780b0962440a0042c001c100e055182e0b40314050140090381080a00c9101910024003602003e51014040104a400802c440402c00341510100d130060f0a108804000c00e00040c2c2c240345241c1c00d9a03000f13424150610080c041d0711411306001d2a501d450312540e03511000140400c520417 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 756125107 1250 756123857 756123899
    0x301080a02060708120408030103110904120e22060602070f080d03090f06050906060307050607050304050d1403070305041401031817040503030a09080c0612010b16120c0507 76
    0x40440000003605040000380f0506210721001c0340b4198030541070301c030503c0c800d41d41500c10301008001031082180049015900200c1114440000c0c5800d03075846882c40445e072918410003000078280240c9842d10400d420948000c49540d0f4560703000d000034a0000c0245101d80360052103032060010b01d0340c08540b1220103803419180501043c01c0d6801d0142c1c0508945802114114021145080800d6142c8100c900400600e80681140e00340401050710340105500250701c100d80801a410000b40d000048030100c0300d003501c0086083d182d40c1400300400c211140034400c2e0b0b0100148410401d40d1100051042c0c3d05080c1c8500a03a1040b14011030481d80c1001c0d0b105804184078418201003865038140d998116090000385103030070f48071004a420740d0084140d2201041541d242404102000d0060250410041d50042e00b00070b003081c903d0700f40c941c06104806480c0c0d00019060380e00c0c0041c4003086a03641c0c014210074103030300304100005c100502e2464195100d001e02d04005c2a94014406140c0301104 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 756126357 1250 756125107 756125113
    0x16080c0714030d0f022113060f051b010615090305070e040206030f0a0e0102040617220b130c03030c11030703032102253f050c150912030108 62
    0x1114400c113030b40380d080350501201507200b8040e0201608030030301c4501ca10126405402502c80300d0681a4289045681d0082000c0c4011107501d994010381c0401a1040c091101e20891949049240c0d901d0040040d03402940070f5034240a07403020400d03080001e29046034419800c45140b85e544801c14405650151402540300da0100702083c003880e00744404a401c4802e03001c00040d14003100081e2822030740b01d90301120201c0c100030520701c48c03007804c03210042e030040c07600c0c450704210454040c112441164098004111100001c04200c00f591200034142241c0d522189501c03440f61241400f03400040e04084c100c4110400f401d20040c01c1c140070900c40202ca80c9038030b40c44580c012007070300c0c89c82888000f6910594940d082c0002c402c65a0030149005140c0c1c2c1004214541040354106107400b081610300541c1c6454100c500d0541c1c1403028241c00b41e501210800404801005101c1200d031842070884214440c46290b505c8064040704901c401e0191070351400315030405a0740480203440e40070900c54013446070 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 756127607 1250 756126357 756126373
    0x1107120c080622031817100e0d050717030408030402041a010228170d050105031c03110d140910061d06030715050304020f0609030c1516080c071403 65
    0x407404068116214440d00303110710004000400080b8070076641e0302c400b01400c0b51b06909004040244003c001524440f03109000e03030140c103100b0a51703662000c840d00c0100b01002641780c060084a141001d422809001c0c100d959040074101508203400a480c26071265281c0409440c80c40c140d0f204c0800043e0060f00600500700342045001d00c00b41c4080103031450628000680000280c040d1801950401c20684a88d180d003410f94050007103480580006009a00400e0044d41c17030040e0030b441c1000380703480e03103808a0220103140c0e190131540200d003000301446041000201103a403501d10b9641c411130b6031134216884030091340c0641058449074840d20081d90307402c9c403d02040340c103401c80e8254450005002c0741c46096845072624010201e0901c1c405c005440802440118500181c0e02c81c096a0101c0e034403802d0848200000e074450444a1500e44580c25181c500b4000614920940d402c0d24080006944074a03064104000550300c061084821030060041c04100b8550008403400c0e02c80c4098020326582c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 756128857 1250 756127607 756127651
    0xb36010e06130221011521020a020c04020d0c0f08060609240c0604050f01060f050405070e060c01021803010207050c0d050c090705090316060203030a0207031107120c0806 75
    0x100c2c002c0c19010011603000c020100300e4140000207101c400b02c0d0700491101540c9405642c0c103203184102d00c0081041507288000640041d48000d590b2120414000166680c2d20140280e143c42d05401465400c41e00105403403503010303402e505c19014600e294032800d1900c954180211801e4100b200d43c1c59106109214001542c2407051125074200b40e0503d076468802c03000318507040a50030010704903406600100c01c01003007000901100706441d81003002880130906000074018981c80c02d00804c0d004a0795100087e03c0c081c41401d854440040141250359103e800d000d0b924041d40c04a184c070420300881100c0c040306c84c2070520851310a076030081c0107050324100740740c1000199103407a4025607003446203010104551f80c4031490940590943e45030309035203007001c4017450f080c18080082c0e1012100b9080c001c0100036008822640e104c00c50440060f0f488069280c140d603c2c0c00c2020016045204608011420150000058141b0b0f80608100518299141c8030f096071240112403a60600643c10040c51030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 756130107 1250 756128857 756128869
    0x6120e010e121602090411011d0a0918060c02010615020c060304081303080406050301031a04030f051b0111030105150a020a0201080a09050a0f060b100c02090403030b36010e06 77
    0x10b140d240c03e00c2a060248a0300015848501a5000d8034000305102c0340d074040350f030400604110704005900c080c501346036441c00909401b4051150741203854407855082c1d605950951045129a801241084007960100d0002d008010f24000c20b4454000880ea40900d2800016184c1c820b4500512852a69549985d4138415820a600c081d06540300c15001000241c445c4015002400a958881e40c981d0325508111114009a1403403100801106040c040401d5105201e80c030842c1180c07c2c0325a84407203446042c070111230225104c3d0311030f51034106842002c0d1030b0000194100c45085900a07116200c0c4440345440d4401d041c400009a44070712002c1c00103500030070a00c0da010082640000340c002c0d40d134039040e081c40301200040320b003d4070f031101c41030070002d05110391680d2444c04d035401000c20408000191a0328100f06020380318071901e00000d020544250409400c15502402c41545040040840014111180c1d904180304c042d916a0016105080c0190750480c0c444003008aa00d4441c9014484 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 756131357 1250 756130107 756130117
    0xf0601140919060f090b100c0b040b150402040905010302100201020f0a0f0917030a031b09140f03010c02150f1314120406170604020f07140a0c06120e010e12 69
    0xb0345500d07100300103684078501807020000c190030381c070200c2c3d02100070f03040201090070300003e442032109a03280d0001190039988080e510035880140e96001303440383d44141c800d212031000b0b120350140c00000c0c041604209500264100c0344281c500d4005103811004c01d90917405840e104425662061101900e001d104480d440c0500c0030034105501e03860388401100400980b40c403400358041c0e2000a004110541c90300ca0b4450101100d09804000081c01f42c006040c1600751044007440b150982e04c0e802140d0320507450742400d60000b40200440e2007560390194643d100d045020105416400004400450700c107050b5129503d00c0902d00440c0e00180d6400440b501c610384003d8841c03084180060b000c0da0040014000b07071402d0b84130b600502c100c6a2280a01500042c4803500036170060104100b80c004140565594581c4080759103000d000f1801c0040c90a11045000741504550032400500d464022400300c010911041060044400511402d82666465103064102e07500500c00380d2403008003440545 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 756132607 1250 756131357 756131401
    0x906010c1b08060a0b01020d09050a180609050403090612020403031707120e160f05030d03020c0f010f0c030f090308040b070203041e05010305060a12021011010203090f06011409 78
    0x361a82e4aa940c2c243c6401c8003102d5030400c05680300300c08030319580c040281000418951401100b0103003018040380d1400b03043c1c0700d0441c40c4000075455a25600b507980200c330203000c154500300300c01c0c5031a080007070444103039101c2c00001c1004407020340e001d10300f28000c803403c0d25055250368080c0c2c0e4010004a2540c940209440b0400c0300350b00602c03540e080c544c05601907618081c40103018a000c100503161021000e94048810b140c12400308200c1c9481c00f1401007a88052420010388565081e9002800e010640a19901c20b501e020903d26405141d50b112541750060b0390380410410486101c20700c22207030400c102070702084003d000500010741000304c00e80d00ca01c0c61700c1540d0038595a4402c2007002e000b246110b540100f031050050099581c03502c80c00d5800a022910b0700481840c3c0035403048003544504001e40914107040300e0303010072405210740440307910705403008540e64502070900603151401c55403440320a00030340c00006101c0d080480d0802c0880300c000e110752402d481d144d9100e002d01282c40080 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 756133857 1250 756132607 756132653
    0x111912050c0715051207030e0c03010e060606030c07020a0b040608060406081e030c0f07080d09051e0a2111010e1003091110090e010f0308180d0605130c050906010c 72
    0x14130301c011136041b4040c1c515500c001c548c0403608880f4500307001c6800c10240c0aa0f1400c810b0503e8183c0010b032568104105480da00e6032a1184140c5e40c10038801c0b0100a0b4104020010008903900c89038000e1003100c100341c3d2402c0c03442d21348204110039180300f4400c1501c940d0184400350400c401440040029622103011680b401000804843c18001c0024004007190401c000070044040c05002e22080140075180c078020043c10f000000d420031800c55003a000752421038544502a40700c054102c0081c08505410111000b03a00c0b0f10082d03026030b000e8003202c504014800c05801540500c002842c400070040c6031701c5403050003030b00441c001c280c000c81c1030342d688807100c0e100343c61500c80f0304c0a10a242c40940e01c044003141403040c500103065042e84048188402c1482c10000310f0003042c2501c9508405400821800d445079002508003c1c500030701928061405081c89072001c40313484000c6201c1e104484460b201546d843c20824400d07001ca442e1804640044044c20006150304130000045c00e0780504 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 756135107 1250 756133857 756133867
    0x601030b030106080c04050c0c070b131d06041a1c050a08070f1b030c0504022a0c0f0d0c0905070c050a0b061e0a03060c111912050c071505 61
    0x2820f41e01954841101da0b0841e440400180c02d1600800707500ca040b002d1141d2802d480c400d0304980d25a41442036103010000450380c405100d144891140003040300340c98490000c0b0f4440c18003080d0351025a5070758130440c58424883c1c9580540c013001000098010840b14095a19414144925065010484550080c40c5d91a000102c0c03140107081041d00030680f0b42c510340d180b441c2c0b00568160035505909406c103026001c02c0013444c0031600320142c641c2981e000d620784405051104031400d880c10f4158000030b58000002c0300030320000c0c00c1a094401103c09a900d0f03071070941889200001c01401400320781d0a982d040c8041c010541003103400003100c1c0340015000b0725503100d650620345410301c125a0a800f280034400c46103032840b1b08001ca01d45109400c07e00d0900000081d11462051000400745a103c1c0c2c545032003c0d016426202d04c0d0402c05059130315040041c90074020424051030b00316019442d2a9000600ca0f00c140155581d0b8120307800181112418080e21140c4140c03055141e60800a040003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 756136357 1250 756135107 756135109
    0x6060603070210021606060b03040c0b0906070f0311010c0e1c081e0c01060f05010f0c023f030c0717011e1506110a02042a0801090f090c0e0601030b 65
    0x2000301402e180030490416040c11703a00d0310b4419220a54004010590140140300104001c2d0b04490111880300740c12503540d91203200854039070700540710041c280c003544000300e409254208085940095444000300320111b800035081e1480000040d0b07054107c51035809821100142e000ca5040d858011615141440c4d80300c03100410302c04040002400158000c1a100303000b100c01d0180002401203940042d20b42030400f4002070003001824505030401600030801004e42d01c5244275410341d81c80201c0841b4071004042484452044030180241e80050184115101c00002200b034a9101143d00003900469152841405600501005207022550f1b03804868205000511107810b206030220000301d1001000d032100f05d5903e156501001c207002200055100358200403034144074155041fa000964000c0d00a940e071000c007030540d10728a01c0300b48a031781010a507402c216100c0c100c4104007002d000e9401259004402c0d81d6075607070002c0410145810038410221000b40595103e0018500058544a400 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 756137607 1250 756136357 756136361
    0x3090f06130f170a0c03120c0807181a09090901200c0106050402070c0e0714030615070f06020c1e0a080309190323040506030c03060d05030a170109050906060603070210 74
    0x1040c0a004a4101c0c1d800c2410150071034804480b040110341c0c10031068640410141140000400d158208103820190811483d107084200020b0301d90707070503160b03100c0c642e501100033070340e110003c5a172080d0101c000040c1000014042e40b1000180c10864086841502c91141890b41018142e407616540301c000205684d2514405001c0b49070042d12030b0034000d841c0010100c920000500340d00304004084c11030340112813901c000c4a40024083c3c1e0b5602e0701041c2419030b1a854003a81b040144918400c40c2c08405100d80c43d0054010740750f040054412080419000d41d1403110210000101c54100040324008581c0102c05958007422010643d1800d42d1a25070403014540c01d00d00c02ca01150036641c00d05042c0d00f01d0b0381924041e10606049038a01070520000402c82e01005162003500100040010007034ac039079030701e004d00e4640e00400700d079240c45c0996000341a50651100c1c0c3d40c204c00c0e8090000403174060a00440c3d009850040241481d030301e4220034092194070040004096110b220034804021101d4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 756138857 1250 756137607 756137617
    0x30403051c170f0a11160210090305030403083a05060d050a030f230d05041704120605070e1011030903070303051b070e070c060f050c03090f06130f17 66
    0x541c010701c4902e4003500b90011261790b00114440380364148103685842c68010082078179113404448266000800900450760b65140d0341001300103000210b800403c1114010141003400d0718404010b4040d030100b02986105100c1c01d1014a2070301400c038032140b0b00e0380164441a0048005400108054000d17120189480907115088002607e603074551440d5580c05501c2d408818024540c141c18440a040e002e0454000d55108072443c0381d66002041c10800d501000d0100300124001c0c2c2c0ea2220364039000b032180c405540c0d00a648080c01c01000840b118032901d86100049001001c11408003500f0300200c89a125850031010a4441080400c19039079080140a000b58800d65034940c2e1102519001c0c401c8103400d0703071b048800358440c8405020900701480d0785503214215207440c1c5540200c80c14120050a411011001c82030300c1c2c08280028811190021403042c818101160b41c0d400307440e041c0341d0352410f00302c580050318102c1c68000b100041c103842000c810340c0d00408225030140d894428604995002d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 756140107 1250 756138857 756138871
    0xe0c0d020f120703061a03090709050c0c010b0402030105181008011b031b1e020304051008041a04020922080d09120302070c06030b0301021e1803030403051c17 70
    0x1000c56103118002d4a810b80541c0201c4a00d024404d0a1a26100c62645a011588402c403500044005012440108800c1d4001d0089010511060410b05d40c000c00350351040054a9140d4240300c09400c003401c0074000c60b030407120083d104502810f0b86403407000c00d54001508407000f040d010f2000281042c001d008000034280004900d8801c0c52002001608a03119105021049030105c0702c292403103a000f00701380d190039042b030f110740f55180107041d0b0480c158426900429400304885081c1091154403c200c54070431441400c650f600805450027031400c00d001120000c0d48010302c0700014426a2604007e200c4039225200009100040c607914a0200d401ca482c459402a0b6200d50442c00d00520700b440c1102d4082d541030840c030384009500c0303810355041c40d400b44c842810780390f424212040d1400d5044a19104c00b0b6540c0c4140e03c408100030b4090b83e485100390714054000111000c21a18000c4112402c699010000b440c80c003601c03d0740014540c51110b40c102c184402100c010020f12030206401d48100c3c2 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 756141357 1250 756140107 756140137
    0x1e07050307061e0b0d0f061812030501061101090c03030e0d02040e03030703111201120f02130605041b050405100318060912030c020c13022a0d050708040e0c0d02 71
    0x100d03030f443c0d00742201e0035400014451200101c0c0740001c03410043c40b5040e034580010000c24220700600a4404c0c0d40d200d8000109109000f443c2d0042090381036004a0684010356104c2c2c2c05050741480950980d0500640030301088001907082000a00031030a200f00898087d2501d40c40ca452a000501260010840c150140d0000410030050707640c58840e40350300301000d40500c1d0400300c51020400a1542c1400390350f24010140400009008014140c100050ba00500f44090390150000100c090846803284078090f5090194844240002403c0ca01010040750fa030142403a1500e000c002d1088011810301c0d041c1030752881a480b0b00081d2116501c19240215404280340049142c4082d0403c07450580d00d04161401c5109030790954086032002140e0002c5894011155204140c80e009105030040182c0404550303000314992900341c0b0080500b0755803101034420003218410180c42500c101c21009000440800090003034a0000318680d4101e940140c0302d6080c10400f0380341c00201e034010b00650110340 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 756142607 1250 756141357 756141401
    0x10b07031d0105430c0f0315150b03091005090609030711060708070f03090b0310120303150f03020a0e0c030610271e1a0d1b050912031e0705030706 65
    0x1200e8800c54000429070f9101000c035076881c5072182c00e0923181001d0025001e81e140d50442400450303890000000d0300c1d0300101243c0d2828000c02040e59140b0000100c102182001c00103840d8142c0842d500e842800035401652510f80c881e902c040d00300d0b03004403165500090501045000c11200f07000f80500c2c13407295002c20b43c03020080c10040c10380b060a038026181c0c0e081c2081048441c0300101c0c80d00d011a06031146002e001c266920f41600a40f80c401c2450400c0e80940b58000b03161075400782054100c0303000f81c40d80c0b40c0c01503c541c13900788042402c031803030740062604002103400c606044c8800c0040d50b015190800b1209028003034201e11070541990404190f02c04041403000004144084c00700840c03c0029403000703440c20f040355401030f40c1112005848440410541040b0403643c0010002c251300d0b01d0324100d4070b800700c0c03005040c5e904042d20090280110f0040b410b4a108004200e900001e0780070711150040c88081c01c00d46e055401003604903007900003404548001101c4d0f01032000100c003030481c403201c90 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 756143857 1250 756142607 756142613
    0x51005010e0a02030403092c04080a0908160512150f060108011d150f031c030e15010e0406021b0c011101090830010b07031d010543 58
    0xc1d22018200030b0642e4410020321000036000800203049803c62011b20444214184440d0504113204d9071015500001004010405c40644010811401280c449080e020386540c0a0740c0e503201b00c0c1040d00000035494405001c2490f02c50306510389401120125007081504080c0704201c40d2082d96031000e02071108080c4440e40da001190980504480c8030105840d030144000b8000080000d41441000d46050600c1c0c1201e444050084100c0311010b401c8850107441441100c60214081a40500091914160704408100031521812502240301d40c0c124603420950303903c0100350040c00440c0c000f582008040500300b00c0000703551030989034a01811414240341e0001d4440800c840b0220b405901d803da20000190b00082070f03550745e6921121041c0c00700282e811000041c40030b40280390390054038600000d4686040d02c0100419440f03a40d51484c08940c038030180503403d540362982c50210364140103c030980c014641c000400701940d03400d20044280d030303040c2c21411110080c3d05a52013044100e0000c080c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 756145107 1250 756143857 756143879
    0x4120609021c02031b01050f070803040c0e04080304060c020a0218040c060908100b030f060c07170715090510050106090e1503060c0a0c0c0902091002010902130e070305100501 77
    0x14000140c45000a081d001c2c2e4006611440000b85da50301400030007801e0305050340b01e4010f40c3d01c0100234001407540e034280380c01c1c80c02c10340c0c004480440d181e101c40b006c0400d0388032442c00e80786d01860b841850182962207550b50000641030040d440c4007107116402c2504007581d1040840c028090800c02c06c0040340c00c0504007018026841d4003d4ac0502503441d4003000000d900107a00f09925101040c006101c98110000906040003104800400d109207410701281806072001400554031401122034030008a0a5881c0e550240c2800034019121003060302580503450f400403010503200d0004d030360603101401c00010440300e081e003001000a000d040180800580f80c0030140c0c0046240020781a01c202403c0000d6852100500fa422072290205950009e07078054408190b02d19401443c2156054036801c0d400000e42240c01520301c501107054180c0456401849411041500945102d080940c08281080079104002c42408540300f050310020114406000701d04540710309020108a40d45001e00e00c210b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 756146357 1250 756145107 756145129
    0x120c06130e090604150c05190302120114090a090f14061801060510050f13060e040f0e0d08090a0804080c01080105011103071b0b0304030c0210020c0105070809060412060902 76
    0x24250744000d06000100c0c17010322202034584110b030404940300004d180200c07400d000b0108940d5448a004044019030b40e015005061030b81034181e103c41050783e0f504000c0300984208660240c0000c80300d8041040482603802c001c0e000c3d400b5088040b200007880e030710120310141940c100300c2a50004030600401110300e480c0b000c000d0b0031000003400000d040500040200c1e0094080b2024040c000030900960144901503d00425038000110720b0f55030340d000040e21a452030440c0038030031480c01c1e01c0000180007a06c0b80d6204800c2030300c02400b01c107000340800c2e1108807024008450a124800c0d840c000a08060018000303060b180015084559082e40050080c0b98180c008605104204a00800405c000004d441d070351034001111300c80f1940107041085001c1030a17000144c0c1108000100300c10b154220025603002c5100761601c5645000291007241c5034040c00e201c1030b001503420499500807803000c00c00f804e69000020038907407810360342d0b035000002c1c00c040d50f604076035407078030f81544809510341204544 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 756147607 1250 756146357 756146371
    0x6020f043f0c090218061206130c080a05100807270b030a1e0f0b0402090702160b1308150a0c030b1309062c0705120c120c06130e 57
    0x203050360955a0340003400829809555145a40440d451110726105c4103e01d20201000d025207580300303e8500030f860021001c507001c074049d81910001d2205040b0790710409808091981c1c4500b01505d415145201030701014040c0700003403003441c0012a0401080c81882e00410494a82414a018a002e5141d14000105074000c14602c2c0208100b510b0300c000c5034514446610050303103d8090002d030114103910140c188050030401000c401c01040094490602d80524022070304088681da0740042269034070b0359035240281022820303500b007100c0b582002c050040001184520410fa075141d204141c0361501d030703071100c0741443e605074248a00801e40d8401c4444c8a502c80c6001e1000025400101d0340c100c403815941d41c40070f0354601c180c0c018056207500680548101500090401c4400302c084110030408180e0f032101c900032000001031500d0041000903448015201401c01c540c111800c11030380b40f6600c81c20800d0782c0505042c100c00c0d0303a214802000e4403802d6070243c2d50903c4c2000c018a2040780014a95 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 756148857 1250 756147607 756147719
    0x503120a030516051903150f140307082812030501050112090c06141303050c01020d08040f170409092001181e1e06080c040b03010306020f04 62
    0x40f243c0c155111085134011000705010032203003030604404500500f1140c024211484031602e01040c003407241641d42d401c845801c45100d840d10305250030035440e51071038803c0390070641c0014084544141b4490055404412421048250040e2903d0340b0320250b111054030000a0ba5030703c0148070560304003070803c0201604560410000400b03941d0040c4c4017005014401c203000c0210402c04400c030340e0900b01c0d4400f03100b040303140e2080c07662450310a40e10410b1000c0540903024541f118281d06108100f00d501c103030b40100210981c0c0c0c2e42038403030204600c00c0c0b00064002070740070403021400341c0c4c290007000003040c89803102054047e0030102c800c6004800112807410003000070100c928003240ca4503005c0c00c2e52010303203c02081e00082c001201c00c00d20a9031194441d001010041c0781c4c42a2003102080848e003d98843e140e8a0781c8001d140341d01d9210f540103548014805100600c04918254003400d0380b691102c84042c40d142d25189405c6606208a01c0000c14040302c40440f550030000c0a14140240002c2d914 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 756150107 1250 756148857 756148891
    0x6090602030f0d0608100f1d0c130b0a0605040609150e0114041206090c0605120c0c07050627040b0102070306240f1401021504020d020a0503120a0305 66
    0x200a48070b100d42101940c1004000c50001e03800042036101c88000d04440701121103030004081244040c14a0380703001407805150031300c118004070428450011224171240548404500e01e400c20050102c80602c410103990341d101a90034580364200e0031000b400b09a10b078a07480701c2c580705000748041446e81000d40308408168021407050b0700602e14101441c4242071500240c0c01d100850b005900640e485400308800442d5004240800c541c000300f02c903801802c4980c80e858440174140c800744613100444020141c1c0030005528040548040c000040c910000e4408072030b07803180000c80c1c41c1c203e0341002400490318440c10319140030341c0c0c1c880041e40d4000c0c1c4080c44a0580040080d48980340303403101030149038070350301c4501015410f840a003030340c00e0b4401c00c0703200c400c0d07124942740403d68068000c601e03e076610040c00d4006076000080350000f001404a641e00165500d60a001c2c24114500080343c100282ca0740100307860340c003480080c400d0103403040941e40744c455028005040d1030740548220f00d96401e901e0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 756151357 1250 756150107 756150119
    0x8060114040c0c020918010c0e120607051c0f050c12060415090e01021c1d0303010f0b07051504050d09050904020d062d020703030b0103150e15030102070b100609 71
    0x2c0110184d01114000b01d9903031104003000c062800c608141c15154606a40d1f40c01d4160442c100f03200b03400050310a2800707503650880c100e81c1d482c01500d22601043c0107015000408114019900c1c007100c4046010901c0c141c610306900030750310103072910b5508000c04100e201c0c0f81c000307044203a40e014500b100c0a0201d1040c0c610581d120611600850100b03075101c0c1d0152505000c01d40486003c141d1300f01612400c0b06540c0302c502c3c01841c400d051002e010801720f65a074811070300001524161400455580f0440b8504184402a43d0091008507010300440801030048000c10486505c01d13030042c0064a143d1003601c10040c414200b0384c2001c0c0c811046401400701580b0303421245098a170303003e2000100d820084041c01804c200c1c1c01800c0317400c0110a1b48bc02202d0300b447d005808064442d44090020918600040d4151001c5150740d0084000451080000820041500e07402681c4030b140380042d000c12502007426030303004039007d5a140c1d4120050050301d12421842c040105010b02e0032a1000b41018 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 756152607 1250 756151357 756151367
    0x1502190303091419030509030f06040b0105030d0906052b0519050106021b040c0324060905040506010f08070302041a0403020f0301052a040f060f180612020d02090a08060114040c 78
    0x400c4c054100b00f40804c6400c0152402c0054542c9000d89100701c2c2d40610706454102c42e0200240a801d0082c01030b64180b5040e0350181409000340e41c4581c407810304106400b80303261400000f256007000001520300b0506201d80162050601030041d42020083c03050003256a032080d078606074401011076001c6040c89a040c48142560940b140085402040340c2940071002c402801c0f58202221800b00c1c0d03048121001200c58081c00100d0f1500c0d1520003181d0750703e00801c03040722012118580800c2d00060040042403283d4440c035440525820014101070301c1c2d0403110001d001003003104500304000a814400d615202000c07071840e01c0d04070024025480c03c0d0900600c0a4403401c003a060795030202805402d09021001558054070041c01c41d0310380c43e640d8030b10041410b00f4910070400441c0008815083c0c129000c1c01c140c1c2030303400341c0e2118802c9114120301c00300258401014404090360901ca86020b5a42e644000c4000b403090200810f41c0354103020140c3c411400a1002034451498110072502e280d8100d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 756153857 1250 756152607 756152653
    0xc0308040608061921050a1a090c010801030b04062f041703130512010204151d010e030304061d100c02010216050a0501080a14090d0e03120415021903030914 69
    0x24003c00c031740425030351400601d031135030625000700000240b49404500100101c2c5d09403003801680d00310341c103c031400f00040d22804400c1c0405014403010b00002000716180ea0402040e0703207026030321381c154102d060480b6004240320242c1c10340600c84c0003e040000b040c3c01021101e0144030000550b2510710202ca8400c1e03203500301d00c0340c9809840070004002c500c1c4070a5056400400714030680e96942101000c0082400e044103443c594020380c510032100d031651140d00140c8046002400440ca41420b10409450b03040b288111507125003c008042c41c465100d40020649818013900c4890122070703144000790500c0c0032040006200c443c0c1740e80410080d5500c1030324000322102800c00f01011388560041d000501442d01d180c2c0d00040340c0c107040c806410400543c0c10120703003099480710717070380080302c0c08054842280005030400540c00b404240055074020f0b000005900c203e00440355507446c40410440c05c080501c4048c5e001c2680c030500340c810f00034100394a114411651000e0300c1e4a0503442003000c1980a0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 756155107 1250 756153857 756153899
    0x1701020c0a1103160902131401080a02160f05030c190305040b1602062d070b01030212030c060a0b031b090f060112060902030a1103100e040c03080406080619 69
    0xa50b482a80d10b4605209105108001d1645400d4450b240c00ca148043e51180d0301c007000122040317400242004810707200b5000307030905039504080e070b840e9040032074080c5d00301e07600780c0b43c100340310f4850b180018500e4008842111301c504042c503141c42d4007440545c104400c95891403450209580e00d240003070350000c02c46080d9107030160100e0b11340401030030000e941c100da080e000350448400502020a40819500b510485000880b0604044401090180140a08000100f564071918014001490076403850100411003074112824030a40c06246464030b4000d603001c1408540d03420f400001c034101405001ca03c540860140c00c1540070020100749011401041071410380710303400c00b0441c280e20529501c04090081c900501219031a00b0820b8025841920b1440d1200e1500000d07034659092001030340d00c41d1048007117200c1c0c080e24044860b40420401402240d40303640000340800060324500c0500080c20160383c0d950924500a0140308182e042301180c03203540d0038ac1794004c00080c500311600c0c40140030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 756156357 1250 756155107 756155123
    0x29070206010b0307200a1101031a09060409020402130f0b0307120c03060b0a0306080c0a0e04080c0f03040e180114010b07031b050c01080c070302071a0c0d05041701020c0a 75
    0x10302c0034001c071a100c403500045c1a4014109010010710b06002444880e90380c065645113140c50313480401507040304c5520949410000745001000700307a02d403400301340382d20050162012415a91650004003280d0181c640034101c151842e000340040d241041485000d0001c550200d899400c02e510064145503c040403140200e80f40c441100d0683d1080e001f07003000300b645100c1652a01364100026015010a00401417144290700200403280b81511122080381c109081c2a481030312987c99242442c0d200d540460840e00c42c118241103161800c0004000900880c0c0305400c0d10304105000c1210348070907020079140c0d40e04013400360082e0286030b071420341110304241420756103403118903040d2041d86042c014050b954003072040140c01d1240104080c0b03800e090998406c0c000c0d50721030140850b00d0080d064003800680c04501c00703019400072681103004200c4240e80207400d220ba03c0844034034001d08100070800148012408024450a406c007544c0200130900080d820110b5a0400c65078810452201030070f101 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 756157607 1250 756156357 756156361
    0x11812170406050a1401030605011701050c120c0f0c0303060a080319030b0a080102040311040c0212160201120c02010f110403110d030302120c18090c0a030b040b0d29070206010b03 79
    0x5403580e41300408440d0b0801e1705000c0c96a69051000c0100b00900c14107200c44044140c0221105c418481c06109891240c1c405040820200408500c2c0000414803200d82204100d200d0b425014103014100310001075001703685d44d203411000d00c40350a000c0e80c09900c00b0382c0140981c44114440c411269003000440c0b8000401a00c901d0008040d8142c3c0c1d4001034255200042c0031081c0400040c51180c040820340b000d0001540c51f04003283d0b9242d60400d5401511070901a0004045800c000b0501441c01498002035800503c0424401c0721040300c03c41c00035031b40d651201e0548039000c0c021200000d410303c64081c201460358440325200710256800510448004000004143c025419510203005c4080342c0091450001c04c52200790b44107245a520300c0d007035000c1140640c6030070782c0d400c0c2c030440302309101e82d0038040402c0b429400780524845203584683c58081690305502ca41c0700400350140602096100d144906030084031640b108000010107809850800640a400152031411286040300c1d140c0c1da5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 756158857 1250 756157607 756157621
    0x103060e0a0908250203010e0c06120604020708040b030708010b090303041a0c070f0314280215180f0a060203030f040f240e0c100f090801181217040605 67
    0xa4131030f042104403a040110156070f6407007041451110001d100b500200b01000d0703807100560356815050b45a5500890400110302c4281103410007a03004a0060005424410036941d412040d80080d0002404414040200000c1a900035421070040031212034644c6001d4900c0701080d00ea2040b40100307100c026103e0001c0b2001451402216001800d407819510403941741c44003c11410640e20042d40c0780c030304442c80703400102c6e00459203000c03802000500140d8010302d6504150407100420042c0e034443c540e00c040c5101c80309000000c16801e401c0340c0ca0038008031481401c000a5140c0700030b8060144980d20018401c040e000030840c1c0d0010200f604a19440d40e4614007540c5040402200a26449007240c0010240c91400d507111514103640f4000d101c40904050800e40d80c22154003045d030f002c5404411914118007859400c44544035900d4810340f03054a54141c0c6003590120103000c1c1d81c99810603244002d01c215101480150080342c5080614204104040048124050000341166903a0800b10320700c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 756160107 1250 756158857 756158873
    0x1b0b16020d08044d010908030c0601060e010507021011010f18110a0308180103110702010906270e10080604110114121302030727020705010e1c0e0103060e0a09 70
    0x55184131403240c454610a900f11248000440080d07980480c851032004501c1300c4c004001d54112426400092040d41e192080444806286044143c1440420826400175855158606d445000680c4540440c01d40c01e01d080c40c00c484800c8100310034071b403414092402005101c070101c90f110703400100303807038070800e0a1001580c0304820780c4c8010711842c400a040101302c88140840a83d0780000d0700c080200803211143d100c1140718540703009001904120060003141e028104e0510f00c082007280001da61815014007041200c0903420552401e13110320104580410045220005030004101825840c14655a52120503d40c407400754103000e0300c414410720b40d07000d040075954483c001c100d030322940b4200380100d1101561001c009900074011550041442d0000898181d2050205c110320b8400340c1c00807442100075040490110f40554032004d4000e046070040001c1900040d2502c015001080709020150031807000007c2241403604162040242c40410180144d01c40d036500e2001c207956040d440c02080c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 756161357 1250 756160107 756160193
    0x19020106080d0c05101109040f1b090302270705030702010f0603150605090106050906070501020c0f060a1b050403060e0109080d0212010e161b0b16020d0804 69
    0x440c071a403055a0000d0b50301c900c00b41001400340c02681c0510301801102ea090f0382030080c00b03060306c0c41c00300410702090500ea80720701000340300154001180c00c695585041c0800d00911044001070301e2000501c15803a10030450448003410f03c1036085400b501250313000307106000503c0c4005100b030101c0058190350003074000079034420441c20100409501d07403404900005440314103c0c6c01c03914044001c242820201c1d8024140c61490b01c8050030a51036038100240f540c003070001144c0ea0b540900041a060204101c1d030040840403801601d060315040f00d90300300311040c8150a164200540c041a00c0158000d0100c80590782c100130045004038008100a0140c40034400042011000068480c0c14081580c003812002d4080da841403011f9030b071004070080c808070a8520885481d1a1030b02c60000034007a0202c18111980888a400d031041e407906c0f4400c401c00f0444454014055841e48141440d07414865683c0004c03d0f0b0030040300f542419102d07034800c00000490078401c1400400080c11500404003000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 756162607 1250 756161357 756161369
    0x507030f0303060602060a0e071e121406070504030b04030804081b0304090605061804051803041d130c030b33180411040902130c0905120304080319020106 68
    0xd0091000d1900400400451041d540140540300c04140240d402c2c1c000c00c4083c1d01d4000081501c281064403c8600f51460515030314408000000001c0d0f003102007820303505545c0964060481110300020b1203042000c001d00260401030200010700005954a04c16030300030740c252901209560765850728126910074003904854600b07120b106005000f0b0000b004106590001c0814400682d407070090003101d0182080c900c1407a0060044141705003001ea101d9a44002d0700388101c2420014140041c1c207540c4550482038030350028500481014500b000b642c0e4104540340f044138020401500d501015841501008296481c620003041d00380510003180e081c44280f11010071b40c1d1000003901f0b00111116140441d0103000c1301e83c4410b0001441d00c80080c4240d0f00f00e041000741c014400d01b0000100102c8604076404142000510141e014a20580885a5054a034a00c02e281010100421000030a030072401a0f842000107200d43c09010041c4d40818100084000154502ca20164003500c1a60451 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 756163857 1250 756162607 756162623
    0xe030a0e2b03270501091217130308030a0207031d0108070309020604080f07080106060201050f0a020d1b080f0a021804090204060503120301030605060105040311010c2d0606051c020904050703 84
    0x2981c0c0d00f140405000c411118242c880207101d5503909002c89402046005c003a01c9040e0840e22406c598441d10003c22a4401503080c0384196034403a9180026908150752503000f950380400c020041580081240f582030062024040d0000310000c0000c0414400418100400d070f11240703020115210802942c02401a900940b0743c0960b44003c4195181d0280c8121100340d82031020001d069401841a1405402021035140e00b076900c01c440840a03600c0381d0034024a240d60b480341c101c2d0248010b099400c805185964000c210b0070314007507604c0d03500400307030000c100c4a104000c100d565050311800300d02c541c801030341c02103180c040c58000a00146900d070f1261f03416008002000c072550748040020f6043c0e03486a04200020380791800112a5406140002003240300c002450821075809000700610b400e208101090715400003900011010611050b01d03070a00c01c100d580c407001c1168500422002d410180e44080e10240104008483c40000d0701c0f019000d203920401150611005001003070285410141d0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 756165107 1250 756163857 756163907
    0xa031211060702010b010201110304051e120f0703230301140a0e04050c0102160e01090522140c0603041104020c030c0a29091c09030203010e030a0e2b03 67
    0x4064041c2005c01082401540b9002c1d480031040900070a890080e9004002000340700500c030074160442c0f07110041d4454600c205c030030300000c021440c001040c0b0604050200c070b45540304d40c40c000d00301c60500903066041b038800084142500d590442502c1c1101c4402c854200c4900000340410811511078124502190080382040103006000400e48026031003a0300300c0d5500404c100700502d400d8401e004213500300c0d180300010400301c00f1613008244c00000349802d40703482c504402c008070300c194200e2004442c54003164a80320800c203c14403150104000689941d4075503e42a41c0f10314000983e03003425031140b036011412940405041041d079666021500807a420b0001d2070030303c4003803a554020000d6030100b0a04000346070080c80940d60303020700074400040003a02012000c1ca0200314040720281d0070811126400009a07809000b42c0f02c0f0f450141000c0d540d41c000a4030000c110900b031288403406040d52543c0048070a011002000c03131000440c0e101c9007400140d1408486020b181c40200741b0180c02d031b601e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 756166357 1250 756165107 756165121
    0x9061201050c13080706050304030311090301140109061a040911190305090d03020f03070c02150f030103141f0b01170a1b031107020d0c05040908031902090a03121106 73
    0x10040c09142c445100f114960342d51100705a030345581a0065100054042c00840c00180c0681c1008000e5030001c0340070f5003031030903000c040790844403600c0200c54104906d078010082d0032810310440e4098001d0403560707644124030040700000c5114510500690b42c6d5550220703110b5a502d00300791040e1088401c400320748040c1d000300c000d01500003659800050300808000400c0507002c0c2c403c4540d24444080d00900b1344d6519801134540304e1011300d003640c01c00920420058147c810320018020240c0b202c60305500c0c0c0d411030a0038150441841c2a824480d8412028442101c081100e11800140315a50204000700003000484174013100e500004080070f4182d0a016030088250800312601e01c640a40303c00012087c1001c8065840841022440d140204888409030070a107500c2a801c2d07014010203c0c0490b40c5a010608131080600180c52281e00402445800071407801090400c00182c07006606004441000079031800c910310005041d10400f80700016024002d89280d03010b03001500c1940d050380782450f = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 756167607 1250 756166357 756166381
    0xf06010c0807020a2706050a14130609020c0f06090a02030601270606030b01030c230a11060a1506020307080a12090c23040203130b0c13031118090c0906120105 70
    0x1041c400c109806c0450104642c14002900e038101c540355005401c1450100c0c05101441d001101d8103040700d5203031880420045c8450000b44040d1002500510500c00c1c0a040141400c0d8050443d020325081074010a0240e80c0c00a00541954808035140c2c1c406014180d16020303810a80d608a02c2003414118009605a0141d20a406442c1d080c0c80c01d01c02d25030b0f030850440b0350381440320302c00001f60b000c01814001c1d2070381307540500101041d50600035582c185052040f0700d0000304640d440d001d240c03154002c0b004400c3c2c2c0c10071800181303d180025410b01500c0c0d03039042101e02490740da0108104084991051040c0707280c01c0b0300e4100f0b400055284040b92a880c2020b050010b013841d0101e503405444140000b41070500c02c881c404e148110300b1018600305640c030540400c1024001c0720001400b4007000b56090074005840d4000c43c803641c44011080100814400d080d5000302413401d2200b4207200b0400300410100300a003d2a508440302052503850350009001a4010503100320340d580b8150800103191040 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 756168857 1250 756167607 756167669
    0x50d0210050c09031b011206030c170715180e090f0c010e011e05040e010e040201030c050c031b0f010911130c140a05120a02070b0f06010c0807020a 65
    0x280000d1101d076448200c1c5060038814410b0031500750f884004000e1100ea54500081902c0e401407401108100003a004841519081d03001940c4001915004000d0408401c02d0070160342260805080c1c1107142003044000d032482100703540c05102c0c02d000f00d94020070410340d041028002114a0b100a81000003000c7c1d0307110070f8014511114800c40d91405d060358014000c3d545880016902d9200e207529400c80506402c0e800b10301c500078014184800f00d40e80843c00e010a02901022541070300c1480c241c0001402d131050040c9800500a080050421a182c0032089481b1884d0781c03500220f103202c001403241e141c0341405151103459464070601a0400c110b00c190450894000ca50880c020f24015803590101c6101c0300d0700f1408031f00180c1000e060544c04070040c1079020403a04200382170054080c0a030002d80c000302d5207094203950000d000d40402440307500c0700743c228806020307003003d038504000081d00f4900200b6001d00104404110401103554006610b40600701029a0380410520a5031001884481d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 756170107 1250 756168857 756168883
    0x6031e09060c0f090f03060906022503120504020a03020f12030a02030d050f07020607180f03080c101505120307020613050916020304090c12091101120911011b050d02 73
    0x2100f04a4095106459090589407a00008002c4901d50303511540200001c0d80c4c11141241c0074003044180b04c000c0c1c1d00325080da0410b400500c980a4071490010140d40d51002c0d400c1016141000344005030300c803c0e0442c0b007030703a0303044c0d402071403900d051000118040355850040140d44030000d42c5090140e40800900710342c00c2201c1061140b5181c10904110804013102ca0b000182c1c041c0000402092107250454010542088840311150301c840c201c01704503115400c19210090005062541c49404200c58101005c00300010080044421621a4031a40b03034030030103101d084d450a100041000c240122600250700070107090780c1e40420440c407905c1200f50b205182c440c2c450000001e02605a1502501040d005035015500d043d00f805102c20081410021140c00c0100306a028401d0a24034480c00840d1030040780c2c028000b0f2407035400144060440001c4040326420401d03140c0010365074010182d500f000074244685110f100440f07450300d6a9100c440602548102401c6541454020a84c240c0e246c02d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 756171357 1250 756170107 756170117
    0x308180102011a0d0c0b0d020a0908010c020a11060f0c0c01030b1206060405152101050109020f040909030e031501081002161103071a18010e0a06031e09060c 69
    0x1810059003202c2d00440000080c01200790040803a180c103500e043c803510f00c604164940389448001c0c80c401600710324400e001280d40050941c0b1400c1c3c10029010042410400a204203001450001e450742c0307070356000409610740d5500c0c80c046555030100707031070305005011700294607103640d401400d9564944803805400f00e03140c9404102c0504020300448078020802e00209095200e50080c4002041c0080156140d188900c0c00c020031603030344002c400941c000c1d0380644041844030f480c94508444060b449803417801c0c810091403200c1c00516040c0d40c01c40c0c070440b10010784e08405040665410014002c1683c1c903001304840070104400902105040c1d0305104201c406260384881c541c01240f0454008095400b0083d0444000560710444620861409403e49600382d64890840c0180c1040714030041d10010041640701e81c02c03040b140a00e030036030000d10307222207040b81a10200e00041c0d05802140209074940c102c1e92905041c52540e0042a92002c0c0c040101c07003c1030400c540108111480100065 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 756172607 1250 756171357 756171397
    0x60a121b0c15050708010b0c010b0409051005070e0d1106040305031c05010b0304200d20031203100e0a0b03030307080a0b0904020114160b09060103031725020c09010308 74
    0x30b40030700c200d03440740102d611240300503420507001c01d21035048194510890742d2141c0300d04e942c07616240a1101c00342e120340014010480111016401e84c0c10042101d030410a212500b05256510401c51000c101c0d0044c0c3c1e542c0318021041b0200c1e686118a410250080c4400074101d65800358450000409070160902000f4990322001c9560755840152405010380650a5143d03000382d000013403200c50600700804003c0c445002c0e59509030303c482d10f400c4451440c1019400c00541d81818031201c418031500100641c5146020605c00c5e0312910280585c500b80c03e041000504500481e0784003468482c0c0090450f034891605080040191000310340165900341010800003107401c041c0303a1076003c3c0d503058440c1e4002240b5550f12160b02d401071550580c85400d5aa1180b002c1486d00e9000c4d0300503404500500700940c11803c000d820080e24404032031200d8101420002502140c154038000d030300c0000281c0841680d40c000481c5091149583c0d1980002c4080c000070800c02000010800000e10f112801442 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 756173857 1250 756172607 756172643
    0x1208090c0307031502090a0902090301180b1503101104090b060a0806060d06030804030c030204050709030f083603010b0a06020a0b04020a031403030906060f060a121b0c 74
    0x590000d0300e4140d09079214690900004500340710111901c5244071006080c803096400040c10380140342d00080e8803540c00107005002d8102805200c2c07002d42003d50f5801c005020341d98640754603c004000041014800e02080d0311603070140031900f65007102c0c04050007644540c0310f026581d50320030305c16420b007a40341195081036820500306031408101d4545414441c0d955050500c500750344550004d0041b60b60301d100100029a000d009040a58004c12201034840e0451052100f242e01c00f8040318103102250104000107800426201c0d0001e600480c2e25403a8682924201d661494500c600242440c8002e01c050b01342005c0c000e85445034004800030b01006424005104e15a20355004050050304000710b0000810001c028042d009880588600d060b01c1d942d0300c0301c02d0a03442c40d20108800741c000200348501c840e002c211250f0040c504645c0034075250160b01c0050303050b210750300b480700a0106030030500c40c1c420403075070003200000a14240399800f04080c81006001c0510110126074071174a41c540042c203 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 756175107 1250 756173857 756173863
    0x1e0305060403180e0123060408010e03030a0b0103020f1801120e01151a0409050c091c0b0f060907120f0606020c150301080303040f1110210903140c07050d120809 71
    0x4a4810b517801c0e84111205940710109092251b15594103c1b808000005014000740700382403c121400d00a95224244400b0340c00503540c1d1000050704160041c4038200942607003000b1202c1101001f85040c000100b80001a40c0d2601c26040d41b86a0030303e040b217000e00204c0107401645c01f40c00e01555403010309454901307003060354542917030b2000492400e00c0b003031020303241d10760140d60000c0c43e80308210309224844000591800d07112005d440740c001483c61000070887c192003800d40040e503101d8864481e19002011412598005240b00304110303016040904440c0340e43c0c0468004c1c001c4c2942804800d07207500010b990b84c03184003400ea009480d40b000d03820b418140c940c10b41c0d040c0e030340c0740c03014501c0c5031100d80754450781d00d48075003065521707068402441d030f101c1d6200c400d80c5404070314903280d8800d038180241c80d0080900081c19020380860420b859040020391003514500c2a454190500d41c490a000129519011050300a50b8105040c4400035080c0641caa110750300004841d560480720303980380004151 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 756176357 1250 756175107 756175109
    0x5190c14100e0f0112020f0417010603050c04090602090d0503031923040c330e090c18120c0307080d02060c0d141f140108011e0305060403180e01 64
    0x1400300802c0501d14980340d07402c40a60f10b0140b6201e45200c850084110403a070000c0e905007810340002400300850707002c0394015441c82101600802c41c491660701d03040c0c2c030380d035030f030101540b007a95100240780807c10141e05480d000500641003290001c0c0d51315109035a0760060300e40000300c0707404001c1e841168580e40103820005804240b912186147c0c03044581e0b0070303d00644112000c44545101280500c414812144255032000c02c1c00c603023180b41c520031512200b0344030801040000004001500303845850425400002809001c1e07501c01d90420480d90310700a601a95501c12a10040e8440c946000a400010705604809490b94207660350003556035588410800c0c00586c20807070003e0070034201d02010380f420310761200e00481d0b100e0042d2510345444000b02d95948803400c0251441c6502c00c649400400508224812086600000f50010f00f0b540710501c92008501c3c0d00c40e14074550680031001c40b20003103074040100c403802d040c18075003d0080b001401e1a1120a0340c10603001650081d0386441038 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 756177607 1250 756176357 756176389
    0x50f0a02013906110a080115050f09010804110d03020705090622020306030102120103030c0302160b07060b13090311060609130308090705030d03020c010e0601061b05190c14 76
    0x240e1452610780340030782c0d40d805541030b01c2a50350350048002c25103403840180000d041c03581e60322001398140301050344070820750440041001401c3c045417420124080489070103c0003400d01001d540d541c8e20700001d445103d008507a82100751218508105a00014070700b040c3c0f10210307a401480d956100a004e582d155010803a2121080c14180628040040d80115040b010180000d4604500190003c8112400307a008800140011000740140350f41401281c1000720b16043e00b1000300c0c5411151049402078000c05000c4907035540700210242d07580c2030400711541c501c0c14240040c102a0130003034002d41c1d103c10403215601507035000501c03919010720716600c2908074490340c81c80954103440c2211a81e42c002c00c102050b118003030021456660400807400001020380d800359490301110700807400e550014282300015840b000040c40401c2d0070520402d204540c501d141c481418140c1061032419411007a4800c04d44c101d0b50703011003404600341542c0706071000d0140c003400c800401014051504511040c403 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 756178857 1250 756177607 756177677
    0x9112d04090c050108040609050a210c030e0f0414090313090b1302070204090b0901020a02010608010516111c0201150501021f1505030327010212030f070903050f0a0201 74
    0xf44400c0d0b00410f20980c010340a0314000031028110340c0c0d010310b4018468810345040d200c40a100e09856242c040c1984990468546000310301e9040e54007070a02c898030849a072080c001d0a510b48103940b25075111011422a80c81d06ca0300d5820081040b5850b130380b007540400141c50308003e020540003c14000c03856150700150540003600040f45029009411414040ba8426100d48007800420a01d112907805102800c0005030b0714943c081001c0d00710345d0310354020b030400d9050408120801490000c03005a140d45400e04001d000c2025400c942002000902560702060390200d8204840c2c3c154002c010012540c030b440c074681070322000160380c0c1700407442c000f11750760120704d0031120490240c0e0407007030b08145010703040014542c981000034259002082426607a050a040f10391000c2c5d0038180c1c01c61280002e0001e0411307550301c4c12003a482480020b00b06001c081116012a103407a11070a041d0000303640003803c0d00c6c41d90900204050326041c0c140030903030001c0d040c030050040ca440034000103c00c01f40c500e080 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 756180107 1250 756178857 756178859
    0x1826070b04090504020d06020c0124050a0e18071203021506060d0e0c0604030f05010609021204030c0c05060301030506070f05130608190501030b0a061508010909112d04090c 76
    0x1412018080060080340c1008011b0354071030028026001814050302c0500020802d441701e0243d07409a50058040e00017100c0302038800308499200c00c48113500341c0b48020030380c03105a0780c1c190313545000070b844650a0b00b99104010b0005404001c080611055034444d0342624424520000d617040e10040c10b841840d0320460400c428007800c0d0030b940c031075001c030380280043d114503066001c0000d4131504158015907040400510000401101f031080e000980381c040021801d00504610120407480010001000c3c03010030401070040c440003030b04d40801094010403440c5d0b2581c40c1c0c90850707120b440c10f44200300800c2500340d414043d14010410740340101300c1c1c003152401e00352511008544605003d0030000a840e0030014074003609586d0f0003001d010398094205c00c112403c0c00c5600c841160f126a000c001c0d03003481c0c2c40300000119400340b03145046860680b00824004030038181003500c901c1090074568802030550a401d500601e2000c070543e02d40c1d03e031003007404041c03046007030001341c0c0c80d0403400514100d25018 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 756181357 1250 756180107 756180119
    0x5031612090804060309020f0618150c0304270c050d020f04050307060c050706051813140901060f0e1e07140a1e0c1109071826070b04 59
    0x1414181400c60000305070000c003a203031441c1651281e0880400a81c48180c88000d5003422101400d40020903640103140c8004006005000002852032034450780303c081e11001002c0702c503429282815038100542e076031903a0b1290001110150300d81d44e003040c948408800300c2e505030a4401c542083e49203840f51840c3c00440590305000f036000502403011600b042c080890b485c3c804000340b0000d02503a0700c0704074001d0020708001d403809a0340d034404000c00004100c04121450107541c510f4100505550028402941c5010400500007085248034800100003c11416610541041d411540703101c0b0481c0c00070f0f0311021282800c00c800c88012080b1002c40303002c814416100d040b195801000c07480c01d03290841900c24008181c0e40240c0d140f800190b09000c2402c140f100f43c034030749c10080d01c483c20080100541543c48a1aa054a4682c0d034407968140c40020500350290441100400c003c083e17140c151034444420502003814020030010b1007280e03050900d134100001a0f82c07000d440d03030411018103140c5400 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 756182607 1250 756181357 756181367
    0x213050301090f02060f070f0521030108031c06080102160b06010e0612040609050304080a060b010e100f02071e0905010812120907150215090c0f01080406020f0a0507030f050316 78
    0x1240c03001400108020900204c0c125016981440b071140014250ac1120039041544030050010400c80d00303207040004004c00c48000085400c0340c415a040081d80c1541c0c501800c005003080d910045295000180e4039210190456040080c144200107118140d00d4000045410510075420f06030000010803e80015001c6142c103660722620803840403441c80d50780c0c1d80b024190340081d0311803001a8400c004150810026001d685d929400a10b03000d80c0004071440040c40403500040340c2c000380507078514040c0c0000c0c03003800310b42d0160400d21542c981c012003085510702104424440c001035a440c050000ca034040303022500080300e440b00c038003060034113a40c607103160050540500356074000d110b5442c0028111603d0010803103c040c03240c016040001c502406104071600040008102e03070807000e032141050395400a100b62920080c40d1000303043d50f983c5040d80082c0705410784814001c2c40800d807608001e0f030050041044a01c03036510303c00013503a84541560f06000594550140413010306030106003620527 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 756183857 1250 756182607 756182617
    0x1061704080c0109150507080c030f15060a050a0201180b06130f050c040501020d020a02090123180402100306080a141009060b03070f080303011412010501090213050301090f0206 78
    0x9a100903240603099089142100d02c81326040320300f01200c3c080d80401c01075921541e03500030102c2c10440041c3c0f40110761207201f48030060059055418440c0496500903e06081c6801c1850203801141e0380d04240e58040c145030482c500800056003402066000301800350b504011860384402e01107a075403200010800b0a815031410318000e0740c0d0360200950a91154002c040c0943d9040c03031415612400c141c0024201503203103241c20f0555111041090050300c5003e11181120303002e11403a980001c1000487c1c19004050020303d901c0050720a803111102c10740c2c1004c1c1d01130391007103c4c142001e2071007178002d400f9034403240b14011140e04802130081c01702c0d1f8200b41c98158412450146e0f182c0c00108040542129400002a11140d039180b5400301d090808011241c094440c14400d85081031234020b18654910050082c5802007081d0cd1900c421501e883c903aa0741e280d000c4000038042c81d07031a031900b03030020741180c070300706400403000000012541030600c60403602c035801035042d0021600c1902880415440 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 756185107 1250 756183857 756183863
    0x20f1e1614040b0613270221060d141513081e09130f0e01020f0409090c0503030d050703060f152307031d0925200102090102070e01061704 61
    0x208018103c5a40c03d1900000080c0c01d001100c0d4501d03411a021b2840245400d26200b80803c0c070402c81c40301d800e003030440100d800341c200120140381d03551907001007000c21403187c4005043e0f600c04070900c85444004a40354a008410681482c5203948118018029242040c3c01070320415042090300d03203c50342075150440600c4000810380c6000300341d80100703800503283c580c05440c1c16500c0d080ca10301031145000d9080141011402542040d2046030000e05620651107030005155981c0301150410401108070002050014280d9454440c00d10084010b4002190300078006441c200c4003292803090a092602a104880700a02c05040e42c3d240c191201038160581001401c3c1030014600c00100c0c8000815001d88240c1d140d049204240c10540343d81c00d840c19a441c884ca400004004d4650200310b511001e50000c2501c0c001665080300c815a0000144414140700b06200001e1640c007150540052aa01400b030342121040c96464480900c40300c001c2c082c15000450000043c1c0740034042002c0e0704e0304180 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 756186357 1250 756185107 756185119
    0x31806010f2c09010b18060a05091806190e06010317031008120c0106050a12080a27210506070f020111040905040314040b04030f03020f1e1614040b 65
    0x1000e50642d2482d01e000300c452100d5070703440b49034200150400070001080015808040002410301400046840350607001c2c0c00e0141c4110f400007500c4c004840c9580c0320261b58074007a075140b420700da080412044a422101d4003000e062410b0140070000008155040f00e4100c0380c509c440f00410307429645546e00107000c03810b01000903240404c0e480c0052241c0c250094072440103d07500c444170003002d42525480e034001ca100e1505001c0c10000c017401d00c0c151034210355101180d2a030391629248161040c42100400020054443c24510b0329401540b803807500b07558510991800340d09085074800da00c0e06107210f0007849600017801160446010b04004188079000d800003040304240c2c50200901c5400c02e5000c0721203651941c0a00041c150000c0e6400a42c4204000c824074003801d02404a10a10940c0300040c04039503e004000f060510a01c507580b420040c900580d40300d02d542c07a40400d880b41e02107103250428080c0010003083d690b11500000f0031605c0b05c106400a4240d04410040140704150507550080 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 756187607 1250 756186357 756186419
    0x140f0f010b0f03091c020303180616030b0102071d01180e0c0f130207050303010f06050408060c0d02070819021e071703130801020309010f1e2a05031806010f 69
    0x248440d81e28611070030546d00031521380c90305c4109074540b071031222004c0d65030750070032418081e80c802c0601500c0c1191031142008180c0c1034407540104c3c9801ea06038890343c082519015207508140004086504031844608140480e00080d501ba00031103000847e40b1880f64400c00c0e61503a0707410000d002010040000340501d208800100100d4243e038810042100e850300000018032810120f0301c1d404d0042c00300e40c940b841c1040e0a02c0207450b40c0b404054050303030000d48003042201522500b5011128103da0124017903844216a22142460000d140208805805400003402990841c03581950300242c1500040c05024940444d0300802c12642c011b10100d400104211410b003a0107001280040414400041e038034a00900f040f406c540b0200c00300050785c2c0c10304240c0e08602c00ba480243c8241c502c41003000840b117411040344100300b5541799a91440580007003865403240e8114001d07511038034454400c1881849520541903c40009029a2100e00e5046000b4400d41c0c01e107655a0000750072215000c90300c2 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 756188857 1250 756187607 756187633
    0xf09030c0a0b01030506070c0c2d03060903090504050603030d05150303070c030308060607031e1710050a050906061207090f0f0923220204140f0f010b0f0309 69
    0x201d50350301400c2d561500040300410410400300b100590013070f098503002c0b040c0c0c85075599142c0d000d030f901c0c4100409088080450b00600c65040c1030b2480540d100c010541e422a924500786014111100082d00450803185c800101d50502d40030340d500c1008000d01440c038212907412424020031018088940ea083c40c554200441d89041009021550144105a1003030340303140b41c000c0800c0d600810581c0211428088100081d42080c1c1d8400706000446c4c035000c0c884140d0074100e50716441c0c550108203120045052200c0486450320460a4038400e440b21050b00703860740c0511045041c15204940c002c0030410210b1a1403000c1c420f419000260351034521012540c503500811880b2658112003400420074404000514003032180d9500881c815580348a900003552400080ca50024180000c1c0d14103c60440c0740020409200350415500810130010401c04001034012003000300c0700300c400341c070b040004141488603502c0f0041c120760003c0515880e0074103001150011740c101804401c07031482040501403c0b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 756190107 1250 756188857 756188863
    0xa1502030909040803062416030c0c06030b0a050a0302030615150f1b06370e0f07050a031115300a0c020c040e03040806091b06090105030f09030c 64
    0xf01e000d004d00c2a140e0a020040200081140c1c190f083c4440c40d101c841d4101c3c00300542034640d0710904048844210b086410155145544014020701c61400c0c00000304507543c01d41c0c07240c801302e0010b80d041c1d0440c075112070501c07100046030301001c0d5040d0310040024220b490034040c3c41c08444e0340600417000b000c0741070f5401c441941000d9650070701c03642c000c40d4003500700d8840315002c0d00911000e8020700c80342c1031840c1e044211814105002910700c4003540141d1540f100300403440c41ca1035030b10804121000c01415804e844040e5429400310f10300800900144620b064401c1c441034a03003002004100a00d101d0401c12490b0241d035001c01d0801c0700b406440e640441a95414450300191402c50041c200040543c04420034010207560f401890038448804155002840e000d240790107032000100104a5006a40f450080d984034040e0361046c00104440104040b42d0f261610b901d0180b40d24401d0294420082a4024850f502c0c1c002442400084d0b8203101441409402004403003e0301d03d442000904641 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 756191357 1250 756190107 756190111
    0x810030b2e0801050a0b04051e0a0b1e2103040603021614010906050a060f0e06030a0c0815160507060b0117100302030705031504080705010b0904150c09050a1502030909 74
    0x100b00d0f59a81d04000307a8042c9401412a103540c1100c04211500d09150b20701c082560080c83d2038a07400d103440025804014503070040040303034001005401000402d4120381001c0100c40c00c03c500510050010780c0d4006031074401d9802d409081c00c0034504082c10244101c00a420140c00d40b10301070f9050f01400003190819810612402c2404000b01d030181032800d00b10203440000d8841c81c40c2c546001c00410125242d804010182c0e005000b450305151954000a8a04049540064a9201c1c0d1140000f0019800030304282480301801c4c8001117681da510b07072103420590141552020030400c0000750001003507276100701c00d055814101f814283d070420303050042e00c0d002102c05070b04d0311509030024002c0d8130b0300304484801000b0490040c401410700c10404038a03080701500c004c0ca0203034046481c1b410060290081c844507a4060007081c0c1500d01401c2c1145086444030358003807080c1c50b00c5000503d591060b4081e100360b580241c2040541c13403401012010b0007454103241c3c0118007060000fa9056543d48200074 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 756192607 1250 756191357 756191369
    0x60a0f17010603020406030e0d0225031202010603022701050d05010e06012603040f0b030402031207060c030c020f0705061b0a08042120010915030504030810030b2e 72
    0x40e103032410404061f00319024031034240e0590340a150401c6403a42e00207443d548900080d4030351903004a201100b404058034540004204c09980d25084142c0c070b50550240342240e0084039280d4400ca04100300407002091807142c2c40091104c40010f010605110a40410780c41c03090000155910340010051b082070700a81007644080f54080e081074000071490400c1e03a085030240c02462401d460900c3d451f9031909981305900d011a00813001400b176680c213000a116141d0200c0720f003559422035140030401007801c0403c1d400800e241c0340658003454400601c0341d00800340d14000700171a504000405c0354640000d4048140c0349543c25641d2a401c2040c85116212846420056144c40c01d200ba441480d0340040d009002100c000600f800110720344081034200340d28107042c2c0340d0500061400483d10303040644c00811020300c013003607443c050036850361201d03126601030790f10070341c07070352281c81048194644c81d10000d131244011102050144040740340c503005071000c510700c1e050402c5511406101d092032640c405 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 756193857 1250 756192607 756192611
    0x30402010f090f093315180e040201030b091e130b07120b180a06090c0804170f0a0e03010b01030b03100e330606070314030a0603060f06140906060a0f17010603 70
    0x8000892180e401c18540d0300c040d0410381c031894104100815004081c0c448d0307418103000c540100d000c0d079010b603010510b8511b0103012442d59140415904491030042829401807090080c0020b05150004238040d20b00c13948440302002d2521105012203011203c14032790135005a407060030742c1f150703584c551007a045400c80c001c080345c0d14035290071400f04950303555000505650800f20480749a40d0b01c041184e6000e031b888100501d0609c6601c0c004452406000319400c41c0140010790884030681100e03908210000460090048100000c011402d98070407124884d015802a6042c039080c02507070700000d0840400204a40c0c804090528291140861001c000c200341c0080a9042c00100803544666100b4025101c05151085650300207050403510310410f03550000c0070001c01c1003460150058001580c00030001d03c0420801062100144001e00c50200d011115004024081c00c01c2d8580a2140b01d005140906005116000703403811010f51700030004028070002818400401200c196028064a07600 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 756195107 1250 756193857 756193859
    0x112050a09021e0a120f060f0905160b18030102071502132301082502030c101a150d02030a0605010305071803030f03020c070b030402010f090f0933 65
    0x1444260907003c040d2520b08404068104541c0c0c4519090b0011280c1056140b003d641141c240184586007841d00144118101152207140304100d13042111382c14002c0782a5003074049800c1096403490038602c82e1030226201404810b05c281d03c1e1681541c05548041e0001d4034003040c0390383e002c1a0042d00f0f2001689141c0c040358810301c80c01e0b10301c1d100000e4584030311100604a41745132800c4482e0041480c50b4100007140000560040e4001c08040c180045402d00c00401800380801030745940069443c07001600c5510100070781d1000300d00a039802c16180600403e0540d0319241030040c19041440d44c1380c030440080005400c2400c19200440c411390005c40005180d50a001c0014250740d4068151810040c2040c255484000c40103094001c4039030600346046003943c03806050303019000c1c0c014400301a005540001074055082c100075445503100b642c0390308030464209400d40345550640240d0601280042c000c0c88860034981c4074001d4603024a080358040c0d80006044000e03d03003101e040f0724000d80c11100c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 756196357 1250 756195107 756195109
    0xf060d021504062006011427040512160f0609150609060501030506091501020c2e0908030a051e1b011a0f150c12030f070507021e0112050a0902 63
    0x9038140614108401002101c48a0481d00e5905d25060081403000c080700300c085152682d80ca041c1d004241055002c0c6e052900480c0f81d44505141b04440548903402103a4600d1017144020084442d940d03082100e5502044194a511541000c1a4022038049540700080e9011801d0907800a000303031070820011800740c5c20000444c00f9501d8540c01903040c1420300303090042ca680d440a045034880702d1020802048240704004134a4041c41c44d030400d80200c40d1011117010141514503444010508800030050842c12800c202c03a000c2d02c0c1d108110b4641c1050218241c0d25218038018021055960141c140c205030008050405500c0003032902c0484090080d0b080e1150340c01c0c002c042c960418502c11030038031921100803c858100900ba07081c40b810040c1145c90341560118159141c902400e01200c2103900c0f41c21401d1507581c01a40c480c207820070b0308000100c18500c250100d03164a58040d040c0b80c4a503959a9003034484d10701c1e4594290500c488006c05040121a5205070b6100310a080004a00e500c02c0340 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 756197607 1250 756196357 756196367
    0xe1b0f071407031203050901090b13060b191238070201050606251e1403070f08030a0b040e06150117010608040f060504050601140909060f060d02150406 67
    0x9154405400680b41080400c91209140d0103510355400c012426907601d0070b8885c01403a9001d0002d0400c040740040c0400340c0301e42e50510318003a10601d002c1000b05064010840c0f21050503940c19032002961005102c0f10350407008150085106020035010607040d01105a00b104080840c101148106400b205140762544903250300308000d8002042641854804030303610f44210f0701030011a0707094001c0b42c404a40305058826205820070034440e400109548500c84041c8102400d035102d80c83d4441040801d83c0210844104903409040020840480e82c0c440b4041d4000400601c3e049585003140e0445c1e840d5401046101c0300705001612851400840a00c0f4559144078031604100c040350380d0404906000d5007441c191030460038900324680c0c6614244800d109440002001c40f402c04003408200000050454180d415140748050b10415190030300c590359004482d06803240d030240000c00c050004038450b180d000400a0120070000ca03072500811520003401041200101c400034081040980c06 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 756198857 1250 756197607 756197633
    0x209010b0a0e040b06040503060408070b160e010305180d080f0108070f0905090c15040812070305072004090b010905070e030a17160501020c01050a0e070e1b0f07 71
    0x105042a08008842034000d0207180030380342d50790149599160107191030f55440c042d1001403a0080886200707113010310306008150131100c0102d0300070f1004801f04111201004842e40000a10303925904544540c0004602920005d48a00100d64102c1d1241c10901c10a22818028035460389411030503007050811810000310581c0609100d03001113200b807104280244242040720805580410076071070b0005114100f46040020701d0b40844a1a8091000c20b505e4001c2c0044801c3c0609540d00510400c01c0403106214009004000680c204600c02c001000007002e40e4401d00340110842500d05150041411124060808d99940285d040108481c2d15907001c0c440d4001960701c0d0650600c10080042030ba6007842c0b400042c2803510396010440048400c805480010b40b40d0040e240703049010741481c0b4000d40c040790516010b5401c190000fa01050203014400c210307083d080c01406c115240403614449601c010b40341401c080c3c0041c0010a100c00081d010b802e9010034814031a955004600e00b080c02c0040c2 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 756200107 1250 756198857 756198869
    0x1e15050105030c06031f0f060e0402120a0906060302100c1103030f032403010f020d23191404121709030d05071106090d09080f1b061213020901 63
    0x1048014032060310086081152481c05880c400c0d100e0305c076414030014211071000703c20b5412480e15400908a220101404101c601d151241000403101d641404140c1c8581145030003c840403902080c00341d4502e0b0300040c2c400d4000d5200080b981d417240c1c005842c410448041ca400281010071580501101164026032640124025458000c0f642034110b02070000822445810070115040380302c00c09600004082003100800800006e400280410002d40010010184981c50708000d51030700a00c040c1401144621041d00c000c0e00d81d1404980c5000340740c2032554aa400707032102c070000120b0403491003050007a0310030424001e10520781d01d030040030064103801c0a091a104041400014070010044038922480403e001c034890350780d442e0549081c1050a191101c605c104410003030500c1000c03e050303d2004840d5901c1002e00d66070b581a0b0ba40e02c441e54072104150f00405000603003c114a01c5202c1c0d1024081d000c07d09001856900809000301200d8541c1b50f9411041d03180111302d043c1c1641409801 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 756201357 1250 756200107 756200111
    0x907120f092a030c0801050103141603020402130e1009110f030126060712060602071a180604080c010e0a061707120e031903050f130c031e15 62
    0x181603102c0301ea0008580710440c1d00d49208484844a205001d40b2400107980c00c003c1c4000115507680f981c0d80200004d1205841001d80710401d150100000300e4200416403000b0070f48034070301d8215020400254011190800d145072205400900820b51040080c80303001c42e05000f141c61b070710b0b1262080558151005501c0c1d99a01004400440c011440549041d244004903845414500e503c2c4808904504802083c25118010410005943c0000308520540c443c560500c0010303601d5400742c2c2d859000d80200900d0480d84000c409200a481002e013032144600311900300314440303010228130143e1080c1c0140300780350041000007130156045403490884800c1036880c041050720f0b024000b13162820303070001030320103000c0c14011400b1180f050800c80304410404000300a0030100040090350f0764000a49460003032100244881d00740c4c02482002d100c3c6140e0030038800c2c82d61320310440d10f010320982d600440314052030020220114100c407007118401c104e0350ba01009050340e00d04200d8800324129000d81c110714 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 756202607 1250 756201357 756201371
    0x50607030507150204050405041b080f07090f110705070602070e1006110109080a0f080123010f03110d1d0604080a0c030e1c0b070806060f0d0b0907120f 67
    0x20390702000325001681c00858000c07080059003240e1010748100d44c40b40e94003c2c200002e2000748040503100c444403611401c604e1680a950714180303501c81d01d613081404015080545c1c20000444207030003900c4250990703640007518250903813800b14240c012030781c04e0764183e1204505010482c1c04100303402c0903212440d00c894180c541081014180c0b01640607010030001001110403041400b5000302401c0b90340b0140d4541c440c60b11502c001d16400510342030b100040c1c015000001c400310900c03c0004401e50307181001290001c10001551074200c806007072020556948402000701c41e010001e0816800307009404217240700075003c00114000e4607604550281c002ca401e00c0f00103020041110307161005070601c1c174a10f43c52070809440140009072100e4100d21a50341c12001c1240c0700b840c8082c9103104140540c481c1d00d03031400c21100e0303034030440e401a0060000c01220842e80800c4018207980030241c3d0000c5003802c00400420840c40041d103916000c181440c2030080c0b03203201801071911005020508000c52 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 756203857 1250 756202607 756202613
    0x61518080a11040207030c020405010b030a06050f1c17031504061d060f0a080f150906092e021b010e0307020a09020304020406030209040f110f0108190e0d110106050607 74
    0x24460b84030151040d40d00203030f0b140405000d840320f841002c0c0c004000300203541c0d40e56229145940221800034000f8546500410b141c5400c0000340750300ca00150991012000a030f10000800e900018162001c07540a4101e600c01440d0750010340c402e1040c00c1c61f030b9000e00a0038041c0030549505400803c4006080c6503000d8a905c40040040d60100c000c40d250a0311048850100780c09040f0742c0c001207028007405082c40400702d4002012250350401e42d5025002d640c1e80841280c0328541aa00f01110f43c015000000013482128104800c1004064945002264031020f074000c07a0311034058120038011440002a11b82003c0c0310300703001202010051031500342281d001400c890745500a102c81d003580071010a081d034445030f0121000d95030140600500f03003001d0801100688864404442508000c2012410342c1030040041c00468011b8503281d860380c46440303403440103034624211401e0480c1d440d010f80d8005203003041012441c011a858000e0402904400182582d505c4c2d0481400b400b01002a9400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 756205107 1250 756203857 756203873
    0xd03061410210209040905061b190e01170103030c05072c0901061d0103200f1c0501110c060a0209030c0d140d05031f0b1804061518080a 60
    0x4080b005902049100141c20301d00c000070301800b140f040e0018544490740041200000c0c3c594000d4100745000280c0414061001e01540300e901d0700d1040511402da10b10b006240600b01a23404e241b030506040d10551032094503e43c810200340d0059001444103040c81040c01000d201c18400b806e07054404040d0240801e0f0003050310040035115031121440b020003d081200c0a50040d0301030039080300c0e1801c4034200e11f00c3e005401c440c28042551028044040021190742c448c42c0a148440058035404100d1140003c0200c1b1030401c1c0c3d11609040c04504100380061402e12072005440c50000380d59231140d9041e4041d6180444c002d00301f407003051040040e0602c0c0d640004554211080803120358060114503d4503500c1d03007400000c07841c500c0c810000503d0020350014050340c03164111000642d6000d11180082c0000030991090742c049038420084e2002e4081501e142c20b800072000f40004c01e400f070b6115115807621080e00441400143c004480282d224500810341c402040b01038001c10340d12142da195035507 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 756206357 1250 756205107 756205127
    0x50907030e0318030f100b011d0a1202062206030b04050121170d0903030b0118090b03011e020309010501124107060201050a1512020d050d03061410 65
    0x6500742c510460026613410041221150718920548404410f504101d401a2810702207003800305807031001011002400d01d0f00b15007900c00052194034410b191110211201000c084c05a0700001c0801c403002403403503079100e85040d20071641c080da807046152040050444041d0844244103608000040107072104c454409442e44603025032210b50440c0354981281b564542c41e00f6001c006002050449299245c1d81c01000701e01e00030b840a01070381d85c01c0801180c0029100801c46a000c10038103003841034102c00e9000c2101108041c00004854486407041a24a02c000d05080c07032180d000402c000500b0350038040d0600400d45610302528550300c907079808a45802554000304880041d0706011000b042039503812802000c6030b094005c1c1121001e080a40390703a094055407001d90b0910780407844030640c520880203540c080c0c103031400c0a10b04141d102d031000c6240d0842039074000e6180c00d101004c40e50903c0540c48064241c0c0b00007482500e403042480400503010207151082054a01c404080c1c2e81100c4040 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 756207607 1250 756206357 756206377
    0x506060a030512030c0c06040516050a08030a0309060b04060305100e060705070605040312060b090a1a09060f07080f040f080102040b1602042a030e0115030f060204030813050907030e03 81
    0x40c4d00c99580c00f440361a103000d40a104620741c07141c8001d110501501003044c0c240c1d40300b10010322720302c01c0d1903400b4000215028858011907178403c014070442a8425401061070b0303442075070046500e1002000040a6a919401c10345203500107802c2c144464026104071000381c412030001e003a6a14002c0e602500c1070052840281c03190740c0310800101014421400c0c812221b100410400c804c0e500d9003419180b54201101050145818800129100c02c41c0da001d65404103480e600585400307840300610915420060030910105c030144003000000328040c003d0500455040180343c0c64070f1504c0d1030254076880c203034400e0a5991041000b0300108542000300e44410080b9520941c0001461000c1401800c450003029003c2c0020342440c00004483da00c400c40c0000715503414041d45c0130303907202c1c20700700c4181c1c82c5540800a0003d0003000010512f1401c4000580a10170043c1400d96070b8444400c1035100340740e4050860035281d014000c900d003d90400d43c0010661400304410101710307443c2c5541e031145810382d0f = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 756208857 1250 756207607 756207643
    0x1c290a0903020a08031503060a050a050f091b04090c06052709040209090a0506150f0a050918031b07051e010c08030604060b180306010b1603050a1e08040506060a0305 73
    0x1801c0030ba1000c807441e001d0f40c021f0308548040c50600383c8075005000c1500c607003900364201000b2800d40081043c8050040940c28081c0190020303c0401c0506004e00e4002660080c0c0c9507821040402d081d034003000c0081c00700d44c80e425541c91032038103c01800c808484d0840b1a80128a200c4200c90302c4100003191304c164103440d542410789641e503081d40341600b00c00d0020041c1c840d401c02c00100c1e9040e032200d0004190141d80e060200c0b458202048a0a08103025043d0044500c10000b421850301a01004030000d2070401c1d41c1c641603d2030203d06000c0c00304010002e00364081a404c21960070044283c210501c10300d4601080c84900500080001d2480607004d40440741c04404946c0c00d42d1180d0021000302109640b80e5618030201101c000f00c1214041e601d4480c3c01640b00014561400344101ea0080e1088542e0440703990f91550141c1d0260850160842040304004a00c80850420402e0b010050703441d03122203801e0714140c50003a2070000000c0159000b65100a02000011400945844007a00401075 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 756210107 1250 756208857 756208861
    0x10e0f0f19110301020c0d030615080a020a090e01080c03070e0f060d06060513090b180307060c020111040905162309042d050615091c290a0903020a0803 67
    0x7000440c12400c90030303583c1c1548005402084060001850011300501d42c0381070041d65a14035414003052078a80014011078600e000151340e101c3c040e8018501c031003050408005d40c2c0d0311100000320020098000030000d901030034000c0c040345403c0190310010446203d05c8401ca04d0509114050082e0260980d03006410b021000390070000c0750b400074006813401a140c0c45101d001e00c0f02480103031103240303800c0e070750000d110010526451051010700440340010000b94941a280d551321002000100001421075503074910060003100000e000304004c0400301000310305401d01c54100350452140d9883c80d0144691076014410400f4031100340014601403548140c0c4921400012801404c03a03030140f0611010301950010448280c51403001514005410410043d0b9401c0d003440005805c0c41c0c004184070009010000b0300785401d1000f200f4000a41342a44a0b484895440404403480103258406007882005010f240c03640c2a113506910880b00300b41401802c4070b03030701d020f5103803e8111000303401601c2c0080 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 756211357 1250 756210107 756210113
    0x20a03020609030f010f020a09211509050a150c020f060604020a171e0a0b1c0305070b0a0209011103190e010903080409090c0b03160e1c05010e0f0f19 66
    0x44d007080d00c0ca240c000384080c02c07401c0c880b140294410264a070108000a50201d0b0819903940d0980190170000c00000300d040481d00e510340700d500c81c13441000303400b5103e1140c5000200d090210702425803251900110001e188c01051045c0c5402d55440340855105807075a10042e040051003d0f0400c00640e40180c3d50306070b9240490701d040940600b4480c02000e4000d0000f0860000204080c3c0a424580c042e0342c4d403590b08200d42038451000c0003c1e0f014210b80f0001c6001e82d46035a21041407071107810b146151940ca82ea940304c7c1080b003141d48415082c0c0c049a006200c0d600310380800510401c0802451500318240400312141d403504109504011090310201b40507405000030601442d04a0801501c0c2c60b6105080d002500c00c03410110341081010500080c2a0489010350b40500c0218112a6602c4401c003000c84182c1500c0301c43c0daa00003101110319541c070030544031150055004100105d410361500f010359242c610a504141410fa220680c80d070f0b400d00c8042906040114443e208031400e0650b82 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 756212607 1250 756211357 756211363
    0x60f091005031b19080705011b050613120905090a0209150c0d030f090317070302041a180f030703030c05030702040c082712070c12080309100207020a0302060903 71
    0x50492a0140f054140b403039080d05220000302c00c10581255081d4129080c003028180145981c4246081c9600c007180c144260340c0204072920700944000101c88040529484080c41c05030152180010001c0103010081400000d640b01140445070b41040e41c00d10380b4140200304403000040484c045254045540d070750075907030005105000401e40c224a6100c6003044c0009465141c0c40714000d000c0303481d1800003400301e0107c1c05854525074064584150041c181c16502410342c100401260801d03a00b00030214070b2099030f4003802c1000d0802d480c80780c1c45000c41d00c0e1924150010402061181503034a016014a0f98002865416213a01d443e004490460340e00d842d600d180248070b802075001341001858202c0c2a0301086151007685240c210000300c03811100001c0e0f002c440d51400c05c100307801826091744009007240040c6030307180c46072540c4004180d0b01c000317002d040044008210340b5a4000010b100014204006008928040340411454034610707900044d0031050a100c000c1c011040807a03500d003155814 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 756213857 1250 756212607 756212609
    0x30b0903070b0702032101140105070302010f021b07141f030219080604180506011406071208190b060921060124020f060c0c0a0501061517060f0910 65
    0x40b24040e10705080c1407201075282c0e00300108062413131000000340d00c1e0688071541603030704841600c048084580e80400044443d035201e0756040d420f40d03481d180a0303101d22055200400780380000d41600984003e0802c8110f090109640c0202c0c0c0241c1010000d8409644000c5440f188005080100c3e03410144090190080d000340c161074651561126101c20f00d0b40c0d0030040082c4103a1003200c0400c4965004065904045207045025285038088801230040d0000c02441e0000c010740240300c282015415540c94800741801c1c000007000030700c0f43c1c00f8407046010a240e000c0c003080840b4810300004285001098460240200c003900c01d880c050754450003140d401411584c04022042a50965030b12601c840c4080d02c00b802028880104035654603402e00c0c130100b210034051400002901d400d4a47d00e40340101c580100320150464040c100c09000000c109108100061001000d503130700c132041c1240050f00b8805070721041280034030101c04104041e40d840a055810040890b2030080f0381d110320021864605031 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 756215107 1250 756213857 756213863
    0x50f190e10050f04121407180507050c0a030f1b1b0b0403080d110d09050f0d0302090a1211030a030906091403060f0a0e0a0609020906121b01031103010b070c0f0f030b090307 76
    0xd47c030700070464101c1101076402c050f146590078031281d03d805004481c54170501954210a41121000800007440cd600b0010245a241780207a661500300601c01d40724030070b4a03001c5031441d6500b441640400e600e02000c100600030b0b1880241010b145407101c42c038a00c03c4050301d0a2059031030750b0343c950b00e00b492029548081c0050208120091881c980700c1d030b4850040d81e08084c0d40c4109021001400c0c0700e4003c0740c45e8814007130040d9600501e498100242ea00180d9411584050f21031102001500c0801c440302c049806581c4074070010f440c111001c3c145403403540218440884141c00c4620b941c40c0003558079003080304410004660340d100d40004000f00003240c001c00081c09801c82c018140303c040d4010301c410070300071206091a600c032a004c1120801c0148840840c13030300500c2c0d9440502c2c000115003248408181804510701c049001030795282d601c00d8000c0350f141040842d40e04240302c02060140007030080018070582c01820190024064000c074840141403001500024468600a03c02d9520981d4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 756216357 1250 756215107 756215113
    0xa0609031b030f0201050a020406120b0d0f050d090b071709190b0a020c0f090403110a080a09080c030106030309140303190206041a060907050f190e10050f041214 71
    0x410b840e0003051400d00381c0d80d0f2401982031030041640038401e44201c070304481554483c08120220044800040d06400844c01ea0162401c40300c0e101083d40c944240003040d1017900513000782941218084c201001d19008150910350900c1104001543d0b552a4030301c0c03581c45da0300d00352500e0a010016142985000010303289102441000841c3c402810151030000a00d07000d45070349001e0360b420301a03400c03914803900d5803001d4940301040100f806041c1c3c0c1031486115605484001d0304585898105a02c40811200010504501000502000d200d1f049403100c00724028044549551801400d012040c05002c0c6603014a01800c0c945030f404004403108440d101c114500c0c100d010850103520f84408a03800d442000d400e003014041c000088080031b215400007440600d00d80c840d050200e5554100f40725038200e03582d04011a034007846072814548502c01c01035480e4007000b40f09105101c0d000350034100010a20500f0300c000150940040182d40554501030943c007504100c50401d400b042c1d0042c2d0040c40140 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 756217607 1250 756216357 756216407
    0x32b05191b1208101410030e10050c030703050105030102031003030818101b0504060c08030c0705150603120909041202161212081915080f010506030106080f0a060903 73
    0x40e044606103116101000e000e07407600b951500044014680c0301d030225880300e182c00010560f11f000c5d601250b40000c120741164103019a40e9102d130115030041d680046610340100800961541c98014640501015002541141441010fa18140e21705005c000c0c144215000021424400401c08000703850071541162840707a012503c81d80104160343d5420b441000f90402d4454484c042c0c01107900700c41e070a507038140c03041c0c6258072005015007019021182858042086001051081011440c685020035410b400b50508004044c6869030350381c44201d54410a200c144c0c00d541c0c4000045600ca5001010b00000030884a004c070b06020102c00440074112a017000420b080d5068208410810310072a98030780c1000040e4030590761041c085a595000010b1010a0076403a40560461580d4108040c030b03001005441d11242030800380f16400c00b02c0030b0382d034032030403c0100d103400d0207034030003d21402c0702401d2900a422203e81c0c0f1001140000341406031031380709503020035103e0621042d00021080068010b0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 756218857 1250 756217607 756217643
    0x10111902191515050a06030f02090a03060507020106240507050a12020604030e1822140d17041a1911030403030c1110090809032b05191b 60
    0xd15042c800404094500070400c00e910681c549010243c2c1e000030301c5001c44ca407420f5011005003010354101c40700d02e602446040115180c540200c00610f10032000172506103403400c0d00030300319030315a44509001600e4190741c0c0c9241010031610b03000e11015241c19940c0d0b00b00d5040c1a0b00e4907040040080c580140340d801982c0076640801d05038080c51284e90348021810340c4008001c0a860b5085000301030b406d541d40858141c0303191004014403031070f0612200743d49000790303201c80d11100c4400c100452180c01c548541d10000303030b02c802d003e803895101103012026410039840c0c490101003403161008080e02140c0225905180161042c1e14070500c0400c00d0080c44410720085856800543d0101d01007070a040516400a015000521492101c000200800d0080d4481d440c003030501100706461000c0108001b80c06030307d0900452a050113180325140030140002c8c138120710440b20b1840343c0d040200510021381240c60908124108007000e140000340e000c4844a2808800c03024403004020f02040744a071140 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 756220107 1250 756218857 756218873
    0x62019050f240105043b0f01060e060603060109092a0302160b180f010c110d09140f180a0e0f0303010315110a0201020c1011190219 58
    0x907102021003921000385031002002c0c018442c02c00c10308210304407100144180e0800b940040b0304840342c3d07401540b06200c85000e060000c0c200c4207508244400d40000d071011100200150f104c4500d0f107100801c404d51030300c031100f207818602900e2644214030000100d4941e030300c58060080504040780d01000b0440c40d8002008614203884244e50040c2040c12103c100789009200355041c09400e0b8401c003c1072003850307445400d0320100608108001c3d08000d200e140c2c050003007108808001441d40005a00000894040d0507841c445400e0b03c0951700c010b04007084158869480700817900c10410424001d030042c00021050708200e0282c1d600328500041c2c040002480822041c022950800b0400051010780740090b101c140b12200203a9540c802c00040001500d030f261482c180e5009103000051600c124a80b807000c0c0c0d0300071f405c281d0050b90049409160000e080c4040e42c541d6448134000c101c1100e40306084034083c0581c0003c00011f01011090004190080c0205800500f26003003054204440c1c2c50324800c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 756221357 1250 756220107 756220123
    0x2107020f0603010311010c1401180b010909260403021f031104050a03030804020301091202070e010602070f03120c2406151e0e0d03111606201905 64
    0x403003461441510085401e00c2021241a079070445540000031540100556034508400300c04c4581d001843e03008032644201f0711810780a0300b01d600c8410081400b80c1884c21840310180c0044d00410b01d4003001c800002d0340c400040f50003501c1c03841d0703030045240380b11440c40f0507002e0f65002940000c0d5410143c040d00c183c0d21040c601812407510100f001301095a1503c000d0301880c080d00d80c0245244201b440460702031031001782d10610060000c19100c1e01952000007003020380d202c0d0070141c3d000c072030148600b0341c4007080300780075061a10003848003a00d0201c40c242503040910014054103440050a6002e5104010580d03001d500100d002910500445020382069061520700c1c44e99858007202050891206103007900c1d4000356039805d0351403100301d600e00041d0b20000c8908018044144d4250149071150100301c881c03603000b030311401c1c1d0846c0060703044c606000c911400354580341920103062080c142c004919442031948442000204140680002c1c6000c1034104008210380515812404004000036588 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 756222607 1250 756221357 756221359
    0x70b0c031f03020114090f0604061e0807020c09090a05010606021c0e0a052707020604020103061e0312110a140c06070c05152107350702210702 63
    0x5400505079907050445104a40002800142d0241c0842a100700c01c40250040c100000c0562a80403505000a00d242d409680494003045090841a50030b03020400c0310240c120890508085c030b0325003500000d45810003610014880c0c28600301141e90f0365010030591103a140d00500800c41c480d2680e20195550b070741d01d5110101c0500004004400c00e1107007800c4411082d01a03c1180d005040500b000111030b00a2131075804c1c1800b45006c20059081d0510460060341a50003601710703401e250000400303550701c6821418000c848070250b04441030b01080e003001220f80101e010304207404428011504400150340b1403801d80700c5e00d0020400c0c4103d0010080110b06a482107e150f02000814001240640200907144052084040100b8200401c10507600c030000031005160044900032810807468480c00041f542180c807042001c1103410942030303281004202840c800c4030f5007014a000001917000110511415044042400d6038001c000f6096054000c80700c5800c6a4031a55006c001600903050903 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 756223857 1250 756222607 756222631
    0x30a0e0a05010c0c120203010b090c0403061416200a05071d01050105041403070b0a11100e030a0e0a03050601030302101401150309050a0b0c0714031815070b0c03 71
    0x1480d507025250030f403582a404582c40c02140d140001000504e81d0446080e42c25540b908506002c6545209030680f0503648191403540351410b5003051402c46e0988091060341d0310403902400411100301445070021243c51500c141c802c007080250700035001440f072448042c3d01c61155060f0402402048040941e488140305015884d03130b00071600c84014007840f510740401d004010500007020441588000608003508070341081ea5550308104440d4851030000c1c0010701d200c41904006c41c018810000010501002400006030f00c401035601ca20841410700240f06940700d0010142c4c0f03444a60030011a080b0080e0350300340d0307940d00b0080c0d20303955040010300c0410314142a52400383c034185a07450585240001c06485501040d400b54002e20901000796014420040c10f00f000400c00e5030320138400c3c0151090182c5074581450207100300b1003603d50910710b5400500504170f8400f03c07a0810818610100d07440003041009402c81c400c1403142d00e00180a80560804201d001010400114020440d036000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 756225107 1250 756223857 756223859
    0xa200d0506032b0207030c0f03120309110f030f030d020310380c06041217060603040b100905070f090b0306090a05070306080a05070503010b060304080d1d030a0e0a 72
    0x8041e00c8403102044002d0303c08001842c02e9034079400300c2d00c0007211400d078012220b00c143c40c0d44a0595101d4294810302e55169080000d204100b00000d010f00035150505040c0031382c0403a5a034009095608480490003101c542a4001865808208400303c8030001000c4c1e85c0d403040e101c540000698412a03c46890809401300011049401d401c403c46012030071640d56030071900315051101246401e03a61150300ca83c180214004911b0600445010340c2c4180344005c1c001085c260003810f060030344a60386c44181e60007001c0120648601003140c2e0301035400341c0e1040c5660340d111000081c0c00da980d0011940140b81004101e070b8641c21084104502e005604e59001650392540208514401210120381103511200410385600043c2c0040d80c100301719090205000c1d880707400844c54203118a40548266020140c00c0029083c20300c6001c1e140e44d4180e0b41c03075145180a0b00d412102e441821064100305585814680403050b40c401c6194602240c2020781c4ea030b038807094a0090005a24080a500c41c040740a8 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 756226357 1250 756225107 756225109
    0x30b0103020a1e4b080f06130602070503030a0f060b030103021c030e030a030512070c05031228020c0705031f11040302210705040204030b0c030a200d0506 68
    0x40c210805911043c2071001c6500b80420900c0144080c01c01c2d00762003001d640b13445450800c510032020400141c0d01d080d40061034041a01c54104204d900000c96604500c044044108001c6a2294080749541ca00800050315141150080c80340b42405001fa01011003031100c0c11605402807a0380305c0540106000c060703110302c00440305120a200096004040010a00303031100b401c0180350300b180c02800c140ca002d44030000443c3c180740d005070007100003810018840344801003d850f01d58004c13480c2d1500b080340c1000c0d13581c0c4030f03a04c0c4103510071003544096020015861503000c0944040c04032411110b042c01d50107900c8841c010303402c103503a00705140c0134201000c5080d00b0002440d03600030314106119007203403c010744e0317090040580b2050300c044888108030120260716043d40daa01d178803c41d2007440da5821243c1d0f028030308014a0f50000c5110368010402000400c5440c0b21050700a02450300c02c650b00e4641135148402805020086184e00082115081040069402414007080005420710895a03070030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 756227607 1250 756226357 756226379
    0xb03010f091406100c0219090c02070f05060f07052107110d111e090c070506010e040827041d0d320d0e0d0e100f03050604090b01030b0103020a 63
    0x260915007040e644466031803005c0c415a25194054000307411200050452001c4101c1080e454004034281919403000c49070941d410403100000f0a01a280202017604100000b143c604c2110f800c4001d000d000320381c9106005052100342d1501c0000d00042d04002c0c04004071215941140c101a1030140291000d280315081091030180003950003280c07512480c09460800400306000c4074419a20108142c50042503159444441d02500b00c4000c1f164945519191061400310140c00c402a1160103005220005403c0300a48410150342640c0b00d1644540d0303c4241011104040402c3e171250070283e00790840034007492480100d500c100d0a407212036801350f1090b0b42410410300a03c07403140807034030200300840300e2a8140c0d0600c8046041e0134a04070191840f4825220048250582600f024072259804d9810203680018030030191055000243c0700c1b1805004211014205803e268030307103000803401c0e0f840b40d10061140c0c1c1d000c100702905503100c4c1003030b04c8104000d00040340104070142000c03445000700 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 756228857 1250 756227607 756227611
    0x91e01030302060420130c020c061309060605070302060a0b040e1603030e01020c0a050d03030b19140103050702030d05040213090b0a0b150301030f020f041d060709080a03180b03010f0914 82
    0x1900d03681c03a203c0c1b400c04160017001045056000c500031081c01211607502d501c000c05180c41540e03030461055083c1003800303044071410360003402801020010317500081c1d00466020b41c0000461400601080304070042805000d182c0e40c290383c18060905080d03880050004000c05882c00781c0d40c4d95628003012001039a50b84e490079106039203c004120100454545140c0c000c0d1070b02c1c0b1074503001c01c5503031843c0b000ca021101c0c0032080030306a2103803132420300c440499120b48015004003460b090245040c44017020751a0b2041e8010f042e811910307080083c042d0b403586171690001c0e6101100801070800b003420000747c0c004080d20905413076070611005a5480c84c0003c140242c1d80c40440a442c41c5902c1c50307680340031031040403800300e03000501d940900d50a55101d20a03907040d5504042e806100a45201c0c8450074114014442c1c1c0a0000c8040706001c60031002600e110a298503050a60040b0b0b1a1308081030140903e07030080e540d8001c00000401c4805000841c201281c000d0041881a41c182c008250001402 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 756230107 1250 756228857 756228859
    0x606090f0c020f0a20090412030e0102040302090105060a14030907030302300a09180603151b050f12070e0111012711040504051b0307030c0302091e01030302060420 72
    0x100c010200400c03201044e03d204224107600c83d241070521701001c45d200103c112000d03694006400c1c402441e9503090b00a480c0c003c9507100c021460b2500b507500082e0702210600807940140000b0410740051030181c0c00c18040f0443da941415102c0c80c0c0b441070aa03850880340402c41c0107004000172180240a4204100000c000103c03043c440c0542c0c203100442c881d080700d11840104100000c00040071034283e001e081f04001000c2022450600352704003440b03545030030066400110300c1d005400c1c041031010041c00100c120070b4a803240c1c1e111a4404c0e10301280c060704908400d441d510340305210740a50001000c200d236140c20b8840c140074074103121125089034000e1102c1d140d40006001c800800301aa0b4880c1d0680612540818613803508601c081001c03a182100d0031030702a806a1044400401411440b42040900314004d00e00d1608655610854440d00c1c80000d02842c4040c001c2410100e00361000048941c103001108480d603524280295901c90945050350845211800d6401030044040d0311001803038 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 756231357 1250 756230107 756230113
    0xf0f030708070201091d04110906241e0705210405010c0c0801020712200c06030c070506070509040b040207030f080a06090c031b0f022104030606090f0c020f 69
    0x15207640020303a100d5141281000182540441d01815100f041d502e11a41d8103806000b40c80d20b46031030300305402144800f41c0301e40d500d4400c1160541e0b400e401600d07400500c0040c0b2080a252100d459050300030b114001503c00d11a081d10300310b08502d0805042c900f8040d030304a6000600710080c0341c0d680d0000c02d81d56003409070100028003540d402515648030035807107031048544c038035039440a490032601304910840340000301e1036200641c10b60003103132254903078544c00c01d800d03803a03030006140c2e0758949981c1c0b14680102000300c00580c0b034210540594041c10f4222050b0782d01440c0260000b041c5600208020307104524100010141d03040c10720036100c0d5564980c59030060b030803400d001a00c40c048000e0880500030b03100c10004c0381140070303401080071005681d01c0c003140700c100d90307910f04200b81c0303000c001d000030440504001107401d58001440400341c1100c2040c100c165441074045036143c400e58001820103130030100e0001c0d044610340e01146480500c008100111a44a001240c55015000050907658 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 756232607 1250 756231357 756231367
    0x40501050409020715020c010c020c0a050121110712080a05040f03050313051b12030f03190b04020f2502090a11090d030806090705090916020309090a0605030f0f03 72
    0xe40198000c00b1800d0040180c48917000240c02020103913401816115041d0f5190780041841c0b03901017004d400485000c84003000e030b00f81800d0000b442105050030900303282009256213a18442a139103d4030a41390103d14480c4c0d91050b031f080005000c8440354800e0002075954000490087c02c0e441814052680114020488010783e1011039840e00003500c0707560019601042070000550801038080f00c8000c0c02121030314110780400b000307650082c21a150320290001c10007881c542100404417540201c000700100d0f441301c40030440c10b0080081020b010341152000031b0884180c070b509005032000c40349103542101c640042035800104d02d41e09000c001d40000d05480421810280354000d2920391803048001da0802003020001350702040100016000316002d5400e100d42c4d070500e001059070203d201c1c184240341020000114100600090080c0180340700d07686410400303407090088400c1c0610080040c556410102144001492144070f1b142c8203204039410070100d0040894001d521040311000b0758104 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 756233857 1250 756232607 756232619
    0x12070b07020106030f030c08130906080d05030f0f13060501080c100f080a0f0906050109020702032a010c170a0905031e071e050a06030b011701030203062a0f0d0b060405010504 77
    0x6500c0e4910f080388c074440148000750144c0310b21000341e40203000020000c90450b240c50004c1e81010030b24246803007002800c008010b002c000d100b88681d0000d1160002e070410340c0e03170f000b4480f042c090305200040220f801d01c0d0001400030301c0050102e2107260222107003c2000c00411054802850b0038036103201060502c03000070b641c11580c0d0710900440404101c0440ca4103a00c0e9122400c9507804d811000c0c0e50b9034049200b42c10b5007407c10410450032081e201e07200d59040d200e105601c09601071039055040000310b40c6400c040000d4104954100103490401c00d40701c080725030700507190101c2c42c0a0740303001e8843c101c4c4180103c07412080719103c0359150301c041d220712401c110115103810b40349501c0e921032411040300010702c2d0300c1d000943c6000340b2656400240c0303900004001412002c101c4034034003c0b0400c0720300500240c1e801140f8550018014800c001e8042210482e100303d000217200b001c405080b001c15071480d074032101001000500003204042049042143c1004064083ca010f1035002810a00c001d0080d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 756235107 1250 756233857 756233867
    0x90f0f100207080c121b0402040503030c03191803060207030302091305040b070f092c16141e070309080123010b0c2d0a0305070b162f12070b07020106030f03 69
    0x106c110003500140c40d154498012a10b940d112a00c00402030b80005980d240071a00c20440801c4040c6a1404608070202017a810014898030300019002d580e0010390703601010300941c1118512440506012800e1810b55083c2c0010501280c050301c8400406000816540c86000c2100c52044030703441d000b001d14209401d000412050300c84100d03003034094211011041c44091113440c460701070004501c01501340031800600d07010560300c0801c68144284014501c2181b800e0314001c501200308078203512010304e41000c5480155a0f440f144065284c400c8580041015881d50328108003082050359860341c0e1110350507c00c0c411f0000340042604401020003076004c180340380000101c400503000c0c1c0c4608540061a0070121000400c80106100045203001c000020b82c1503039210b26030400c96006505040c5014004078044401400800c1440007240c2044100040c84484040b41004960711912605082c4101f07500001c2d01f40d403841c421400203250148140580c1d0309883c1e01c80e40720800074016550544e6 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 756236357 1250 756235107 756235153
    0x12090b0f450a020402340b06060a051b060603010b0603061804081e0a0e0108061012020d06030b1f06020d1419030603030809030f090f0f100207080c12 66
    0x10040c010030b000c0300056034580c00a00815910804000d101020b5074008025a0742c0c2c1419200c105140b120505022a110500140d482a0142d0f8600e5888900a00849107071084035984092990800540c0e600001c00090061003004168020401c0740c00f12400c221903400b003203540c2e50b8054030404040d00000d03500c884868010b481102c04600300000030922040500c08900d0207101042c0100c0c0075044660300600c01070000c1400e0070200c51034105200461035240c848003401040c0401c1a80030f001d5491540d044808449010008225082e124030b4184e068000554180c5420045612030340000d44207070320030201300c4546400070200400e50200a072187c201c0250402a1190107002c5070b001c102c0c0c81c8085880044c1c0d15500090020704600c3c002d01418005045084d00303900901900d0698117004044980d505404c807070480910729020300041c03c1030791031a04181c102e041040325502c1d8940015172101900c00c2c0d04161004068085c05108919810156034941c6a000050050101300c6201da048 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 756237607 1250 756236357 756236491
    0x120c0913080f0a020f1e0c04140609060a09090b010306150b04031b0e070c060c020309010c060209060d090308041a040f08030403020c060408070914090a0312090b0f 72
    0x7a04429242c0401806d041d060281110740d0100c4904101c0c40c1d0105002c103070a4034034221001c000e40c175849008400745050081040e07000d046c5240100d180c1f03984241c00e01c03005298001040c000b852007071404a48000003071004481c10b030b0610f12a071009030030034402c0ca026034003424103080c205403a50700c0d01e50201c0c42c0c00c0d120140e00c0315120804240110403680851140d14280c5030780301040700d24605101180d500343c035900219002401300c0e400ea0303030384081c1e0400c0c110f0708040302588444112000030454070070740741c031100448d1a24084a0406401a107030030720403070065146100b00c58203003603451240c0b40708440082800c40095441d07000202c0c28405183c0190017031048950704094440402c0c140c0e0310540000f43d1303560009001308182c0300a805135403841c609104e4040190f0604004140d41c0c0c003031000e0010309100800107011607a1106911082e0031036040318220186040aa149222088080e201681550442e5100550390820302c10f4003489640f070001002a1040e004810001c910010ba4443c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 756238857 1250 756237607 756237613
    0x10f050403150603050c010309050706200106080c1306060f1209140c0307090b0607030305091609090308010501051c0b2205060f032118120c0913080f0a02 68
    0x800030482d04298101c10360103035400001c4240c2181881c604d0011002d01c503604060600707000000240b00401c0715022581c050406014014003941c841070b00c22800c1c03903106620361070004006107200001030320b00301e980002d0795490b07484105c040301103040d0344040c055400440c20144d03102c03040901c031f061385904242d1015800140002c01d5a0b501030b0800d03190200848039800411340400da460b01344840c2c0c009142d1180204184038400021800718007440d10090306040e175642c0001e20480d4248004045000740f0917221101c0c2c0d85541d00c0b803009102134a001e500041c22100003107a130354024002c50300303e100551038a681c82007050792000b0160100c161030380c0d00141c5070084054034554400d500c0c1e41c0f03e00f030000e02060525203c41030150080705650041d12030341c802c14441c0101300480880d2203110f05403105103540d80c2590310119080d200d030340000c40d4000c0080d4440001e00030380401d201400c4441203c1c403214a0304c80d50743c100d44100c2e03140300c064900394007000300300c12105400004002c090300350b0040e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 756240107 1250 756238857 756238859
    0x50a05071505040c09060b3603150f0109021c0903120207060e0c010201060501050f0a09033806011407060b150315040c080a0b0112060f1a0405010c02010f0504 70
    0x119005480d030a0b0f80c00c441c0c01d840c51505208001050141c4006040d50051003424a40a0b800305c04000c2e000c0c0020035040c90214550806c0301e000c24040b01040300c07014084907102480540c1c0740f070b4020411a2100b410411600010640710001e0088441c0348030b040801c4404d2407800000c0400805200740100c007481603007441090300c15142d00241ca016400b880300010f1508501100d1420a46101040b50443e40351040500003680c1000c1030301c02c20140540c41ca904c0d001e10070400c1d1011041500003410040c85803c0c10960020102001b42d541d41c4020140b5560700155403812940d1003043d031702d25012a900d1101c02158540040240545600a4401044040800c4e001c01c0d901c0d04050400081c41d9800800c101c400070300700300390040501060300e0130081c0d009400c000401d18540039000d44051a15545120300580c4190340d80c00c41819080010070805656541585a00a46100e0028446412403038003103455800300982c0c0c02c598041e11500c4010892380c0c0111168440c3d00d0182041c4502400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 756241357 1250 756240107 756240143
    0xf0603250201060501090b0a170c0f2808011a0a051303050a0314041206020f0d050903182e05040f030303020a2007171005090606150a050a0507 63
    0x20314810880503035000001d03141e051000040c00b441181d0014440500c042000240346030b48040007102c400c900e26507407401d545030650b42d00f103280320341c0010071120000424201c0c5112110340501080ca0b4070816024078090109405444c840001d01c540c4000310301c0c0410800720700181d80700820003807029280a80c640b030045025065a100e42c0d41054485a05c08040c100030150051012105480c4d030f0b0680c42d0038280b4200c0c181c0740681180747c0081100d0b4004c50740003541485a8107540200c1068a014040b500e8001203039942c2e40c1141443d14a481800c54844826040000614000c0154040d0800401002d1804501e21140015a45042004c2000001105080d2030fa075907011318807030f5602503624417161a005003611040111000302c000c00e40b01038051401e0001d203c9048442c40041070945a0142d540300d82440c000c0c240034608282400104143c800021404900c514821200f000042d80c010801c1c0c209402100b558030081642001513a41c49406540503002c2140700d400400f0070009014 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 756242607 1250 756241357 756241411
    0x1504080105010b1b1b01180308160224030a020903070b0301060914041b030b030123040c060507030912050a15020309010b010e060906130503030a05270f0603 69
    0x68850039400001042a908075114200d110340310200d01130080a0300f8103440f00125030f03080e050b40701c00d041c01840403540301c0080303246a4640085030040c5149407620200c224240d107048000c081280f1800d03c040422814405141220007401701c0c8108680c151780e203a59421000758041c0d8100c2c0d50500c9900c10014100d080345c40194060102039607a0f400d014600100c405000d0f6100e40424442c81c142960704e29000d500241c181d00385d00321842c0106030b900744400800c2c014089102e49141918020484801480b000d102d0140114800c040351401c440c4e90703a20840c3d00380100c03407000300050030b54142008040005240781c0c3c4160f0250040d240081a540d0f900444458a00003450070550040100000407030284510740341c0354400e0800d0754440c003203c400140744d4826103409500c20500428003203885092409494081c000160031280d9071701d15140050156040a034286111110141600b21100f100886c40201510040c041c6080b540d001404c1010310f40004040c84250f0340074940b1440440111 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 756243857 1250 756242607 756242609
    0x29030c04050a170106120308070339090b030105061209120a20060105061e04090213180209060d0203070e04090c0f0e041110020321070815030c150408010501 69
    0x1d8215800c002ca60092000d09490f050303070000081261000081c404030388c0081e0080c2e4001918500001c15401041d0f0f0560505410382c140b02040300014030f132002c064401e540740124071665480c1e5a10340d554680808000303100900542d50040c9083c042034010000d000d20044c0c010021405032014411181c071501d155820548111000070008240c40c08030060b14081001001c2208001d40907030343c144000315000384542801e20b00c0d1083c2c0f0103800705110800c0350640300075241190381550b48842d82c01100604a203235002d14030190b2041903603c0380030308041c0300b1a4000140900799504250194403414000c3d08003d0941c3c041c0030402880f00b010350b459201d00c0d410b16104d80c41c10010581030002140c5400780e41d8006aa03128010800d000c007141460b03103210308511080f00c00209a8809540c00c03030442c060341081d101f1310780c00b036501a40c1903140200c0c0641b0a120740d98030b420899446803082c1d111040c45c0026150141c20000b261026410310800c2c2c3d0381c0361654200078074a803541d1660954211703802 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 756245107 1250 756243857 756243869
    0x3170408062401110d051803151f0f060302030a020702130614060705070509040503090d150f060b03191b0306051507020102060f060d060203011e29030c04050a 70
    0x52280c214211220503506895400710a113401100000e014400d59942c040c008154014050041110042e4180c224090818207201030107131109a00b100b04800000c0106561440e0b011401c0b14071070380d007000d40e0400075048840c02c140b10b090307032803500406078006e60029000d5180c1c2034003045400c0240e1510840840310700b094030000200d95217845103c3c00d145800c0d1160b03a100e01d00c10031028010410016280041d0f42c41200c60100079140c500d400c40c954072847c034045030170680aa41110a0003082c000b040c0c0b040594806c06e02c441102070100c002110028007035041d10500610211304111403e504c488481c40c600a00042d03c940054205c20503070021801c8440042d4035010300b80582d091100404c8a41c105030000d003400d1055650020351581e1000b400c800219041c90700060682d03554181054055400c2042150b032941c5071007510003a20952031683c10720030380d8100c00141c881c0090700240380da220241013620b000043c40c09044820782c030140440b41403003028000400d0507a104002d050041803 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 756246357 1250 756245107 756245131
    0x1060e041a09070f0513020c0d02030c0c03060f04140a050115051e1503040602070c03030306140a0810110405031005010e150102060601030203130606030c170f070317040806 76
    0x920904114100100240340c0b0301c441d000400e041241000301c4c5081d10903581d003142d0345445a504000c290700280511105055248202608110030780d07000704c010301c9a1380d079510564440c84120b80c01c3c10380da11800c4d241d505422205400040104074602c002c10303154884281074800d014450340b42c9900755640100000711600d0318090400c107610f0101c0406005414440940040c84010400240501c0e0040d1800000160020001d0100200d81d411503842c150300c84034200e00c40e5100e060040050100c0d024001513500301d400c1c17401ca1440c0400741401143d4980e001060001101e00c0c00001600c58a5910f8000e00742c148400f20b031030340d42800314003c603004182d0009019850200d02c90105000507009142203c0408a026210399000c1403950f4050b40070b08016950340c692114080503041c005801034001c40c074000d404020418040c00260403035000004040403400c1942480361140d00c0108400d0280d803184d0000c000041e14903d2500e070030b00303880c03c225042c9651064403500b84101103982600c001 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 756247607 1250 756246357 756246383
    0x90507020d030e0a030e0a03080309030409050f091e100509161203050307051606050a0b04050a0c090e06060417010236010815030a0f060e01090b040b0901060e04 71
    0x680c1001901c9003042146018458111050161511007000000190401281164000b019152038203110f008650041c0d4150b500d10f003034416103840760031a001e0320200501b00390110f10002d80d150701d018050040d2034084c00742000b200c0070009800d40d0416030320030715002c0d40b221040d18a10314405c1500c02c515000140410074114580c880b4105080e810240320f68004100420210f40e006041e0b9502500c9820419a1800a9480c11900b880c0c1400000d001c1810300d0204161010103401902c101c02c2c00340c40a11040d01e900c0315440c15185102d0f40040005c0b100941040980440c42100b500040041c0c0040e242c951101c0b1035005590b041c10702e81112f40c1d000200d20255404141d80320080d80421076030f0300e0708900c004001350052110141068100829900421040d50000c0719015a080c4024121035200c0114a00541519106c810036038519240c24800213010700c040c0140c012a60b4001034400300c035580c2d81c3e10004a8140035100700940e641e10382000c21134910403003009000c0d03405041e00054503 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 756248857 1250 756247607 756247621
    0xd020609243702030a110102250302391c050a0c052e2106140d0b040305070503120c0705010f06050102061b0d0906140106090e0703240905 61
    0x381000c0000c445000310710012580b02142d021003900c00c4848145000c004c400d41d5100440d0180c00740159443c0d403907464840700d6030f41007003200990115038860f8080e2385c0c80299290031400491180d00380d12124080000c1d02c803000d0060400240c8900314010209600900c0041c1401440b40480004407003e40c002071403070b800d120901c1c120b200144001c4501082401d85045400b200300c1008010345c980141d142c1c1541509402812854402189994121400d00342c04a20b030010b00315900c9403400c8001050741c5503403282045a84240707920f03008102074801d0385139540e003200c5071ba1000400741c4560100b4403142480031503290896000d00b4a050380103403034015900703060b4216501c00d0500746901d882c1000811480c0d802140b1954000c40900031441800790400c09410320303100d8800743c04255881e24041c841000901d900042d03041c0414000b20709103a07220780082e245100c1900426120009400c0002c103018466000362401032540c4413005008102d440518642c0d88054101a200301e0b200c20400000f = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 756250107 1250 756248857 756248917
    0x126010b12090102270111100c030e070503070b070c0e070c110103140f0a09080f07030306063605060d1b030c17090309131a0d02060924 60
    0x80b6400200861601007802c044040070f1a030041481c040112648020300c00c0c1e801085c0d00c0103441070013401d494038a901b0010384801440d142c03e1660100c2c2c60500c0d1010b17901c1c0d0000c0d08a050710760160040101b54242220002c0c1500310850885266042e444041100704100c1030300d5005540319100c41a11044034038007000d01c5804044042d0405180c150120350702a6216031540e0844240400041a40c4805103010003038411184090510f8200080c5894541e200c84014074200380030759810846d09455803000c54808820382c0b030100884413080d10000392088c01411602d10506104c020103201a910380110328150043c01030030182503500c290484481c4580c0040c150429040d10b000c000520007141d02800420b80e9112805024007180300096006078100101c0303080e100f0042160742e111501c5020400584070703042c026500c940c80f5050707070703070450901f080c41138a80d070b6000b886281049480c4041c0903044540044e20074092801d581103251041c2018020101303080501c5c40c0c0360190329a40e103516030b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 756251357 1250 756250107 756250111
    0x90b070b0c1b03090310091220030a0905030d080f0a0203071b1104060f06021203041a0f0108070f0b09010509130c050711090f0613060308030109060303020c010c020f0126010b12 78
    0x245090034090040d00023600e803503003045a11103a061039000040041305204115030300c400c1c0f1010754400003c904140c07540024040c3c2c210b800443c1190f00c00c8030030800803103c0640954a03400c441c40c5400c0420400c6810fa0003840d030246852038540c2c1d03070b00c441d80044280f46940400c00e540d2181145040f150360700740b50244002400081d00f10131903161810500a542d01c220a00c4200c925138048041010000c1401400308036418010442d200d6052404070002549800e118002061180d035000151000031651503408171603a0141e6241446420001511103500c0800b0840e8499070b0b000810301c041c0d41da44150b00342c4080700e80d00c403034803800c492501041c0e901c08200100c1c814800c08003080500d4840d1016140e00c04030649010000c44516604880909155003000780075503400700c00414284259030206085a02039400ca990300c41c851001501d0703e040104000c1e4110301000a0305d0f07295400340c40310180d118919900d09a02c404020782000401e00280c220132704410300080c0607856080903440703030381e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 756252607 1250 756251357 756251383
    0x1b0905071d0f01051806122401091512050f0105041503050a0f080f16020117270f030c0d02010507050406080103020d0c120b0106020d090b070b0c1b030903 68
    0x20500580078000624040c48099807207040042c001406080d5400c100c2510280d41d0f8040c004645a09080141c07a000b035004581c800301041c1d04524040c100b20b240310480020300300607165504464100744881c00112010b084410a0141040038000c0d008024812580b003491091140b48040d4105401c02c015a80202c01d40b40d600c00300808140003044012400f0181660700840f400c04041c1149041140740c061081c1502c1c00c1140402c0d405610f1500d41c101c0c1c6100c40c0b0036a01d60000029403941c2401c4d00b0001d480c50440da090360103036030b41c5180e0f0000f0300004003c00c01040303a45903010491140d2075a48002c0450358039070020008900800c0e024003495030000070f2800c2c290b090505002c0d0040103e441484003030300c81c410b050b403641b0612003510710781400351980740140084100c0302d00b040c0401500a20070b076001882101401c40b01c0740d218008500545030859401840e11642e52580c1d04685d002908216494100b0052540c0a80f205c506404c0716442d1113000e0f680b240e250714201410000c0224210b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 756253857 1250 756252607 756252647
    0x16031e0206190c170a0b0604060f20030d05070201020904110d151809150f0905061b071b050d05070f06090f050103050717190e010b06161b090507 64
    0x2c4100f4582280c0d00c58081c0c05030b90501e00040c0c0d1411181c802914542d80105c0e04528000740108116903c039840f0540c01e82c017512810b44400d03079403c03190040b400c855112111f94205105680b900b205541069411160901c0054140086d64001030200c6407020004402a0b50000b0910714100c01d5014483c11754001d03501743ca071860f152034101c00c00c4d40c0102418000180d0703035107014400c202243c11454004102058108551a400c0c1c8030b060091004982c1641e0503c6102c00141e800250000b0386c0a144001d00322103810304040d6550120510080030050500701c080610205060701c40305c42c1800300702e00600044c034404d4907020140c1c0041c58142c003c0010000c00310800d001a1440c020804100c0b4801e103000601c3d42e483d0402201c1416240c890051800605000d000007216680e004015149006100300311600404044a080314100e85000340c1000f410300c001a201c07080135141c140130394068208103282800140640354038601c3e07600b00d05021991541401103159000405111400c032502c16 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 756255107 1250 756253857 756253871
    0x60617040506010513060f060327020a1707120b1f06051608090301110903070e040b0c0c1504050610080d0207030803090a0204061517010b16031e020619 67
    0x503140c60b40d205010301070198601d203000b400b24000035440f80c2c00400d81084000c0340303035845440050207004a000c107081c001d605600c89100c100300c5000100304079680105500072182c5008400e06c40703c4200703041c1b00140d0040784c600289094a039141100b10302e12a00c0f0035000340c07800c040c44a4142501190806046480000038016141c000007102c0600b2564103203c030211045140500f6644140d5441c40c0e010750030054040c99003140140540280007044050ba4481911111103500310002220081e1100b0080404907081325213280060406103e0a025226107811003030151000d16010349048907680d001ea0200b0000303400011040011700094000380850925411000390b07190081c0c040580420000004103d90b44401c0207203c04143e03001d407050142170703580d80c0d00b0f080507000d041d80310012030039000c12030240c0f20b02060350f075069900950490b410300b032a80c1710020310000344420440500201031003e411142d00341142c0000408258010301d414035046810401c4c3e011403070307040303682c00d410000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 756256357 1250 756255107 756255113
    0x501091b080a030e04061508060a0618091116030816141b0f120408070509040314091302030103110114190c1b0e010905090706050f0a170a06061704 65
    0x2249000301c3e07010718003a4804c5424000107001054207a120500345217811003102074180d04211194495401100c48074000d6643e403c040e01d604102c20585503e0000032101402400b842d5030081c20340b07101245103141002c114244501035036030702d460f0503070200b04880200300c081042c0c1c203e50440d840503860020811802c0c00c44079040f44c0996500303940d4032850242c01c402c20800030000030144035196001c440410b054034681058642c003c0c05080c40718040d0700404259420704aa105010700c3d495580d00310344c508001042207503038204482c8103500c0300f000400050030040c1341c0040c41c040c5008541d6480d2140c403010002d0070040c1c00041031807681ca02442810b510b90462040700403c0c071620304000420000360710704145c030303041c0010380740455240c00d28000c03c06805103d04181601c200e100104030f60f8803029041359407054940b0078400010300402180401d1020000035001c0d09066090078000070103066039540017417404071580741006944580030807005074841100454289940c6a541290401e52 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 756257607 1250 756256357 756256363
    0x1e100b01031e0513050303010902070c1502030a0c06020f030408091003060e060d020604120609120905060d0c0c02030d2309030705010e03100c0f080711060105040f060f030501091b08 80
    0xa125015030b242c2d50700004142c1c821301c1c0c0380b510b03803554032205890383c96031283c1080b0000d4101e01003c1c0c1300940d001c2d0707020807400700408031110900d50a4000354100f22103d0800c40d83e00750860700445801d9000e000d41c0c07103603501c0000031314001e900c00c58046407507515117018081c01130046007800c0200340c14200d0800c030103030507448110b030081c00039160303c43c409803e400841c029128030b0740016054650a103031007080c030a107940014100c0384520314850384810301e0001241d240c21035014466001c0b10801403030041400b81c0c0d0002803000400c2c00c22061060301c5800107410b0100e580c5018020a4007a43c1c60308074000b51100d400185120380012074103100c403660102c0c0d5503141500175181402801300701e88900380d808128800449610403810702c8030781d103c4e4000500c1c3c929a8144d80c40420814004103038582d008210082805052078000c1400ea86400c041001900d400c040b8482d9a544d9017901141001c4c100304450041c601400010416000c985007442c41017040c6c6804210000080c0b9080c04690004 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 756258857 1250 756257607 756257651
    0xe1f0510051009030c090911030312060103270f03080106020304030c0308090d0c080a050d0f020d08100812090306070e090714090405091e16060503091e100b0103 71
    0x1034031880b030807001da01c000340c441400310340003c0c01540341c20b2400600910150410022548070f5400e00c40710454030014141e8a00598a52404107085100089d05651003070388000200e90410040c06c0020508500641081070084130903038495029030780410a0603080b151183c01841c8030701c01540380130b00d1a25503070501059404010035226001072014541e540e6007144864079604802e00380c0b14690707104190395951103030384000c0b204e500070725403062813050060b10440c07003241035600178050b42c3e04410350490b16410000c1246185400c8000d0100d003444041005505118214102c241e854510104140c03900c440140308504008000012521584030f0346425030f0421114104007001d40364480b994484c0e802502c81c419005807804003081806100081d501081188410140c03400b0b490003802c41e40c5034001d0b90b2181e40c03039400440041050500c120b009503031085100094981d40107188405034150304010044080561200395195001034207481409456034090030204441d44811007100f4071890070b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 756260107 1250 756258857 756258859
    0x5010e1509100e01060c06230406050a061e080705061912091b05010f08010308190210060e040302070b0a0906050d0e0106030b071202130306020f0d0e1f051005 70
    0x85107001c520302c1c488900d000e1014040d5a40340d00350f9503031281402480c4c1c00200304103848003424000007801b81000c80d003802454102090209107240d40d103407a0342000d0a0040c000e1000107655800001707420815000d800e03c0008100c024007062441c101c1d159280c15280e40105214003000c10555059150070101e00d0320581803410301050040118000c000103190001c0090031120880740803030f1040c84107919101c01c3d81e5098a03a030345c8030150f44c0c40860300842c6c02d00009001a0082200c10940b001072010050b9440461040365919000143c2e148291764a5a01900c84440032000313000406405105010107422441892828568541002884550503200b424180000011039081401c0c1c65005450100500390003408080e50341d2812008010013195280c0000304e51352965070703a00d64940200d4220484905203403940c58115103803a00298402035441202110403c01c00807800c074140260182560071401624107000b02c1c1e100e1030f14059001840001c1c040c508000c10146050f141503480503910 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 756261357 1250 756260107 756260119
    0x61202010c050a0b07022404050a11041d16150207061d030a140c0a1d0c0c0a050a170304050a2612100501030b090f1b0313030305010e15 60
    0x10103003842c030304260329003070041e00d100d069008000100b0340019400941e031190410200102280a44508400d0b13415600101190460b80081c000328139a100000085d240062001892a1540704803060098611011381a1a00500c1443d042e20030603503102002080204181e48a02104030030081d100c2d800b0340600c401b4400b425411450001044010400250303018048503170100325404d00d802440120b1003a1a11841840107090041c180449540d0854000c803c031031440e85082d40c103607940381000500c00c0c19448001c0c000341e04060310402100c0301e02030060380a030441002c2424008004800c840c002c9418940070000d020009000044a04029420007081e54241003501c00c42d840a000c0e4030703800c5045c404042520440680701d030192a004500c206110b001080e40c3d03000540513503d483c440c2661248840c0700240442000c1c2007104d50050441034990307686403050707402c604250401e985203401c000f1158242e03010117416201c0d0314090030070154200f0302c0c2d1801e818901d50280c400350703045002e68 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 756262607 1250 756261357 756261377
    0x310061d0c19030905060601180b0f0706110c0c040908070303021c0204170c03070815070215040308040b151309030c0c1e0902090306040204090807320106120201 71
    0xd8128058526503800c9902d1044050103035040140940001c180c241d0311401000045591580a1501402941d40d40c5580404040c0f9041003034030660000c00380e5400740b00040000c03100103a03180c031451440030b045251894031400c1805010380f600d624034000c140160301e01149000400e1460303060b1404142e1500d0096942c13a000d080640254070158500d80210703001050200e200e03811803420480c010508411200c450513103c5c1055600d400700c1c420803034640c02039085040d40764898041503034050302500444070080c2c040c1114400c1002c0c12601030b00004c1e054001d00040201e03542d1241d400102c99010380090140006c00034054480c40030300041d00e00e070b607074560a0406002c4e042e07080341c4036000050700c42016510711014032288410210344015540d00180070590034030610a0310003205001e00241a199500c3d402d00005004c2c0b000145d49490044c0328040010b01c1511055110200c0745840500380d0071401070a8500e000c0056900944da41842400c0c89440103c54465100540918082c0c5083d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 756263857 1250 756262607 756262621
    0x6120f080714031803014b1406040b13021e1308280f080c1c030c0e0d2a060206100e1e070e130603020310061d 49
    0x18414480d00030000401c4141210402c0d2010001c4e00c044e40000c4450814101c0e03041c101400ca40142007905c5e031511041000007034010100300030804818004805d80160102d040c421014044256810340140d40c8460040182c40070350303003a2507042401940d05004048215000901070701e900501408000c0d40851200d00c0c02d040410f00c1f80914030400310b000d54030118081600e0102e40caa006440c800d11a11344be82c00005040c4062050350040020030708907842e40703541c8038078003c000c4500a441600c01448103001c000c4040c80b0700280040490491918400d5001019090310604100103003440380400c0e110704151030f5200e01c0c81105510078540300c0c038600341e43c4090b0031929005009031910541d80c1800728016400094440c0900610498250b025a40f0b40b80400070707036000c9404201c0442c403000040e04035812a1b40d5942c120303043d410600a14800c80d00420907e04d504189112003c0d2210401c200394141807044051101e5800024400c880c102414103102d162200c00b901010302a0324002002 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 756265107 1250 756263857 756263873
    0x60807080a0209120c04050c030405150604090c0806040b0c131e030b010612061e05130605031b040e0105010e060d0611030a0b0429040902031606090f060306120f 71
    0x2060000c0111300440308201001d6560415211514051454403001c2440d543d0000c3c1581e110b55403150090254942010b40c2c41d200101c00740c15141c0040d180e44d80c66000407030001044028081c803134000c000710f01d0281004881400c001e454001e01c400104441d02510065040a90584062010103203040140c1d01505214184a60000d415200c02000101d4016886110600301005076802401100d4a50007110300d4903140ca8001070085003100c0c8108074030304014140020b8006040c100240d40ca5403980440c1c20514824078141584180800540c500c2c41c0030b2082544011254000700041e6041014a4404000241c450b80c45050508001c5041100582104a5000d4007586503500c2e0700f0280c1c5410702814011140394802c6080103408007120881120040000143e01070f000b007074031090814032000303004000c416600750286030008065010062503110060019a0b1790310701c45031134070383c1c000013200d11a00100f042608080d020003400e00580400e55000e604507400c0c243d100340500c0c141c11 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 756266357 1250 756265107 756265117
    0xf13020303130305060105270601030504020f1002070611150103020108061f030c0e010f1202030c091509100c0b0703050c0d1506080109060612020304020a050909010222060807080a02 80
    0x49400100b00088204200800d2a40c100c44054806103210000e022400c1c0c424a03a2603c4802c80300c40b03400001e040c640c440d8010740c2d00710b8006414101c4150100d0040790b160184e0488910169002400800c4882e52001c0c0b041e000e401c00070b001d00304006540c4440a40960103100207410003040c2c2e004600d013030f0340b002c66500d50210307050300d82c0100607030b4000064007400c114030703030040818161140070210754003e039040d084250503030341d0795228140b150081400940000d000103030840810320901c880c030b880d11000200a0756010410070f449030511020030000019608420b0100084014541e0004042802035071700a141402c001c10349540300040c42c3e44600031280c10744d5110f401d1180030000f1608110240040d50301d03d0752945d689a0b03d980c1d00342c0c00d94815208140021b40803071200d851100381ca038041c1d40c005100401950300076641d5400100181307070a4902e4440c030f950003d20040310003005640f10300c81340c0c05841044c1803c0d18164024000c10b00003000d60091094440010b5000c8071954115a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 756267607 1250 756266357 756266377
    0x270301020f16120309051e0f010c080f0a0603080f25030c0b1b070305160803072604080d0b01020a0506010902040305011107080405010c06060905010b030f0f0f13020303 74
    0xd51160482d0030358640d0005022000d84020314200007070300029200340215558a50440f0060506000d81c1c0b0600740281505150300b145401441c109020080082c014a0303007604a035900c1d807156040103030094683d914080e01c100c1034103203003c0040001034003280c143d62a40400806c4603440c0c49100d042110300c5401b03c1502c4640c1d40c501d20455041642040c5c542c0c2860b8010f4952205564500c05c0d07104610b8000c10080c40800d10600c24800068032074002040b1442c800a01c11000034101d83d1011820340042e1190408102c0040901d00c03000c42c410002e02c40207039032800040709400d00c0d0300c13a00b00034403600c0f0f00c2c00c1038240c6529100180d64000c010412881d50b20100b01e4207990794501e0458002c2d00103020442e55542008078008100710308000740d1320310542041e55641b03054038160040d10118082d1004884568540000040c5a44944905402480c548110765601c1c980703441c280f10a000c00401845003a0010000c1c00007101d485800d645e03205841c4c0c0e803402500c0c1d5983c00001d282d07000e215164 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 756268857 1250 756267607 756267637
    0x11413030210030608010c030b030c060f04091103180d08061314070f0905150909041e0f0303060b030f0a02210c071110140307110a0c1a27030102 64
    0x10400483e815448002150701c8500200302000b03141d1411020380e0b04200307010b0307410360003407005004902c0d150006180b54500100200c0c0340542e50030b00c00040d50018000d40001803070110801480ca0a03000d040008280d50b40c0c081c06120080c030320003601440000d003100d4000ca8019040100344a40741d480310103642450001c0211500d82050010700e09542d9004500024ed440d1100080600f0640002140800e0b0406500e0510381d84100f489843c910040080e1846a510202c00035001c0c9050300100e14103014011a4080701300500340230b13003521500e504c81805c81104004105c80503160605071034200341c5081000d80e544181c41031901c244c0308803400102111b080582408110340840c0010107045224001181c0180413440c04c0080c1c040b03a010500380841c561007422070800c1204030042d60b120701242130510b0603990300603010385003d0748041c08450305051054180700215443d50103d0600e810f08200601c2c203c80d549008481140110b071220200440880e401c03031580d4290199451102e00d021a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 756270107 1250 756268857 756268879
    0x90601141204080f130614070b0609040515130201170c030402040f151206060f0803030f04030c0b1602062a07020307050603100f08010c05070320061f0f03020114130302 74
    0x25804240160301c80c0c0c5001c80c091741804c0e90703040c87c554207032210560020400605aa104824840340300c4005204480c0381c02a0b00c1103800903415198480d0090101c91031014140420b440090030844008400070b404000d80700c100003d1906010880f0f41c0301c0d40c1170b6008200300c804000d03410013401091011040c042008800419601c0140303008920403401b950007842001d545448030480710340b09000d030303c3e066082040042c44403115400c80d690042e2003494084041501134850408603e400e85031014008040350074905016410881d85030450b50107004484403200404802c224000c04182c0240381c40c901041d03003011b65070140009002044050643c42d9203103004044807000c00c0990050030004600041c0c00300b80984144070300c02882c0b82680b126481c3c61181c2c1c4086e902540e80801100812456070850780350454103100003806050695861501450a0010744c080000075411000400c0e843c1d910400142c0c0e84100f601d200004042c0c18079941c1c40c16100e20046038071641e04041d410002c103000b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 756271357 1250 756270107 756270127
    0xc0309080102192706140f0f0a0206090c010e010c0804051201060303090b09090a0e0c03161401110d080c16050606091f0612020904050f010302090601141204080f 71
    0x507000710880426503078180642e0f02c51965a0544c0501680b15031850840ca5007841458081c00f1051000e490180e1218200703103001d82000f07002d41c00302d528855050702c041418003405804118003504491200f002e004250500310008000010306501e140c100924260a40c050256240896000d800301604c21700c80c612090404e41d000c0c0416110450000e032140c1000101c20044105880c07144000400301034464407118944400303803c007a4803014660107010046c481355a41001f81c0c1c0682c17094907400350f0807a4075100038000090720008001d410311010000c004081c0d030020904001c070341c00900341405291900d200380e60503805260038001d80301a4842c452028450001001032044004840c1a40b00340d9444000501035103210b02841074440000344184240e902803030000c0816040e000b001818088000300007010fa60007039420381f400c034900358010b2043d4100701140f41c0d030000007828440b045101c0c9058482044c807440300e040d1022004017010800304101c000450715201d5a0054203500c030040d0319 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 756272607 1250 756271357 756271387
    0x1e120e120106031a010f06020a02131b09050406060e0d02120a0206030406140a181103160e040b09150f0c040909060b0f01030b01020d080a0e0a1202060a0902100c0309080102 76
    0x1c4c1c1c1d2890300e848480000145059450360560503200c00347e01604d00200c0c1c43c3e080c001404050f580400005455004a950a6904032845051b107155170360340103c52032901d000d20040b50580c0d00b0110800014005400c119111150726401d0103604ad12082d00b40c10014001e9410030820850003135101d0000010b000512881f40c008580344881152916041e0f11006060301c1114410680c00c0160701d40307500c0301d81c0440c01490070544040030150a403804010540072244c11000150012100d0380c81c030710140404c1c09080a500d942c031104003001055807018114000719400401031540c1d070300d40b490000241e8200708100a490003091401410302600c07000f441d014000c1c2c8290309640c3e02418140b91240e01300c0d0710900413414105c0d01a000343c20344014544c03042781e140348018041c0c03d0060b1510b00000c003004c1c0810580d041d82d4050a6440c91121420381c0003030a241c8060070079403900c0c0c2005503850140c0d9484e0f008640c00101828060040d00b100d20701942c0509165011800700d51001c141b0380c043c00100 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 756273857 1250 756272607 756272633
    0x120510092108070905090405010b0306070518091e07050904050c0a0e090c0f09030705100309031b120c020f10091502010203010f140d06020301121e120e12010603 71
    0x40c000301601e41d040c407a0403620328004a40b903000050701c2c0c030020025400d10b080138a40180c054800402c414841e0b078040780ca4660240c80001c00135500049648840c3e8064020b089102411642c811050416400070003449400b20580110003000101180c00b03580a90201c5c0c51514019005025510b8040752072190398200c1c04100f008601e815100c05014501700902c184030745400c58845040200504180d503054019040098140c03140440100b02c540d106030000040c1c15080c0e60101d0061524a002000d90120380070500507074030280306080000d01e0f2448100030800d01440c242110401c0c0c1d00000c0c2d01110b0007404d654101200d1a54400d81c290f02c004440c003034401c0d1000384840015808001ca080b031200340f141c42141a8050420302c03554450031a1141180700c0240100b82c03803e9961940d0040781d01c203901860880c000c101240d010030180600180d240000a240b10032410801d44444607200080c0f0603d100704148d40415407003660340c0c0d03524401b81c016604000c01c5800c0d01e80c6040e9009400c5 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 756275107 1250 756273857 756273893
    0xe071a0423120307020d080904111c0e03040b041a0d0e01050405010614030616020c1302031603020403080904050604060b04080102071106030112110a0e130c0803031012051009 77
    0x108540141c040c1c2c1c00104a50000ea80944122500805500c0c0c03042039800c080c0440d03601c5030f240d02c010700d01014003102900103100548142110360030401c0160048076460a21500b007a04103000400410303180d241554201c030112420300175403d258507210720192048000c2035038035615120404040600c158800d503c5a88610020040540c4617800f02002c0505803100a41c1948038800003200000c60000e1a0030021141c01201c0c0c08a500c0c00010b111a90509543c0a4159010007080010b03055030700740d100c420089040462905007503840340425445000b240310b00035500e45000c502c483d205e0740e00200040400246060b240ca13110015507000c0e44c08100155440074010100c82c1161130981e08484c100c58441300b5080d6400d5160392040b5400c3c0c251610150700030044c4800142c101c072002005072058801c0d030108010840c0d149892106404181c10900c1c2c254000d00c05c00500c08082c510306001e68250031b84040c2c490b211850518506003ca019680c1003c3c2000c0d602c0c0d0030020411070740981c03040 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 756276357 1250 756275107 756275119
    0x50901060c03021b0f040f0e12070c0608040b0106080910110d14011d041713170d0f110709060902120114090a0b0f09090c130e071a0423 60
    0x76000301c403102204c0e8400c8110352201950400d0001031900e5800034901c040d4140b804208842444021801c02071010071200e0340c55000034040c0104909002072601401d002d0138448940c0c2026100d02c942c840c1c2c14003586042c04051000f144060f64200046a80d0b5807041d281070080c80b404490442c0c01c1d41000303005110041c1404010107000c05115200342c1600c10302442c41c801c00568405010080c60301400542c0c180713900c014918490351000c8000d00900c032642ea80401c10500e0403140b84e0210544031041c40c0b650700a241b4141481307501a40c0d20300300062a1800304495024202540d0500c070702c079400001242c0c80e1000000e0b01c01044d401034418004103603041c1c5485ea03650910100720284003801c1503800711201000a0b490140d81d8030400c9411400f42606290041c034401080702010241d60001081e80029203400080ca0003900301110000b582c0b03030a000203c401c0c8400e9603116094011114114104c1c0207081100c9481801d443c02400240d003506000c011401d003c85030122000ba5590081c1c0c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 756277607 1250 756276357 756276373
    0x30207060e010c080a1b200a08061306151d0105010e0a060c02090711030703210605010c02060306010315090507031803081302030c040606050d051b0307050d06050901060c0302 77
    0xb43c050809065003541203d04549800c26008049a03034031084405541c0364038964882d00045031010410042d801a5806090064880c1a04108884001c0da11005840e481542007040c0003072401d9800c01c0c05603000030085400f400c0500155441c9035690421144524001e8400103085070b640c0d4864104c400a0302c410501c40030103170910402a0280c02894085500c038a0070100504001c2c004980c0302d030310b07841e005c0100f5818244141c01c60380300381000d40c00100381d01d8078aa000c000d2480d010103581a407034810020a403601001901040903103030040d100302400700000b1003590194202d000e00381171034030134000c04d1038590a01100800c0e0580321240000d140030740508524084c540089406030b0180c8030340b80103682e106115007020718404422a0180142a02c0d4030594450f40102e034050724082e1140ca0700d54807607440e0142154401046400302100700f10711010f9010030300c0c040300e80041c4daa00d405a0341d031281601348030190a00d0351145400c07820200000402c1580010b41c82d004034840d60943e1034407 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 756278857 1250 756277607 756277609
    0x110d11120c100f0f1407061103062d010302090d050105090607090b0403030e100201060f090c0e15030105011202120411043b0c0301020a05040e090105070507030f1b030207060e 77
    0x100d05000f100d0400b04802080308080716000348a4103c01000401c6598a0030a0956420080c0d03012851903005509010040c070103149881d819040b043d0204100340f10000601d0903850400d040b40b08052818143c0c0001c41119585504405103086034002c4000d10442c01c10385c49007541c804044614a00081c0b6412022442d40501e03c1110103c80d015540e043e200d000100030090403600c10140c5000f03540d40e94600191658602c18110002c011880f000100070200000c05444503c000c64058483c801d0050b070140b200589406581c1075610a10703101c2c05042103081008028414015244480840d000402c8100941d808500120100641c1d0900601207082325030b8282242502c20482c120300c1c0488005250b210b80c1da60001c0040f0040103c0c1c64404a15010908a07442100518005540000c09000b40e855001d000c903003080c25240200310903c1c0852004200e8043e05000a04200d1160040740d41240700e202c00c20803408214540c0f150208680c903006e50b43c4d11140c0318843c0400c080449038001 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 756280107 1250 756278857 756278867
    0x303020d0e0a2c01031202010b0102010e060a05071808011a091003110301020d0f05060a1712031b121008070803071b0b0a05091c110d11120c10 63
    0xa18038020304810362035070410ba59000355011041003100344000c01e4581d03c45081c071100c1c081d03000354010380002d621104d00500090070340f5071603140d10f41560304100d082c0d44a40d40001c0d82c943e01c004c80c03441c0014180c882c800304468928190980c2c0300903084c409004207200b10103600181030070480c00e0003542d030000240306014656108461b0082001c0c0d0807442040400c1ca507d485070210403005000501d020003500d00e0804039580a81c3c2000e0141c1c0d12000c0012034280000203102600c1c901015011341c0312500c00d0103540e07484248444040940c080003050a403c44aa204583c1020755151319840b820004170b00801c090049550324807009420384001580e840101703400003900c90110146184c003001da21400044c3c9006d030401860300c1d0340d6100024001c801c0102a00300c2c15400da5805642c0d04041d8104015640c000440280e0090117613155030024005103102c0c1000b10b03007980c1ca282d0385c060318104040c1e0180380c22040c0750400d80080706036070a00700120b40a506400121401110010320502c101d91b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 756281357 1250 756280107 756280127
    0xd1107092a050f21131e030302120703020726040b030907091418030a0f0e031507050c0f0c06070b04051603030809010b041a0f0a1a03010303020d 64
    0x31000c11030310300030000501d4860180103032803550401526142d0a142c01c540154400c0c4001c135161000c48403034010324402c031144990440990074822410b04c0c86519031941040001c07100040d41c0200d058070804060013901601c0e100344070745824813000d02c2c108501401960010300304852341040600502c0c90010750405c500854600055400c1c207150400c0c4145981f940048c3c0300c08001d200b03401d00058511014000c580120080710620200340c18030f403070944a06042040d90040300c0c0c10900082212903888501c0f07060507002403800b0301c041140c0c0008241064180c007102c3c62201c0d003070402c025640d50800c00405484402c1e0044bd4231102c18090303000c0d101c145a0b034001d07a10010401500001c208060b10058001e40100c080e640405140c0d002058a00b0160b4411030200e0301c660100200c0042c28466006452410f45003400300702e0b50407609403c61500c014085219403000381c0c078910252101c00d8528003800c52416181c0e0301801d0080301d0402e030b4000344001c90052081e0005400705502c42d8103045 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 756282607 1250 756281357 756281381
    0x61d06031506130609050c19030204060f1412010b09100c02030d0309080c0f0c010e010f090504111318050105191a09060703030b01090b0405060316020c030d110709 72
    0x8034a68580c0030030006106581030341c1403a00c41c4c40300c0c00030864000911a4901031090824074603503a12034000b400c190307000d40050300800d051051008000b816085a100c04242c0d0741d0f40303019007101c101c4003d44143ea005031030318840c040c1c4580001203401000e040c01405081e40c1142d07120700705400c1c000c00322100c00c10210000d4140d00400042400e15009401c0300c3c00041c480d000643c100140d201605290000e0120f048006511521007152103580160b48105001e2081c83d01010380b100c00308024050440c2c0e44115800f850391030301c81b104107039064401d0307030042c112001203055215a030309080110385000190a0f010741d89040000030f200d10b020404c0841149100b42e5205040b480e00060094400400002c46425031003005034070580c2e5240c0b001880345078441d07240003c1284041c0c0006008503041c0d0401c0c4020304080206203d541d0f9100160ba600c201152443e441840186030f0490074078541c4601140c06206010f800c0c080035411041a0b495400004101d0300000e6035840f0704020355545044072 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 756283857 1250 756282607 756282643
    0x50708120726070f03030c1206060c031d0a0e040b0702010b030d030b010504120f05070905061e12120409050a15030b1302061b060916050d0c050301061d0603 69
    0x42d042660360705035800341c00150802403418441d00343c0710710b400901d440504500007652803d070f0020058021a49003200000b80c10704200300340c100b14014015071000035025062140c1c0100e01c068114001c0441c0c1008a0301504a91503590394088407003103481c003964111142c07100c0d04002614644140324004c0d0b641001002011a002005010350080401d02426230410204100c00302d0110f003449100324505119401c401c1c2800d2550500c0b40c02d012003a080300078180d04020901200fa80c0380a80140c1000c10140b0341d049203102d510010b04080042481026035015045c0094095840d0700040c104981400c8818007165494842520869165070441d50041801100030300c04070742c0c1054442e030701c4000c0b8180784001800b2074002802540111501c078032500417024515548110510181d41c1040c2148000c1032441c200e6004800714406500489000e88201030802040c8040805501c5c003c040140082250a4840116101140c0c0482001000428071804582c4a003000a030700c014030b0f10f0b103080c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 756285107 1250 756283857 756283883
    0x12020c0102061e010618030506010605071a06010228020a0801090b090a050a0b04030314011806060806150306010210020d020d0c170c1e0f0405180c0706050a180507081207 75
    0x700790b81d1041d203404080843c0c042c081007c4000f03001008154040c0c00300f03413130386034a940aa20b0082d80620382498802204542803040c002a640c000607504001d20b4100106014079130741920094806d441d01c000a0b500101a05001400d801d041d1b01451030b00340204060003407030703132840459a80c0ea1a606030080c82980403400c56000700e1420000160030500c2881e01003865408460141c49892082e00710300e560010390741d5030b1198000240700390f40c000c15580c05d00507454600180064000c0c05e60218000342c00100200080340da030b10a0190603080c41d1240c0c1d003151500c80002021000f508404000c010052500c00c0e9150050700442100e00129216440258070b0303a114100310204d500101d00c03130082440c0c8a1540262400e06030050004c441848650940760b41c5440f04002c1d00400c3d00300381c859000c03504410700040300140e00485003101c0e0061008030f1103441e2480c90800408410181540d018003103040c03841040004103020048230158402c80e0346015001381d403a0710a11860400400d10300c26455 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 756286357 1250 756285107 756285119
    0x9010803030f152e08011403030f090402040812180604241b08070b072102031005061801170c0a0e030309060a0203220302181312020c0102061e01 64
    0x245903110500007409029221a6240003400311803505003613910040914607103801034544c0099018010075803000e050094030b42c0306010039181d03c0b4000510042c00c07000900d00049440d9601280c0081003050100c811960495816130025009181103542151604503010190300e03201c01640d0607555002e02806078048040300f80803481940034009000c1c0261446682c1840c02c5290355484154001c0c8003ea9544100e0701e04141c0b0500001d040c4400c0c460602004080c805c08101c140e40b80003140000141d4079211400781c02071550440d44806d500141c0085c0289407814401c044950700d40c02038031400040602122103c00c0385208175000c101034102840b80d105443c0c0304a201414010340581620310708084640400d40d15400100d4000141e40006000c0501e0b50984003280744841c0707502c2640d09030a0941d40040d5200803440c030300082c42c0d440940032484d503032080704020440d19444080562020141b240194640e013090119a0150040c000016510060001c0d8803041c0d05642c201080e607a0701384a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 756287607 1250 756286357 756286381
    0xf03012408012718020a05030706020a080c15010f060806040501050f0d021f02010603030206070c020a03032109050c011709060a0207050316111309110907170a0b09010803030f 77
    0x1200c0c904144030001c1da0f849541940f4810036000100200460b040005540144914036290b68030150103030744404010400c0b958040f0303a2500d00d9034401c04a640d1211031444e024508074503910706804503030700c030300001620f08040744081e000c80ba078030307100c0e000940e446600b040100d0341d00f4425560051203072200f0101c0c0c0e260103005030408500c020104102c1e0b8a680030301801550a020b94480540c1d9203100c18820705404001d62640910b0320703c0e10390004826540810300f19540c070b00c001401c0c4441003202c2411f40400111410000e070442ca410004030440b424071564800d141e800c030a003c2a150410030700008040030405108120b001c00800c1c039520b4600c4030400a40c0440405e031414041031284800010000803020141e034011000a84080500130803c02810b5121069001c501e280a01403800034a01003400801d48004030340200c0c2a946001c401d8500b08588842400c12201c0e41040082c1140300d43d018076092081991000100e07070321b500100d42d0381e10059510a218000c10000200c0c3d81c40b80c5 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 756288857 1250 756287607 756287639
    0x6090c040f0e0102030a051f150305070e130c030608030405060f09011b06060303030c1b1103100c0801080111070213020a050d0203041a161d040e030f0301240801 71
    0x2141d03001800302000c2c0364040c00c90300290350740810a611581448004806551400c100c441c80c005600d1620f8944016165482c490800340c409058039100000c011074056140400f1054001c1c14817002200020030b040010f244e04280340380400c0c90714002041d41c2078004150341c1552000b83c0039615061280c855100035811a40d45903040010010014041817a0091640c0c44544a45000b060b500e085180146c251580c0c912130034204003103c0c888001d841c11407881c80c000950001208000c8103400781c003080c10003121281985880b07040c4084003402c9a48008050b04a40065008020320301c600301001032203100d4440040e502203000206420180a698010440841c59042c09072410080406000590f001101d050300c001010419120034408060804c41e032181c54200c200c0f822144481024120440c50240554a010003a68007921a1110380c030800e02001c6e07201c112910b88a01104410059000340074040881c204144c0c2d00c50f00c41c90703181070542507115a44810b2410703030a2840c09200b0708c0310 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 756290107 1250 756288857 756288881
    0x5030a08070c090c050c060106030b01090311240702120c30120c1e030307030207030302120f0601090f03051203060f04090602090a080f0703031b050d020a0b0906090c04 74
    0x101e40c0b0000d000e418610841c60404521780300c030343e2101001225a42441c41c142d03c10b1050600b4a04502c6103603070701210410070359a000c0d0b0307441c0240040b5008034001c0034076000c0070300710703c0260500c0b454404107070006441c5240c400c540e240d6501c0180b4290b640c844048640040e04040906a2075810801c10740c14400100c108074400c07481c000e0300311006468442100ca0805c542c400010701400030f480c05004050a0290800c1031940c0281c006800c2540c03807000500c546c0c00c0550116100041600c02d4040b03800400300800d41e140e0a00f000249120011000d403803d0380032512401d07002526040f407048030000c40b504000074028000000c5003140b2107520050815501440480341035006039264800c40385140e00401005840301c1c40e400501c40c0d900400c0d04400c03000d90000d103041440090009248080e60303854540480300302c418076a0300d0800051210001c0190198a400c140e0007580013401240b00c3d401a581407000f03803a900744850311800c040c3da80300c441c0d030005d00040c02181480c1e080402242c1c4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 756291357 1250 756290107 756290123
    0x212030c062a120411031606030c080a090309061103090d0b0f07080c0301091814010b12010b0d0f061515020c0a03022103042d05010207050a031b030b0f190605030a0807 74
    0xc0c7c00d154414601841e500103a020960303806503000d280e40e0090815038082c448035401c00c80384506480140007070034103114900411414410020a421050003900e5000704c0c050710030410206280341c900f0250700c0c01c44080340030155610015414030300c80e19410340210182c0d05c40c185940d0030140c0c05c0e80906654500203142c400c2c80c110032000907a000740901c00314800311000065140c049410400000c09821800c1d0791070307060080885107692810740d521107490784001c0202c213240321854100080d00c4040008040c1480c09600064000c01c510104401c8030803035802c2e1034108841808102c0e418840307000103508480c1d1210900324443c02040c188000c1035140341124149580d450300c465101c2e0380341080c0002a40389543c0d10807455031103a04200508400d0015084090402000c11411240d0380700103030000341151442c0800c0b110714050b540255800c156002c406140c0440c02814011003915411100c42c8c0d442c8038403846000c1841001d080e110024003800a0000035150442d054001c4c03001918001 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 756292607 1250 756291357 756291373
    0x41505040321110303060117060d080f0415080112122a051516080408070804031a06090601021b0f030114090f06130212030c062a12041103 61
    0x4003004800714815112803100b441164200c0c0000303001015400c24264594001d000744004c03a078015000f28501e000404a46a0558030000099488030004d41c0181c10444000750007081100c02c640244191032140b03c000c0340e20540c600c41260341d40024414041d141000581c02030020303150150354248003c00f440d042c54500041d10f000c840790708030b031484080301c4c29108c800881040024001c0c030b10004401c200c0410715181c1111200c0b541c16054009004100e886800642085030007403c1d11201d5800045040e101d9440b41b1b0301d1136205500c020b2103484484900c000440910f00818494810750341a03000c0c0c10790030703103d01c540801080e500342c1442d40107501d10f04c81042605c0034450130350441c1507008050f800b802c001280b41e051500a45490500d074115100f0494000240c0113a024940d40c196200c464050300424150b0a44c01454606516401100b0a02030703036842207a100f004100f0f00c6c25200d180540b668481a1480c801c41901a40802c0303240b00282c0440d515000c0d04040c1480602982c40308 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 756293857 1250 756292607 756292613
    0x1902180108031905250c0b030f07110a050a110a08192f06090a03140a020102011107051203100f030f06050a0b130e070503010911100c03050415050403 66
    0xa282600200160b41c4045034031800750010030006000d1143c80c2c20024030b072407040c803001d07101c1e0040642e111100041c8007a07100d003088050322401c00140160040552170707050825a503d0030580603038404001400c450703a084841c0201041c0c0c1066181d10500030410f00b0340c140d59540c10201e1204a20b030344030800c41800103441d241884100030040003000802001d101c50315107040c0305030300c502000042c00c9204101c4440e84940c0c03640722002110403a001629540d0880001c1c2d120312540d00000e1038000c501020009503080040e50002a9200f40c009110082d1414400d80060007141005400356006045203000001008019500b044088409941c2244c8546040080b079181d54011039000780707104e440070b042c01030031b11030940c01000464050290130301150005078000c10000140441c02c0e520b80001700180c100b000501c0081101900a1101c010130f810011008243c004030140610f80400c15026894854203014909a60644510b800c050a0100380781208144003409801d12a0800001c808 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 756294964 1107 756293857 756293899
    0xb010603051f03060b030601090507120203060f18010906050301020a1d120f0c031b0105030c0c070f091a100e0123070c081606021902 59
    0x1d15440b140028418000c408402c44081078403800000304004507a00b20440b200343c114180c40a50303a858003410140c880032212600003801d460300708c0541001702c1d405141c210034060a40c82e000c4024a010030b101c42d1082d03d20050440a101c010800030410740542c00c0070305010342c02541000503840e4040c000c00d10005030345110807a20458012640c46106d0b2130107490145c0ca0450301c03019050a0069142c5a60344161800f03802031504040b590034240801444c0c0c603078103a441c185103549500b554166500000500c80d01c3d4040e0040004200e404080c00d10041c00d0f44520015040080040e05100300b1040e0283e2800b46850020740300c5843d03000240c6e41252f41007030030186c84801040c8e2849181d1440e03129101d0138074101148620038045044805001d0b107516004680551440240910100707101d442070100603407140d00e0b006245c180382d048004001c0d00c05815500c1ca40380300880c0c020 = true := by decide +kernel

theorem cover : BRFrame.Cov 756115107 756294964 := by
  have h0 := BRFrame.cov_init 756115107
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756115107 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 756115107 ≤ n) (h2 : n < 756294964) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
