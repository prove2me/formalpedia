-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0078
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:43:20.444458+00:00
-- url     : https://prove2.me/submissions/d6c2307c-8996-4715-9a10-b0a27089286c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 13848927 ≤ n < 14028783 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 13850177 1250 13848927 13848943
    0x2060f1b2203030206090a0f060c030204091806050603070f030b09030903100609050106050304020d021002030903010906050411040c02100b04020d050f0403030b0307260307021206010602070b1804020a0e03 90
    0x400c0070501c1d851420000c0c070308000603124a9003500109104000501241b40001c07206910480c04100c40700010020f40080c01b4540c82003003518100602e52140e1139514100008040c4170300c5041107540ca40c0d42c00d2541c1e44829000f44100300460314014000728801081e0990700004010803280f03003100020200e8140482d450342c0100d03e640704d90050240351007501503035015020710700e801070039850240c00007142080b40c0d100c00b0740200b20b0120107038130f100d2081c03045892000003d0b009205041c000e1030648001d040460b030907075110b000303014000224545405030745081c401960040070080240303030006000700b82071003040758019400c110304040c59000d030103074511801c0d0390040310b1910b140c98140a030941d20000c03c20b500c02d0308070745d200707006040702200a00803210310322458071884008032040c10714601c15000302079404801489403210041002904505075555582a100700ea991224002118040e8007172551304030407039450340a081d041c0b5030302400801c42a49031001c45286650046810240b070 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 13851427 1250 13850177 13850227
    0xd110c03030c0d02010e0a02010912030c170c010b0301020703080103021c020a0f080c03070803030c0f040b0310180207031706060706050a050601090b040807090e0a080a030c030c02060f1b 82
    0x8a80305050f19020b00c960303503407582200098010b180040d40002e06c0052140180352905c07d114881005162088020300360055100d5640311000141503007400e00c54000e4071508040d58204000c2405504040c0240d549280d41621442d5099003075500700b22402a00b81c080b100745185001c2c410026035241882c20740200884000088c803d420803208500f490140300341103000c0d43c05964108030080002040782d51003100d42100f030f52154a0701d12144910722070f580c040d1010550100a120480d03040380b081601701c40070a19281103200285400340164000c111003c1c010850f82e0140e10041c2c10420080e99214100805180c82c004440e81e0780000c0704c06c01d881d01118595600c0803c03801c1d5801580c050058621450b005041a107020001d0b030f5600d00d24003035440503d448103031201410f4000c002c040ca079154451110f503144c15203000000d008000518883c1d00013801d1a8200b2400d900200d1014010784034030888003030547e104401d0301c5c65020070100404842c041044003202e03100541d2164900c41d15 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 13852677 1250 13851427 13851433
    0x5040b011101020f0d060b09010818070f0e011d01030f0209070e030d0c0201020607140d0b03070e070302030a1505062a0a030206010312031b030903090518090706030605030d110c03030c 81
    0x103902100717a01110078a4000820b07900e401c201c6150240c4e000f601c520362260b20040501c0703001080b07544590601d001c65000c1040300d690040301007003111040302018161a440050082540007888840c03a0101c020704c0302038940c61003070403c44050b04084030080d6105603a03041104036242c6240c0820f2074200c10941180015203207824030b02c00c6690510503550000000e20746141ca0740341409190342c035441a6040310b0180d03030b0b541102e8440c60320240302c008001c1040c006c03036001c1c0346803001001e000f079402103511120591400c0c2d11000f004441d04604801d86c2c8018003880d05002100103c020b0320391070b01840c40603400c440c140600c0340a804108a44c441d0b4801d034090f2189515614241e4005034401318052705250400300d400c0d107844500000707015440351515000c1525070a80c01d040e03d061040e42c0040f0b4005c3c0d07205070140408403034506d82c98002c00b611000c4504050392400708a08451081c0100c40e41a0080901139140f1442881f1f101c0705482c100040d580102c1d58070001031b285511194840403950 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 13853927 1250 13852677 13852687
    0xb0309010c021002031e10170709050a060b18010e060301060c02010e0402040e070503040c030b10080c030604080301090b03030c060f06030706030c050724090302010609061202090105040b011101020f 87
    0x79505015022202070030020660075401d010075030740d8604940b0b950b140f984490700c02c0010340c010044c010b510000c28456903507900d811420340c0460b0b200d100a01914070b10710300341000b1440700c4d00e0300d1150703c04036100360b045a4104100c4a0070368140198484040d81004081150b0505a655000040d40207110640740d0b103075010030701e00c0050600d1405804151050b48140410000001034907200d0b603225080e8600503942c0e55841c50010f051001c0c03a00080e050b0b420781400c01a2102c001c60f04d205c140e55104d4212924204024105a9505d83c2150000d01c3c45900b400108540d18058002c1840e0b144010252410001d00c5002c2d1403420070300300d407240e00d428401000d2140c0c078141404a20040d00e0f5614041c050700703140c80b0300648075101c0c5403001440d0518111800302d1900d0700300c0031810345d9003c0032000e00c20703400340307042c028060600744c02040700861800400041095074110f91116096018000e03c010381e20780300401c8000c102d291004d9040c40307000d10321160f00c1a000e10007030800c1d02040c02d42c0740c3c580c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 13855177 1250 13853927 13853951
    0x5071401080c1813050907090501050907050a11010203010801150b030702070e06040b030a0602090a08190b0403030207020904050a021201060501141b03040608041e020d0f02031e010f05070206010b0a12060b030901 93
    0x2047d5a441001071510701001401603448449100354052201e0070810356455140408840b100e02ca18400c2659510200000c07429243c19048800c10364120050460900e4480c8408483ca100684002c40541e108400400a400001020350b921000040001508800c1c1502190074102c001a00310341040e07000414001c140742000000c80030380f20700402404070244400d10181e504244602c09040354141d1030020307003010b203e5011180030580c060061401410a031030442d40d1a0b83c0d100d0205d204000a074600000c07000d0501c20b000803030740140e655898a1400c130307404072500d03880800c1c084c00340f840e504007003404070008000500c0207081035510050289098203100314200e1440421000c400342c140c0c440c1003d80c0c0c0b04a0301401c0c545c3c0109260010702014030001b0f25140d011801100c00c1c3c54050100b038400710042d400380d01c5560703500f0b000b48820f9803510403ca8555a090207641c1400100744604106103106648a501c414481400041d00c0d541f0782d03805c10080d81040700e113003145070f4403100c07040340d5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 13856427 1250 13855177 13855183
    0x5071a07030605060c1b0609220e16140f0a03080304050105160c0809060c030c0d090e010e0406020c0c031002090f040b01050a05070c0902030c070318050f24070605010305071401080c18130509 84
    0x115100100141c070751b100a2f60b04200840146200d040c0c60229407210007109a030794240e640180d0b040080188c1a5a0390783d1500d5846604100c0d82500c65518090020340714880500c41e88542d03004070340d610f60440314207a40e201404c3e0090080390780c0200c0107000c0250750140420060151791000c1009040b403020103500205034400c2a0808108420204010000c0030140c40c0300d01d070030075400301000d80c036501541e0140b850329039105c802c075a051051110189a000d119402402c881c1c0b07060b40c0000c0d0400c80c1320705000c02c5e5807030581010f0000308104200c14615204401400c50309110390503202c8401d07510b14081003680c1058031040e07505003000071042c0c01c154025060741c00d840c00d001404401146030100050281c00840e59280c000c1c08080c08501c9004121213040d0041c940d03415400d9140c6009043c48001042c09000c102e80340d206001e408120340c04150000c3c40383c141c05035540d80701ba41e614421000b290300004811403440e1407070b0510207010341e250101181103200204000555107059001585 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 13857677 1250 13856427 13856441
    0x4020409060e0c0f040501050d0209040f050118020f0a03090507080d050d06080c100f0210050406060305010c090e04030e0a0503060a0509010b0415050d0305071a07030605060c1b060922 81
    0x40360903040000c1c03c404c400c85000c1d201124400d09045403980c1a00f40d80720068030840094a9120b898400200e001007030790f9101034165000c08a071411040f051034640022807140d84460390001d2001d00c4102c80303030f071f1180c0c00001e441489802a82c100964600340d40e480d1602d04441000800d03408682c80b131540300e032441030300c004085c0180200f42d1100045e000c12500c109030b1240900300b10203088078041c85e60007000b00540e8043c1c40b520030030280ca0079003070200080000e400300f16242d50034040b2404245105120703450650310582d940300c40701e40f0380b0769003610b5810702103640176004102c01100242e283c1e81800164801c800d0720b003010401d440c0142d82c09003143c24100306070340f00ea441c002c03054010175200c0181c4800c1d21400e443d8861950181e0400382c586000b2090010700380300144a41041000c03038450054000c0b0b0042d18140070061b180c40030840940100400201c01d540240b45054842e82c400d00107100d4540c000d4031462515004401003601c6200e042c00c8103442c4030030032041e030000811030b00c9011 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 13858927 1250 13857677 13857691
    0x6010e0901050f010e0402130b070c050406050a090e010f050405031207090f0b0d060e090307030806010201020f070204020306010c0203030a0c1a07020616020709020a170703050f060d0503070204020409060e 90
    0x604540c1407100085103103c010036840d04100c4241696881c6480c0c17541204c2c0c85d11184d599581d030280d034841800302540d0016808890600100800040d20306041c005c01c1c060300d00045c210f08071981054100c500400140304284015922102c10416803006441014002e50140004d140c0d43c45a00f05c540c42c0360400500081c0401c90140010403545083d02d07510b03400e0701c0e1400070443d65183c0761060741e0083d10b040d4110042a8404206110b501500000100111071081d103d0a0490313903441c005900b01e0154000c20340c2c0400081007444010b1509074000e640c0104141001d880c00d0303501d500840d1540e00700760400400b0030042c48491003840500300951a1015480d030007046c0d60716180380002c0d11031401400318981140da407051411954000e00941e0064000208119111010781c207008005488411810f02c030064064041441c09100e80200ca200e84240940000d5685400041c0050141c00c803500b500e560000f48644401640d035400144000c0520300d01c04104d1904015118094000290103c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 13860177 1250 13858927 13858939
    0x302040608060a05060a0509060903010c02030a080919020609060c01050c0913110706051305030c060106030501060c110108090a0b0a09120c050c04150321030e1515060415020606010e 80
    0x40103e43e80d8070003140d0b10110986070007900c41c402300c00801d08500652503075542c0b550170902d800c0c040d2640000030742583c11041d91100c41a403204110140c031101c41283c5031104a80001400015040240040513540400340409140c0101d00d0101421144180d40080501400040103040c40c50034440c80d82c002005014208401001982100054418244011704094035080082c0300440e8072520b100e190364010b420b403640d0740062542607840700070034010503012a00d0200007084c040c2c8104c0504909580c08121281c0c0a05614019581120001d01505451080035031103000100c1c0045034501074900740c1000f00b0b60325601d140251500c000c6043c00c404110383c500401c0c2c00700d0800117007c0110340081d074000800c0d0036456920320451101c1d80001d8000300b01102c1c01c0320080030400c6286620082c40c0c1d0108078200b050b100243c2c55140c03800b10a04050042804114001004004101b080314003c09103880c1541e94480400040c1c0034850070405070f0031000400c1203550b0810f04400c0010021200 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 13861427 1250 13860177 13860179
    0x5011202040b03060f03010b060408250e0703091104060b0705071a0301030f0f0b0903090103050709080709020904020c0d050406030f0b090103060518161d0403020c0d0c0306020a0302040608060a 85
    0x400b08103000042030319104400c450464801520298041080004003801807a51551200c0c40c9698860549100015582e180303650300e50821a4069800162032840d10302140544801c041203000c0c16815000356960f08050320282c14561f00c6204010062986078071440d21404a03040807401e01d031113030b032041d0f100c2500c0e10304000c50704503004101da065950060001010744a14140071044020801000f04500016414014000800400350501e500240d0f402d110076694084110b4440c90188904c0030550b01044041c070407100660044d0a0488020304010b040036080d0701150326002540b0703c580702044001605000d8107515000b008031080d4030040501140c0c000c3c0020a00c444014031001c1c3c20240d5030300100c1e04c54140c0030484100220550300b10384115514011840400e1074038401c04404055801940460f04240d180c054407a54043d00030b0203e4200361000c0c0300e003146041d03c0440c3c03c000d006d1000300c0000c510348064034010555aa00680391401d100c03010740f042d030000c2c088910407046404 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 13862677 1250 13861427 13861439
    0x90e010212010512100204060507120c03020c01030c020a0b070503041a01030206070609060207020a0803030105030f010908070f0201020a0f0302030901030605010c0c05060a1106040b0405010c0503090d180314070501120204 97
    0x3120b81100c00039202401130502da505002c4c00c040c074006060340514000140024020303805000307490080c0c000c0c44010605614003c0c01e0741e600349c4c0c4032030042c09030b00300340c4e1276840540c000d6100003211a1540103440f8003080e6076a075580e61410441d11000400d2005c828441030061031030072140c5000340c1c44410380c2c042d41182c00184c81030203202d60040c861070300c0320b00300820482c2d1501a102840d50103001c1940e030684480601e0780301d42007401071500910032100c001025100c140556a501e9801440351890056035488800c200c404100c000d906600c03c804204000030030620404011500983c051500d951805000405541700c55104e01d0400ca00700c5010808114094458821100304651240d41d8003120f0006aa2104040e01aa05280544030420ac18070110002044c480c52060b03008001000008405490a0000751400d520686c04031891501c0e17030b806101c1e24500b42a0240c4008070207031b03680d681d64100c1400f20b4204062600140710402265800c006552100c0e2801c070010340c00d02d81411 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 13863927 1250 13862677 13862707
    0x515030a0c03060236040c050a09030f020406120501090c0f0501022d0307050303060a0909080d0209040906060306150509010b22030611041a120601030e0106051009090e0102 76
    0x400041c08290740041c811380c140030700d4690b18042c0c14004000c01441309480e400c192176451941c80c0c46000d1410701482032811440b4600302e1740c842403142c6501025038156290301e8000282290103d0300075a607800081140c0201c081120b003410310820000c80c0450481c0f40031a400445c5900000e0718104101060040b60307000f14001d052029400d90f42013150203808004030880101e41100145c9000c0000c030b00041c00008801548079102c04d5031484d008039601d680906c00c61354012009000604280502e102e15142c9030000e01c41e40c04000e10100d2415500e883e21801c9802070307030080b25001e90395004404048006c00030040100000c8480d2417441d071405401603c548140c1101c4890150030446465030000d071080711401854011900304007c07005a9903820842c0d229004011110f03000b4152403442c200c061040742c41141d10000709042c182c40d5207006601034900c20000d01015526064081100d4684c91640c103000401d50341c4420300c4c42d1905a101c81101d0b002c1440e00300e140d0040041c55400e00b084 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 13865177 1250 13863927 13863929
    0x7150c0509011e1707050403060608030901020c190e0c0306090609070504051c0c0f0e10030c030209190c1e030207050a02010503040512030709051810091805060405010515030a0c 78
    0x72115286400034031980c200c4080c0484003c41c3c9807880e1301424885095884406001540e1240f202040505e03110b4410390380d03034020b09250600582c0312041c8003881c1d0400d16201845141804030311094192607200a003241d190440c4c295004050101c20489113182c401540c03500074509070b40550560500c074000611920031b900030f0034094800480301d0b000c00c07000c2141e03c0d00d01c00c2d0422981c40400c0c0d10340158000590710341c810f0840c003d400700e0200e490b001827031180c0021030340e00280340e4408038503560900c00080002000c00c900c004801d0804a81031055010785c489003155640d0741640044483d070810405005030140108161040c01000000380001580000301a02424015200c1d42c861418500d044206440d001a908000c014004015044641801514011100c2000061034440c1c681e903140c4044600341010103002001f003100c1840c076032003c05a0076400703c0c000c1140040d074407801c0c64243c0c1520201c400344e42d10002c21a118003914010f12056108501900e88590903072220140c00100f = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 13866427 1250 13865177 13865207
    0x1101031a040203100b07060b030f1906050a0912020a0201020618030d020903030f0c060f011719020a0f0b09120303060604030b10030b04030f021b1c060e0307150c050901 74
    0x30020116442e00c0c0b0701c01c1d144008001c07885d101035507290103240c818090000304020354040d1290320318a6208000108801c400010205165150390741e2946590010300350103003030f10034203030f0703682901c5000b240040c0d02c00c0034020a03d40042c100c20f00070b071000a00d015401403440c2c0809a290491014845001c801c803207140c1c01003840943c442140c0b0740080e0441c800c82000c01903844002482e69000383e00850303844e1207000c0700b075102c03101070783e076080c0c2d0121a241040c0c0314034064006491820450394840b400d6940030b4006040e0040850300d03070041803035100c1d05401000c0b07142008140308d2254500040c0a042201001b800745041d42010004584240598007000309a02c0d90701000601003410041ca032401190002d401201a05260802a200c050ba42d18840f0050048003610035080140c11b04921203004c1c0607081c054510300d5294106c01c0d46808110450b002c948030710040c00c80100c1000034006060103003031590316026031202c10340b00325404540c00300e051040c248008441a80c0002d111118018 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 13867677 1250 13866427 13866431
    0x61005030402040b190303090909020d1b0506040f05040509030f0913020d0c08070e010801060f0c020102011b051308010c0504030b0a0e0a03020321010b04050d0302031e071101031a04 80
    0x3142c0c03000501400d81c3c92405a084801181030740d021040282441003181d00980b01c06080c180c413042d001c801c0d1503400001035000040d0001e003074001040c0e011001302c015100b40d02d45000645480008200d60301551000d180350708284010301891510744507a0350071646c40b00080d49041948880784070315015080794244906484c00030a00c01b00c0c2c003901103800500702480100607a1031881000f800134101583d1a60001e0f02c1d02c1d0078210340b54000c6414a040e2401070701e07450b90307582c00d40000301d0341c5c0000c03250201d045548944071b1021170300c3e043c1050217800035280c45140d01d0b14001c102d403c0d55080c0d1075104240c1603040000d0040103903048411201500d4026000198941c0c800c0144406800c050f244c0c0e42c814855600310401785607010020340f90815000c01301c1203181c1110741c912154100c080c024099448c10401007002149442c400c0103000d248a40190b07410910301c028003950391520803045078056100020f01c0303020000076401c288560102401d08011300c030f9510843c040f800da030484149019907 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 13868927 1250 13867677 13867681
    0xe0a05060d05030c01020304030e04020c060c030a090501050907030302060c0304030806090c1b0c010e0a08070510090509010f06030609060e04030e0102030d0c05090f061204060b041107050307030905030606100503 93
    0x521400031560350305400c50103d80d990b030031450509001707510403241580080c080c2007200c047d901c0e05000711507011003084020302c00f90300c40c80101c0c20319a10161507410282d42d0382c11a040051420301441e44981c600c9800780100e903185040103030403d94028810340c107a100c108100400290044000da410a41c15035503004e0b0750303441541144040c49807a95818507800641d80c00c0e0700c0018002035101034100c00780e94a240c0f0310418418072003a07982c0c90090fa001d130303009a1b4003031105082c50300d5401c100d44031601e0110a96130703507100410000c01c8213801ca003080381070600d4280407082c4c01d40246c0005040c61601049020728001e061200c018018000400b0003820080d5050342d40c1c42001a161540480342041160021491011f001c03903000142160041c4910741e907098040c5050000c1e1120040400c0481c0c900d642c442d40c40200904500340c4280d8015500c442e140340c2c4504804c09011543d00c108015582c1d00518107000d81081e0490b40b155100b070340041c04005c0c40d03840349400740c0517900260910030340b40d03 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 13870177 1250 13868927 13868929
    0x30905060f0907090f05060f0103060518040602091203041707060801050f040609020301060903050c030106080a02010503090109050a06050a05100602030405010f110a050d090609030809090603010e0f21040e0a0506 93
    0x209600f42d000700d403c103003425404049485c06501090203100300b1603044080e1180c0400540617180c5620a06034044071844807110890b81c0510310aa00922030400149800d0a0304001000c0745c640c00c901458950001c0303010f02031202e24408103400480440000c08420703150440040c411001401440d00031840000451500c6d10b407500040c02800442100399240e46e101c000042100200d4802130716284100c00301d180c4c00d82018400c0c401900c80c028060010106a50015151944003404070744070ba40d0380c1c0c501800031034014031051250b41d100b02004125407c002c281001a204054005004100042002c22009070000200c1c3c5c01c4880c2820003a2103000040c0054400e1000750b281441c0d0350040109100c1041804142c04802213080d850310441c10352140012140ba449030302006003100402c0088000d140b03841008680d01460040022030902c148902403800e02600616085a0751b01c0b60841190044d2040b6500030701d0003854050606051412164420424028000c0c64003d5a144085002 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 13871427 1250 13870177 13870183
    0xa0c05070c03050c0120071719050a0201030605180a0e160e060102060f0c0405060f041203120e0d02060414010b1203040e0c0702010f030f02160507030210030905060f09 74
    0x150640185840c07900d00c0e501d040c0540c941c003a8800c3d540c005030f00f072841c0d4043e1404c11160b4440c5c191007003009290950401c0b1440b80c01c50001c0700d24450302d1103400001692858100c84405401c1d00c250040c200791001c0348005010344105801c0b0354031450621449022058000703440305e1b444407203032002040d41c4d00403481c55414440000c20304a2a2540b041020485c100000e03a03541c02160282e080340d6155407505c40d00d44507458143c40442c0380f100f040204019a262520141c61480b4081d81c240b0b2905503590309605144218503000c1b008a01d0f611134900d42d454485c070400c0350205551000d001000c1220074025190380c0001c10003080d25440c2c080f503c413061002d40c40801c40510140040c481e01c141000c542d9600c0e0401d100c2c2c034069418180005085800303550a4418169068540340a29444100c0940150948006460080b54203000c40b141c98098050380054950080740230301009400c6005100102d0302e021180070a040c20102c1d0100001c0d4000b98065000002407000851501c801c240141 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 13872677 1250 13871427 13871437
    0x7050c010f180e040506060604060c08030403050f0c06091509070b0304060e0102040b030f06100c03111203010b04050109050a0303200102092706100207062001020c010501030b0705040305060a0c05 86
    0x198003a49110007003070a11007015507134011030040d1704490850f51200c0802c5514816800b4080012310030441040006078580e0140d50003074841e04100d030404141200c03d482a4100d07106050581c2e21010622400e09004d02050f501c0341781e003180c40100c900d000b07507036a40d59074001e110700b9210510020000e406c1c4025903018101100720a00250f41e5940d64a1814005800c10b41e0007800c2d40c050348001c5446031818400c00c18006069855040d180c003819281a1444511081007a01c54010100c862480c1c0742c010000318045e084010a040c3c4542c02c0100040c0f51003042d401c40c0340521130030314052011a4112a0510f1504030061030f204401c0c00d6844404d001e400340c2481550840c201c2e00c2484c2606d45007202c842d140c2042264239070308aa40341000c000c43c48031603998103030150b04005002d000072840b9440803001c43d455810744541020700c203a041822a8829442ca803102c0e5920b50040c010040c0e00d40905070403550a00d071040c10281075840340d40c0c0b80c0601400c1005442e540d503540c00001409807058070 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 13873927 1250 13872677 13872707
    0x2010b0409050c0118030c060c080d1401090e03090303040314030d0906090b0901090f020402031f030602130611030a050a0909090605100b0a02070e0601090302060c010b0a06030207050c010f 83
    0x2011a180e50b1912940d1080c401020380d000c81c444d0b058442c0381e840304a00c3c075011682c00550340e540180c542030041e118040d64400c1602c03240b000b0407488148007040e00400d00762030f440740007140c0103603d44280e4200b111111100350f03945030420070580026641c00801d540990b17400405440000b400d885c00c40b851803003608518400035040071114010301c005540030b24052401800b01c41c0c2c00381c0e584011a801c0318080c6100500e00040380346510050b00b0190301459104e14121082d03030004941d42c0f200c045900f0580c3c0101c404640000e8090404641c410740d034001031400e420080c01c0340110058641d240d008070380e1a00100940840d450a020781300f0703030150005140d0f800c01040101241d0a0044c05800c0c22590001d45501c07022000034514003460855540031500c4e8084c110039400c080c0010750f400c03005810745040144c0a10f0110151381c841e001000f000410700000154541880144182109540d004a05040c414401e02c0045040441c3d20900e1000074030b01140708110464040c1e4000f06231006034 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 13875177 1250 13873927 13873931
    0x11a040e0702010506030c041b030504140106080313050a06051b010b0907020f0c030303070509040f090210080f010806010b0a03240609030c1202030712030201090605070e18040809060a02010b04 85
    0x7010750340d90190b200c180519001d4080d200304c100c0c0c1c0e0080c40155141c1c040c000e0091164400504046446584042d800522032556107480c2c40684241c0d9094034529004100d00707802c0020394890078500c6803002401031100f990940c0f58146010303c041d0080c0030340c41c060200852855146c80c0c003188290b008100044000b0101e44082c1001d0070001d542e842e0341c030b104070028031500f0704056152800100f5607200b20000d135916481c4ca1011000c1c000949071810800c030440c0e88418490005a580c001c01130700841c01955441c840d441c0c034100000c000750041c0e004007603641140d0b00604c99441000700300c41c0c40f03591509020a460501101c080c4165501034000011075918410100b44542d0108414003105d004171304c501511500c4640103a00c07041590002503056200c00020400c0c1c05000604061380e9000780000a1420b5403615004c0655408554140c0004e020740d01c81c4a4030328181c0c0100e0403220b441c01c1e50005c2d80c03901b952000c415218080040d80f003040c021131310508841c401d42080444801c0035100b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 13876427 1250 13875177 13875181
    0x80904091101020607020106140f0d080703051213080711010c02090a06061403010506040504111e0405101e080606090301060305010c03060602030c0c04020a03060801050f040b0c040e011a040e 84
    0x10790140781c10501603005005070400b14601910500400041c1c907042c400030350107880d64908010030344840d201550f030000a00003400300460b03000c1c80a081c0c000d0103901c031140c2d610102140f10005010003400d011500d907241000c04045420042a6a0039503442049104950000c0f40141c03114413501400079400301542007040b4580a40d90403c008a03041c503264103401000032100b492050000b40280c542101080c0403c0055145c2900001c8003030741c0c80c84185183c03000750510200c0307400b8045000501c0c400005030030062418000c01075800000180350941c1c680c901004400c54240ca1125003004011105c408109c0680e00e000031110341da2402402041105d9076450814007070141c0c0820003020a182420004007540084100e03014490410098107803003010804000094001410703039020199155400301e4141802d1040d00c0c090786a0444560941c40c0a00d061b05620a005198000081080c4002c0140342d8034041d5090540d1031600040c9182c4015035a01100c602036030744413121038121241 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 13877677 1250 13876427 13876433
    0x311041b1205090d05120703020f13030506330112140108010b03030406080c0c070308040b03090c010302040803040302040513050d0c0b010f03030e040216050303191503030203070b0408090409 84
    0x32240780715981d14240095a0f6008000d6114148082c0c01c1c0007181c0c0c20404d0001500c52800c8480c1d12907030608005040c000c0304100140d15400140359550030310510783d8140140700082004680c01000f41a25a80c541c000c240c402e041050143c20205d070300c60304d0302d140c41211b80c040c003000340e2600ea00c014204000783d6417541c0c0000480080c855901994070300003d1140324200401207505a030004c6d20f40b08280d860701095140740e80c2c04000441a10b0040d924044000360081c0c004000030107400b00180e44a0800401c1c05050403506000c10b41898410001000503c0e800700c143c60403070740c04580c00603e5a4550411102d1410240f030002c1c101e01981c110054900d421039000000c050040000f1089aa21303182c0004428010b8000075011420718071030b5072501c1c5070a80047c02200000a08032480b01d034103658591458000740e078100c10352b484105031080a54800d11071804411a4000355600451840d10302a45074454070001408214a0000245c00d008411040b181e440c0c81c007610422002890742 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 13878927 1250 13877677 13877687
    0x60801020f040314010b09130c080303040c060305090a111c1401060e090102090604030b04050c10030c02011a06070201030213080304090501150206040317100b04080717030a08010311041b 82
    0x20208846401c20340003030b01e081c064140700e800e406c16030203007000441d80c440c3c01c9401440e10101e038044a00301107800001c40c84407800c0c0701950049100d45400700c0e40f80d04284014040d201d0051a4081d00e0b1b002d51903d00c0801c004078205029940c0070703148629100d06081308500135140341040504140e8007000c801d900e200b01540010704446c2080000101a2540c40c07c480c00e07032203544901603100030288014008500030540755a005445103040ba104d90b80018089865030b00c004000201203903907200074481441d02030040320010390749086c1d290741030b480c07880000d002800740190203810154086420b00085401d5400700010b040751108582c1c42c1e954680c41d10700504001d00036090b0031890014450881800091404c4c0510762540343c0c202c40420030f034a003188480c0018905811304641c05000181540d555008201a003406005411440e0504502d5699040780c08055a41039104000c80001e01c2e901001c441d05681e0310000441c00310a0240008001c1c0915900128000c0c0705c1c492000c070429000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 13880177 1250 13878927 13878929
    0x1621020d0227180c0a0504080d0905011e08010b090a050d050f010605010302160b07030209040f090203120309060708070201060b040b09040506040c0509010c05030705060f04030306091803050d060801020f04 90
    0x5070407080c4041c01c0c9181407080303800720282c0500303c0c0000caa0115412107000c1001d051511220b180039030402d640c1d6944c0501c2c0c04808445c420206c1c604c441c060004d540d1240e0503200803599014012810b1486074030080c2280014416200701c600c010900002c03030b990300101140203040041106444a4190401684445440c814038040f51b1800382c3c0000d4650180c026591440070700c0c1f11309500640e9503140c00c4c02c2114010031800030140d080002003076950b2540b01c0c04580303401500c000035984400344141031500700d1400d0400440d0006104002904400041c0f09031300c50700500d007124080c2c8a810b4264003401d91342d006201940e10104010070f56003c1200600450101120203101c0c83d19550305100880d50179140c04000110304022003602540074602c0042c20922a40031a8641001a200c2c00d061500030394004480801e10342c24041456071600504003d4888900100440072400d901a084c032001b00f81d00905000020034143c0700006580e20042c000c0034440000d641c5c68190070050700c49a802 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 13881427 1250 13880177 13880227
    0x703020601060806010804031403040201030b0a0f0305070806040b04170405060406050a021006080309010c02130e071a04050307030314130b09010207060201060e0c03100312020102121621020d02 85
    0x1582c0f000515079841540d409004680540700d07d40403803000728400c94240c2c00100142e05241e1901140306054440701d04083c001c08060300320a20003804c6190083c28040540e20904055120708240300101e502c1061031078006900090b1480741c0006660443d05a0042d60321142d0b010f40081800256150000010715038404640d0a94150840c181e05e002d0442e405030090807040e41c424410741d210340d40117290108046000402084d8141004216001983c02407400034403590413407182046841d240303000a190314920440450305040c10040840d0703907a01c4611020f13003000901a6403d0b0064529000c4452100640141100445c0c035280c04060651000048038014402c09000282c031601c1842500c0503101018074110f09925980c075080295003010b001200c801d000303200d0010002d80d07030b1088042000c081d6000561541c0400e0311f04240e1140c0103144040c441a541d0490740f5541c1e2003000312100384001c8418003ca100b40f200030314001e0041940301c1824501c001765441c1800c031501d60700e01c19480 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 13882677 1250 13881427 13881437
    0xb0c0409050c03040f030e010309020418060605010518010f0302090909010b0a060306140f0301060f09150e01050607031124090708030f0304080a0c0609060902040c02010b0d02040e070b070302060106 87
    0x2ca000004030144811a400781c0041c1685108000180c0319117030480e4a21030524004c5420b42040e0001412224130710082e98010700328846ca8001c10503a4042c0500406c0c0908001c4c1c00c00d14205041d4403480707101d00340b45040082034084080158081e505403040154058402d000d40d2a10b000158020011003522503c1140c40e02d1000950318480d000301000e13950864403081c82d90200307000740001c03c0031042c400c0b179140d5200c400c0418480e032606510b1004058101003c0784002d80416070a03101020b580200c0180c0c101e4100610042d01c840d0300704d9084592500d00241c12200005d180340c02d0084180d050b81005140b00141010600a254100d016031140070a41300e1a59541070110f0342d80c410404616254002880068041568800900341d07007034480c1040052030256503500406c860724800112105a962503041c01581050b21880e0004880c0303000070440464840002020350350b485a0081c45130752920100001014203025030b0004068002d03550ba166002d078a0302070740b00e4009014500000d2 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 13883927 1250 13882677 13882681
    0x201110111070201030b0310050f010e060d020a0b03070903060203010b04080105090105070f110f06010b0c010b04200d09020a141f05031603140123060301031104050907030b0c040905 80
    0x54184901d00c07414008100a600c1c00300c5030360055010304080540140e050041419440030b1080c2400360901c2448556017695082d81041c814580b14400504058000d041241070a40140c540000c00c1e410b80d200c1c00742060300c0f6a214081105c0c805801c2d0001030002d4000f2000190111082c030107803090341c00c0e4000074041669400b61940c00c8920440324203001495140c00d003140c4500903007185043c1c12014043d1100300c01040071041c6000401e90000900040000f8941c0020768284614005154200c6060002d804401c10064500e081406041c68010001802e00b00c00706240d4840310400358041c0401c5881c65039884c0e9a480046603030340c45070145100520112083e444035418906440c801d480305411500c8101e14001140c0100031f820042c942d0380c2c292040000400b0b18128020421014540c0c10781d070f10400300d001c0158180c2811402542c05100500c0002d0f000480402c0c090403d4500250983d2041c05c000c1c40e004c3d255202a181d00840c10a110300b01044a00500503980e80917001c1c8010f07 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 13885177 1250 13883927 13883957
    0x30109140c0f0a050d031205090c150a0207050f12060c04050103060e010b03041104020403051b01032018011803030504090b09061e0a05060d05040501050a09020102030703050903030403140a0201 85
    0x403101e0b144403907201000d06028030185c90700071241c0310a58000e240180350001c03803404038001c549065502140c2903114140d608614031f440c003002131408041c052200d040080a20011b980d5054038003074180f08101d0030200e400d01d6198480030b51050383d81c19007100c2c15400c2c0540c1078001c5030300901500d40042e04142c07011031044c10650009049525a410240c50b50755640c4a64411804015645500a80820000000c5101004000f141d44000680c0608076001000054111100d802c3e288014001e00402c01d10361a92160949203107407032002000c6240010b04004982c2c42d0710702e0b0541114205509004024594402d02410542d4460f840800506281008000191314111042c0d584035000d081c200c64150031450b030300750a001c001742c4036100154980d80040c541c1d81101c0b0f0080692950380c0b08000074080240140d58000c640c41008004090319600001e44074840c1000c0602805000174034540c040d01c00b0000c4800442d0000c44c9919020755218003541c0f52429401c0590018030802030385820 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 13886427 1250 13885177 13885189
    0xb04140402040e0703090602090a03050c01030c08060307120501060305030c030a030e06060913060609020d09020a05040504170c030f03010f030204050604060f2105030706060314030307050406030b040209030109140c 94
    0x76079083c0c00040440340d9402200320081d00c4510300c00c03111540c0070f101801868485030102000307107201d5409802c41c0c900180004045610183d800000c102d111001d110302502c1c08a081c0041c3c4980c481000e02091182c14070718090040c03070303000401b0b521002034006980000480a0042400e01d99001d011030703201000007541e103a0b01035800a6100e850341e40032441c0c02d8030f00d603e00400c02c1e01c1131001180d0265528454001c0303030440e0716903440c05601c8401d4602149071080200d00680003c843c10440d505143c0c031424081036800a40f0001060300003000c500b482c0e02001528107200c400c48101c1c1e40c035a12210741030505422444100c0c0120b0a0401180c502d150a004e604140c0d040d2003011000c80e458901131030006111250b9000b41445407044981c04a80c0500c000c01c24280500000700d0600d2844c50158041c14440090300c0048d0014824001030a074800100ca0440d442031401051048490f800600244a42503c0603071540c40c00ba5a10104100310008004481550045d14038808250040c409 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 13887677 1250 13886427 13886429
    0x21c090302071203120f140103030302030117060906010b030702070f08070f090e0607120b040609020909010e150904020418060c08060409020105090402071e08070606060c020102060714130b0414040204 88
    0xc1000300100c11103807011684001c07504191b03014003042d0518611a4810716800c02e0f00305a0000350008018000d48401402d0903221040110040466140031000390707454800600038954600c8000010900c12403081022801400d0101c420b2403041c2d80c0d03128060b039540fa81384140b8004850468001464a4642c0300d40c1c0003a40142010b40701d180d0720710008564141912080c54840d5541d80c4000132140c6030b86c0308400280200540042c0e595900c5000c00c1421001648202e460b040c6040c02c1010150309581a13000d0148252030103d080e403140d10004014010b10f116407102d00360300160382801c1c0000c54204049824441e117902520344c842a0034441030724003001e07019001c80d03c2042086440e0800d640200300141c0201030181d01c80c2d4502180400251411500b0b5400e0200810010300340480303441b403200281540d0410002d41541580041e4607400006e082c4014400f80070292036240c0c080c0c100700c2d0543c11003042c3c1018202d48030019a2000c0c0c0140c000d0540e074034135500401e82507040500c01c440c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 13888927 1250 13887677 13887683
    0xf0e0f01021b12010c09030c05121b1f02060703050f060a0e0c0d0c02030406080a060509010e0402220e1203011a0a020c030106060c05010b040501030b0105011101021c0903020712 78
    0x342d07440400801d00c40c211a90000785400181d01c00b221400c42a00707129000780c1a19035600c40602c43d2540c140f0324502c83d0301c0e400c5140304064503440019501000210a400c03201d0300307818040065203140025000d0100d25080c80034050202c070704501511343c041510752103000300781c0f020001d944500c984034801610440e444c5401203201070040c000080001401d86c0e101d01c006c85254942074694000301c0541e1001e680e0400580e0002c9414040c03990401d001d681d0041c0030503400c03c040e40c9032a0001d0384940041c41420001003480020405549070180c07000b03181c94500011235100f2a4465480d0018425003e0901d4a80240300007000c10450000459040b6140c01c20583d003100604c0700400200c0d0f10403d910015803040c00315920007601c0a00800c001454281c40c8c442219040341050f40c00d4810032250244100c0c9030400602c005443d8900d43d80c190341c001c2c40c01078550f41c0c0400c9214020710034580c145c000c01d640301c6840020100300d500400f11092081c0c3c00e407a079141d5115980300040380512401 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 13890177 1250 13888927 13888933
    0x9011107140105070c03290108010c02100906021204150c0203041401050a0215010b031501030c120b01020a0b0406090302010b030303090d03150504020a09080601050109081b040207020901060f0e0f0102 88
    0x10710807503100e000905070407800703560300400d11036036a41d0344c50030120a9420421092410406a5a9011070160b407500400c0540002e02c070a00c0d002100135211401c04100d810255621640001845019410b03a25210000840400e1702e00b0035051510605120002440d4182d0808400704141c0381b01000303880413950142c640e06910803404006540c1900321100c400114072841000e0341c89006400d101d40d0091020f065101c2c0d07a0708040484401c1c2d40c0101480720705140c1018000291941e0000c2900034245401d04009188010400100d00380115000003504a245401c00e0105101c09070388a03000a91181d002000707082e01813404c0c141c8a0000b1190b1018a42090301c2c0c004141e8001e0b000b4803000c0004030b09620a080d1500b00060403038004001d1000050380040302400000000c100c05409002c00b4244824141c2c6003d10295032442c0c0301404080310458420258100d890307d40683e555250300600c0c0c0ba03020f41c1c4038070006200d11049182c0000040c2102140415030420700841040b000d010303405 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 13891427 1250 13890177 13890209
    0xf0a03020a11150f0c070906050907030c02010e0d0e090907062003040504050705220b0d0b0a0305010c02150c04050a050108040516140108060306070e100504080303070509011107 78
    0x94080407400802c00240c2002032100c401502201081c0101345694425084644039079552040d2490202c0d1038201450141c5009824411566400c0340d09a001c101740c40c000c941c4c6c01074001d0480c007406000050721402c2c403070000443c64443d00003400701c081c0301d02030390a2401c0ba6a403242e075076a03a0000307100301c10106600c044c0910002085055071140f0200303000c1141c1c40c140e0380e40b01180866000300c3e6980000f030004a62070301082c011800700504c841c2d024640f070314040d040c045d603c88184038040c032050f03800c0e55030f152004440e100c8541450046801c50001c000c002c403c03850103511020b024810030030031070010b000580001150016130701030301c0c3c019209260203400c0c4001551b00e9407000d00280c5203032051104110382d1504489035100980160032031240c0100300c1c00d0001d00716800241807a032003900118100b00115a01100c05c54840310200c865007407203020800161070604c5140c000403010701000040052640e0081d00078043c070a070a0f40da2010683c417588a464560b107190181c1e040140426032 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 13892677 1250 13891427 13891433
    0x50c040e04030c17070b0406050603010504170a0311210a0c0f0302030903090904060c020d020604050a0f080c030409061701021204110103020d06030b0402040b011704031818050105030f0a03020a 85
    0x900c04075000d218050546040e040e42e084c0c00c000e90030200b0200c96184401c020802040647d005468203c0030640007400682480d96031003082c0350700c02d4444400300c0300c01f148160b81036220750072000b01c2c1c00d41501d0455861080c980c0361207c003c0c1000410900195180c04118544102d114001c42459503039200c1c15400d0004108a000c1d603c06099108144002d103e0140107644918555000700e202d910001403846a244001e8100188841614191b411400401c40412404240d4094140e0b000d07046203243c3c01c6c140f400c0b00d090301942c05c0c081c040d0311001c01d01041c1005203900c0300f0159100c400440095041c0c540c1d1260a1748100c1400846501e007170008a40003c000f6145c0c401c5000c0141009428050600c10b20002c40f00164001d446440c546030900055041a03c15904096020301e0241686451205035968104004d4002020442c0d0030344112200030820104d036000e01031050307031003c0d101c802ca00345001515081c01814482d00507442c00b03442d0b201b000610028071907410303006007000c851151 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 13893927 1250 13892677 13892687
    0x206040204050423070503010b0a0e01050d03140a02030c1e0d03051018090b0703090c030f0203030702100f0207170c0f15070503070c0504060b0f0306030a050d020c04050c040e0403 79
    0x3d80225a0341307180a40342d105060b00301040f02d0000e00c1c808000e154440c6400209429121100b1090303004201101c010302c160380180c0c01250554005944500301c100f1030b0310381104e810342ea50000c0050903e02050460ba01c0d0b9012008046098a00c412074092184030441c2120181400985240651001d02d00090503406900180d5003d400d08811110f10395498a8600080f404c109800b00400d603074079940c030204502c0c09181e941140b8285001c00c8281c100d651030603140c00c0d05000181020024549000855604000311210281e016010b0074484c42d110002402c00c0340c5c40d80c41000980280d038404136204070081541240756032a000144042c0410a040c00006070441c0d43c0c960f0000c540d06038501c5c00e079121070b0003171240038402c4c4001c1d9590315103030a01c0c000c052003a4211610450412000304214603e910580c0d1803400310b0404142c2d2a107901002a181000025005201d0f009914030740201d9074007c1480c09005009840c1030066558003000b49d8a6403203580035180d4030240e50800b00c1d020a01c54 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 13895177 1250 13893927 13893931
    0x1006050901030902010207080d03020a02060c0306010e011101060902130e1602030315030703050604080901020d0306151b06050405011a180c0a05040305060f070906030203040210110c090f070206010510020604020405 94
    0x60040c6c4000982302c0721205e091410420200012075000524090400da0401080707a2002c200f1f0041415400c0c284002001a01c011492604202032400e1415070b2800170360000006000c0801d085656581141d4683d020541a2140d8082c8000540001d04100e4000443c407405840c213601562440c0e80d00d4106941d0346520359012038052055010200004038208000c900071405140e210752a2000f02c000245051012a1102e04050230200200b052132500c0c0c280718004604d600342003030392907205408480305240e118000b03407400b030804042c04181701c0194802c035010103520b901940480e1280c4148a50401c2c11001541610414000114003440401c09040c04800d14a401c43c9041e0362078035420b01d0442c080d640d44400380007880034815815001100b403001821142010760851510360001614104941641803d1211400491040c12000e2287c1090085d00900b0056642421071904a43c484116041c0c0d015200e040000305940c50821281206000b01e42c0c0142800e559550a000c050280 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 13896427 1250 13895177 13895179
    0x40c02070506070804080105060307080a0b0c190c020109061110021602060703030501060905092a090604080312060603040b01030f1509030c020103060b09010e0409080702150d051006050901030902 86
    0x203040012805558002c01482d50ba4081c055060701c89051241c1c443c212400a0300d2603100358008801001541c4010500b0340c002508035154049070350f6804103900d6248100950040000650741420103502d4112841c1e4888030300030390310807a44944481c2c0035240309032000360803051540300e07500d800d0b1041050780041031103503400b0150007580001c6901044041e0042c5504030086a281c2c801840304680c091901d0f80240002c41c6d041d070540c20984440251a907510000c5074200c8061548208404440c408031030312504c0c058003090796103607640449500c81d00480d0f1b01155640400d400b00300c981c03178280c0a407401180c00030599a010303440c550f0b4003500070076001310454903142100c050301610b41d6548642d45005002c0d460f0015840120f10006045844540158507036040a010009a51364020380e040320400c41600c0003d19080300b410300381504d008110009510031000c0044044072540c00010b040300405100040c4115200d0300540c0c2000d80389402004002202030040918561003070300700c2004180 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 13897677 1250 13896427 13896433
    0x31e031302041812050306010c060b010c0b07031a03030403020108060108070c050109120314010e0601050c03040801020f04051206010b0d0209120111030907051207050111150907030201110102070c0302040c02 91
    0x10a07070200d800c0d1010424004007945079980740109010005452106000c40c0d40303000352640c60302e6000609100d071407001c00f400f29a580c2d0350300740701a401100300c18001d6400c070744004031920345548020060504a54005104281e038545000302d4100003003901c0030303682e0503156001142d96120044402e034100038042002c100356180b112000c43d2082c0305103031301c40d805209070807841c00300d00d00050140ca50344000c00a00401c54801003203000c0700c040c40e007038001c40c00740b034010303511680030241e0b0345140210b400c804440e5200280d40105030441c1c0300148211201601e044c14400c00072814203403950001d20501c95520030400c00c0288060181d0300070994110300425100d807603a49040018210380d54016911801400001444000f8800708050340040900300d0714010801180c3c034606c0c0c0c41e15002d126103814849032008484030007009012506401891080d0880b407880e00e086d030b4960300c1c01300344000c0c0e020a4568541028000b018022038006e160414010034503680b86900307000081c00354210b2601140 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 13898927 1250 13897677 13897711
    0x518070807020319170106051602041a091302030c06030103080414130504030801050a05040b030304030605072d090f08030306010e03100216050705011b08070f02060c01051602031e03 80
    0x64810501350040610b5a155a10110612481c450040d8180c010a080c010f0900013846504004110613207810b5041c1c1d80400c100c00781e4015004021018505254400b101204004d90b1740104071000c0d8605008408540d610001c0f0300501074244800c0c040a81440380403c0140920b01c2e41a6502c061020068424040c901c0805e0600e0211401554120000342110004021910301580c405002c3c140403241040300d03040340c60000799648110300c0004d12080e2190b00080034180107843c040000b5640409117426500040c1c05c084040040c00a0140400e00d0101d000c2014118040b81c1415140008021440c50b280c0c1801540c0e601c410403e45607241c420004900d60148140c0007070034641e02080044408502c0514206050000380d400040c1080140d000100d110b0508413005140903421803021662030031300b070402c605034106800000c6e4203c0e5000500808103141544560b02c114503d9413a10300074440000c00721386a01c01c136200d0740884220220030b0302d00c0300f468900454000b0b0200d102301c3d040c4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 13900177 1250 13898927 13898947
    0x60708100e040803150109080a0f0c03020303040609061202131202150a110f0604020603010608040606050402040605070605090a151a0301060902040302030601060504030c0b0f0c011a0102010605180708070203 91
    0x240e00700300e0341154102008000e03c801d003540c0da10004010242420200b02c2d441c14000310a54a16402c1d80141520f02c2038440f00007401032a00c11240656005802e607aa9141c80d00b6001d041c1d00f0700c0d4412400005c036880e88010001c6000d100391000491022078a084841c130303181a031540d90842c074000707036402041e024144642010400c010008610390b078892012030002c94000758202091b10080301d00c4c2e034101c901080016a12035040302d0541d071290600d1b920f55200ca041035402403c2a81090b60404d10024001c90784a4000020b45491445070300300744400d035204c101507a100c000d0341400a200280d9950341c10710152141d040802c503070044040103200303d41c84c1c0c0000f90a441070307030b0f00211900303a00080c03e0081d802c0c10701c000d0303003d4015405c2c01850245145e40700a038460192046031188800810701a070300e8456542110340303021010009100d81502e0b9038141c01001c184000711805036180c510001128280389c1014645900200400d41c0203a075107034016141844020300c01c07030440c0410008000b035 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 13901427 1250 13900177 13900199
    0x1050106021c0512070c05070905070201050417071a070e040911032e02070c03020402070b0105030c040603020105090907020a0c0e0103110901120f020a0b0409020c010609050906070810 81
    0x92605500030728020096026004190b1101840101005002c006a101c00560140b8903608860740b450084a84400b0341401ca0502a09401c0071020764240803d02c0714069054000c41d00540c00f0708801c1410002282d95400348e40301d5007000504003480019501400d00f1006a160f42c0302c14142080221003ca0000040488801c4402141e400c8144500000f05040400002c4100c110a403404425054080500341030100d040c04211607954000035003804110140b8440001168060005d548030b1207140780900c00400c1c2402002d00900c03c0c140700302c8481c50f00f40a054101c90301070711007034682241d010512800318801001f4206500c1070702000340008200180c140001e245045224811794107514000c445012014003c511421400006002460043c01034102c010740c0700f90024440c221520114009115650100b0390302c2d02c2c0030400203600c0d0310980040c02921000c0000b08013040d158220401200e0058900e28265400711000a114500580801c0c0d084440e003034000b04005c5d611410404 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 13902677 1250 13901427 13901429
    0x2042406030207150204030317040203160801020307030c0311040b07050307020d0302060406050708040209010504020c010b090a0207020a15050913020712030204080d020f031801030902030307050115060914060a0e03010501 97
    0x100007030b40080c2c0d003014031048401d03000120315040c001703514261464800900c4e40345840c24a04007064000c001c40c04540c1c2c100242d6141c00c0c041c410f50307401103540c0c3c03c00e20700179001202c07c40046402c105140741210320130304c1040080f112080b08113040074144201c0755010380040130121400c1c80200500c202580c0c8a8940040891003907005102518051a00310b098400150903030060154140500006940f10b000300781c10344105481c0103071120840c1034018054040d00d280940c0101c555014410340441d00d030002c1c46202c0c000c0da005002c9a6550402800708408414013200246050181040b0b41ca400b004c000400804110003508054450711411884c821b50401c0d0408a9400a0700700a40f90f014081da140d0620503001401310402030b003d40e10703200d01c54100c802031905843e03a000030301d41e030180d44050103158020b41100d860304103d01d401030081240441c0344032101c203212000100b551040d00501c0035030308a1180c00700700c0079030182481010b8001040303290a000d042c82c0180c20a4400344503040c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 13903927 1250 13902677 13902689
    0x912040b0708040f1e120203071701020d090309050102010c05030f01030305070807060606120507030b10030c0908030318010e0d02030906070c05040f0c080901020f04030b060102190506090d09060c020424 89
    0x40026100c0032030703219017840e4848402a480c030715030b850160384d011400400b150240c4003042c0c06000700801040c0244a10f00c06c1908031444c00d08060145076001103041d0541c1d40a03002080300d00440780e011b94080c001200d40b1a960900803005100003407091000e028141d101d050058100307180c0c0d0703443d035040d21411b030422000100400d00303200b61148a070061940000240c2401c0203c0c4401c3e0002c90b004075001c10701001403545410808a005102d03680304030007001c1000c10f80b502c1c2e0504450414007400722074081d4191b5801c2c4902004412800300711454081450f03002949003a200c5000c1c8101604244810344405a0034440010161287d000b140180b00d18007070001140f480202d40a0059a00545105001e0b0f00c14449401c80c203ea11044a040d03035000880c400859a581d0300403860503205d000d102e1540702c0d480076440100000010018052440036040c3c1d0044500881c0071500f214076132143d000055454000000542460341c440442c5000c0411145200040c4980314800c084030741e80b0003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 13905177 1250 13903927 13903949
    0x60103151d030c16060c030c0203031902010b0a0602060108031603031103041103070e0709030b19090305031006020c010504170a080f0c1005091f0e0106030606030b0912040b0708040f 80
    0x80041e04003c2c13010700b80c2e0307480c4d036008040c030507041040040c01c5500403803004060020344648002959010400c3c1c07008905029103141e54903d00840c024081e00d41003e00d2406180d100402185580c00884d4180c10790350300c0d00c001e50804102c0d050348449039199000076000e040d500d10f42c1c01e6460410400440c406da02601e40810203c2654007454544241a4002004100039005018000c0d60058661f81102d40003041c108080c0c40300302c41d410600d01500c40c0a8545898400f089007050b400901451081e8051031904807002e50b54842640ca8400d00341c1104d00051040106020050f412136407000205c507540200c60704440c142d0758102290340302d01d100b541403403800b01e485003510710100440000469035000c140304d030f801d00880c601d81d0f43c1c005031401541c00c1003950b080005074041da03000d18000c1d81040002d002807079890a0800007024030f8082030b10003900860004146034400aa01000e088101c0402ca00c0e0500e0302000d840c1c280c01c030800441d07044904003c0000c1c0f92201d40c1c2e1490250a5000c05 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 13906427 1250 13905177 13905187
    0xb0415050408041502160b21270105010302060306040c1e050c011503050c060c0a0605040b010302010f051602013213080706050409050a0e01020a030b0f0f03060103151d03 75
    0x988022013145007000465003c1d5020840c0040c001444908841c2c042104549420302c60820f51245040e00c5011080c891a640070044082c400c0c4211b009070a4180851903c1c951340ba020840c2a94403d00020350808020008607201d41040c4e8044007481e0500d1030040e058890145c2641e104005d507400030701c002403000c600340c44003080a2203149400c0810103051101c980c81c50b5900c5885941184003180714440102d1408100b40041c000700e11070790741c4a00100001e20b094501700400e02d400f0b00050b0300141c144c011554106005204540750b5030342001048400307404503401110f1003104c611000640541d4007100302c00002d0352144002140d28840c80d00d50b203810b1000c91f042218445a4004100780e40224030410460750008120383c16a200c0190100f03030381e5a04442d4101a00e8a803c0400341c541c070002d611100c81358594004c10349114126800c43c840c4851200b005082e040c041e03055641604490010000034917605000050140d07418808074001c04e400102100c44110404c4c10110340e000010 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 13907677 1250 13906427 13906439
    0x30318010327080a05040e0702070305010513030c0605040303110c01020c010c02071a03060609100c030f09051c02030c0901030b01080c030d05040608061302030c04030201120b010c0b041505040804 86
    0x2441e40e4410b0340c4000c8404070921203010346640d0300e210401410f07003100000d452031540d01c108200d5019000d002601d84a42c10505c0c4029640c0840c0e02c01980d03d03528080205a1448919800250083d056a62450302e00d1458581c8001084041c10440c20716607103009240d07444400c0009404211b051000040e26500c101c0d000360700b580d98500900d400c54225100030b0000119151402411031800801140c4a03994400814031714480d2920701948111080d071401d201300c1d484108018010310a96910644403200401a184000769000d030b071364440d400c0050001000c010704011200039000a04031040a1210000308142603001e80098440c8119980144040700041000d0740c00b03404160010844000d40c0301c2c004081d40918062001005031070310100e805a61210006025894484402c540d28106800411001d5105100072800318003038116a1001009a1140c0e243c41d00301078503080c521881aa48412460b10300030f0040310320202410085200c2c07200f40c4529807141d4810554940e072141008 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 13908927 1250 13907677 13907681
    0xe071a04140405060102030a080703091a15040603080d0902030102040905041101020609060f040209060d0507090b0a0801020405090f041b060309021c050d0503090f011802120607020604110406050303180103 90
    0x7032681c07030007607090070140f0015907400400c4688806503460414025100c81d00304038050030a101e4044c10100308008000c12100c484090180103c0106145600200010302444151601840060940e0500384017034100788405800c13500c6950300c01000185010b0301c88191404035017003a5401c0d075000f403c2442d20039042d6010447c040d0001d250300000d104a00e8140402084604000c2c0028001c0c0c2c01040800c525448940c00240895401001e40703030415240c0030000d000380340c1003014500c205405840060902ca0600c00c030b4080d900040c080e56195581d240d000542c0075005072007290840d00d103003586209040009000e0001c0c210a07500030a0080709801008031215010344054422241800702c4000075800050300d220f01011400c20381e840c1e1380da14040740e060000c1c58125034141c0d42001002ca9800044402c2400514421079481442c10180e854460361104112981e1002d81d0051002c00e001c16259a611031000c04c00420202e00103455002003070a5802449140110160003422105150303094 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 13910177 1250 13908927 13908959
    0x90f0a110103050f0408040513060918020103051005090412020c0604080705090a050c090d06020c01020d0e0d03060605040b0c07030c08010b01030509030c07060809030d11040602060c04050604090e071a04 89
    0x1010140313920704140e00c1782d08580c800e40c030540d0712482d91540d40c104040891b070040390051144850801021070400402c24000134044022400a80303000002440d030858007101400382d4501524188140e540c030380e5151401d000d02e210000651150f19590800c0c2d035960001040038000450103000c80341e180100b44a400407006e44800c0c40705041200300b0080a109000380c81c2214003c5070075220212060070064001d00c988140c801c809c2d4000103401c44100501e41290310100703240000c480c59586a00c2d4110101e660500480b4000380042000300081800c03600600170700f415035020742c0d0710f41d9a240c1c1c0361104030755a580704e00f070706e40d4441501d0402c13903030035100707065002c01c0c0500603514100204107800d4950741503014403400c2c0240c42021400c01003040064030903081c1c100804000d00300311491200d820703402a101718001841401c000811000301c0ca010b490031508080e00c1c1030f06060412034a180036000480c84005140f080050018503040702270041d80051810710350b500e43c0c0d142440c81561202c048 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 13911427 1250 13910177 13910191
    0x6050d14010605070f020f04021303030e0d051c02030405130c0210090804090f02090909060603190f031101020705011e06090203010f090e121206010e01020a02030c0603090f0a11010305 81
    0x1103840104107142d0032004488006074001703604080c0d58151b100144078141043c0049402038408140d030008880c8040b654001d4074001e8803a00c3e500c124100c00c02400c480503150040403a00140640051011042402c0110b448c0c1401501c0c01e198a0340301044078000c1c9240031039601600c0b5881c050302d00d601402002c0030381000c21018000100c1c10b84680c0b075940b080d8411902080d80ea044203000d50a1158141d0350070038001002d054560410300c00d921b030781d03c1d015925103110b40070784040d41914002c00c0e410810300703da00c011710340399078115a02c0580350100307a05c0d142b1140e95020803161000500a10540c03503042d4213001020700640c0c20001000c00c0350015080103100d0f0b803040005200c1c0e0441007000c04100e0f1108080443c18640301d50181e410701c0803d025010b1340101c04100700107003103050311200b440b414080e0b03192000010050012a69081058006501504444420318003410f22000450b4848207c070103c2e414003c172081d0b03562030702403940020b0b20b456004c102c071a0010340e80f5010345a08051 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 13912677 1250 13911427 13911461
    0x5010e0f0d080d020c1501030b010e040c0909080c0a0b0906070c0b0f040c030203030a090513050105090403080403020c0a0305031b030a050d090309050a0e10050103020a0e0405100305060106050d 85
    0x16200c0082240480c04580140090314085060480034510790101c0b880a003202041c0c482c9a8000050107502c0682800204d8850091400124140ea01007801510594015901103261803501a82c48014490400295442d007410001c0d044141c0c8100b0110001c0d034840c40ca0105130386401e0308101d081c444081c1610702041178041c814004600e1603c4001d80020600107842003945951a1560500b42c0c642e00081d0507000110f43c042c0450b81140c45401218000d031a01c0001041c4010740004685090207015400990f10b004a40480c0c414810154054440d00403160200810000a000b00d541c070350044403d40c0c400103425448032089100080c1c008400c0b00103504159020001804038001c8104a007019a607a1610109040c46440f5442c0204030103401040010707201e0044885400c070454807455030035103441c00000ca0354032030310031906e1805031581c484141346040c108110180801500a104041d0380172170210100f042413042038020046500e4441d602c800d18070700c510170303981c0b00d011a8200603 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 13913927 1250 13912677 13912699
    0x150406090b030c040b0f090106080907050303041203050318010501120215031e0c07080a0f110607090b0c07030812180a0809041d01060902090f04110409090f060504030905010e 77
    0x2e01d0001d294608400e00303c3d400b04145c40c117440481c2000c0003c02c1090b82c8100c0c00400019840d0300500070900905030102660b071182c0d00c400c21f05950344507070301c40d03051000555403400700424410400355402003c5203d840b04203241d031940640c2540d0080c0c10006440070303400301071000c6150220010000560050f04182141b4200d80e002181c07050300403400d800c1001c9400000c500c031004c00201ea101552207001ca907100c000e4a40f000b4034861311600c4403404526500869850070900242241c46445544e940316000f5007880b001c0c00d140c1c2c21403003c0085a00c04c2e000040700140d20100500038031076541200d501d840c41c041681d298003801400c041c4495070800d44081c4003040c241811204400300659010800c0c51031740c940e90a01e0120020020700c1546441c50102c0c0568040d002070003024021111504080d0202c410801210a885091784045e81c00b04420014003946401c4990318a004803a114907020340d0740c641d40e05840742124200e0004001c000240309640c0c0007a0030070000241030b00c0b000c1c000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 13915177 1250 13913927 13913929
    0x50a06090e070e07020312130b010602210a0201061701090b0c03090a020d0f1202100c02010605010e0409030c050d03050604050106030509151503070305010e070b030606040603020c070509150406090b 87
    0x120303214040c90040400080c0081c903100c5c001c00846141c41068044c0005904e441c1c5210941001011000c594440201c400042c48501c005041507440c4682e10a1070191030402011542c90307409140c100c0b044d9500c031007001500541c0401d0a035801c079800b800215072145245007410025100809030f01c2d40d03420a0040c00b10601001540c3c3c0d600c01ea045e113001c0050302c0d03942000c0d0004001000002c200340388114082840640c00300d0032800c2004e4102080c440080802d10aa09881d01800340500140c0e5503a6505082d01c0d0a0300325422190180c04d20100c648801d480d4242401c1c015281207000c03944900510005091034406c0b80d00410711460100084d09111001944402c0d190b440f07954200b2010300030606c5d42a56006600c00c42e40006e0460f080e05689140040c00707006c07001c803004180c0c0144400020030086040403a40b080704000c3c0620b02c0d06040a509800a40010b1014441d900c5401170100c3e858403210705c0341d401040b0482a5400d807019441c2044107440306504020611802d144d011055 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 13916427 1250 13915177 13915183
    0x30917010204030503040905040f020a03060c08070e0114030a02040e131103070b030f150604061107050901050108040f0302010b0405011412010c05030c0702040b1008040507060f140912010f050a06090e 88
    0x282c401c1f00c03101042d19107503810620360368041440041e5100b85100800410484541d0117800307a0a000c0d11500780c01c0d0345d2010191443d00f45550041e000c94a500c0b0401d07404c413070000055078480c420641c018102a101d09140303060344007c0b2091040c5100c0609c4c104103001c0c0000e08840038050460091444e1350030b00c00a01c1160002500d502022800100445c5a00031074150000c145003000d0030aa8640f0380c2e407140100031151081c80c2142a01401202040710705007021598140c50f01030315034070711b42e44480c0d035411400030a409040d01107558400907240290794601405009000c502d05000050010008000a019080004501e560b14010700c076510759402c042580d5010b85844c0301280c84000340d00104015000e095005c0d44e104201c00e49001103a6000303500e25004a00403401c4502c01910303840c080d500c84500c50701c2c000204407007032001021495000e000b80015100a48940c0780048281135a40c2904c0c1604018080e450311602044142c07525480b800e80280321008061000404407401c00351 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 13917677 1250 13916427 13916429
    0x20a05220302120601082109130b040605040203040c06050a0c0b10090e0606030a080c0c09010e010e070f08060d11090f0414030405010903060207020301060302061309110a0806010c0c1203091701020403050304 91
    0x400a207c07000c40200d0800041c1a1020108058140c60050320790a160300c2c001c0c0880b20009210302c0c90080301288509041c800c0d68410390740020002507450800d501501c0c0c5812514802c001c000410310201c00150140d05514010300a8001c19070810303062440e01c00c159103043c86c0080d20703036205808001081d580014a21850307900076406540d0303031600810f07150926003441074241e003014108000141c60162000424120b0394201086841521216004c80740011a2100d0320001107580010034164502998007180c0b03207120f890300b6000c001f840303000310b007094004480d105502e4900f03008200030310012a203814140340901002d14503060800c4000307400300381c0e580030181003a81d01090000440d102503006001454009011a880d86400c144540000c2054040d081019040c080200c00ca0152507040d240d1407003c0351105412513482d14011542440784103002c0d1035000a45100003020301c450104884040e0180c0c2e54245410304107400c0500040c12500b0310740e0079a2041004002050b40030047d18 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 13918927 1250 13917677 13917703
    0x5030f06090a0204090e0a1205070206030f0c07020406080a02040501080d0c060509030d020f040303170601120e0c060a020709150302060415030603080a0504090b150904020a0522030212060108 84
    0x4030082c0c4410098000a0240d5004040c034645130003100310949400103200802c00344140304e101005404541d0403201c50050890083d0801401e0001c0340208014108003a406200428a18208031441d0001404c0d41c820364040c10094110144080075410070f0300549015001400003801400740803000145001c0a403a405800f02d507a50010541002c024070231242183c9410405545901003852802e045038024441140840c418180c07000341c3c1d600c40101244111816156100bc1c00380e42d080910107484d81d101055103a0092603e54600d07a69020081c010501c06a402440c00f03d0504501600b155402128a1000456658100700594400044505460446076030b00303e4240c245c0002d90203400340e90130007843c000c0e020941e84800d65200c0d011f801118001041408810307070080c140181a0b41b040d000c2d03d040c0b001040016141d061903001414803091502d045403820034004001c94680e0348414103003810030700d03008040003075181681c0c84044412124001d06a15450407100c11f59030540c6014003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 13920177 1250 13918927 13918939
    0x806060c030403050a1a0906060d0602070f0c0b0d0b060403050a0204020901021501080a030801050d050705040c0c0b0a02190f02060a0b0d02040203040506090f0102090102060c07021207090207030206060105030f06 93
    0xc811010381441510015540001214601e0002c0d142005007500000096201210007400041007580c2c00500e542c000c841c081d2002c1c50345030321a25100d020754000344094488601c22134442c400109100c100900030021003409a0312100d424941005036a00c090010b03110391014003082c40850301c0404c41e00d0800e541140c0050342d444000d07005074248100205c10650144004000040c0030030040307120b440381c2d403003503a030307000d250381c0720010002c143c1241c041c007034059800380d031091140742410303800402643c4aa04081c5480041031303860074120202118a440740d075070042003a08a015080d644004140d03110300701103450700c04c002c000075500c01004000030306064035035001032429269081d491019070b030080c1c01990740c0d00d418144940c1d00c58054800c4071482c4140c51031003100c0c98061003036810120059024168903250700c5c4c00b410440d00800b00c143c0c0c1c4860141c40b100301d010001c00c64000201844a030260b21180c2904020b81007400c010051810b20908100700800343d410603c500303900100843c0c0b4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 13921427 1250 13920177 13920187
    0xf030a02060d0b030a0f140115180504030318141507050706090303020904020a030207050d05090d0b06030712030804110a051f17100f0504060b040e0c0906070c05010e09010303080606 80
    0x139251400c0442c0c09450320075502207500c24484400c441084000d01c4000a202c031030703454078035008002454801c5158806ea03040e080c4112685c250040b94001d03010385404140701c0298030407c13040707041d4840300702d400c1000c0d04500700700c0c8201400f000e0b010140c0c00005544c6803a2024024103c1c1c41500c00040c2200d644492400806020754107541c1d039083c2c0038004540f10080c844000e0003e6001b6102980c80e44200b00c40f20842d1841102161018000a0010040c520f40d17039840340042c000180810717905009524022911842001ca103070312684c001c0c2e640aa6030b00f42403d0601d2a01058000d0b580140356000d400d0103a03494140c120240051071001060f01d0700703e154000c603581c4411542494080c1921400e000b04000c80d41000001d13211001c0c1c0c210785042e5070344c0400003100c50301c1c07265041000003488100b04502100d400740d40d2102c01040c0c0189052501070006000f0351100d507044071300c06907100c4148055640310045510494040c0d83d01c59495041d501d003d010b030307580145082d110f1400014 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 13922677 1250 13921427 13921429
    0x303071b0602030a1a09040206090d02010c0f0308100602030a0905090702031209030405030705012604030504030503130906060c0201080a0b0f04050903031605070b010e042406050f030a02060d0b 85
    0x11200c0d1005810030710864036800c180d00400c001e85184401109001c2d100c109403600c0740707020b843c2c030340c02558001e08807490000300c0401d100b0a03600f00003007a0305000f50030340444080307801060030705e00300340c825074408030a4600882584032880c04d5070482411580b051001203280c07500071070303044103681044582400365602c00c5401c80c03452081445111070500075405100031031000201400c2541c00131010340d8070041e21400119103045e580f5252141c08600b0301110100380204a04042e0054020324040b480d083c4c4a07102c15244d0b42c0060088250503504503000c10480c4540e2091401030025881d003940b0a00701900003c04608000d01003020007a9920b40700c041c1035880d402d9034182c14402800c00e103ca0b00d040038126449400440e0781c00c5a0400d0160f0601c030f25403042c421a4005640005690840d900309900d203940054002c00885181451501a008404004024109050390103c01094181c2080c05001420072120038660090348910090380060399001e0613504107043c415800a18944154 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 13923927 1250 13922677 13922717
    0x3080f0c0102070f05101509020a090e0903030105090705030f0f0c1303030509040c0302040806040308060616050105060a171207020409020a080307061104030c03060515030706020d020f010e030307 86
    0x808034060640c0b002030404208441390f211402058050015101000b141700190025160600c2c8040e2201c441e003481482030344516400360010300b881d850403840c0d13591690309040d6421000d071411900c5903c00b1004004c68a4290b040ca54005a1860118110706101c07100c0610280003034000c00034480c0301800188010485001d41e1045100000040e070440e541e810301034015403108181600442c240710400700000c6c028000c07282260303858401400fa56482c4d440071500050302510442d4400010012101c28440040c20114480d002d080001500e050080801047ea2102d600020610442040740804610085800c0742c034005060405079950a0342d02c0010000c00c800700c8020340c0105019004202d2103000005090800d10035401002035158111484d03200740114132004002c12510f05051000a80703d400003038006910900d18441034000c132000a06000607500030000590042c072a040800d94100301500341c5101e9074008110b80d0f0740040c4466141d100003084031060080c4c60f2032990b00c801c006 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 13925177 1250 13923927 13923937
    0x6050709060507390311030604020303040e0714030109060825150e03030d0501080607050903060402010c020103150b03090c01090518040201090b13050406050f090403030506040e03030112050115030c03080f 90
    0x344040311915548690130888066044c0410346d41028035510070388041c140061414051a0000c004606080c5040d01d052078417440148501d040001ca4003034249582c0700180a14041c080c442c0c0042605424495170300c0c43e00c40303040310340e59a2060741004013220300741171500b0206980d204001010f06054094050b41c2948590110750f4040c440020941c0d04103100d039220358181d071119001da07165601c4882c000c8800740038000d680784d85900301c580400c00660281640900c10f91060502191000c080d600750111020301e41d225000320f103000003c000c1d441c0010701265000100900348000400d00b8000410201c003003840403a1700c1d444011000c6015a0300410440300107140f01211300b44e480d90714103901034000c6420b100d140c0c02a800c1802c0411280382084904050140142400619903240d4404401910003d400c903a00980c3c1c0c2d0b41e580280c003c003800190b0103000d40790302c4042900c0d2540f910a08458170b210b03c3e0482000075100910000ba07404081e036080383d81182509031210501840c88be800c0c440c2d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 13926427 1250 13925177 13925243
    0xa050303040506070908030c07060f030b100309020a0512070306020a1125060c051c03060b070b01031a0f0f04030203160b0a20040303030e070b120406050709060507 72
    0xc4100000c00c54001003a51044038113a5590484c2035480103070a0b85ea000b600300d2507610f50040c41013071018070b2084808007c0c41030a4507003c41c11001c0c0d480880c58030350800039401d0009454005100c15404d042d0300302c000800742902e0750181ca000303c02d8144e48401c25400020b0000d41c0000301042624847d0403881c10b403011040540d040704498840c000d034034000452840203c20141500060250f00500000340072981200140c182070051141d0a030041e0b0381c00f03101e0814145c1d40c0c00e01003007019403400039081d6148035031340040350b5504605101c840302d11921085171402c40740004004600340c0031801d441d0800044c04c15044c141c0c6452034180c0c00d50085503030025801c260078400d9001d010710700b5807503401004038140070880c50b06008452100f04880f5014040c0200c010003040000920a60020300225000000d407001540c031a00301c15490b41c040038449070703001c2800082c4014480705103d5550403004a061040d840c514013180500107000f5403a0180c82c50441c0d0080e0b2007500740400f8280ca00e820 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 13927677 1250 13926427 13926433
    0x30c100e011104080a0c050306040f02010c020d0c0609080105010902040321050c0a0605010501030c1d0d0c0e0705190903020a03030509061209030309070e04110603100b0408010212061c020405090a05 87
    0x626100c145a9503104085d0941c1e1059881c1d20010301c2d401c0118144c1d00682d0080501030384c10003a9001540d00d040b4051080f6002200d280e004e0300450b40c4080c1c0000500714907a119500f5519040409003581c00682040e4481c80c4100020400103602c0304490101c10742c100c02140f220705c0ca000003030340c00c4d0148285038030190090102c00d104100a80c0d2061b07040c2c0b502600c0801100c00a010b00f03c4030245940c5060702c11156400c4002c40b54038080712108056071040ad82c0c05103064850511600c0b011b4151544004118081605071004940c4202611450414034128171094510b800088481010740710140500c0400078000c0c180d51604021117031030207c66143d802882c00c01700c084680da940122000c16071801080b60105808800000060103103420026803403101526004010b000d078405454004109150000020030920308405080100520400140c80c4c10854442d04010500202a1882004840a00f85100c1c2d10b0009034000d50790103586c0001d1a5071011141441c204c03072440083c00c644 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 13928927 1250 13927677 13927679
    0x60e011110020d0c1115130602070506090c010507050607081008010e0d0801050301020c0304170106030218090706081303111011091c0510150515070302010b03030c100e011104 77
    0x4207150000e001c00801d5080c20403400c140d64100b21410600c425070600150400c0010310b46010602c124180c000c40080d1110910714190b03543c0008a81c030581084500d0b8001c0720030000c00d42018044110810030a003050762400301c41d41e640c2a15031000a00560510100308045582c0502c0301e004200035005a03002000076a8640301c00c1703030f81c1e0003070341c110040000c410000110b003505060081d645800440300c01141000d0800381c40442030009841c0e0400c541d9603800d0000050b9903209024000505c2480c6031402500700300c210141845070a810050330700009000348260081c800340c034003a25a400d0700e02014192a0301e00a50704100d0f0f001441141e65040202814090030618001d02e00e10600b21010008a0701d4401e04540b00c030503800000d001d50b0068050031306450440d03001800c22040320b0940300e502c540c5540002d003006020980d100c405ca107021400600b010780910801100710000c40046081c8000c20050641d218a001031a4000d19111910140300900c00d4000314503411100608548035 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 13930177 1250 13928927 13928953
    0x70207150203191409090604020c03040b03180d0c020f0a0e0106030b0103140705040e0a0e030d0209030d0206060604091e0c0e010f03050601050306091305060f07030b0f0604060e0111 80
    0x2070f0b0480e0414184050802d2080080c560043c01110a0804034910690500c144c000410034120b80040009030407540030440c40b03011010034001000075144d0b0900980c0c99081114220589107a2000301c60640e41c045580b40c0c40150700f01c0b6109103030990448416100380801c0e008036551223104c0e80705003020240d501c004141241c15400581c0c0c010001c1e0390810102c00030707807858049814213461000105074208400d000741c013400400c0550040010001180d01d42140c01310624540c00002d10503600c983c089041c1d00c403460248410040107807944000d105070309025000514601c06c0b80f09140c0500c0c0c0e2010360701407000e52002001502e1941c06003c110f10112010040d00300300d4880300d1782e400214070410f0321514a019100b014021481a51000c0c2950360311000d109100801400600d6000048004200050410091107100c1c50004140c0ca81a080c8920060140e5641030341d1248510640044403069454460603a8116030052800c0080b5044403001a10641b40b00300e0703c0c1e0b401d4061074840c4280 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 13931427 1250 13930177 13930183
    0x30d0506120604051e060f06010e0621010e06030307030f030b01090f080307170f04030602070201050c0a0c05150702010203030609060a0e09070e01090b03100b040f020c0105100603150e0702071502 86
    0x80f01d407140004a017405402c80385980390f5800722400303201180060041000395118286a0080c1031000d400645440c2008144c1c6040078a0f41c62000708064040d2f0040c03010800c4072005c0e036000001a0003c60802042d99806071000344454403040c209036888030681b0b41d40e80b00383c094000500348522105c2c40584c5503141103840b80d01a8505503912941c2c400300040004480c03088600f00301001340107605040c03c5580303410195101c6070059040000a100301c1c404c84c101030001c40d06003881018440e10b5185004280464001c400005030740e41d5109200b508003507600131041307991025084503a18119550000002c8801c1400c0c0c2203001c00011180c1001080c10001a0310b40c1910300805c8180030b682c0e40c462225054451214900350103412010301194400c820b9005002c005030014400f2030031a14404e0b40004a07041031220a0950b03440c2d0381400b0f85440714491000242c1480c2c90305202d070610349241e009a40101303100300c01e0440304c00c02c00144014400e010200c044d20030303035041440310f43e10400005e503 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 13932677 1250 13931427 13931443
    0x50d05030301050f090403020613050109060501081b030d020712020d06020703021b0301050610030207031101111201050604061b0c080a0f0308060d03080c0a03020c0106030c081e030d050612060405 86
    0x101030464003100b260701d845d004c24464451640342c1e009014990319a0b1662000300225a0110383d690748503250480003454500a890181803010020300f040400208494a05c4074101d00d00c40c0a500420b600d4a00964081100030680d540b01561959009440c40820078400c01e168000d4070041c030203c1c503601055030104000c15003d917099002055008168205401c0f01d00c1510540c0d4480940445050300b14060340291490a0280c20403a2000c8148440a0700f91503101a00f00303005a80007503068290350301c200030113000d8030707054071003900b042d080c21009440d4800b141d2661b40c0300c01000f401307542040314903171a8001034000101514003010f414502290302240e062021404500710000040c2c0700d0500c00c0f14402c03526019a01d0f8200740d2125132142001c5c0d0f200045c1001019003c00c030700300c101c0c00240182c40c01544211818880c11340b4000e111424510440a170200c00e441c1c0700c20340031000700c0000542d001180b80030300000b039940707805d0300044010080468542d80c601031402044144080030401da0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 13933927 1250 13932677 13932679
    0x20307030c0801150f0c02041407050301080d17010605092805120604050c0907030603050303040b04060c051e18090405010615051c050903072001020106050a05090708040606050d0503030105 83
    0x140c8280d0f21503030610030060b442000c440c0017400440035076004e141300b0143d8141c0580080d00005500310302e000c40440508088034400c000c00c50000041040307810411203c48015a113242032280d04d4007400c21445044c406110f52001c00c40d000c60000d990390317902c5e04403c0c6591110304590f04080c0549175a401c072112036125032403040340d03201d080701c0c082c54010405600c070700c0d4440302a241d4100c168040204041c00a0705410405d5034859001c40007a40400c001d60182d805042e0301c030301618003032420400351144084585c0405c407003800310548030b4108101840401c1c42c800c845a0701c98907818031589415a01a42482d404540d200600043c050107522000c01c1d1903520018138900c0b9015001910507100d5995000d00803c0c0d0100f1070202c40510790300590300214003409403403074400607443d600e8a0a513482740103454200b400900800d69030b0244142d000034003003075900084143c68840020721112008018101f800395100005041042640c0a0b20244c00300401444102c010341c108669a50000d000346 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 13935177 1250 13933927 13933937
    0x602210702100903020d031104090c020610050d021309080910030e0705030102091e0a0308070c0806060a060503010303081906120201030b040e0606010c080906040306090b0601030e07090c050409020307030c 90
    0x80009402c6030190791851601030b00103015071602414207d00a125040504810000501c00410400803500800d0500d40303455008084900340b021040ca01c1c510140d100380d20500e10800e1460042c0c0712040024a080c1c0c06100010b12580c4604203801c035442500d0b6056849813069a850400a030076505c07a6400319400d40407601131039262404e2500705e200340c61a8690210240c010003c604800080b110f00c0000041d0024040a035039980b1901603070000301084808503c3c1980602c0500002c1005682c000030466030f00c5d900300c0c507240c0050a18801800003a040100000001d084010003800b02829803219580c10000180d517804002c2c8030805400040740002d0514119140c00d28107801200103407095003000c3c2c005074950200640300600e541800b100e0301507040c45848181d0340d407a8041c00085005400103e9080315a00c4c02060051000b0038460515140012070114001c000581c00c00740c403038007000042c000c82812816034080c082d507030146001e180000308106003194141c0044210341c00316260 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 13936427 1250 13935177 13935193
    0x70507030803040b0906010b1b0a05150105100504050f0d0201020a020a090608010b01050415210e0304171603060c02031318050601050c0a080d0207020d0c060206150f0d0602210702 79
    0x100548034442803141c3c2c4a8007230284007041b900046901030b2506008484211141d00c40965030746802c01140c3d51011600001d0b210041141d0700b040080c02c0074181c41c500d03043d443c0c2070030140050812200110080d006071080c807001d10869008225106145400070030300340d20342d5543c406000c061705c0e00d400382c0e034002d50030801c0210310f550065090703c0030713501407070002586007034064011520074141071960fa800191032001d10568040313034410000707400c1101d0051980e0300d0402400d1b0380038004002000301240d0011045106104032107440d0400c2d42d07800034011070504030441c0201e10758010100000c0e802c005d22800020703018071500508506d0781080d40c0c103008503075400f0010358841c0640120b81c5015045881c5003400500144000c00e03c9000d2500018103004c00d035000306003620b03401d040c100d8401883c25400c0c000389404200742a4016413209440080b84d104030301064106012a02c694040c0c501c800c046010016142c0544461300c43d882040501140d511500c01c002c0d480682d03090000d0b020301c3c64 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 13937677 1250 13936427 13936441
    0xc011506020d1403070203040e01060302040e15060706050703020405041e0506060403030507030e01020a081b070e0c04060e030c0402070b040312020406090e060f130903180608061005070507030803040b 88
    0x18500c03402001588828070400100100f0f014140d00040010003140802c220203c0c00f100d60302070b090701074612a500140c443d810322840c10203191000d480c01c0080301250f94088020303620f420072503030b4241c1d015202041c961642c040c140c02034001c68220f07a0b0b0040c1480c50203445d20148444010a904203000700740480d494010901116110b40d000149c0051001c00880000c240984815001c03000c040c411178654072003d4943c0049604800c988800e92481d1310310854102404021240c050444030558441c2418005d940c5000c0b8070880c42400140131400f164149540e5040c03084200035800600107540d200010326100ea00c000044030b0440c041460300741d4908075840d06100b50783c19030750760b0349a584890341020340b100030004005210941c002c8540c404242107131142c491115a1050f00c4a022411541034600642000745104006c030034400c241504000056000030490b03005602968200d07000f030860041200e2903c2441c801400902c50040700008014203007004502c074500600301ca03400f41d19128 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 13938927 1250 13937677 13937683
    0x92b0c050f061911030a0914041109042d0209030d08071715030a05010506010914060307050a090b0c0604020108130b01030b060a170c0301230a050415020c01150602 72
    0x90003a604204140b045401850703e051010034003040900f06220480c81c1000790794075582c00708080000040145004002d40712000e00c1c4e201c0e0302881282c2c14071002c0b103494400040d85c022004502d00c07c0b030f202c445001c421a4011000c0c82270400c0281e02c0c121854005a0f40c07406584a4007a49000707100e8010710050240c811b2141c82d00a04003955410345400e11498001c0d130000026100302d054500e5070164003501c0d40c0800c190081c10340f06100128041c03910000140401c203881c1c0c402410424044c03404045a51240c045942c40100d5003407142d141d9143c0c00d022a80d4030075a800200b0b40200018600b01020300024940c9e100714400d9a400d031460751841030601d90b0b08400003004083e84000c4005000107a410b007900b5a0180001e8005560030f50b0f40c1001000c4081c2c0100500da80f41c12801d400c00140c2001e0050b00003004101c502110b028000c10b1014030b80c11401080f1290b405c0e61500468104030f031003004540e43c43e03940541551220400ca40c0c80340200f40b4040d0401d0503441c24034002403400d0002c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 13940177 1250 13938927 13938949
    0xe0102060103031e1e0e010201050709030803042a0b031f0b03040201030902030c040c0801080d020105070909090606031a0a050901050108030d02030603070509040f03020d02120a05092b0c05 83
    0x155545140c0341c2c0441000c60300f807401291109050192000064074140000c00345412104c0103542c6d44494880000006400c44d1005080602000003a88040c0042a03694085942250b4010386801409500b1540d0084109680241702c15941141d400040c051240c1409540266002d50000d08009002d030486805000b441c400c2558901c0d05000103000f56000307902c1980c441d800541035852071444000003408880c29180420042081c00c00140071200302007100c84a01402030008108500700f281010741143c4840c81211303640c0e61600300300e00c02c009080d0043c000942c1d222a500c00400c490f0101038402180407591400d03a17516040c00a000d4507014083c060499242801440c948401500820301a6100508154052054a00004854880203007103442203000b04003014121115141c000e0410b00301010050466114800f81138818075801d04413180c00095052183d034802c00f00000c0b1780712034404522640c7c5200034110140069101c90200f80b00d2030310490342c05604031f49400400c07030b00c4008 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 13941427 1250 13940177 13940183
    0x180a0303081b0315010806150408010618020c06040b070c17030708090a0206090f010314040f02130209030706080403170703050a060b0f0306010c020a0b0307020d03060801090203060a020d020c0a0809010e0102060103 94
    0x1384240310581d4000c4076060380086025206a102446100c0d0702000c90740240d001d160070340c2d51408104400281400480d06074049600254501140080c0d0166102000781000c3e207540580004555418000d0449000071070788801d0b855140040c41056502940044500401181c0c2e820f0001d2900380001c180414402d80c018011402c095071001031000109101651350306255480210700c20320603050301c44500c5a40304080c1210500701c1071050020b10307414018200c0890f8014010750403030b6540443c0325400d91340c01d0300c1c2c040c5071580e035800c0440e242106018414070002c1e496003032100455058000740c1c45085e19480521200d966404400c030303d8850540509070501050001c0b82c201e41c4214603650035540000c01c0340f480145c4030b441c003914581c001d82c0c0003405a80060441c3c2d8459405006500c001c0c15100000c118200942c0c000c00d4985038001c3c80001c880341c0c0080d142c0a90226030341075903914900d05084981d0724000c1d00e409005944101130315401300e032009405a52035071000130504c4c10303694 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 13942677 1250 13941427 13941451
    0xe07050108070503090d030b0a05031009030e0d080405010c0f020603041a060a1a0703140c01020706060b070f02010309050f0d020601080f010501060c0807020102031606020904050108010c020d05180a0303081b03 92
    0x780396030708400808c00104426807012440034001590ba030b0030040e02840b000e1810001403401c40310715020740901c5501480070300402c000d9034010082070148090324100ca6080c02d0140c3c040d0924079105080c0b44902c10000c2d4050004020302c001d0111050b44081c030030041c6070030841da68603030004101000d019445600000207410000010b8400024083c2845a2007410300040e10494100240303103d401525103460140c0d40480e4480900000d401030300000c00d40c003c4054500750300313074561010008010401031706040c0ca070030040c810801c04010290200852806a0ba44403112940c0251101800c1c41881101e2160300c0703500b0307903200b010700c21a03040700d980da1101c50006005690b0b54040b908012410b905601092003c926440310f248807000c001480b40b2401655450004100422100e041e08604620780c500394005800980006a00014a205080c016100e4149030110100781491100e0704d0f80049040c070001082541110b00280548140ea01d81015499164030a0055020464146854134 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 13943927 1250 13942677 13942693
    0x3150f04050c04050903071e0203070308180604050109230a080a23191b12030f030b030c041805010219090801110306120309150d0c03060b030a05190e0705010807050309 74
    0x300104231544440700143ca04e601020542d40000e410b10101d035000713450764a00007602d00b12400c20035140180e840d00440e240d5062500b021700007451403c1034080c80b000c140120072100ca014010200081c1400070003405a6445030311081d0703441d00d83c400404c04940c1005450800003070751103a0049039a64610240082029101d007409030126103400e1711042c0c5040c82c0780450941a60407589145000d400682c40340c00061043c1c1c54010495405205039204140c90301159003034951780801d0031800140211004280c600d10410a20001182500d0007001c0350320028400f013096201c4881400340f50002e455503a0450750f100049820ba945545298014407001c20000c0c440e4a8000c0c0324480084c907850880e4102200503000c40c04119207040030070040807003c02d500c3c03448685800360382c650b003410745406d000715450300300c81e100c00e1300000e03081c245000e80707450000c0d190364080d02840301c00042c848030510104214101c11078442c0910b018030380c00601d182000904050003101101d01a818140041c20a0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 13945177 1250 13943927 13943933
    0x4050a0f03120504061b020a030e0f040b06030a0501030c0f080a020616050a05070e01060e0604140402070b1510030b010203090d0c080a03120606020601060f0e03150f04050c0405090307 81
    0x2480000c2401c805200104203030b0300d0071000d24450075110300c1c4a4480081c01954141400c100301b4000390300c6004540c000700010300002c1d480074030801518001e0303401485103900c0c1400100900b800e40804d0340c000001004010b540189038001c00c0c102c2c0c2c094081e03e4081780e05d174494450f9594250050f00c8483e03000f0246c40300181090002480c141d592540c00d034031024515914981000041c2006640c1d5500c481000d00101c0b80300f2401500504040c00c0900c40030007070801044090282d885144d1510800c6407440c0110b441d90340403510803a80c030007070800040c030307007184044d140c0819010814080c0d0149401e640b0050301038800d0b9080c4030016002141406020000c10011605031401250501102c0d4000105610100a08102d2501c80e45844222040805e481d0342110320591000045503c2580104061b9410020315032a0300c4c0c6c80d1a02603180510100400c2c40c0010300044079140c02d008400b00011000310541d1a4000c520076401c0d41c3c0d21034803503404c103c151441503641c3da030f10384c100700024800 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 13946427 1250 13945177 13945193
    0x9040e0106030b19090803090a060c020105011a0c01090c080a0c0603110f030a0902030d05070501180f0201050309070b030106090e090604170c010e010203130b010e070c11030c03010f0b01140304050a 87
    0x180b44c00003c000716075488150343c1c40341d094000f5070340d031302c0c0551140d40e0b04810051240201c950040d800d1000700a59071400e52030034914615066152540310000800c1846e018081d00031440041d00050130001071543c0b5081140c0c1c03007207040ca043d10844480310300824181d11a00036590b41c054145012410319041d502e40078216800039080c501404e45d50f00c80380300142c5044c044c2c14039504498641d15241c61450414500359490300c4141c19507040d000d802c2c400003034414107050040f02d40a01c0c00030b071a941c803540c0303203407905005130401c4480c48004000002d01546c4040304105803040c258103858a626400314095849105490042001c080c11041000c0381116001800d114180c040002c1402185030607414226031042c0c0740180c400d403201c50540213000807500d10b03034010711160700900c1c264905030400a0921882c8240108900420001d40780175950401141c0d2030594002c00802071074810b0f20020000388580d08646012400e000c1c07007000310311800c1054a100700c2d004005021104c0942d50f52480d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 13947677 1250 13946427 13946461
    0x30411060d0b04060605030711030f030a0203040c0909081309020306090109020f0702040501170c0a08120310170109030f050403020604140103060b0408010507120207030f11030405060f09040e0106030b 88
    0x60025a030b888101103036910b5000306001060b45444151352420001c000400c0800c503003611a110f503000300245245902100c081303a5120404490040e2643c46074034040d28030701c0880d40003154a07070a25400030103104001005100343e8642c11111030905666540c444246d00040702d9581d407159000004001d0009a500140400e68005410358502151507000030210380081e00900b025404100101d60f001c0e00402c00002c00c1130381121440910392402c80700d01e503180c00003000d000460002101207074980b0350540e03012000d462003125100c244d00008000034000c20540718158001140701818419032406a411038098940250000345403038186914010280e095410700c078105035a0301800031f1403908080280000e011500000324042c01c1a0030002c01d8051191082d8000c00c0c0304001090009030809040c002c08070042c1004504080c00c040c240d400d60090740d200d42d401080001d001d1052000e40340040c040980300b00c80030404203000800700c0e0700b20b8a080c0002131503c110740c800320722011a03221181c4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 13948927 1250 13947677 13947697
    0xc110109080111030108070911030103080c070911070302010f050603030904050405072105060702030412150e030a020f1e06010308030c0904020d020415030506060d020c03070804060207080f0303041106 88
    0x1405aa607003140780c01c494144100c1c21078020040018080c002040c81003000810380301d0014007460030940350304610f80c401032200901c0990001340901c0800c4090180c01c000300801c0d00e0401144503034007074030200e9500c010011001540b81201c0d03091000064031a0300e0140001034015814002e410051000803c0c0180061ba501d00c50f200000460a0104142c6007641120786540c4254060610f4070a2411801038034240541d00144000c1c01148110710307219000640099200517400040c10a480041c42070902c2c198080c000000c440e01e142d5000030700b50008500c2c0408442110540700c0306141d80c1d40444500d01400d420200041010443ca40b002e1a084203004a20302d181c0440720380014220303031001040740035035900410204405048810702c01c41e50041070030140a1031034480001038003841a00b009404840e40458072039040001041562952980501c000e5984ea895613001396480c40701d413051203520700c101a841c0c85800e4000c000c0d68013443c3c0c4204c85040240c1550104034064004203051 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 13950177 1250 13948927 13948937
    0xe060d03050919030201080114031b01050c0105010f170c09040b06191203080703090f0b070203070803010e060f0d030f0e01050c03120906090307020108060603040201050c03071a13030c1101 83
    0x740d0540d803241c044800419122452440c560f1845c4005040007005a000703c0344400d518120110b40c0c2c80126032a880502104106800b050320080141d03040d0103648a1290316619000000c200c0800c5021018150f4420091140c0221048662035540f41000b40d0580d4001c10302101040c005801d00c4003041d00000002e04221040c51010302c0f2407110703c03455010506190f0120106028141c004401a812074003500c0c003405800040d40391200310801c801001040003c0d5031000a210510910070b83d0040d96101017055a40e5948255400351100240c1d4081d01c14040300c1c5816159251a20601c0500c55158454251504014000781c401c560303a8003c1c01d0510204105024604078181700a10745a0800104000a800d0400ca4030b40341000c010141d103190b5004101140150303800810880e8404811074000d40d607513540b480120762501656681240324840452030030108030490b440000003207016145889169940d00020105004402001c2e02007146881d0800208450300c81c2d000034014107040c4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 13951427 1250 13950177 13950187
    0x4020c030304030822050309012102180901150909110909040501090c05010819050a09080705070303020c060708090108130b1509060603040302190303090c0b0a03050a060e060d0305 79
    0x1440341960320495003103000418034010494290f40c40c602030550251989070a00800c0d4684c1c3d039950b940d10405244a050221481e558042440213403030b04020f015074500295186e45c45061101000d00301480c80521401e100000800c100c0f1b0300c618010000d40b42c50307958080304e6141c519002c004100c04032130040500820420b20455840d041d94260056102d0000010a9107990070140e0310081d007500082d0402080c1800e120040f0300c412150750100780a0100007400386ca0b161001401403d41000080181601103180c00500501180c00412240241c003969003542924040210500c036100000305082420300044400b0351240c40103070752201903c2481d00110060303845090b40d0f0502152142480603140303491011500303281d021990002401d880c250300310300740b503074029444800f0b03c0041da180f03c03450f041c43c13414140300390800d240307464000e0072010070640c0b18080302500c0c4c0d100c407021201090070140031942100407803103500300f126080c80d100700c61070b140d407020800c0303503405e40900350100710041c88 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 13952677 1250 13951427 13951447
    0xc01020a15110a080103020f150d020c070f0f0e010b03010303020a060c051c1a040902211903030605040b060a0206011a070b0a06030318030507053609070b0a020705040b0402 76
    0x30007007400001d40d031504d82c4150b1452041000030b240468245001d1005400d860940005100946061400040340540c5500c803c4655620300700860380304040250b8031200010b028518a401c040503941c07540d08800300e90380ca4403510700e000d200a06c40207005a01c17400710080880c04682c4002c002c0120f03807070700a280084400c02c481e4034003011086c21551580e02c2500050404003041d242c0c20041050b0b038184042c402a070000380411281c04d40c605a514070000a030004038034207020f8800f640801018501b10b8800380e05008004052600803035015524088030384003903107045070588544440030742c0200990ba0030060302000401c0314120030345000c2014031200f00014007800b006803280e140f441c4000343c000d245040040c02850402c00460354034140000500100340041000420384406030f803030200010036801586445070038424000d4140d11190804514882800c003044d001c0c18004c070441c1c03961600c400c01c0070440d03c1400c04207405a80412410030080c00e2541080c06410402040181041a250 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 13953927 1250 13952677 13952711
    0x1803030c211f050418060b0103020909040807020f090903032403010f090b010b160b0702030913050609090d0504050d1406040305070c0f1a09030106080f1006080c01020a15 75
    0x900c407011007004002001645010724030b030050040c0000c03101481040e030b1056000c03030f40f1005e0910141900d500c0d0306950000f64000c0c0c048884000015100a030305240034100324a154000d400120705c07540c2c0510501c541403500c4a0000d0180d540308000e98034607210f40c0919003900429403003003d04c4042c60f0381c0d00300c6299000e00c00c0822101144401084141262a0004031004140c201003060101030004004001ca003c0300c448285502007a401d2003034940040903031441c05602100b03540598401d6184505da005500300324090031065504948036110100090b0b1903680011001000400503c000c01c0036103003420503000345500030764252034400c41203d00141824000c80f003c0d4041080012120200302114030400010028262035692050030301d80b500c5054925003900c405032000100b481c0800c0e0b035003903200f4801044140201c0e500d01d01030352030881d16206280c40070800503190103400210700401040318409500140e000e0122940950703149003440510151117030b83c8540c3e0b88141a644000340c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 13955177 1250 13953927 13953931
    0x507030207031403120c0c0d0f0203090d11090f061c020a0302030703030f0f0306060207030f060b040515041505031c02030d050f0103060b031902060309011512020103051803030c21 79
    0x540f01550b940d42c14492011010007018040340700381881088807016004001ca01c40c101e910303043c0351240c1910185e900803031450141c0350380c06522000c100c4116082280c1311103040010801628408030795510a407442800310000c44c0c00c83d412481c0c080b00d0050259101e040c002000303100501c5030500b60f031207402103882c00c102c58000b24042003900d0700c21501c40d50401d5424110640a00e400d018040c24568029140d1044d40300003025001d0940345502000700c150403501040ba0301070010809403501c2c2e24689900311080480d1401603150501400010141c01100c406aa0014000340305c0310318050500c240100e4000c8800045020621110340c20311181d02a090144a100a52126950440c1407200890300c10299079172080d03001c00c400c5032007041c81030300c01006e442c2c040310a43d072203076160303c05140544814502095105040440410385d203d1f07803104409403500030b0b0f03000c22841c2c0e034485011084002da01c07805402540240001046030030140c3c010003201108100e00d81044002c000300881003c41 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 13956427 1250 13955177 13955213
    0x20c0a0b0103030201060509090709200711011803020906060a020f0709060f06170a050c16030206040b06030c010203180616050607080a020910120207050a14060901050115050703020703 81
    0xc4600420626034240284409003d00320340c1c509483c00c20b01c4100c0e0742c900180c401ca00803140c840c03121010203040000200ca40c5030103c1c080039540d02c40c82c40c03d44050a07561b0401400300d000700741500b41c00300b20800c1c100c0580780d001e03001c0c540d280c544204001858102c1d0464000710300c10400c000402c2c210500c000b5000301004240031032418100301c21401d0011003500808100100018079088c0c00402e0a40700390043c00c1d4400c00035032925480da11045600c41c04c0000c1000d150444549810503500181441c03060f40205e56070300d01d13070711020700305a140c0a8501005005174024000c0300424072501c00c181d41a44801080745190924100211084c0d01d501d000544181d0020410001c9041d0840342490b40030384008011032030503070007500060f00c01002c403e400d810092501c92000b07100c0110703412100c4154001c0229501c520591a0415010202e807110b0007441c00340001250314008140901416104141d00210482d80d0402085815801160040c0c085101303400000011811106041d100200 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 13957677 1250 13956427 13956443
    0x306090c06090b120402010c0f02031204090b060f040608070306080a060b0f03010e061b0c0304080102041505030709060302070f120807020c030f030a030507090902030c0409060501050703091503020c0a 88
    0x1241007400b8100601c55800141902403c000c0c91860082d01c603401c2d5801542400c2c0085250380034200303082845080f00c4029050311407240545510004070000c1c00882d0b0403140c09100200c4400103020340e6009000060040702401e000c20b015560003000320b990b100c902494002609a6105011460f2152940e820b8914959a14195100c0e084c07040c0c87d0303002513038254020f0140e1180010340710703a103480c01005025070244601800012884030012603603096110000c581d10f59843c5d4071017600035800f5116034003240c1c0c003c3c050032407124003a17415244104142d480b18440f0b545090b0080d0040e6010b408111000c01341550168001505410001e0104241c0c0d81c4181042c6403011001c3d141036020451248250311012011480c2d54000003110710313664251502068984410b80c098907161516007080b4501070000c000c000da2910010702410440d900803d0038840340f9500d0006580c280b10b102405070004604003c213010102860281b1140050340d440d0041c9421402002d05042c40d0b02c18204540c0b1392 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 13958927 1250 13957677 13957679
    0x902160c0e10120f0206030601020109060608070e0601090803030609041509030f030e0307020d020d050109050a0f0204050703060e061e0307060c1401020f030f1024030f0c0e0d0204060306090c 84
    0x42c0d5455100d01500d040819140b42c1e0366103032524194210344d0b6400a100d01800000518141d10030341007004013503441780c003e0200700e03125104180c032480c0700c0c0034400402e0fa042c1c002440d03640c440c4040108944000010754950380b108028060703160b80040094842078140384806460300046d200700407030311f40a41e03102c0c907003142d1241000b4280d402d420b0070301c0780640c028408580540e4076000400e400310b43c112100009101c052a18501602200304007a02e075000745180c404c00d04c454000c881a10038400c079410440756075000740a0b8100c074807501961448440c40000500c5034208070a19080f00030141c1c004041c1c15041000080c540b210a411003400a003220016001b040307401816040c80c040008000e5040c240d180203031000c10300004044a00482d03411002c103500c411800003400c00392486000744107404200804c01c003140311030740250f0400a8078000355000081414031035403109001c0c50340c1c2c074070310018034004220350a84110005c1c0e0740075a42c0c404c0080051240c0c410a0304071803041d401860f0003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 13960177 1250 13958927 13958941
    0x612060906040608070501050d1103070f02060705190503130b07020102040302030708010605090402010c0c0f0303030e0c0d050d03020a0e0301060f05030d0203090108060603040f14061807050306010902160c0e 91
    0x1100d4003500150140741810814007120710041040e1095440a2038101c1c1c98005a0341c0c4007010380b120030326000009500105009030076600c10039900806070740e602203e90507141c458007150544074030721510803181590001c102c00d20b40b003032000790f030012142c030340814010b00d20b6101c1840724441554401e015030b6000a08108605041c0300003402131504100810605181002240342000014402030405ca9890300300e20410458a4500019000d00308608130200e4403440c0103002481c18440b00034280c8124003018040d860301419400c0300c598400c0c0a08a010808042a00079401415803403003070100c14000382815032824031505005202c608200070500d403520b010305040810080086045410030040c042705640c00040d06070b00060b050341d0310b41d0780c1d9447c0d007000c80040b8065180104003100002d68801d1002c0001452809844e000380c00700b0000c000c050700300c2c0e0f0392910b0344110f54041c1c1180d0700400c02c0c24410b90241c100315840103011640d80509943e140b4143e01c040e0096028441ca100c240103107 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 13961427 1250 13960177 13960189
    0x807030b2e0302030114010e13050f240f0f12062a04060504060e0103020702060d1a06040e0a020703020106050303030a020403030f0503010602031206030124090c05270609061206 78
    0x7180031a0a04503d1541088920f180030700c003684210b070600c617441d01d041c800b94507882618031042c8441d6000300010b040409500b09102401d84510691007868119400c0c10081700702d00d40c2c0f820000510100a048404042c42043c6251055865009031007040860b0400d1092140d030344101010800001e070074801c2004251680181d981703480c0c0c08803040c0002e00440303800c40c08540035501d80b03007071480304909203c0040340a0f2040b208001c1d001350010849041203c60750b00b00107105440a1000b400619002003842410f008038810010701101c01d01c0440c1801071141d008000443c000e10001c00c0742d03500e880103e4a154420303140700d060306600040130001d00d58061000b40050055181035403855241080003983ca006104424107104080b41c00320b2581d40c0c007580f01c0401c00c1c40c0104040000106000200503280c058807072601c1c51801d02605040d0140700e041201c0c01640f0503000d04420369a50188851500c0c01b403240550049400c104941c4039956040180c204507540c04200038061401c5070038060 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 13962677 1250 13961427 13961509
    0xf0609051003140415090602190e0102010506030a0b0421020a06050106030c05030408220b0c010e0106030f080c0106030501020d020d1a090c1309020705060709120b01060807030b 78
    0x70405252400885400a40c402c03416005508482c5244042140301c0c0c01800500803408000c4c885880000d0440688038a49000d00d142c45480e120000516092001a800d0390310898441d03502d90844450100042d8500300d01a40240c05a150381e0314445518410a40c0301c14141d41200c00f590002d8143c80c1000518040c1d1030161034030703240c04d1124004483c00039090b40005480100400f0b8003065124070148004a0846000e02c0d0f49a90149039640300e01c082c2d5182c3c000701d009240e81d420191505ca0a0300c0502850048907032140120440c80d640c0c0d11004800e0700049480c000e995241d85000010501c240040c0103418035042d801a0b481d500f00d0101c101722520170700240303400c003648802d04420b9616064540c0c2d005564000307040c0d9401105051021a030126045000c265201003042402d0002c0002d42038452425900d0302440d45032601000f2914001d07642c0000d0035000c9013401808010700c66100a40c01085034140424030501c44000502011140b07481043e0341c0001104850710407034011040c0c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 13963927 1250 13962677 13962709
    0x110613030c080406030603150207020108010902030402030a0f030e01020f030f0703030b0112020708030f1812091504150201180804090c03091e0201080a020c03040e150a090f15060e0108100f060905 86
    0x148ac000003580082d001c24414400d410700c0c10303404400501907450501c0318090f85948036103045888102490301400c1c00c40c4440c0003c1c01442800c2940000b02c00010449008604690001c2d042607419a411006810040412410850120300700108811680090681c0358411b90400c2c0c1ca80c40d01c2800201c5007980242049020401421103c0e544070300418055891500a03016580c0c400c034403408142455054560822440360000f000030b86400080a004110300c1c455000b0302084100380a070080c40420144007400256040104000328041a40700c0704200a503410f0114550580391542150010078492100300b80900505074000c66a11a03207042c0e208a101c2011420321060201640d5a40614010311441801e07030030100b4244c01005500e00c48981005110251807910703814540d02070110172030f40040b0b05040080b11080a40518071a800b600ea6603030310501d000d4803001c0115040c00000e490780410101009000c1000e0046d0781b00300d40036010640343c443e403081c903140070301c188600402998 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 13965177 1250 13963927 13963931
    0x21008010e060d0501060f032001020a02010206070c0302101b0e03010203010f231005070605060114030403081306020c03070b0112050c10050c03040312020607110613030c08040603060315 82
    0x1402030741c589051058024406441d0007411626502e46640106001c0e000740401c11025440042007000c11308401702d20311684041c4c001c0700203c1c40016642e42203811002405038020500042c8644e200b400014034160003803040359620803510021004903401c01c407041840080981c140c80806030801c420140e9200c042d0021891989400340c00c2200c0303ea00d014112541d03460181550b6901c0040d80c2c1c0340c094078030040542040107200311002e44154410202260f000c1d0910001410560189001003068074002c0c11310f603d151783d9998200c0701043c00070b24074541c440d5006007810105840740702510603815244011b55a07185242443c061401c416409841546001e003846000250040f405d981218001d441280081100c0352050f1154000c050882c1c5141c44017040000034041d854441040b4444c07030b030302654031a4841c0c201c100d90034007584400068641c0b25402082e51980c44180c0392105502902d0700001003680c55440d4451580315600c040c0000f9182e0301e05000340a0340c0b01002310039506030307a0b007 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 13966427 1250 13965177 13965179
    0x2306070206010807090b18010605070b0a02040302060304141905011a03060c040b0a05120a02040302100806010206040b0c0409020304060b010305100608150409020409150e03160213060b03090a02100801 88
    0x515030399040540200b022840e11800c006c1c03c10340300c204210b842d624000500e80781070761b1a480c3c001c5c119005518203940c40922240840c03401d8003035208550540e900074108070325582d29910341441e020380215001e001e41c4030740404001d401c00d42c00c9040000314403d000214400704401c17540b01030844c070309241030b20a070015000e000801240c00c08035400c444c10418441d4a0311401c01d0705913a10700440301c401c1c540001c41410400c1c41407095000304144d9200b00c41c41242c40358408412100210304a444501607131020000c00d0200e40d04900c41036111000d1000c0d14685078603000d0b1841a600162000c692564641c0d2035405950b03014082c50780c1c4544401c443e410725900d46400140f0180c000b030207007a5030005e0b29500f070100751556007005503035a4000d0024040d04c1c01e00e14080920304281005032120510b0400811207864020041f117103500d0702a0307903889042e13502ea020040d001d103130600d4080905a840c4c0c0c000480ca00d84002442c854200c2501030590320b0840c0c01401121031104204c14100052080 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 13967677 1250 13966427 13966439
    0xf010f06081e0106050904050a02030723040506040e0102070b0115020a0210080a02160f020109060509031e0c0a2310050409020705010b060d021305090403050f0c0a230607020601 78
    0x9111000d0304100c2d0302a4100e29001010a0300400c481d4105a4011085804010a0090004042d10245c1c030070340482c0e000640c0c906510903d00c01968007000c0303003051400200f000d880d10b5003000f50040c40080000805a006c03040ca2801ca034042e10040f103c0a45441c010080071746500014540002580054070305901d080d0700048148810503601000c1c0054040403404010140e41600c00050010001c402004500c1c1044105080030000c01ca001510120380803820030302c60820f0b9440703201c000d001031001c0c0b00b00040120505040003041c6185200310a034428031580c0315035003100286840068410b0082c00400b12070070200883d1020303406402c1040c4252040ca0780001280e0844101043c0141c0750356480ca0320b1800343ca084032920354407081c041100803002100d603009054210310b0280c0d10240716601e10a00251100454010f00400c4062003820042c80010005040911022080d44d183c5c0c680c5580348010b074801c0c3d44103086274401c0012580c144010820000303400c80704500040c000c07980340032 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 13968927 1250 13967677 13967683
    0x5010e04020f060a030905030d050115140906070501090204020f040e0c07050a0b04030c17030105040c03110403020415080102040b030109050a02070b0114040212160905061914070204020703020f010f0608 89
    0x703102180140000500e00c0c2e0481c5c4694404400c1701c1d4058152503407400c0d91051038010709001e000b40b80c0b641c01034030504c0240f24046c40351850f40500c50800c0e142000b982100300300840d040102c06403070554035040e00ea001641c440c801001e00500815009848508142542c400110010a084030b003400800119000c01d40008044941c158402024511940e60345411500a45052402007a40000342d03e9110780e1310340d10000e14141c400a88041200181c6407400700c1c29103000d503082c2ca110342c03001c10040c40541041d4012009100c0e22200d505c2c0040d6480c00d9150881e840780d48041c6014030044010700a0042901520341c1201c040d42040d400c11a484d12070784120768040c420144803008800303000c1e035141c0b6a80c050702c4909060044460807441c10740501e04070940003900c260000360b003081000c0351500d0100c09503100844078615058a80075451416034070720080c80c18411060800340001001a80c2c1c9000030302c0321521a5020303103058010a030000c0d0943d580311803480541ca040c0340040c00b01801c00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 13970177 1250 13968927 13968949
    0xe06090708040204050403050c0a0b010509060307121707080a05040501030606030614090702010f06030317090a0c0b03070302070c060e1318030e0604150f141303020f030708031c05010e0402 83
    0x4440c0001c0395110f5180a40c0c1920440c18030304d507607000b210ac6c01c20078050446019030482d9401d991a0302c0c142d40c1d600401d43c40b9034942c003654000104144041c000700740005000c01d9004e0484d40c10b24a01170907a1581e40702604281c10040018000190a10507943d06001e10002440c550400b4003800d420880b100400d454044005805510b0340000984d5540c400d410000c1c02180d189410040b040e141d0400600f9407031100b440044140c1910081440c01e0000281d21100607000880110700b03504140d41c00d0090392014000c4400c2540903c5180701003050540580018103550300c55540500302070051050000710700789403403042440c1c80d4200040b01034043c00d92440c25810301e007c0340245500710010f00e140c0142c0e004428168144450f800c11960070a030140840c034000d8030f8181c40001d00340300c44003161203110610756131050004d5041005081c03031800c8034240300b001015103541e039468144542c031350b4010024148642c0f0307119822141c0008244105405030000c40c074500c0c59490141c001c520344001e4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 13971427 1250 13970177 13970179
    0x507080c010305061e010909020d020a02070e09030a0f1403010e0603010e0d0f0e0604090603080a080f04021c081b010501050f030a1a04050307060603060906061d0403110313080102040e060907080402 87
    0x10b05d400442c9141c0c07213401060081c0c01d1042085440704007810142d0002e4001c1e044003005485154800301d018520800c55604c00d10800b802145008070102049820b039083c0f121751001c1c4804030510790785008a200240d800b034a8692002000c510707011040600f9100392021054607504200244070503650700400806d8a0030050420090500030980441c92500c138940c0b240c0b245d40d2401102004100784400109400c1e252652149182d84403050040720040703058800a51001c0c40c410305840441e0000940c400300ea0280980740e04054034400d014486070808a0121101e0b55100010701552800c420060b0140301d05800030302c070b0a5a9540d070070510104229220050300280c20003e42000b1701001240c444540c80402404043d680e0f01e09100a031600741c0b01101c10a00340040420b2074820240d16480b5a040c6031401541600c0f580c5007070f80c10744021003c0d1082c0e030000704100c20800001c800101c008101e00400144d03901d20f4806034040c000300141105101d42849814004800d40c408003080c0c00bd50 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 13972677 1250 13971427 13971469
    0xb03130b06240903210d0b040207050d09030201020f0109030e0405040503160309091a010804060b0402090316090501090209010909110409050703050405120f22080a0507080c01030506 80
    0xe601c0700065032031200016041c08442e000c6000c00d500e09018020300740d040f00680480d210784241540b403800c605824040c15840b0310741031103c0505503205401100011801903c01403a2480b15151103003070a00c42040300010070350340703c410011968104255140400510300030006021160b500030131800c1c500d00350b144681d456a0120b42403000600882c1c401041a40a00111303282c64274000c0c000507078074441d1404e02c0e4030300710302c68a95039003401601442c400140d450440690b95035841c0d9005021a04c07408d90869400d0103d400d00d80c9040103c03441c5042814000c01000d03207020034400c15944142c00c01d81d481d600500080c015a60880c15030011740c0c241e01d0001c24400d801008034000d0f4000d80d400218541c0c101003d0126884c4c059000328083c40c00364040d2a440035180314860140d110310300715800030920410044030b030b1001140d0350701d00a0020140d0a105a030b980c0078814608a1161819203842c1c004800400034208208805200c3d09803e00f0300b80300a20b030090001d950010070283c00c2e00c17450 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 13973927 1250 13972677 13972681
    0x5030619090213021902010c090b0306091e012615060105160b0f040519021011070b0c0609060901140103020103050408090a0605180901031502071a040302010c03060b03130b 76
    0x56110000e100d55082280300071500e1710b528880c1600c0c403031040c0c03803c03c001d5483d1040e62003005116600d26410f40e0f0150024500e5500c480c02800b1003504001c0583d24a800ca0381440070b14040b1101d9603074003c00c0e00c081c800388002c10000b0584040c00101e401440c6036030000074001d0414001c21002a440082400c0840d244c0d000307843c43c0300c9103251000f4028000311810302042b0400f05100034090249001c2c208455551403411040c1004820415000e075201c410050b400c80740521603c3c607600e020107850280c6d80380b25917500d40c6074515005072000c1980342e0040410480c115804018140d8018280002130041844400c81c110040340c046c003000e41090703101e0000030b0521500710100c50002e030002e0048403815070364650044c0b450b04603803640c2c0b010b000c4038001c811075440d00c618014140c0e6002003481800c4040d44503450001d40c45250b00b03c805107102c0341000a8100e24200d001e108078003079000400e014242d46c400030201da60039009029a000207205004034519007141d8411003a500820180e115 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 13975177 1250 13973927 13973929
    0xf0605040503370b01030311030c070b030604020c010608012a0c150603020904050c01081e010b160203030f0909070f0215040203160602031305060702030a0303050a2003040507050306190902 83
    0x141036000395800c450103004041504100007070013082d040340c4c025500c0c049842200c0c80c140d5100c0c4103650b0003010300e90110b04140003940c044401503400079002440107241001e004411400d5420603400180391fa50344034804400d8103c1d2103584100c1000f87c0f10503100149642c28040d00d002070300900a0492880740c0004030380320456611103005150000c0c031294031032805142c042ea4807000445c19500140d5458040380b500e21449400f0000030001c2600c1c142568280709401d42d0790340081896480c55050100fa00c800350314144024110b80364499400e940d9401414103008101c04041c200c40c08000c0d96005103800c29502041a035000080e808039007460351928000280761061119400880104018001070183d40000c01007414a0080c22241806940d410810007607005035030000e50150000100d03000064401d501841e4801074207070b000112010300d140109442a13141c80d151901040010600c414003204014010041504500415180ca480300e048081041e800d07400d20070b000d0b21410a9811 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 13976427 1250 13975177 13975243
    0x403020a03150906060e0702010e0102090d0b040c0906060f021504030e090a0e0102030a09051006050105041e0f060903060e010515060901140d0203060a08150408090103090213060f0605040503 84
    0x10f084c1c100c0d0050107401d4950190300718501c400c1c0e440340013541ca40401140d02e84418000c0e50700c0840c000301520030445007511a0207030400001c1c0129021428060080b50b03031803041c4a03100140205640e11918498000d5003e071800143d03450040c804070100c801c0200180e40954030b4441003030161451500d84c1c451142e25005003100b0102e00e803c1c0d500100c20800d415015502c000d400381d014a0840d61880254034030b0340202c590a0245c980041e400304010300c4800c04194403512001c00341c24034200d45641d104801e580403e90b43e0400c0c0c0000b460300a0801c284103c0340504483d42c01c002000700110304010207000340402c0c17420300003030180340d003c18004003580c01072103001c0d46840c024041b41d55402c1020150380003075000f15001440741c203042c600400c2c52007001070210f1040c102c443c000c021603100d0341ca0364011500084141810175841e0a200c0e00181c641c5071200f060502c1c000c4001c11140d041240603095040550004020000300b4030040046070f400142c01c5024202140226a8030650303035800c070744 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 13977677 1250 13976427 13976441
    0x7050705100c020c04060504090f0f080c011104090f1503031b02041401050405070908060606090d080a0306030309060c0f08031e0c28080402040c11010c050d050601050403020a0315 79
    0x80c21501d05480c82d011280c01103000c011540c8122401c01c1020745400c2004111840d014010b4103242d0984000000030b44800341d5800b1581c0140092810900381c500250b0039100710f200308136a920350106040085034021f00983d240260b030080280300ca07132000d4055041d50215440041c04000703441022461080380901d200c140e0540242041c0810012200e0107001d0741d400b0320595004626040020704810322a82c1c0500c1502d10280207070003a61070381c80c04c07c220f90b040303070704a280d100118207042c3c00029280c5006001703c58983d103001c20360910f90f084c0034009112550103a0309202c44a000d07030002074000c0080b401240d5021104544a4503102002102100510740e400741d02440102440035041c3e186c0c014040c02105500008200c400301005009901007449088000c60595804640149840c2d0401410300d0001c4c60408540c00c1c4c40c00801d402d48a408400e000411000148a000d05e403c0e801903580c800300030300341603151a00d541c2c0803484100e160303c8090301c0d40346020460500c850050300019 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 13978927 1250 13977677 13977703
    0x206070e0109090f021806040302010c110301020405040f0504020a0503060118020f0919182a0c080d0b150c070303050a020705150c010510140d030e060307020c0108010f03050607050705 81
    0x2000c650103841d031100031b6201044441402c11004901c1b03c90746040ca04450950303034181d507041601c3c0300d950340c0e00f1035050801040b6945550207200101d4161947e02c41c030510072041a00c086040c3c1040d006110742084560081070081d006180140942505510102082c0400c014010b95500c0312002180c1c46005e0200d54030b61024001000228110b01d80211109940720718402e407142440032a0f040c8211490100f000031024001c1245103580c2d00d21114a5003002c50f1800c0c410a00240e5540f0504540d01c66a00300d464160b0302c0f030b2150745074109901612008442041c24610b0300c1c0225084035552901480b00908000c800140307400c04601c2804504024030703000c1c110312080b2207101400e110b5a0001c0c51040303503d40c640700008620459001411048032813148100f888601103406020760049101000c0d020301c00803009115150300e41c0030085114100541c054400b460000000400c103039070690007405c5164050806102050001c6070698004400c1d042050341e4050302d10703210303040c02c05442c151 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 13980177 1250 13978927 13978931
    0x11042607060801150503130201200a060509012003040f02010207030c03050109030e040203100510090f0801020a02011404030f030903140a0f03060f1202060306010e030f010902010e040603030206070e010909 90
    0x201d15811490050503280c0f10b00342100070082d540c0007140c0900080751449000b42072040c1a90265000702000702c1c8440244a0b248400c21507140303494604000c12008031100e0b0f9803082000079103082072041c02d12104400d020a50ba4110000d15110346003c0504080e000710204908502160300030040b02c001168020340c0d200001d652410114028103148505034042441c0510b0000c0a1406200300c0744a03000d900b4800c1d101a040005200082c031000c58690140413031500041030a10b6038420b058000e01d148000541e40d200515002402d40795484082988080c5c020705010002c0c1e00680c42d200590070a182c0021041c01609040301c2d02802c030340001002d58000529082002d6204105600010158405100d907a03a200e440070130394041c030b124a5001502c47e40c07860005243c200001d5030418014034240e0000d4184000190400c0382c000801c1081c0d0b9582c0500400b1560440540e00307000d04111000c00030207245841c00303500e61800910600030440340e41e4041ca1207070f0151510710b010741040101 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 13981427 1250 13980177 13980179
    0xc0405090703020909010e010501020a0308090f070f0317122a070b09010c020d02100b0307090e0303010810180303050405010906020c0c01140a020c060c030c010507050301031511042607 81
    0x70150095110310001c500968840c4004a41801d158031040e040325410b900400c2c60072100e03142203d0302c0002400746880f9000d08801e540b441d01c0100315040c081e0212551030b00a1501d14a42825050b6078010000100341051105400d01111403440d69801036582216607000b401766400c40300c00c00c01e0b03010300000103071022400308140240354040c0e920808002000700032880b580c0e0800d0369200c1688005030b00591003084500d0341c0c0344a54000c84210080a0308490703909480e01c441c5410754000e80c81200c40c6030301c040010004807004002041009020000800c000c80c0000c01182d440c25107003002034141500c640109081003800d501c100929900003200315114a82610280d48590110040c0340c0016440c1c03281c00d4101e074110003100c803076a480350004c10007080750300c0a0014079045041040b0043c0030610101c08140404e004840c0b013207860f55921a525819440c0002c545510038580300c240900d0003540040c3c05c000003046400303403015030500e2000e0104140c0082901150811107911130300402d08 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 13982677 1250 13981427 13981441
    0x3050109080910030e0c0402070203010b0303030a0e0d080105010203040312301103060306010306090c030f0303020406030f0b090705030a02071415061e011206090c0801090c020d0509090c040509 85
    0x6898840003c035144052504034801c2281520b00f401c205204030b4024001c0039a0341e281560050214510150011851807003500c0044e08680048504c03d0f0825100d10500c40000401c1c803e04000180e2410506225410100000d64a010780d00004004440c6603804e02d034024041d42d11110b038405403155508852070040844000360300c02d42e0802e44228145102040610081002d6901c10f41e4058000c000613840d646030304000c2c01c1c140e0f1068590813502c26000c0b022901606850302030b02c0c040e0302c0c05603a80e40707032410003001c840300e60000d844101c2c605031100e0200c1e41d40c0c140841e001b01e103502c0c110b5140e8480d0741540700284501c0320014056040039100d030484d80008a510140e0754652400b01c88541d84801c140401e08101003204a5012410b142c0200e15600503840d50a41300740d00c0e4400950b0580310211001120800c1c4203100101d0321090040242142501598481c11440d1014120403070441b0b05c0903103180540900d05219190b004005a00f0104c2c2c0d1007518000d0000404403059414451 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 13983927 1250 13982677 13982693
    0x819020d0b010207050f0913030903140c0306010b0a1e0905060a021006120203060708070c060504030c020a080102040b041404020d0510031106070206030105010507061508030d060f060806010c060603050109 90
    0x71112a0260140110002c0c15241c45d200c40e0500c40c002170000260f44d07944003003810070101194421024096044004408580601e281801b8000d80200a0548505074010149060300c141e01c0f8215001007084100c1c000d5920101481d4035841d120810007400035440010313149000d043c1c00c459000600440d0024107a40c1c00600584000003444040000030b0300c490104030f8105055001a42503800f4501240c4000d102d600c640e9801002460300c981c010b00c8550312001030300e00955041e80080e44459075503065160a039009001022410000c41c985450710301140c0b2075004510540c810801e081d02c0824090722217404451804c55814070400c4180381c0005818050b095a01090300d94a050342c044182904004045480301c40d001403400b400c42c0c0c648001110f403a440044211001d640310350034405225006450100070300b400c0005180c0301c900c0360b0703803400458549034001514030300101800c00ca116000181c1641011007807801001000349801c060340a0300180c0d100400540c607042034001401070803 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 13985177 1250 13983927 13983941
    0x10e160603050903030705070308040606050402040e010918050c01030b0f060a020717120301091a10020106080c0103090b06010e211f0203040201200115080f06180a030819020d 77
    0x161002c1002d80c440b210581d54a000031181000421810021000800e006110b042c2c1d003e8410100400c0282d11140400c040e60130940c066010b81120100500c0b02c00e102c0c0c0500c0004910380c2c0d80c0d41d080c440d41c5880301582ca81e0004485410301d80d0303d132029111511102a01916001d02a0115550301510300f4025034070074081c0700720f80740e001c075401f610030013030700d0209640301100080102c0701d0659080c858260020301c0c0310304048600074103801c208e03420b90700c0c0c80d2221000c0b00c4080d000010a2490000910304011801c0621410140382c44048800100b00c1209540c0001080ca80020400050b601041c1880300007898122040d0310b20700b06142c103800008a504001c2c51403100000d40040d002c0081090340816a4000c2c04078542608101c1006040807204a266030307880004a003818585070b1000144481e90401200c603040504807050084040142c603400201d0b001002000100e106406c41c1c940c04860002000c016203803010440300304520448078084003250904550f02d000c08503100008001d0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 13986427 1250 13985177 13985189
    0x2130512030a03140106050a03050a09050f010506010306090204050303160302030f130303020c0105040e07081504020c0106031a0c030a0c0903020a0b07030807030e250b0310090e01020304081209010e16 88
    0x300006169034008603d603050407070b00c1c0c0f512002d0900d41c2002089e00504001000c50401070350300d041020208070b0812000c0d05041c07812000050b0380c181440010107448481d0003890919004020800498500100b21481100000280d1000072850724049086200d1000c41c004440004210300003021a40c000c480d0840388030760202c1704d60140c3c0d94010340f8640181e1140e800200c080e8000608c0f040d0045000d142e0102d15081c8050200e86940c00141c100c0e00503c040e00b05aa40d02c100500c10860b0106500340c0109081020105520b00145128400c0c80000c0c004580c50380ca403d0b0800c1528060341340c601c00703554020207403e5620317100c1c1e55052058001d0b050550007d00b0207000f1a5203140603100344003150b54031102038107444d0000000032481c00004003000b031040340a028000380132102280514000e96000009114182c5000d10090594500030011070480c0d10410501c80020303407110480f86031540d0300504800541d58801e000b401000d0642c0401c800b03001c0d00b0341d12801c001406114105480e8 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 13987677 1250 13986427 13986431
    0x3060207051501081203041103070b0315010e030f06040305070804030203060406050a0f0b01270e090303010807150f110a0b01030320071404091704140f0904030801050402130512030a03 81
    0x7036140f11307103a5140c0c299400b61003c5001000441e01040750b900000500500181c11101c1142c0d581502d84000da0044820303c0c5141c40d400c0c140c1002e503a200061011500049000300040005424195210030000e4001402c2c842c00050740070401040c041910001d50300181994024609424414003403c001ca424ad001181752410300c0c0b88600e81403003146555101031f507a48070450500d00d0401451241d8034400b0002840c000000116a00781601440c4500c03038200c0696200c6d49000c80d02c5140080b5a00425890700004110380802035222040c4000f0454078a095a0780c08100b111250170300280703e202602207845980040241a0442c40021203014400800301040d514004070945600d000d00401e01080c5032405014014a4260400c1c882207019004a034508500700002503641d5201e0f5001c4020300640e140fa0721150710709071048615a2800b900c1216803032900d030340c00401c1903105000d80c900c5030b603020521f004061402494030010b40030103030100c890506128115070f82c0390401c1e903145c00003034 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 13988927 1250 13987677 13987679
    0xa140703090303080708150f0607060603230d02030d05060f040f05060108160c060c02240a0f0612060905070803040906050f04020c0a060c0e09010e0901050711120309030403060207051501 82
    0x607128801072486147e2229802c2d041100311010403004c0000c02c1c4502da803101d42400110082401841600021842080c1e400400f41003441c0c140440346560500c001c1582040d481520005e40100890b0740e5410103280c0020280e0359480007035414440f0b00355407078001d854900c1d0141107500381d501c1603004140903210351806d40d84456012801103c914640b10000ba06004818000b620302d401c0900b0112560040c4d030080d02c5806891490b1a840500d54141152a8818400d081c07511344240051000105810b2144a041c5a01b0011401c4441001440207940e4410f007410f01c80240300000c060024542030303e9440e5520f0f4807600c003800d101d008151140c6520031182c082c911701442104c40d18841039004d08521452529504000c200d070411013400c0c406400801d009a80d61198564040c0000c558444160304003183c1c1c0c2c070b08441004000c6000e001c04903682d1225480e0006052480014401d11207640340c0e920124a0308500456100410315030021800b441041404203a040e9004102c20f001041c503 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 13990177 1250 13988927 13988941
    0x3030b0a080c010e0411070f0f06180b0705130305120d0e1b22020a080a140919080408030307090302090a02180907020c120717071a0a14070309030308 66
    0x2800310b541c0494046507214040700003038145074024416201c040e0b10400d0a0400c140c862500121424004450410884514408202d40d6100d102c80e105000700c9000240c488641d10100c00380380180070300b8240000465201000b68204456402441e88039064650014682e0a180e503541c024000c450710340d6041094903004c9804c005034400007003c2e111014540303501d82d00144100c01d5103103507900c0d650490140e043c510304845400208541809135541c200300345410020700c0c1c2110030f1804000e001d41034110038006d13071840c0014031650b07500d0f14501c6100d00410130718011f1118031541c1d02c1413100b0b020200030003540d6a04410948101d90098450440c0780e52041c02c0c0d04200d200318400f065032101182c60504807401c08040c5a41e04c150b0300d004881d06c01464500081466138082800a456446a2001c0c020300303d035800040d03403018400000348007035414508820544c404004248a02034004603a805145225204903d0155088a1485c1c1d40f5000e80c14000c1124226020507004200150041030705 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 13991427 1250 13990177 13990183
    0x106050f04140604050408070c0305030301030b09010e060604020a0903170304030206100b16080405090a050604110715020a0201110a050a1403041101080a0f0609090c050d02011b0f06050403030b0a08 87
    0x26800041c0c0b00c0340301a034840c400c001c0284000340041d01c4c4500103202c41c50008807000040c40c050b5006000540d00ca40c95840c02100100000b4600442d5904003d905540000f0024005030400011a400750312281508402c5a41c20740d99071018084031180c40303030314455542000046000f00d001e682602c4490755a5252500780d0b4900d48190304030408108004441307c594030241c09006482002c0040c58150344100003080c0c42c000365001814169030720140607851900c1c3c41030845440c03c4000c079504080300d54131850b600b1540d0118104000f5000284a08414400c1d40005105207803181c2c403035214024000000c006030403a185520200d403e2840c42c1100c6050070f419288210340c403000761754452031508011529020082e11003000140c4483c02045008514020b4074060309480c01d000840e00045d060032098520964803545c00707400f2450082d00580d911a01e03500c04030440031500c6105d45041e10b408038030301804550241c0b0b501e03d80018402050382c580c0141d1100c12040f0f800700d1172152a03813520b6072 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 13992677 1250 13991427 13991441
    0x8040204020d0207080d2f030603070e0702010c02071707030303020c0a0803040803071205060d0807030e03010f02090102060f070c0210050c0a0b070e0f0603071409040f06030312061503090203030c0d020106050f04 93
    0x282062107c1c12100c20b40c00401507503c41e002800b5a1900ca50b1500c80009040058030303080d025035103031078158545c158100318990040c45a001e5142401a5032401140c0b544181e000180805400050301c01d1000820088501c2c1141d00c07001241e40c0c0e24140c10400c41c55041591a90f0000708080541101c44030140170325401150028000308020441359074042007548500421014003080248110180d41c00b841407100a03901c140300075a0700c0a1203c00281803103030007003404018050401c10b10004c45d50100140d035245505443c00789030454808016107041c00b40420f004403903c0380c10107240030401042150b40c0500b1407500e40d040200001410060001c036001034a5030411010320018440b184141ea00c03d240502e42611240384c52000d001290a035030440c200c038501d49441d9502001019480310240380280c80000007000018100110150703a0442159003108040d243d0004000b99541030085483c80312804044420215080e18013078081d2950b40f00e1a4807654440440c44d00314181805600c0b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 13993927 1250 13992677 13992731
    0x402030c091509010e01050102070602070806060423070e0f040903020c0108060a03020901030c030b07050711060f040e13030f140702210a030909110909040308040204020d0207080d 79
    0xc80c000c00041445403046000384104500352610701c19101c281c8503106158064420354416005940c145400607107400d089a000c0d08c2190700ca01820095060302044c0300d500305034100c0300031410911210280290300545100c5100c640aa9414400303019000510003504000c00c4d1084030000c0c00400c10001207801c88103014025070030060101e450f542c0700c1c460542e03001e80020003000c01e168880e0041560310200342c008588440b0710200c1407040c04001c01406a1220301c41c0340c994948911961184407029007150310f07502503040400c2c64a10100b103001a140505102101c80d8410700d01035050510385003d0003030540200d40d44040300c2c94000d120700403816071150305502652800302c043e803d2042c0348130202c030700c20104005c01500380c41c3c16405018200b00d40e40240e8130b9450140c1044461811034103415901700a0041c01c104422250b1100794078031f58040d80500742601655903900200d00030b17100d008003c0400c5403000401130b0400c0070b000d01030840109004c10400c00207441c02c42200c0c0c141342c20000f071 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 13995177 1250 13993927 13993933
    0x5041d03070b1008070b030a0e0d1403040519030e090703020918101d180a02010f030e0a12120b09010302030304050904050f010f061e0b0306060a0905031002030618040203 75
    0xa1001c0b8451210361a00a0002118038a10b180c0c2d83e041d0702d00b003030400c5c2c200b01c0000c1400404d001400500d40100030f1880c2e94103020308280300807100c01030601440d20045101c40c910120001c0c0c24020140100c0714500c200003d81d0000b83c540345002000080703054040c0780b11f4064a40400c0425100c0e1098a900d90006000c004044003051070303220f031810000f031841892a02841c0b0100300c244180c000d504508101c400c202c4d2032410f00303402031080722030141844400707a13000d108a02c2c0540e170b01a040c3c9842140d0742c100000c440002401c100e0030188032140c090300208401207002d41140e4003038040c100307004000000300410300004040001b444001e01c8080d52581c814030040c82140742c1104140d81280c89182141c548500f07a45040b420750341c1c81ca800d003040c40d0741c50b48204000d909055610411000c0c403001480600d0a0848074400c5000142080e4010000481d201c00ca030b900568112000c2c1100400301c820700000100584080c1d402260b81902174001180c2c0c00b00313014000c2003c0f5000302d50080107 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 13996427 1250 13995177 13995187
    0x606010c0606120c03020909060903030f180a030207080c0301150b0307090e0411010305090102070201090603110f030a060512071404020a0509100906030b030c0d080906070c0801020405041d03 84
    0x440c0c0600010000341c9080355541000140c20541048180c0700500c500c4803951380c1465070040060418005281c210700c0c6c1c01c98010044003000220840390700003001942e2048030707261480404d81c101c0200f07000c82c15034460880c40d20b0515400040da0300444001c1c0c070480701800c107041d0038582030741c100c8107207043d440003091414441c9900c0d820286a104407180341075403c00d0f64400c1004101172060b241550b0140e10300c82010400e581c14056a41d00c030003854000d40c5803140a500080803040a40305820415039035101e0f00c003c800e034460448640c04600720319161a800c003406980c0080c40b45101d85403141540340448488481c3c003048070310899003008070040d80030742c3d640706000195011103450420000c0c100540d092917a10380f01d076281100544c0e9140c041e29400c0880280450b514100000d10940c0001da1001c641e654131040701c0d20255102c1d10803a01d034140200840c00600940a004007030034101c400103e415078055000d80120341048405214000504c03001200c254800b00341c0000039001008 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 13997677 1250 13996427 13996429
    0x1090b030a020d060b060315010201050601090b03042301020c060a0605010207030c06030c02100e0c01021608030a0c14190b0106170c09010c05010c02010603060b06090901051002010e01050c0403030f030e0606 91
    0xd08083d1240c020354012560b01c9000707002400c581d00840e454420501c0001030040305590910425070700102c2820034141d25401c04804030210300000340000c00007d1154004075601580c003401e408046000d8000759281d010a80710f9035113075801141c0310703256949003113000101584002592403c803034000030215a10b50402d0b9084000e4040e038241802075114800d91034030b0805183c454210042e0707680000d0840e40a210307000a09281441c47c440306001c0502d0340500418a0110841e07040644500303042140000c42d24040914084104000d1098041c1c0c011092010b5a85141c45901501c100c402d88c0081e231302c0d0f400944002c80e80e80d226082c070225100c00100d145002c2c00003048414014140348848410729038030182907a504c1c58502d00181d4440900300200302603401801035004d02142d580d82441340c2c04000c140944814030409100341082d1048400282c002e40c1300740e08103101d500c000e000c186444180d020407584107200480010380050220825240304c1d120325440100040c000e8030f01d07911454 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 13998927 1250 13997677 13997689
    0x18032107060b03120307020613120c020a050a030b0906070f201005040305250b040204051905010303030207030806040c02060103120207080f0601030512040b03010e0406060506030a050f01090b030a02 87
    0xc004459242e030b2000850300d660350801c0303824001305030305030050350701c2c0340c0a20000d0401001410240443e04054008400211107146c00c0303003142c8007490000c3c0d1011450001500100840d400b00ea00104444c501006200410034058802c000b1001164025190b9950441304400381c566000b001034010401d00314480c44a0100740704c101801e10440e91403442d248061001c0780c8080e01c013280030400001c1c0c0d06406540c00390702d941c032908404030030100d901c4850301c2e4401032100042000780709560301d00014411001403400460250f2800508026540e100e113406402076009190070780101c1c206c00001031b40c5203014020312445005681c040e060607441c6903501c842e182194014602540298517000c00c1200040003420f0700080090001c0400d075145040250a2507400340c101e9010010801c01404601d000c0000c0b0707411103071850700322501d0340e5a40c00d10b80003c107059001554801000010300540410315003005028030740501401d11980d9a5a48082c119821402c129030103403c40c10412000d03103002c03 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 14000177 1250 13998927 13998937
    0x50c0f03060d020d061a010206060d0218060402130f06020114090d030b010509030a06090b0f09031806040513020304020909010b01020c0915040501080307140c0901050607060b0a0b180321 82
    0x90b00146213180c8a076100d07026143d003050500d43e840d41c003420080166074104066a0050702c01c0c0d416501d50718803500403c10520b0354102401d01e2051034030124406131a03681c12512007840c0910003400f8907488032118640240648521030040d800c184085460034a9010551700500340e1000600100b6001c0d1801e03005040c48003061418050240f00c910704030340b41480519503041c8034000009041003076103040601c00d0780242848200703042410400040100020440d411000844c00c1181500300c0c00c400100035201c1c80c0c00450304107146003c0240e410019402071401144211a440c00607502c1c4404e003400c9803503015996006030320401c07619019080401c8165040541034129407024001c1401150689800b0390161081e81c5c00000e0b440180180380c540310300c3d4035401c800a00384c0d8000b0701c0009841d030b06040c001d51b4403801c0c0c00600702c404c0248651050900c18409040303501000d03070700c07040908030b40c00c40e1050f03071403801002076503005078030700428401c1000a407005581090440c03000829025002 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 14001427 1250 14000177 14000179
    0x907020106090608010e010608010e0d1107050a0e0708070e090a0902060f0705030a200c060307030f050f09010f0608030a030504020a0305060c09010f030504030c1403040e010f09050c0f03060d02 85
    0x30780c40020070840400e00400380540003800000c0707059200f40d91050700f11a1154406012a4500168000c1d02280440c00c18134815130340c68100c10b0701010010b15420080d00e41d00c4940c1c0854030b50000901582a001d0f842d2058555488003080c907510034105603100c0c18100b03078166200c036840000440d038806a80c404c0015a001130521420000b01d4048071000c1c0e40495007e0b1006d900108520010550001402010301c0d8400d048081c4034120325180c65032000140701b40751107820302000240846200794404c90445007030000902050414246108032810192810800c5500300510b000f081192401007400300c03140c0000039480e148850380114000e0034007410803644902c0640000001c40c10400c01140100c104e26101e40c1d4401d0080e001404408114440b18185401c107020400885e4002c8100040e40f500040d80e00c0740643e4080030542584100c0c0c120058105404001250750305408130710f44146c070601384040129417112803185906000d00ea00043c08548100300090460a0114456907000c1c4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 14002677 1250 14001427 14001431
    0x6050a021207060b0a050d17032509030c0503030c0601050405040305070b04030201050717010b0d0e1c0207090f0b064503150601120203040512030112060606090f0509070201 76
    0x7201c2420001180d1240200350b583d10b80354084032196151061511000b48800c451100d154005a40c801c0380101070030003452107800380800000c21180201c9040741235050345d0f0301c4410440484040c06028511a070001343c03407269100c0c50109660070000225000c178061500103280682c030b030500300400340074002c3c411020440188071705800104040841c034003403842500082000d1410040082a503061032801c0c4410304290001004106501822203480d90503e85001c13410844410900d49451448118114030061815007484e20603804120f200c16540d40d90418498041e56200c16015560381e0004503a00200170000760303008240309246200750800d1403810000420040b80c06244026006001d52080c2c040c201c1400000d280034400003080c0c0c40b01c44c08843c054280074000a00701c403040026000d82646c00808241800410000e02005070200415190f42c1d6840707018004550243c260111100e6003002c0b80818200d00500900040d40c00000c40700c1011440c140801c0242140502500c082d55 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 14003927 1250 14002677 14002693
    0x60207050616031e2012071b031b11100906030509070e190e0712020102010b0114040618080604030309020307080d0c0204020f09030105040602090307061d04050c04080f0c040b061306050a02 83
    0x1880d803001c0c001c82e400240b018000c5203807d00d0060001c251420100c0c0c21780d41e040d01c6082c00a41c00505040f0a5003a0011307000d200241842c1c019101028500d500e58440c8180100070081644405680c1c1030b03e034240e07002e1249842d03541400d542d40c2210300540407244000e41c002020314104104682280c1207148021490503840c50310103041c150107400c82e00c81000c41d52000c00955809000b4401c07103220030b10b8240c0b03500ca0a036001045038051400703200d040100c10101444407a166401180c003074582031040d1250360601d850050003c05803414100d000c0e0050300000030740c240000c41c0460741540c80e5100e001070802c11364200b200941c404000100100030a0042808a0300c0902c182c41c4124424400166505060b00416207400043d41c400d1080002074480902d00c0c0000c8401c101da0288182d4010905440384000e125003401541c01c1480c0e148190380c455080482c0c0001e04411160040d00e04114800c1450207001d15072003070828a00741c84040f08020041c5600c1140101040f140d5807058842003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 14005177 1250 14003927 14003981
    0x706020403050a1208090705060c030403020303040b0d061703090118150f1d0307050f01030e030a0c02040605040504020105120403090b0a0215070c0203100b0a03060207050616031e 79
    0x2038119400964050b0b1041c800f030f204000c0d40085400c010b6041c0c0c1042d01d03040c5001d24040740d40b0110360190502540380400c034812008803c1040e203001d19401420743e80c032152102840c0d042030300300141c08204542808000215920200c603c00030b03440c80ca001175442c20b0180b20040d0b03240c450341c00f0215020400c41d0700010b03226a903900e03805452030b00741c2c0e552820b209a07094001d080c0a145071400c6035511142c0e03096080c0e59030000300241164003c2c0d801103070a030746144c0164028003111502c4180c60000089444d4021381c00b0b03112906040c4200d40c100700240e10341c814441159401c40f002030200d10f003003150301a050b84600407a0381c0180b00c2d2074050249600c2d010150f800f030b0004040200941d008801c4211907a03260703810154400b1403032800d004019000e0f00000d60790340f0017030b000804441e95080400c1c0e9645440804401568201806542d22802032400701e655010440b08110300d04448414051140d120703001d881859602542c1d031a40051662152000a16002446c1c1c1d00c2c92514050784019 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 14006427 1250 14005177 14005181
    0x908040f08010f0b010206010f050d050f0102040e04061103010506121003021002010c020f010e03040605030702070f1401080f01062709050a02130605070b010b09030a050f0714190302040c02030706 86
    0x140c91070100114008007200310307690aa0340001c03091030640d0800d8005100c1600c1c100c401c20101d650403907000705802a0b41c180f13541007a200502c00002c80d40009030118030b120b00c00b0300d05406144a00400c21412080b40710a4510b40402e001d100c0e4400e0b0100003007110b02115000441e0407000d04280100c2242c1d60b82d0004552301010000b01c0c0c0544d44a0100c140c8a540601c81c110380129860000c1c41517000c8105131a4813481076011304400d100010002c2001588200201005400e401c0c031388240355620307003070201c40440003040b1142c00a551400002c40d0790024114042c100c4016844000d40104c000508103030a0a95081c203003203e6100c00d00c0013401c000140625409000710000060fa40c551004100000d03101c182c01c440240441000610000342030109110304480d560250a611000c1e4070001130f0810440d02d00c05031aa225020600704807141c0071841030104c400703003101e0542c030b48009000d1181d5900c80c03040300303010402c41800400242c18250040358042c0c240e481524a80202a9a5001 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 14007677 1250 14006427 14006429
    0x70c050c030a06061e080309060c03191205010602010e070612020c03120103020307060203030c0703120603081c0f06050a0911070b01080607021b10031508030403200f060d0908040f 79
    0x5083d5489950403c55500f56a001c00240c1d204400000350f00e03818054034503503030b1150140650051500241c101d048071414010b07105038000c8004209444030180700010020000001d10f510018601000010760030300511803102c0d864080700240c20341c03602c0c0050545280200890081c102502081b050601c0c003000d200500600041800c00c104650440c01890316000040d0800300c01c0d076004109014198190f9010354950310741c18500400d42c0c0e8514a41200500700c240d03c014010a07003c11004080b000d640c3d081c14203c042d881c02003103000c48810071041601e840b4803410703030066041d04090042143c0358000074044406244094a410a10355031aa410b050907442820341d0f03088401030125051341800450302055031003003c0c4d60296022400141c036000400750389010b1581d9086984a141c03442c1790024011704262080d86e44859503802d00d4540503000d254034150760340642c100f0003454500110507580368100a030a55003015403e0008000810340400c0642e0401400d003c00104c200000b126070f4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 14008927 1250 14007677 14007683
    0x9060105040b0c1b0904051018020406060e0414010f03020405150306041a0708040804050906010909020a1107080609070e070306090204061d040902090a180204020304030903050f060f070c050c030a 86
    0x2006036038030982588502c02d161110700c0c5c8030310344240500020400026608907603c00c840c0d0005000601c2220100b2001320704031000f90068180f400010344160410302c00992640f00342c40c18440d41416411240b00c0110902508281401749a02840942481c0c3c0c402c030751000c0f9141c0041118901c2d200000c0c40c04204640031225580c2801809100c0780d540f002c5c040d0440f041e41003141090402d59202e11090081d40100e074000d80b50f400025030700b40e102e541c119000b850384907011507130340e200f070100103007034085a81d050202c91180c08000911b003000045c44a1044444001920a480c03d1022504660401070101000c2546822000c2200c0c141807000340b004000030341307841641c4c00220159005030344a201c0014815843c0405210158603009607599024000c00070000340606076468541d1201681c0c8070107500140f020081108240d000500541560b000d802211140f008a8100e41d507200b008842d109442c0044501046500f07014070500c2054912420036110a43c42e4100413130300c0e1100c2c0c12819 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 14010177 1250 14008927 14008933
    0x3050903121b030301060c0611090a0306020309010c0903020306060105030402011e0201090b0105040b0d0602030a09080706020405090105150405010f0e0409050114060102030405030c060d090c03050a050105101409060105040b0c 99
    0x202c810700782c0c2d40c900e031101540d40001840c15980f6210000d031500e0740401000d001a9240d40030103074611005c4003140c410200c0249000c13440d03916818040f000350070844008005601e01041007410b280101102d8007201d50060040c4440c0d0b03504001101c8542010340120b050007403450076480da0040c0c1c0c041c00d01e03840c5110b03800010300c2001414070129182d41a440070307005903e49602c6000607120380c00c0001c1d08030f80022001da5a0b48442c3d94050080c40809005000d10f000403e5900400925800400031120201c412000c60790700c2d00100500c1140f0751002c01c3c03074603004010400c0b481d4041c04000c00920a2428000380408102d0003040c1611127500c42158984d6641d2440103140c101c0c95000c1c1d400031346c20f20041d4109401c200202c0d0b52280000d06d4944144008240c840c030318074071600641100d80c1d12400014540740c2e240380c81d6541d29020002100c00b9424000003440111110045400711800c0140002c50307410f140083c020755040c00f030021410041c0800003c01c002030003400078020a0100c0c401 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 14011427 1250 14010177 14010187
    0xa0909060b100e030d0e06030403030c050f040b0909010b03010e1504020403080313061b02100e03090409050d0207050d020603010b030910060609030201121424030d030c0e04090803010603090305090312 88
    0x4c0609007092840301006015902c2e2800240d40c80e80d01c10399920540c14240040c40428a03c015107042c01100301c403e000030000100852240b40c50f0300902000b660640da0000940d8903038040d055107000034047e9007000c8440600084641d00160000200180064130040c640b945030b031a80c14099204480300601403e451300c800b810400280710f000c50002007000c400101c0700c40b02c01c009440302c041c941e40d00500380e00e82d014408148400d0040300c00110303001303200304844070036480d0541c0c9803040c0380e40b00d00150103507503800074803407c0400c031088280740c1c0105000c2c55682418801c0f01c82c1c0d000030309107903900d00c64241c104ca01440e66204903400342c66952102d0030316516520004064510048002c2040b0b82021084e0050764046482c25811910205d08046007170b40054000e00415805103401d9810b00c03030b06400e003c3c2182c041d40300c0c003070603900c0f030b51008510741e800020302c000d4941c00303030004061030380410042104500c00d40c825080d103846440d0840c070b0140a800060320f00181c80840580103040098 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 14012677 1250 14011427 14011429
    0xa1e0b0c03090c0f031e010612051501150c0f0302150c18060705070e0601050d0f0609050112020a0308180307090b0f0102070e0424140108010b030106050a0909060b100e 74
    0xa03c14a81c8040b0340c2c20700e08921243c0429245d044c03224655480f028400304040110500b90003079409000c40d5a10440306003c10b003400d0795a958003008007244041c0e41301c004103d41c0d1200b1030346485610705031910b5103108440ea0711940040301410040e4110300683c1c1e0302003500e00c5000e12031805144400b4415882d0881001c03030b00d03200b507510115075101340c1040004600150340851b20340308541c8070107070071107103940d5000061300e40b0312a801b40d00d00c2d0305107030603062440846c0c40d034446025250341d800f08124603a2200000c00c0d41c00069103000c2d5100204200800010780340b0001441101c1d050741c1032880d280340ca0000301e454a81c2d00d8000c0c101160310740a140c1014240220030041d4810244002d041d036078a0203e400108038801780015041da1450b004050b845124078170503140180031180100f00c1c1c810071041046408500303000c1c4070119400d03d001585d4030300d014058541920030050803078010502d00340141004091030001207413030640740c039401455555045003a0f0985101500e030340d841e034640700d4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 14013927 1250 14012677 14012683
    0x16030b0402070c0302060705010b1306080601050a051f02030f04060306030b0601081003030804030c1a150402180603090c03030c0d030e03040b04050405060d02030d02030a0201050906090a1e0b0c0309 87
    0x122414022031060103003001080403403540781c0840b40c05480c0c06a0b25000341c1071090140030b000e2103035600014011407541d2042695807000048031680d800b6510b807662654100244941648503050380300740e0f00b810641c038002c3c0521540d5002485401160718003662520340005a070420791110011941e200410420311013039444a6500c6070003440c003801c0500c4c042d801120028070320300000d01045209070010301010f008600402d11036801407803050071202c0f1801e030b03602c008004807050040c1c414900c01c03070005070403d80240c454001a440c41c02002d00540d0b814003a80b500300828500040c482d2103000c2c6201d4034140020000c14ad4080003a10006003811300103029140300c002c0581c2c00b94002c000c200500600344080e43c3c240c64044601041a40f01c0b5030004080c446103500280d494001c07910228010b03900080104100405500240450380d42c0c0c081d00c42e02c801d001c8980e070b4595000000380742e000410f458503c101010041c407200540320700d1911808401141110444490318001041c0003400702c00f0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 14015177 1250 14013927 14013941
    0x5090c04030c08030a0906110309060f0a0e0d02010815010c02040e0d09060504140d0f021005041802030103020306010e060a0b0c0d030605220f020c101a01020d08040f0602040e1603 79
    0x56030055203040b122070f50042806c8114811942080301d081c040c1c0407501e000780219607034100001c010785d4480c41c04101e0780506074400940000400d101e0031052130141024808160b6954058440c40036503a1024035070a1005010141e141c10401100d403a60016a01c0c1d00c80d06000e0f095040c001c1810800c4400c0103880c0d081982c1280d0180a814041003015040d1000c0c0b0303041c10710b010b40c3c0c001c0d40001a440d0407070300300b0310501000354003840292040c101182d01ca0040d0046603007164a2131070283c8000203640481c442030101940540240c0018854060120722854204901504900140d540e60b540c034103041d081144000c0c40343d00007944e142c21f52a0325000d180301501c02211101c036190b006515140c1c42c0c4c078162405203003403621590180410b00055058a01304801c0b2790598408800800e030040007040e8440000b85220469980c03610194030000324020b089680751070f0004692619181c0b02911740d00c000040350482c0d000c02000ca9002180d40a0074011410340d00440026000d5078406420b9400c5 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 14016427 1250 14015177 14015189
    0x603060b0603042004060b0c0d0f0c08040902090d050714010207270b0f06070305090a0f050901030303020304150c0203030901050a050c0a05070623040b090c0607061505090c04030c 79
    0x109100380800300380100c80081440d44001038014400c101360340868007a1090758002c00c41c039840803545e03030300d841004107098071f64103110740d564003074086030b654142c0301c0191064018050400920040c40b0300303181c07a070061481c031400800d80d00071141d0307c3e0b8440b850a5402e400c50489005900c0015403913503010400c3d40e025003044400c010785500780d01c0031040c0c44004030300a00070325611011450100c2e115014590412302d80600304aa0b40c0c1810b00300645a640490321240c01080d9080340040c1803081e842240040c0c0710020050308950340703981c50032800380d00050f0040d50b00014100041d00101aa0b125052205035030703402454682c035150201c203084681c000c007005004c1d8100420051132000c800c0844100c43c0c50b5003082c90315400c05062101c000c24228035092000e40b42c1021081581289685d100c0c0b10324450340407520310380d0382c1c50101c0da110148100b410740c00c804240094400185c2d10b400c500c2540401094070580d150381c50300041c001c2e4000380d4015a940400003401c0c428060030303000c2e640103400 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 14017677 1250 14016427 14016439
    0xa08030c01050702010c1e0c150606080105030a0302030403150615270302030705130e031602030d051804020706140c1b0a0206090108071404030501020a03060e070e0f030c0d05010603060b 82
    0x400108090001f03103022080c0740100c1e584ca5030154038280550091851243c11442000c41e14055a0035180100450302540e40450400000060700c4e00d000a100701909070725501450400303107550740e00c0318107100d42c1c2000c51000e03484040205e0001c480100f144a140c2a680d05e52203405240c90740e034a540d2000e2083e840e18405908024005600c0014004080b5041568608a0360504281e60801002100075100302400009520341221801581d0384c01924003c5081e07030750b880000780c8180d4040c80b0725964003841c0b2104030310b1421a403910350301071f0030b071940641408070740350240310502c121030ac908860181400e100840c150380078101c42c040c541098001c820050030f0080180e000500c0900401c031182d070401c0100000162070a06c130302c150050041d01d03480041e4a9070740360326100303020390402c00b5000300007480e0040c001801120760030b10901421341d940360520007008487c14880e0301d410b02640300c0d030184202c94040000c0c0d10307048500c0da90b00c0e024000000b41c0c01e08502c0c2c160151504140c070684106 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 14018927 1250 14017677 14017691
    0x30510290307050907170a050601020c010c170d02071e0b060303040503060f0903040305070b091306060507060902030f1002030f090c010210150e0703090309050301060b07030305040c03020a08030c0105070201 91
    0x3850002e84501a540c04944140f00f40e41c0351502100e804040c17601203d4080c1075071003404110280c130303004540288402d8080d503000507000401111201064180078002c3c1e295081c40f040e040d000a0004c01e078900560340098605880c54032608102001c0d207048403040040d84086c041440075603e031580d000310044015620300703032515002940d035a802030041c0750400280c03000300d9413a401c2081181c000b185d00c00e0545031402e5031038840e04443d406c0b4030f034564000c1d21042d964462000301889043e00f03039215922002e0810400307854a00c0140308140d4201d030984100940c42d41c4500003000305411018140340096583c1c40c142d03402404440c00902400c1040e404001e0b00c0106a80201783c85013215403030100000c141905600e050044ea01a5001c8032480c143d082c24040f000f689a000500d9541c0207858541c8107594550070306080381e55510800f01007e4082c8114030010b4820b41001d500315004142c0025805d8403030300003e0351041c242d80710101603840001c21600d000001e00402c0d0780200a400208001 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 14020177 1250 14018927 14018929
    0x708040e0f09030a17060604260c01030c0c03111005100302030106050418081c06030303020304020108130b0606070302010204050303030c0720090402060a050d091101091212050306010903051029 85
    0x41030402c8404956200c5e1070001d96181c40e84000d0310002c0a4156103000c440c1440140880c641902a08000e5103004007072501081e54013900640c4d50180803552154030340c4800751400c070b83e030f0916540082e0150182d10201c41c2080a68060140207003401c401c130250b0245140b042600b1901603510080c02031b800c0403594448071400c0701e0300200711070308024220368441140d081000c0b4281a036207103000440c0380610120038584e266000d907103e03e00c00c2e214000755444420388284260459074006140200c20000200503007000f0001d048420f01c640009820245c9444c0003d05582003112119090319010038110140040c42c58403d40c0b20b00204c140d0603200c802c2d071000c00e0200f0360040c0040c0c0180000502010f1443c460307801c03956800141d49040000c40036a2511411078005403c101e800248418004160a441520820061030388440c400c2041c40c44a00141d0760398000400d5035041c002c040200102150091044c12141c0341ca01074001526110000c4002c050800120911010035264010b10b42c0c07 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 14021427 1250 14020177 14020187
    0x308030105010e030a050106030602090901080f120904020c070e061f0804170904090609050706021f1d0a060509010c0906020c0d060b1905150306060301090c02030708040e0f09030a 79
    0x41d58000c0c41e05000303008050020900d0806140030050481d0700c1e00c480001485241e5002d000002000c48405105981e18000103540304188551000d9030703006485c0b01c0c485d01c031083c4010041d055001c0c1c00581040c800030b40060901d503841d400320726480c80039000c002d014a01144500c425041244031021300380e155050003020044001d00040440c00c0c40f019140003a8015801e851100c200240203100d02d14040c60180050301001c002103e040c82007a802103002800850308007020403640081201c46400407410401a00410400e01542c50f03081c04031025821040c000f0b040414090000401c81d414921111421100c10300c00106c01c01100c51f00a01c50654007140021001400303c1c0c03404100821424036400400911060700d51250464000454200303290000d03108403030084136503036680d0a50150090713049c8030403240d85500400400062005158a500c0400e520b0094411642803000d41c0e031307a032410b03030f44950040001e0340040420400c201e100c01c0e056070390000c200d0740510300b090141c801c0949 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 14022677 1250 14021427 14021429
    0x10e01180308100b040b0711010302030603030706090f0b0106020d09050901030803190e0316020a0e0103020105031b090603040b0105100903080301150203070c0b030712050903090d02030109120201060501021603080301 95
    0x810002c400c00481c10300c403428800304014240d0114500d070385075668100711280c3e034480d200480c1d000d0031b5500b48894a6009109a902c10807014014501e030400903a248001000042003c8483c07040010141000c500c00a00c001d019121030f030000c0541911240d009001340030305502c40e1f03100d01d40410040c000500343c130094940000340a4a030b4a907180c0d40816003405401802c1d00f401c4144804640c1307c6000010142071480140281d440842080d121000484100b100340406808a501000404c80d6a10340d0b0714880c02205a108030b03182056600380006150740d00665007968282c1041d00107010300c2c500041e088000002a04154000324599036032181c15010521130030710600c07885401402018000c7c011100c20560048150a20b0790f100c280345020390300140c0352200000c08011240000d0344a81c800d050060000720001c6007418070000c1004101c0d100250200e81554071060f2801c002041001c0500c01c1d0006600081502410507000a01e002003800c0700c44450051820308001042c00b042c11a8 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 14023927 1250 14022677 14022683
    0x7030f080402030109060c090609060206100621060303050414060313080903070e0a0207050105070203131401050d090b0f31020303040b04030b0108010b060903150a0b04060603020309010e0118 84
    0xa80c80d07600c500000740181800007026101c6070a00100e640d0f046d0b0b0082c0d5400c169181c544608078081e442e840c0c120303622207045411107040c1c04010380500080380600207000c40c0b034100c1c1007020304800700e102d51502a140284d100700c01080010405001c108040c803503001075600c081c0c03a08c6003586408501a40603c50420b0050304800000540c01042e4501744070700b00150a030100b600c040d40c184202c2c200001e51000405540c2c6528103000305c1c1b0014400f008444618243c1c1c0b100601e06403c04800084244c162540c0714140041049104c02c0e244d01c0340100c00310517024011440302c40c03405903280414040000c26040a2410754810404440c403131400002a4199410034902c0c20160b03440071a10390b00c00c40d04109807040740880c0000400c80d5200e8454141e900f03d03002888400c078041c080c090580110074500303915400120440940e004200e0416a0010008001103008003500c808202220440d402031400290000704108514209001d46080070408030007c014441111038105000072002c0001 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 14025177 1250 14023927 14023937
    0x80a110607020d02300c030105070c080409020a0219030f020105010e0c0f03060d0812010303030b0906060304061a1903030315050d08030414011404030e01080708160c12050a08090307030f 82
    0x8054850340101c0c107840d00c552801044501417400c1c11803541c0c0e82c10440b00184170b90b08090004403000d01c11403485403525445804541001d040040490203034004407038090441c4540c035001c055a038000d200380a100c50090b11a0950522514030003400c4d150160480c2d544004a034040c844007603101001c0300c020b520701c403803190380f0303901d40d0341c001418030400d4140038103801c002055400f800000b9950b40390489200f620200b2800c0034410030301240e140c003280c40359800b04040c00040c2c0442c0031a0002c0110842950070720301c4050322000000d03e601c2c3d80c1240b103200300444100600816406100b212906501c06002540306460300d0005480482070100041401c48007101040402c0386251000503148800002800b401d01106c10035170000c0c1044409a00241007454000e402d940a42c14040c02440e8030342d68243d403546c03038ac0e144c0b40000700c43d003070342c041048103108401000c42c0c9414006449800d40d562055912260158014074070340c000b0703115070810b400401840c80043c0e00842e0700410f014290400e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 14026427 1250 14025177 14025199
    0x1b0203010204050306011707060c05031c0b12011a01020f070b070c0b0c010507030c05070203070608070903080f0a0905011103030609040305040504050f1605040602071202040e07080a110607020d02 86
    0x12a01a0245a02103074051180358004a122143c1c0307001030700a601440d04803070240d9541c0000321100c02e503004001c0d18640013080080c07400d0307154041559a1181d55400411800306940c041035802d115900f05982031703551501424050840b10110400c880c4091008000840c460004903403142c0f0907100360701030000c0000b807040400010903801401040c1e01c1601503183d5218002140c0608021500302d40020b2401c0d40071200d590150080c1d80040c1c0d0040c0041440c41c2c14210142c0c1c03410001352807982885000140017000420f03050003003800341001c00142c0c1d00c80182c81000740c40100e10741c2055040c00b0a500002c0d929043c00015207501034000ca407042c205071200d0400b95868469074100d02d4000c0d00b0401003200a64018190a0062094040b444120100d030001103a00d8001d900609006804c22441002068003103001046501e000400010700b14180d041114a40030240e844040705400030a612404e11000000155072100d0075640c0a25003c0e140c0e00103500302c2e4210350000e21030840490 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 14027677 1250 14026427 14026429
    0x90e160e03030301030c03020103060515030a0f0e0102072303030403020a030503060d0c080c01021005010503070506070213020c070609052413030506011409090c09010302060a030e0604080301050306161b02 90
    0xc60520002409425682d40c1d58403810841500031103400181d000c6410110005141e0805088103801c0b0070115186030b0442d201d5607502c101400004880e060030f1a00c03140aa15402070030701c020700b84148079020740491200002003c144100c2e85004814950b0024010800825000308011040f03503807610305a075499955a0001c1d003080850b80002d081c4460354000810400700c006032101141c0c200340c0031540e0b661446d02d0300600761078090040540642003840c3c00c0080d41404005861200c3c030090811402c06060b14003181281c1020b082d55807a6803008004000494012100700090300c030903a540703c01d03440f115981110400c2c231481600101140000e0707207a808800d01d07034620055603010b400c0d20060b5039103c2c6011038881e9480c06584c4201a81400318085c0350000a50b002102c601404000c00d83c1e103141c0030010f254000406060074562202c150109205061112a10544c4038000164070395062030103052400c1c400800c020400509400700110054000015500e034803900821040e0044543c4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 14028783 1106 14027677 14027687
    0x316020f2d1f0b0102011d030702100e09060108040f060c02030c0d0e13090201110a0b010e07081e0901020c010204090e010e0303010303090b0d180b0402030607090e16 73
    0xd0001d800c5500b69002600360140500001440503c401c01075907034000640709100540e00b00040000851034900c05480482c00245003001d40c030030808011540b45003000d0042d03814011030400003010000e4400320a4180c6070301040602c2030003210180030b96a5006840461301600405150202c400e10901c400b09030104004d2541c94000301c00e15611005014005e0142e04000c0c60080b0f5401d9604100001d0f0603442c4035107041802d961421000d009104000340a08080114070340a208940c003c2c0f00094150b070407080801310391a1141d01010380213120b008400d1310294000b02c0c0020b02030145034405654841a0b200901141d601c603c00107450381301c240030042c0491400c1e5428003914105d04040c0902e00c001c0040051208203030889411400c0d409034007110303d502000100400c608092110303581145c09400c2240e03000381810f039540c040302c0d00140408070740c0e481030b10300c4841c4510403 = true := by decide +kernel

theorem cover : BRFrame.Cov 13848927 14028783 := by
  have h0 := BRFrame.cov_init 13848927
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13848927 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 13848927 ≤ n) (h2 : n < 14028783) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
