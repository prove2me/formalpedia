-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0124
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:57:54.212524+00:00
-- url     : https://prove2.me/submissions/909dfc92-9b8f-4a6e-84f7-955de86d13ba

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 22122308 ≤ n < 22302164 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 22123558 1250 22122308 22122311
    0xa09050f031c1805041e0b0315010f08060604050705190504121202190b1302150a08090d0306061b030c05010608010501090e07080601050111030403060c0c020411030402090a020d0f 79
    0x1202282c01824440884052040d03007088910b01041ea81800e206000808425450308900c2e00716804208004020b1203e0b0143c050060782c2c5419880b0032452880c41c000c128811120720680d250983e61414040c0c0684414403560800c410710900b581d2107400d803002e8255a626600a00104810a803a14031a550110a440c2103004c05c0c80d05018190281c200b01010f10b400b43c84085840b507403031080d0502d038408000c18010144020501703411055105600040c4080d048400d071b00411090b0091580058075440002030302401005409601801400d0080c2001c0c10300744022030074041e01030061402d0340661150240b0394852042410300c1000d03000b000580010081000d80d441d001038034060074090051030421400d00780c2007124421300107032290480d02018007510442c2d0174074004484840090306503100600c014000480840c0207481400303131002654841c41c0019660744144070a458101120300200b0328140100401342c0c64074030156074454410301d0010b03035484849020708028219a8908881c0c503 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 22124808 1250 22123558 22123603
    0xb030c0421060e030901090306020c03090306040f0311070303140901050706180c0f050901050915031006050102060601050408031902070f0803070b0603010603030903060209060415020c010f02030a09050f03 90
    0x806909404003079601641c414080303414044981552486104d0742c07540045c1088400b000842d6030b83c4e0290034411f216030180d0f482d1002450020340750000c00e540031b4800f43c1e001c0c103040003010b400042040300780100c00f003e840c0c3d5502d075490180807184414405003440d600040c0d202d015070302c1b034012900c009511400c10050900a20710441e5492004070702250302d5204a440803696007241d082c04400c403400240b140b040c03a030a04081c084210b0b0702034000603110072041040c001683c0c0900c00341e140c0c488201d400041d04c0b8034280c0022718020003d0101341c1442010082440880b40110480f80848803440165070540351140e0304038078141240d4404902c2c60803d44000c540b001012005111181c000c042132042d9071201c00816080302c8440c4401070115411001c00c10024210750054445408000c18050034103a0300c2a0745100c04840c3c0d2007500044e0848c401021082d078010b5005c0c54071800501c011820040c00708400391003011240110392007180350030745403079059404001ea415903030451051100c21 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 22126058 1250 22124808 22124849
    0x201171b04031a060109050d0201030902060708070b0a06051c060c020703120906020606180f040c05100306080d1d011110060b0a09060206130f0f0f030e0a0611070b030c04 75
    0x5406080e035182d102c503050400813520380e40c802ea9440302038550042881d000003000d54019401000d2003401240c00c00d20901c0b91030040382c02540900f4100b0b008002d88446441d1400c003060444a03180c0006105403201011078411080081c0240302a030340c401000078685002000a0745010605d03400100503850303001140081c142d00402d608116141502254940e4884e01d08121004c480e040d00942d100b45a074001410521848039455009409050a200c04a4490300480d04040300f008080c1c0110b42c454108015040702001501e800202c41c0c03410340140444201200c0c120b11060b503880d0b0400250348000d610f6040280421500340c80d0f00442000b4003a662050111306800500c400d40100e1507605000503800d00101b0540d03c00d064085072600d00040e01d50b18200038450359041590070001c103019000001e0001010514154000c3d22841028401041045130341c1c4a50342141c41040300810094035000000103540d0150342c0f400d984a6105e130f4030066060581d024a074800c000c42031503000d00c04803 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 22127308 1250 22126058 22126073
    0x10807050708040e191a0102010e120703051b0a03020303040210170c09010e0a08070e07050304050304050112020c0f0c04050a02040605040b0a020114010605030f01060f1d0604050402040b03100906030201171b0403 93
    0x851b40c02a0000e200e0960740c0c4031344644508a00f400c10200170400c00c80a000644148001c5c0300015007112880c2088884940640c0b51409140c400c0380584e01c00014003055203454280752440c07050f030741390105426903041241c86000101501e60383c06c0398004969605203a010f1003844800d0000a041d0524065844c1c58050360341540344184c40c040001000400c40c264405e9044a00c11604800150314180ca0400116036111b222204520415420b208050340001c2c240704451680e1000d00c01090b40d01030007010481255000f40015500c5441003008004180d002016201162400201941c0b5010926020f03400b600003144810002c0710303440f001144094103d4007a6025043d0b2a007800f031960f803104000d42d44512004040e04c00f0908a82c3d4044940d1842d5410441c50035020349018113103030356840842e0580e0406c0d000f0803408400032007004810520450741500805121000b44181c41c61a00064040003450b0b51122440f100342001030801261001200b00c0c0349292040e460b656940c0c0d052144 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 22128558 1250 22127308 22127351
    0x60501090b0d08070f02060913020307030609020901020c040506120a0309030b0708010e150301200a1701030c1a0f04060e03061006080705130504150302010807050708040e19 76
    0x803252078140d079604207050880007500342d40d0307000003c10310b41155522180d00c098001c1c4022030348190100442400d5881c0d0090074126645030590258890801c900080c3c141d96154000002541c0305101c22030090380d001924404021045d1000a055202c501c00304042c41c00602c1c0f050014810541c5d9001003560000a010489004540030019a140c50404030b804020038496001d0210032000440d0115030304025541040c940100006021061051801c0400c40c026450303035240440032500c500c0850700f00c040700132220f811112407007917981035603208075851207280618041702d1205203e60603803000c0d0100b140c00c201d003c0505984c03181d50303842c4001d000143d10742500c2c0c060700991001c01e04e00c144622400c1c082d038800d500c03000e000780d40d96202101c0580001c80c941c50310010844000686072114865244408054001c1d00003860444c000500007400150102c0b0400008202d06000300ea00c1005540680b11400700d203400b00e480701d0003c0051b81d109280d00030b41c11440c00003440d001070360b94007208 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 22129808 1250 22128558 22128569
    0x506010609060801050a09051509070f0e01030504080d05270304180e0c04020c1e0a0501050106080108060106120b0603070908100204050d06020904060e01030606060e04020313110a12060501 83
    0xa001d00303038680404a40d1100c0a10440f90007009001061142c080190880781e07105c94041c4480190904010009044890940d071032000f242c200505190041d52140103200c4444d800e08003802a42000c3e56100500c0c425100c0c03002c052603540c000304040c000f100c00c50102c1c0d15200886d4250f12000312082c0b64403640a80f20302c1580b07400940c800500302c001401003040b43d00e02c410250100c0c0c840d41003807001035404214501103d00401c46220303020f9884007074901c0c0c00b1001c0d90090840d16407a1038600e003140c00607045803040c4408000104121900011050305460040c5000b030b000c6074499001e007020b000d003005050b80c40310000c0304001d103c0da0302552841c115002c81084a40c0808203c43c0c5904901c12401102d40005c6c90150400110744142c004000c03880313024200203003042d0781d212000081482a0011a012904c0350703010010b0b16813000c040004020308603421072a40c148840c29034582204500c00070314000e0020032010403691140024030091a100c801e50ba0f0400e0f852030701200926013406030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 22131058 1250 22129808 22129817
    0x30609061008070c1b0303030203010810060305060714210603160b0412050703050a15050a050705030a050a0e01020307020309010815010e060c0703020301020a05090f09040305030a0f1805060106 85
    0xe06946020240301a0141281d160315403182c5070f015040390250003000054440c0d5a01c003801100c084030f100b072054000c501035a130040c0c4a50403d548682080c10141e0b6112003070341030950a00c08540c000c611241c11480340c0c00c0080100030504003036241c41c0640d40680305030b00c1d5050349640a80460a0724a07100c0c91044041e54801c501030420b1681d924514001c1940c2f90505100c00e101c817481e4070004060b214011403c44500710b0b41c80c0d840ca45048803c000c03c039800c3d825100e07160341341e44030341c01281e400c200c821005000714036040000405501004045030411511800458020449a8000c980c5103207001c009660303070301e84035201a543c0e86c02500803900103085080055424101107801902680059640d0300031540351030204501600003000316201e500581c0070000c01039030244014040c01c02c040c3c495a848950060030024450069a9098001c240e40410040040e81c460102c1c4c0c0c3c0b0510030785e0001601102100c82e017000302401402d450b5000c100324200010300c4030010795076040341c40c01d41d02e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 22132308 1250 22131058 22131061
    0x4030e0f04050c030109020702040b12010c12090b0705160f0308090d03050903040306020a0909060905060906030c01020606060c0a080d060807080a1736010905120606210a0602030609 80
    0x50000b11030049842d10880ca40510040c00083d0081d00146100c2d80028004211a080d60002403a1010300c0e82030200d05a41d60031038081400d0704040b4051a0306254402041043d03c561600c2010900c002c040c141000800620305c4024001242c0746203159812400d0100303804081e1074090001c0c102601c00e103041340b091001e40c00c0c515110340103092044031403101650401d0714594606c001b942110030180284102804003045004040c13286900622400e0408155803d01c0024003801c42c0e000782c9140d00a0704640d00c40c102c0c07a41c0000d40da0b608040107884840d03840721054001400c16014403001420b09a001402c000303107125039004802610682c40549a00e10345e81d1040030740d07480300540020036441803604c601c0300072052500600203d5244901400c42910120340f84400d004060890b10720211445007040c81950340041c2800203010107a40f1218088131003444a903990030020402c510498600500c10114501181e0554681d800031046404600b01403070508043e400407030b01c00d0f006098820 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 22133558 1250 22132308 22132339
    0x70302010b03060a090203150402011e050315010806030c010c051e06040516080a03051c020f0d0f050c0702041e0e0703031706060301140109030512130e0906071d060304030e 76
    0x81100e0055900800900ca4231806681025440400810a0b8180070250f500c0030b4a4907440c0300c61289144441d50342c660349241125000e95030304022075002d81003100d400c0030800d05ea1000101c12048880908055030b06940c5450805c2c90a202840d45264003022552a2100d070380780041c80c540164459020b4421442d10303e501d11003a62201d100702501ca500c480e0920000c02e0003800100f0103400d0b11060500c0012450849100340d80c02104a074692060014080c8030514072442540122910100c0500003410540e030391803114090090080c0c8600d9031a100d040d0f1010160031041042440b0140c14031114003041311260710781e0340900c000e401040c005448a806071900342e05051040c9401002c60b411a400d04003803103e00202040b01506000745504080040b0703904001c84194490884c9255640d95a64519401130040d641c4c0200c0c10109406c06208002d04045522548850035150081030300409d4048489100d02070000345421a00c000180030600d81d005d4502c2c2d1160f0402e0b20312002ca440e440 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 22134808 1250 22133558 22133561
    0xd060e0705031803090405040803010501080907080c0f13050a05060a060f051801020f0708031305150412080d020408010f050106050702130b01020c0a09020325020307020105130b070302010b03060a 86
    0x4549500c0011070800c0050310940500d1010309012a520003140d090009074004a41120300640e8240c03003000300403004000301e6a00c01c15440d4010b01903001b42c0060751030300d4509580d4068074400701d032040c0c1c0306102d45a055100c01034502d41c100380070390f010701c614200030962a004003010f4500c01e0051004078004101d1500a00c10410300380019500c0c0d41c07419418840000408040300700080c118001c0da00c4c034402e101d00c104280c501530f2050758080d5640f4209448020380c035100a9002d01c2c040c1600000750091288103905441c1242e1500300c02406203001440e004846200b504050203200d0b1005c10701040030081540000d59030019450200a0759032640e038144c85900450900035030046c0180000420070255422100300f142c0b040c011a600b030400000006c24034100e5030040c0c0000d40d804000c200d5030b645184986c9603040c20418512002514142c002501c07445901d02c068103005000440c209103003038000310680100f200c1c0e0b607419220401c0d031500a0207003071940d401314403e12695005c81c00f2003907035 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 22136058 1250 22134808 22134811
    0x30f0815040504020a080604030f0f030b01021f060b04080f15061e01090504020a0507060b060304020102030403080f09060703030c0e0a050d020d1e0302151f18200d060e 74
    0x25000d8528480908007000064980140300300c5c0c20100d68040000c010300c01b0040310707000b01e12035201e07100d126071807400003400307081900440c80c101401c10001400343e98001c1817505400c00c042c800c0040e0401c6080fa603130083c040b164080108427100280004200340003091219403000716400342d400760340a404522941c018161000da038805083c1d070040200c0e0480b02c80003000c0d400e06041020510b659640050200d800080c3d080000c900000351141c104422441605481d49c4112036090031820942c00003035603402640001080c0c1c42c0300241e6100c103001d4030410ba41081000600e000da4070000381c81c0c0200a40007203c13981c4003181180d40d00880c1441c201d5042000e4800103440e51144100c03035020003101610743d00c0d0683d0b0190880e160340300281c1c54044c413000b1140c0203400400c1d980e501d010441001c480000c0c400131120b0402d00b009034044110f01940c1048070745020000c03001c465100842d5000b0300d00041400003484195501244840d0050080d103103084440c2c40401c400d41d580e24240345410070 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 22137308 1250 22136058 22136071
    0x507030b060a05090103060302040c050702030c060408120d09151a01020604050c060a0909020301030f0b160c06050705120f0106030b030304050a03080a05040905010e04060c0318020f0111060a050103030f08 90
    0x42446100c2c20700e4400d50103072442040524002c41c41581e640c01040c02c485003444150001000002d80105608040100c001c441400b1b131440c030300d881e24222009440d401801d0380c080d001040000c0c4812850100c0e000b01c00696041044807840001501c15000100701c45215451810700d4403070304900320340c00882e0a030f10880e045405010350841c94010004a913100300e00f00b4040c4035890300086595003c504c040c5002e94803a0310300070b0101c589410800c1070890004e00071900e050004502c0302c807169001d51200c1e8a1030f4403010114250b121624152858016803008140c50420081007207440258003030154100d90b1261803c00141c4102818183c07a48524000d20381c110007000b50806c0000d503a800145a903030814544a0700342a01c4000d40801d4800a03402554030b0305c009810722040c00700500c91000680d189040420280a4003c1d41c03090f905901c44020f885012525240003060f4040c0c0e010503c16800b50058400c20300d0405041c0d0b00901c0c082c00203600150341116840e0314903000e14103445c09050b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 22138558 1250 22137308 22137319
    0x29040618020a0e07121a010206010e040309150903021207050f010e060301031403090d03030e010609090b1503010f06031a0106020703030512040503090a082104050a1a0915030a0507030b 81
    0x50400356000d00f424009042103040206040a080b1503241c1d91058000700004805100d07040040c0200092502c0c0068008501045c01c09040c000000c0c2c0044003041254404a2001c1e00039040000c00d88460304550320182d0411603072000c5003800b01000c2400015201c04407500c1480309641e900441e1005240d19016070002c0301040144040382d888044102000209000c4034a040c83c0f040204e40403854809007100400d444224540c488042802450003401c172142081092014684034040440009001c28032500a6903001d003400391001e41100c54403428500c0709003e0b00d5924507044103940525005204018403860000c120217101141c0e035012260507903900390030440104003440c03007044041c0040351140f0040003035580d141c8607020284001d102002c040e09070544a2600305410a02c0016001003100081106000a03501e02640d802900c103090035403545414084c0e15820580b051040044d40559824104a481411400150b00c2000c501105001366191018203030300340e4118034803256000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 22139808 1250 22138558 22138579
    0x230a050a0c2c061306120207110405060102011103130203060603030906120907080601060e040e010e061902091305160c030c080702041509060906060206040c0302010c2904061802 78
    0x3009100c2c0100c16042c40029080da2410100001409680140103050030160310310010400c1507000946021400c0c0c042d2029450100c00d5900c0780c803103a00320681c140c1b0032a80d81c0003040503640b00354400b50321181e000d042e0039a01d040001c2c04490080300100120310030b106080001d115070902005807500c46038060b00003400e08484d200c2004403044000c00e002d416105840c000103451004000c0c060092032161500d10a42a1b00030903c421b0315030b0003c100e805d0b03070b052900740043c00030001140340d440b0300c40c11482200006641c1001e0b01a102e04000c0c2c1d54001281c5180b032642108590000b4098031503510300b950b084003c094242d40d000d04150001d40868100d50b8901e0205420030014184948010800074500081103485c50012495402c07420b402eaa90301c1c414003041ca042d01c504000341c4080c0c002003030f1303900c1d0554680c840c048103408024100604242c5d80020001551205915580500044109000061050800800100d0702a540541031140d424246004400518001f43d00944642c034423 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 22141058 1250 22139808 22139837
    0x12010302060304050a12050409051807180f020720090c0306040203040312020a0f02070816051c0b04050a0c0b040b0304060b27040b0a0b01091206230a050a0c 69
    0x42d04000d000703840c0f500840c05040300143c0e003c1102a15084140c880c16103a07030505000f881214001000c825421040815034442c654000078200b080352209212002c03100c86d2000b07110040c2480200380d802450001c5404410440545203102c8141c001403981c1040c60508000c0100c00c0e40c0945e200c80d00068204041020b5003459001075900600a00709401801d8849034014126842461100c0000b00b85400c4100107590500468000304840001040520b21407000d882e0425214030500348074030707000540703d14081c0445804201040d0803e599114514081c01c113251241500001250f41c40114500071a28200000581d02900c4503600101d0030f40d956603507418018182d2912441d80800754501070301c0e1241f044001c0c0ca01c0405002104541814140703466024100003070508101d031810b20400104591340130703c5001c00c0390718036101450035035420306100e00109003404041a0b40080104407092003407421080c00d014401c080d50402290b55003507000b40841d510507001200041c01c00407030481 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 22142308 1250 22141058 22141069
    0x60c05010c020c0d030e0102120d090c090506010f0305060f060408150a06060801050108130c0801091103070e060d0c030b0f0117010b10030b03011b030504030206010f030203120307030f050c0d06060512010302 91
    0x141b500040c0110381280d6158007900b0055009003075114809030325299401c042007040707035500f0300400c1043c005018074104100060151740008140c0c1003010380d190000703440d955540c9003800760350b203014068607522074072032a459407500107200460310341c141c5110109124801300d20400084802c25501c2200340c1c2d0a0400455852a0203030a02100c269206890004241140c0042009207420000001c40b150f1178642070810300c00c0911014442d4020450822030b100d546400781d03038440300c21900f404040100d441e08070202580e503000504200c940108110700800c2005030b283c180c810010b0000ba100907040e203801e09881036251030381e0b00880e401c44a501560b0003600411a003200c0100041542c0b0303221045c501804184d2240500060780707410a020a1640501501c2c0c05022200b800c14260f60441c0c0100b5a00c142184540d40e00319000000038500611982c003440d0100201c0c0c03000c0c081814000d41114040d04030300d644400c424130344840001d28034051f00480d040002d045180030748603803035070302040b0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 22143558 1250 22142308 22142327
    0x1a0316050a051306030f060e0c04030605091002030403020105041103030c07090c02030405040509010902040b0306070503070f1704030903050f031806070203030708040306020d0605101704020118060c05010c020c0d03 94
    0xb400418408004034110314684540900045c1c1c1e000260800003024610035652164490a4170500701014410702047c0c40e421102502d80166000c605a102c0d92074040c035281c0c1c80080c2c2000b0741e1010050004065041d00801d02940c000c54229450185a0701056180d1083c5807e8503010b9014407820031010340681c01c807550900540c010349003070565901c003080c250f903012104003103da55250541d4045240c50b00c1607044250040e0300034009441c1080014019100142c0183c05000110005030301c401c4c81480000e80b801c25510904000e402c1500e0050310b0704145001c200c46c103020300c294400c0301284c000291848110380e21680c2890616010600a965000b0441660075000400a140103c0c0400c4000d000840c0729a0006a552100e0041407048074141c1d0042c500c41c55080e0f582482080d441506428902c0a41d11400d045449620045c0d0b80541c0314009000c400c5405940010300d00d401004083d1101e004000038048410260422038035204000303d8190301412854003000820301c52120310 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 22144808 1250 22143558 22143577
    0x18030703030e07080a06050105040507090b030a050a02040f090f140907030311010f0e030a020708030405010e0f04061a0d060f0e07050310080105010f06030b01020105060f06090301091b1a031605 85
    0x11450f2a482c1c2929a0525452660546079a07807142e00402c0941490300c5140c1e403190b603600e001040c2d03d040c843c0c05611844041d116481e0b05407141c0120f0341200d01a03044034014800204484003060741c400300000a8403056120f401c10070b20b05040b801c544000c480c441803169050601504050303065590a4445130200c0341078071050740d6500c04030403040b1101e1048a07101c041c014025600d03079400c0c4100903e4143c154000c492150400e0004210b1640c00048411a20204440d00200e0208007404900100b07030070f0740030500c520400941008004840c20041c0030700d440030003040c404d00e07807108454070302d00c806442056080224000055802480349000c1d507040745109a00b000e44039503440045003918400c0e040892010603031f1008000c82070309841075100c620001c3c0003d200c01e24108000980e001c0040481d140100400030740c910040e9400c1d80110010b951014103854413400544400c1b40101142c09154040f100240c5030341c145c024400140d038816882e030581d203110410399540844942c2c1150840 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 22146058 1250 22144808 22144813
    0x11706060d1d01090f0506010807030506061c0609030f09080a1e030216080309010801060206090d030b01050409181202060903090d111804060f0204060e0f0118080c030618030703030e 80
    0x3075402c480030b0141c05032540c05242480c1c4804a40e042071401c0c8a41a40b0040c0d00f80e2000c5c0c8100001030000c0b4071141d01c00d00450300c245004000b418440044010640007d014918003000030f403c0580042d540550f02070540c1c2c4000c140c1da00d50440e540d44e11030440010b007a50781c45c80b0702c140f4501c010054407849030b40b00344107841c6c607030400d840d261024140a1b00800303020b4201041c0d1b00800d50344081d03a140100007510041441e070600c10001c40d01ca440d4001352608042d155020303840c1d40e034001c10803500100f6401108005036820b2706019040450f00b0202280c2c0d0180541c05110038a100013016401441102c0203186800c11040400410524000044a007240080014041d50381d40318031700750064420700314104180c41c0914050044451020b201000c0501c11300090000d9580541d000080343e0041d10120240b094100040e500c200d00c80410b8440700f0002c00c00814807039004680300c8410803041e4100c89803611101410040e0000e18105000141d0060040c0c2010900c41c0d08050007090b80d034403d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 22147308 1250 22146058 22146101
    0x4030c0209010f05090c18010e04060f0602010603060e0312150d0b040506100602010612030c050312010b0d0b03070506180103060509090a050c03030f03011503020d0f0902011706060d 80
    0x1c110280400d074414107032803900d86410801c90400c2611103500c504424030b018504887c19040c844030400c0c0341c00d1f40303042100184003004151902d900100203028080301e82c0060603a1540024042c0240307000c04c544413070900313054006c03503070f000010303030b050944c285030300341015654001c202051341a9010500c3d4003913520564040454040150940602d01400c058005860f0601100d03c4601ba513034024001c40e031622408210b481d01c00306103624000c3d89898a28001c011604119195009801200b4020030342c0400000342c1517004001408804513500051014031454400c054a5480500c60a900600100820035070300d60701030611700845405040029040791244041195000101e5101d18164003c92204003484810071460046d91380460003140362009010780c1222500061041d01950341040b12040403150098040e500101e504800801812460321048405410700d900b080e4041b4819450345260b842c01c074448a8401c1c0000380c02d032803a203544280c00d0001444104514584140c40b203c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 22148558 1250 22147308 22147313
    0xf0306030602040320100f03020a0e091005030d09050a0b0901020a05060a06090f0209030d110a050d02030703030507030c02150a111201080c100e1908061e060105041d04030c 76
    0x10140010350b0080450514117008545894a0b20101840d098821507000c0311701c1d850158003600c0000c0c40d05a5250240e00e03a403d01c107060395800990b2410381d41c0891000100201111405075000846400718211102c82c41d0191003940c080c004d500819802244815042c4800301000c001025800018411a103091003951912410130030103a4900703140503100c840030803150711240942d204007181590110310709441d000000e595980d40c40b0054080c080800c8501140c07020034080c108c11550440c0c141c03080c00301c050342c0007500c3c0d070b0103000e085010034902004551424031030b03c92080d402d4141d0700140300549a0119910034107400900441002c6e1701e61410304000302c40c21000c0c01007000030342000a06941450122403c001042c0d0040c2e01400d008017200d031102d40c1c45005c104000005450682179141c2e81040c04081181540102809104a03410300c1907802420442001c0b121040046981a8640d08011070b00d0740300724807558091200c0628a401c8a0b4000c0704100d4106109042c048052003465 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 22149808 1250 22148558 22148561
    0x108130b070e01030b06042106020c070b03061c020310050901110d091103010b01120507050403080a050a080f09030708091306030c0915120b060301110c0a0311070608070f03060306 79
    0x719826400180c94a0600500756058016508041c1040b1581810a418508403500500040e030f00c0b065420710200444091141690448d45c8148080003070307410b0161594416081d650003581e14600a114004018500c00e04402c0321102940d1300038068111882107002c8000946809030283c040355680e2040c030b1a0304c5c5115002460200724070800800d4440e0f00d82024100b400107810072601030b9050000d900c1c03140c0c3e4004291700d990f07444420300207169119050225002e006540008290342400596405565048809010400596603494500396603400c4001c1c120a03040c0c4464006030b10501219001901d100041c20207120080c154039598850850b004e001e0340c0081d482640e284028444c140040d42040c003400e045900108801c0c8151031401c803070100d03285294017000d07145000d01380101c0c2081d9401c0d00700c0c908081400203c3c81e00c03118928546901c0b0b0552003400c8001c5201710011000354600400da22007120707859200d851180e903644105480c1140e44d4140581010f603241000300c0051001d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 22151058 1250 22149808 22149811
    0x11511160602060903090f06160b0408030109050a0c08060402070204320c07020307090903031d0f0c03010506060403030e030f0a060c0905010e0d03030f1e0c020c010503040b01050108130b 82
    0x1100c04012090700c0c10300301030308044014144980c1034208102d0000c960301c416202c444c035440280e0f60580c8e110003100b0094408031580394011301c50708a4801380010300010b0390145069507052041000281c4070030340001c2c21500e1040b50a00072508490000780f9602e03065024040072070001c3e20100d43d1141c4003091840100b502c00c0194544032141d9201c48400700380e0000640d00c40e02d50000a40350800540009540c0d40444c4a8500981d8a036420746e401c061003504580e1801516104051001c2145842240c0324400c92104140d071b407046545044c16441c050103203e00030b9070044d0101d8a02402d584040391038080350100c040d090700c20f8828511501c6420400e10715100c0c01890001001c0144840c014000c1100d5400ba9040140c042001405035031464494012281e06040009100604da011000070b803c030102c420308a4002044045440ca18540011703015a01d59826030708504401e9006543da40400d80d809000300c44000014449035014040264208403101210020981d80e565440145c560 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 22152308 1250 22151058 22151083
    0x7050901030f0302011508070b130e040614100302060f090105040b0703020705190305030d05060111070602030408010c110a0b06150d0b0306070341010b041403011103011511 76
    0x1c02104002415070a1195204401101300004112850300f00ea148d6214554020900c807140e00081000260f04c807007499900802078418003410350305c0d241c02d0000040800f14506003050821400203050701002e001c0c401c064a60040046050201003030010100e074100d20030407814850100404a60b008454000d1b00c90244664010810b01d400c0000380204507c256048014504603204240000b50010054501860345000c0008540d0b90740001222001605410054070f8014054042401540403004106490104e4028803040d0700d1450700b1500c24941d022000d500ba00705104080019028020098100b0801029035010340041034a0b006240c2c41382c80e54107241569075100c0d04140c2000e02c14903610401c1810108640c41e44880a8544464820608800544c2260100d2050b10820b0703810601803402ca412035542e9a141d000c04102903000d0300400744070203207406e01043c0f14039050289299087d001e070812401c5901e8030264a031025031300d1441b0000d01c0344080032200b145c6410041c4410506 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 22153558 1250 22152308 22152323
    0x1020a03031a061b0c060316030e0c090c0a0305010e010305030702010c03090b0f040806090a030e100c06110903100911100324050118081513060501080601150f0804060e0705090103 79
    0x4a14413015243c80c0351020001d024a00500400c803114a1951218015080e90f04000c80e0190314006d0705401c1140c5a04101e1703000c40740e00c06000e0040c1c1200d014003c03500c050b031410040c598841c0d00840c1c0500007448000d045a104000807801540308030416004503100b420a54485a1159801d0810742c1000c241c094041101040801107101c0421a6540060905025022000303140d140200080d60012025028540b11811070314640c1c4640100b8400d603802401c1000b4980210f03601c0380c00c90307000e002c200d07100384600e8140c2d0a146003188a604241a0302c14024405504924140400c40b8242c0031a9020303d030382c40d004c040c03034110909030b841d04200300810415002403d2900161041070a40a40c5060002c594020f104207480054914412000655001040e07550501301d510888091315000b04a5418000002000c10380010954141c80051483c03101c138490f046002c0b24901c004007500d40028403030b031011401161103907012035855402c1000751981c51f61a074003c40c00403070f000e0780201e0305017 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 22154808 1250 22153558 22153597
    0xc16180609090c051504090e0c10031e0509070506030c030405010c02070810110405120604020a060e0906040902030f0f07061403190f06090903020a0b0109050603071401050706050c12010803030601020a03031a06 92
    0xd18044c1008840c4016a040c2000183c80d4048411840a0410b0653300302d1943e0f4408120300c104100808401071500400d015668604100c00c0c00311a00151801c0b170307441d820300114080781d82c0045103000940d2b50b10002800d020750b9203590340001c1d01e5074803182d81d601041000042040c1d2100481030122807408001080b81c0d01b420320510141c1025644044200150030000c01e10580e50562860b030419005c80c1e011504190078000a0f05200e065000c041041c0f04001c094a2035881c08500e0008507541d6458102c00c207044041c4081c20ba2008030385486034641c40c2c00c0d40074964a100d43c8054003900a64000141b0b150700c60040d1340840300c070101c040e400350b0b120808000800483d102c1e29400740c54000c4080c003c071f0901d0004a5580d00d442c0c0504035001800d105249000c0c3d01c12410b441c40c1c603800010a001e281001030481000b58044103070014806070f040004191a0800001c907405240c06074000e01600000d0b0700d00b240105400302c3c5081405a903031a1404069079040041c120301d224103107045026 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 22156058 1250 22154808 22154833
    0x604110a030b2a04050307060c051005040c030b0105031605090910020a030b0f040b01020705061c02030708090d11061609170303010602070f050102030703050c16180609090c051504090e 81
    0x1804040c804095240f8800c100a101d2624045124011500107040c803031440d404515196041030304100d0301c810705a182c08200001d020b094a01e0f42e044a008405885090b6201c030141500c8082c41003000c0c144d0580c1007010411420842c00181d8400c460301c060b076160b0360032406100141e030300c030b034400500090701ca02c0308065a180644148405403402c80e410412100118000703034a600151046510800c2e000c034081d84900c401c19a011507807440031000315921320305804060070070b07001a10111414410840094026801aa1400120003100004040c1580c81d40e610707100c134a50340c000090410007030901c0051040381350079260b16440d903500b015545a40c144040246404690307440180842d4000740c0400c000c1e43c01000300c81c8140d4140c83c0280e5600094007007a03203009080e14505024074409000001c0201e13030760384040e000c0742d2b60036800c0c0056540c641031102565a4158003501000e04514100141d00c1d200603101a0210b200d0702c21810581d841c0c41c400e08850340f40c544030005404c15400d4010 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 22157308 1250 22156058 22156111
    0x1505091f020d020c031c140c0703110409051506030312011211010503040c05060d02091009060305090706090e0402040b030601060f090f150e0301020405030d120c02010507020604110a030b 82
    0xe034400e0740d200900d080710310100080d0340c444d0130b00034440c100e0204101c6d48030b1440c03041c00e0b102070800d55000c09035034510342d00019a503100e684d0310060700d58a5062070308050305e00c4c041c050301c041c198000005111000702161001001040645425414402084603600b092a441c1c01e00c0d00926110310142c4021149007000c1054488106101e410072004204000000b00500401400d6a9041d961140c60b00b090000c1c1800074031404110a510080928042411503070018005042d954075a5041c071803525080e0001ba90340d259400b070003000c25500031040c01f03c1002845515445800180042400c40305600030038103062080e0003400000c1c0800c18400750b50794000090800920401c000c83d10301e80c0ca0150603800c10b504d03d8000c0d03402c005407140c0030990307070b07a00b5010b440162000805854101c8178440300a00042d0170400e0008401c1e0a0072101e8440da070040c459948031b00465009407040c1e81da60350310f601ca8007a59031800355003d46032076004800f0809071240c00e8400c2d14080070340d082442820340f00f5003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 22158558 1250 22157308 22157323
    0x603050619020a080f070c0605040501050a1506090902030c040536010e040311010f021801110a0201090623040b0d0e0c01050912010e030310030c090203040b011505091f02 75
    0x21034682c01003001c90a50703030f070081c1810361010b050400a4400d0f1030710715003207600801012000c1c19050400040c44148038043d84446c1c010186200204490300c01c4483c008000d42e194480c2c507010556094081015400a400850784000f00808141c6441d454000181440469401c090606030407940810350310f60a11500c82c107503032941c0441021641c500000040c640c00020001010840803994000044009410090300750160309030654072602048849040f007121914443e0020301d18000c0c0c0c84d1005c1022440141141c0c040e035a5040c030605240f02a540000041640c6a043d1602c0c0007100c6000d000d840600042d085000e18156104076078000403054450404400c005900181407201190703030004115100c014058803241e40b80c0580080b05401001000c0d41d41c10640400000c000b112380768424403a0aa030712031064241c0d280e444203600c8080b800110f400604081c0104014000d480075050000510440d07898070514200601000c42c5042d80001e460524803842c10b0140c10300c540c1c05009c01c2c1d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 22159808 1250 22158558 22158601
    0xd0203030f0a0509060402220c21090b06010318061104030312020a080a0c0909050108030a02061609030201031a100804060605120c04020d150f080706080105030a0b06031006030506 79
    0x14403090130900e0107903880d01d02c050030003031158410780a001e007030b5000c003c03920780120071061302005840f80129006d1300750141102120501b6001c424503020031500b40c0320f0002c0041e0401503e07012551780381d00560040a4009100c08801c001c0d403030000001e2003900ac1c0e004080d5001d016584c6491446c41d020f40450109005100c4250062041070380e1a54404c4c40030740e01a800c0700d40032a40c0703040700f682600d04800a82000e3f038901d05040000c07030445000801403601d41c2d00707582103800c16606c208a501400302d610080c100000c03030b200d00810140d071082d044035880c1d9031009003d0401001020001c1c0c070b0110b28140c14804500114108002c3c408540f02c0d40c002401e0985000480741180c900700c6403201050040079106a501054480942400c1e43c440e0010240400c00c03440031903100d4641022944a40c81010300381d104101c00424458442c400340381c100c450190040c02c44070200d590743d54014100404403038140c8110922074a0f03940032405000011400707840640f41c2c038200124000060400031070300 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 22161058 1250 22159808 22159811
    0xa180b03010c1106040f06061214120301080d08070203130e04030e0303190c080408010914011503080909041a0a02040603060503030301051c0f05011a04051e0115050403050d0203030f0a 81
    0x74540318100c0440c0c6130358007a9100305145500703002868281700402039a000140c0143e4081c1c0d0304000c0006000f016402c0d0310b410001c907441000c0d25803600d01c05100900902440350800480118182e00a41c0c00c85d403c0801c50043ea03040c404198038000300d032001540501d0f01c401c0c08800b80028035402143e800107603042034018601d8842e98103003822a11030700c02121020041190300c40000e000c0e0020a5802601d6a1030003404428424102002110603016a4071100d51901c07100e1450001c071205640d0450b580710503200e092484010030840b16640c010400e507503000c05150051002e512006940344219205078006884609264000301269200e030001406540200014400e65845010381c8060041c0c55583c100c40c01090f24044a40c8142e04d24000c1c40c0f9800c1031082d02a20641c140c0d0184800e0b000c2d601040284d9072006909d060b8500e0608101c412041100103105250411001c129030804605095140550b280c0d1950310703103140c2190240040c1c00200078801c610070341180154120748803000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 22162308 1250 22161058 22161077
    0x712060608060d021207120209010801180f11090702030c010606030203060303090d050a0b0403080f06010201020909070f090b03040602070309050a08070603020a0e040e06090c030114060f0a180b03010c 88
    0x401400714600a002148628800c441c100f04650799008606540d0500f00d00b9665200c0d41d0b01c1c00310708080c841c68000c920910182c0c0011900d2441440b404401c8007404449803c0b401041d1141b1004c0c01c9140c2043e207510203000200300403502c40a411602945080c1d008564881d501007202d03007100c2142e0402c42c1014010010b00840341d800000703480c040d820844001c2100c0d2040e00d01149001e5803900001c00f4100700c2010002130582041801d441503503a095001240d40c1c035040124200d210304208158410009000320f0040c500c120f80c815011102410b022269684071041080e141e0400c903000c44410350009885010154008580001130000b0788080400758104070301d4944840d03031130042008155010880320031051181d484250030341c5000d0402c200410440e001561036000443e100e8615104007101c0950504051180d0140142411308030220350f01c8420030404500c0c03144003803aa001620200c003241104091070306501c504401980000c03030052107002e150950f9160301c207000c1400450030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 22163558 1250 22162308 22162319
    0x70b0108060a06140906010201090c15021204032012011e140105030a030507060f05010303020a050601050f061206060403060507172a030a0e07170105060604030812070203070218071206 81
    0x403803038403501044483d103661b603450a004038018001c4800c0900801c00380000040c9044028480014500b40c41c2d0aa81324502a6080c0118500c954400202a40d4280600040000e010444004001401080301c4080c0740315285840c00d40300358200842011502003090b0141e040141321b068074038010031100034025854400000e03202c5c60030707010180a00c000050300354200034082d444040b9150204804100d51358490400075a41d2448010454440c4512400880d8600d00113040d50a03043c80207104a10f001c0f44802001003d03c07001d0400c94205100b84001700004205000703042c42107405036142d8080c42c0186030b103000c0b41400034103000340306a0b4003044029450840c0340c040c0c0c542c410300e0319025602d49031011680001c010100a000440c010920041440c40408865910b9080309030000d1007142c94203820071507a44154400100340301c2c0b040202c020503014981c2d038103a005502d030056030304046094000c03c0414101d0440b0642103a484810004143e820100b195800d0042c148100710b41030a11 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 22164808 1250 22163558 22163579
    0xe0103080702090a0603050a0b0105010f02070e01090c02150103080c0714060a03020a022d07060e0a0e06010212210109020306100806130218030d0203070b0a020313050102070b0108060a06 82
    0x11000a401243c440c4009800300903160800001158450212180720f006400c011261040c280284c5000807000301c03030b4451040c40040e5801c1560030f1004c1c042c1d03c603468985000010800b00c01d0070015070196600c4910a070ba24950128000c50241d006a50780310103c0b1b11040c2010102d410100c51003114035545005526070006a0b0111340c5503040c01a56011483c405030300d001c1c1054038501c0411107400041210744d843c1e40305581c084d100e42046131500e030f032175840c00d9843c4164100311130b80240e90600e007041003944500009800803810300640d41855416108400c159002404180c0a10040b090036007814216400250060590a10031425800c1c0303040016041480b4142e4401008111030104401d96514448016100c0400710110758941940100c1c0310b814400d14100b81c420301070180e40141d1280003008440000d1b502400121186d941c032503040300290000340c090315500d02134075100b400040e003d1006242184c00344484a00641c5002c20700d916041c03000340019621410940c0411001004 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 22166058 1250 22164808 22164817
    0x305150709050607020402040909050d0206070309020105070f170a030903090e0103020d0f060b10110d0c0206040e07020c0a06050309010f0b060d0506040207060212071b080906070c030204050901150e010308 90
    0xc403109561003100b4000a00a40282d4000503450b9281c41420010403800242c1c04002e6030294003a81ced40d07a602c1c040e050301100d24084019011400821845000820444095082d18850b20800320a0b0326854800192a08003034484008650799800c42801d054002450200500102c2c1c90761f00590306641c00b0401402d54498014203451f1980400c0341004143d0300880446040030b0702c40310341c2030071149000b000101120444441401503144924980b8840d40e10110010b401504682c40c0501e004d17001e409c4044001e1051702140108088410191f42d0049890000c00c001d03a103140c4c8a050159100d4211500140700c000810719218a600c0251100400c0c0c44510b151822300151655806000c42e000e40728143c8010000c52000614010f500c2101c5a490700a900d15501e9000c000144a07900010060400c0d0241000c00140110003c91801e0341c020400c207446400c02d1084940e03690b02207415200300f0307034040c80f450b512600854052070038102d580c0300030303c0b000400e55134951441d29821020300c80e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 22167308 1250 22166058 22166069
    0x7180b0301180207030e0910030c090204030b0414010e0304030803040515090c1c0c030804180b01090e06060d05040606140f06030109050720011407080601090501050c100212010305150709 82
    0x100070503820241743c0a01596030700040050020315031031410008040301c10309140000c41e081450841c021440c501c8074821760301a0f0341e1100c5101c4c41a01e448d103c0c142440b4040c41080c65541d260028007031300050130b202500080d8842e03100c00f44c07203003014075041e406c00544282501c0401000c9040159003803000442410b25a416912140001e40e2342c0100c0b003002d02c00000c09041d80000300e4000042010f600e000300121150241048060649011300320251601010054001070902000303002d0600104901600810028526880d140b40406000c0c00c1e101c00311003c4d145107941f03410800c41d4000c1221034880000084591240d500f0002000403183c1c0418000c2c401220b64940006100310f0052006801000904282801315002e0034602e41c0a04a2106483e0017000b00001107001c0900071046107000f420142c50b01e40300c4070b050900440c1c59402448082c140d038030803854200d0300c141685c4001d1001002202d40c40e8440d60450600c14500041c030980d00f45540511030400c9002a84208048282c1c0d0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 22168558 1250 22167308 22167311
    0x70810030210030b0402190e0604060c06050c0702120105040606050a050a0b0309010603020d06020a14030105090a05090313030b06030c0306070801090b1f0806010e061606020d021207180b030118 85
    0x1d040d0b0b00300318010700b400160b441e002072000800140503040c0035500f100071455592248a0048801c050018500a600c21800401c811140c03900016440b50080350384601900f1405081600e0307600000d1009003c0442148903954480c02c2c082406040e0080700d01520007640c00a25140c03900003ca403d41d9090710581c85207186c00300100d444180d0a4000a0096800030440d2005820605107003009611509449020405034907514091403140416070303040341c2004044c0940c1c1d84d51703410060040c0c00014003010482c00304101d54840d840c03049040102071400390307481c1902c518002003410315003150600014426440802008041e80d40241c2c400d0650785000030200f184006107010540e558140c1c00ba002c0d914110715501300c0c085500010640c4599070998502003070104c40005d2200c9446100304042000941d1404a0080340494000b015982070107580145003207250000c4082002c0140c42d0740d070025840c83e20314580303060f030040400e014111003420b05103154503241a840220644802d20903c2030f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 22169808 1250 22168558 22168579
    0x90c0303070221030a0504090b150a080403090302090a0b0111010b1c11040524010c020105030a0c0c0210020a120206090d080a0906060f051201050c0d051305030711090708100302 78
    0xf140310080c0e0b803c4440f010740c102e94035541c04010103045a0002d000e00000c2c645007070002d003458034242100c448511240091035180c580c071100101e0f10440c000340700ba410700c5040c03100000162a4081c0c018800d1982e2240003d440c200c40000520103440714461400503814008110680c2e551801d168582d66412240c48002d04902e15042d108041070a140f250700519010402400c58600d002c0d036038060600075410741c14907452074015100248a481c1c0030b400145e0900c00620849119481250301200d5400c00124607041c550003c1d1070700d0307c101600c40043e0062440a400c000000840764081149800034200d245059556199900c0c82c640000040000e00c401140b03220304144d001400e00e41e0400002c1c004107490301c40c001a011024451240076516103007420a02d0399041c4a1140504a400c0d0300360720306a40001400c000e40005030100c2d2903c1040843c4000041c400c100070700110380700b05c0300105810091400c10841740001001801884059420460700e00c22403820781044d00c1e8100e42c50b034540d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 22171058 1250 22169808 22169839
    0x30f0d0e0f01020c010204050a0501020303280b0a0f030314040b0306010507140a050106030203060a0c090905040203031b0a0209370b0a08060603060703020c060c0c011104061106090c03030702 84
    0x4114000c1c807520036a5100113031403144224103400602c15950706aa0800c0ba4980d66401240c3c1c1c5d110840b0340245604c1103250440c03845d03040b00850b01d002541d031000411000c0351080060100d0303a45900c5822060078403c800c204164000d02d5503401d12400c903c442e81454901000304e4542d20000b0582410000000380b032008000c50325040f62400010081220290b031003919040c1d000b4140c5e0b0000f039120b07120f2100002d140b0705880c041c91518400a660300c012140c5404485009804003620481e81408103101540c03507045640440005540319000800c81c00e10640140413120101403c18860050603140b400340c201415804940c59507004205d04a00091003801e031001040e86554059104c21290720001e01c0840c005059405180100c1c165030310b907100ca01c02603003207100794540052240c001000140704c00300003001400c1e20101d0000045000000440045460350094100c00041517203000100400c02c0104a05544485140d005282250007800000d031741c0d00603a103000740700c2c09802524848 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 22172308 1250 22171058 22171063
    0xe07180b03010f0603060203150907020705010e030f01020a0f0e0105190e01030f0213060201050c0c060105090c0403080a1214011818050607080712050601080703050c13030606080c03030f0d0e 84
    0x14800290f480400865403070b4a4244040d6006480d1f44a400001101a00030781c076182c030340d65014500303a4008040061a003c015100900d42000031036250003191500b1500c1c00d020b00003014690403a0f42c2d80b0b076044069440180c11451000c0c9440c0c1041002d0040c06448204103e0001041e0b0322405e02c550401403000c012400750240c145e40030140b50000c17600741c101504402c012803c0d51010740090100ea910906000c0160140c40003000340c682c4000c00410071403c10583c46a0040c10b56803142c1d14150303e0307481c1c811080e03001c5201140040c91090448003044541c2c4a4004010b500308124800c81d4540a4100ba0340303020412480b1506035200d49048105941c1d001954615502c20203070b03a910301d001503000d81800011a000004a0f0144181400880c240d00c9158071603031050311810300c9622100d4040300141001802010301c6081044019843c41401d18241c000303503c2140f003c030302c2c03c0c1400e82c03050802d090070b40c0450080e8400e100c2103040801f08000c2e81d800094146000440351140342c0e81a2 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 22173558 1250 22172308 22172321
    0x303021605070803031501031103040201080712060e0f061002060c0f0d050c0a03140c0a0507020117040521040b04090b06040e070903050d09050907030f0e070807090e07180b0301 78
    0x405a1007860b000094041020015600c16080351003d005032182000c0154191a01640b512180c10f00c02c00c005030040d030160284070b80003005840d00940b40348030012500704540702d640160f540c0541510400c505c200704502031035404401070b1100b040701c5500010113507440c0005450366a45040205250003920804400d68440f14174604090105041a42c00500c0991000381080002801c002c0005113112240042a000e148010351091070035240c003031f08940c20340000c20704030b04004440421001ca00c070702c0350079680114001d0000e403501000c02c0c501a00251034417007076401100d10a20041164420030410b0382c0c1100c5000b54042404400351001903114403450b00108030b13120b080d00a0000d001d602203031a00550340705004a4400c1c00f4050310031740e00d1040314440c89902c480054005030a0380d11079007000d40c8041c11400e01003902ca02074185103003408042d411281d400d51010381c0c20400740e240d0780101f071402003117803002d001ea60b810003141c1c44d074807400c4180d500322040e01c600003501c4941b030075032010 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 22174808 1250 22173558 22173563
    0x150b0f0303180a090606020a060207020114030411120c01020d080603010207060c0c050c0a0515090f1003091115070201050708120a0207030f020601060509040906020f121b07080703030216 82
    0x1039550b00200030752200b0700141c90518600428a4810204044446201e2001640d645070001c250640c0c4941d9200041d5010020490400c8a0b04a40c00100082080074500540c070620307055000084070b6017030020302100c40d44400400e0780b046800c12402d0760003007602d0302c1008903440d01500303d90b91040400c0c06031040b035074014041e0385481075001059500000542109209405440c028004103040104240c0c250081039840070b49460744652104010004000c2c044020f06605540d444081c0005c4428540d00c1d440d0002c65110300000302040010130f42c0c030700301d0700007251002c8801d80c409400720740c240641e0030020b041c0702000400070148082c0400352803401402d650080e0b5030b03180c040001d102070740005e00101c01040d5010803035403030031707002141c8541610348507075940d41000035090407c4080e061600d8240c0e815a4200b02d800303402c0300800002c2c00710701420100a0900d00b40b042d21604182c418000078041c00c001030040f035000a002e41c003107036401905490b01586405d514020f6008848035003000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 22176058 1250 22174808 22174813
    0x60703020c10090f0b030903090d0609140619020705060c09010c0c081507030209031b0103110304110a080312040b040c05120106060801050a080a08130506070b01080c0607150b0f03 79
    0x44002d850360010a840540d00824204000e0960340e0329180c90038003013a1944400c603001440290480c0c00c2c01001c08543d24025600032030f40301202d4580c031520551900503010107070011000c00402c0108045003240b081074010b021480c1101c00e45503076444a0014004000300c8400180c83c036000c1c1c2c4a003000300240e03500801c191024a41e00c64a20340d41d05180e00c9082c3c20040a0700001d910240a071003a960350b640d0250140035040d001d00c40a002410f01782d80030390305241c0e588161800c40e622100246114070311568903958407000ca8010042002080c1d804010540d01c1080800d071842503c00d10b42c0d411a61050405109403110b02c0d003c1413401040e0003072a00195408620361117104e05410040c22260303240c499a226076200c3e000d00540303992030f0103417000380d82c00b0340420300020300c0040007480c480103001c0c2142502c0d0b031108001358155000d02c0007035594900c1c500040c058104103011b403407403448040311428a41105039032041517a82032185000355140d615070300d0502584884407140c5501c20300809 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 22177308 1250 22176058 22176079
    0x3190209090903040801050a061211031e0640050c0409030206250c0b0a0e01092109030309140307080105070201020711090615030c09060a0c020102010c080c0405060703020c 76
    0xe10b250749030003902c40d00155600709004142100c08078440c010680f0301d2000343c102146600d4503090250041030000303d405109900740510164141c040c7c80000624040c003426035824814006e0355031700750300c101e2444440003160034403610401c500049818504582c0140c00480354a0070400e0030b0241040200e030300203081864160815a02081c218410050048500c0c0010b6186002c400320828078101480459082c2c40d00da00452410280203900204007040460280707c06481c460a450004c80200d031010340c900007100c0c07541d000500200c2c03008114074000394490300c0c42d14000c001804a12400c101e00c004260140300c0c1d5203003880080c0142c00d40030000e000d2400c2c8410300a0007503200541c265242ca403082042001803421a00d624010038005040420f610454500103105034405044015180b03400c014070141030b1108006011004000c3e212804c0b20381c2c1900000e405d45d00480781000400140e0801c1010b0340b041c0b401502c06683c0c01b95400c503291009854180d28108998405690052aa50 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 22178558 1250 22177308 22177321
    0x30c05030403060507031a0108010b0c0c030d1808120d090623100605031302011b0c0807090501080d0f0807050f04030803040210050f07170403020909010606030506030705060319020909 81
    0x800044c010038a940e010013841e011f041d070302c90480f0342140c565400102414010000154004040c00301c00c0d12800c03e9418000305000002c0c0b410a9a281030400b04000700049801d50004000c40401811134401a141040812411000c0c81c401c0949804850b5628410501440002c0e488900078010080e1010703071501c2c013150642c140315400c417070b00d10380ca004144011498034400c41c10380b4013601200340e80c1001d9201641c0159034501e0a181e04010001050042c000400c4201c08508000c0202c00007808c0514104080c60f4103843e0140c01c038006a40c401c011042d003035980185090384050740d40c07605115640311000c08a03164802c6080041126801180110a01c000f12004600461088484240c61f1805450681d030b1800351003003000280350309118110100b8080c41c3e4140300403161603289840c2c65120b5000820030003044d9055007180e0343d104420300c541500741c41401d4103c4400c90040130728a1a140c0000c0c2d0b9403000521400c0f482824038220030004900381c060302c10000000307010031014500744 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 22179808 1250 22178558 22178561
    0x907050403050d0e03010b0105040302010206010b0705010902030307031107090509061303020f030f12010509041707022202030901050108031c0f0617030a14180f010c05010203070c030206090706020316030c0503040306 95
    0x61604505c02e51038145544610f40c02541101d080f0795068000d000b081e0b01c0c107050b00445403c001c40507282035403102001401030790140b00504045110f51240c40404c2160100380e440d107040e0b60882e0440918080c244100d00c1000225142e001d503012080604003403031460102d080917040d907081012844046803400c034060f014406826104203540c0c240030540e9840c1c0800400c00000e0f11f0142803100c200402c04002c0c0c035400d00030315030035002034450701c0f42c0365a0300390c540c14048403822410040b50f0b010013400600c290038046c903401400680011401c00b40b11030034140d50780d0013804011405030303074a2a03502e450020076003104000303092031015004149035003400c00b82c4a86c49038074403500250344910904c041c60712180035120036101441c102007030040c114041c021083c90312508681440140c8005a0001e00d09000640c4160380c584d5840c0712502044c0750103031410360042c01c0b10426030455001441010b40c00016110fa50755607a4450b041d600b020b007410344400740500400707046804002070100902c1100d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 22181058 1250 22179808 22179827
    0x3050603070b0904050601270512030301060503040f08130f150201060305030f090103110d1b03050103030f0f0507060905100b15070b06240301050a0801020c060f181009021017060907050403050d 85
    0x5554ad66a0034549041c4140c9902c024064030300820000d001050128204186031004107204d190100d25201c95901854450100343c2c0c000e00c40041c003002e041c000141800710081050700d450000344007244c02d551300d561f1240514840c1283c9290b0200310807040360701c603801c090034a0500b101540d070340d05e10301800f0401030462025000c0b4007031241c64001126034420301c110750489030155030b10480d05a0b40c100803a001d40341e0703c001800f0030006000c0c0901081041c4504c2c158103115100910800d00c1011212080d01c081c1c0340138611449600d40c00d08076000403070040b503c1725a84107100d00d0843d40c0c1c40c000101c44807480c4059295407400d000340000c8161400d001141a0b40d0b0171112240744640e51041e00303090744204d0b240001160025000b00360810010044a504011609886681c960255030442c0c0f038405c08000d194111a158842241507040500c5902009900382c075102028142503400d0000c000c1015010a000d03180190002d20294458003e580146901c181582d0161000c088001c02c4140e2 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 22182308 1250 22181058 22181069
    0x1020c0105090706051903060510020a05070506090a0e0402030a05100204080721060c120c02061e0105100f020309060304050a02010207080715050708040f0807030303050603070b090405060127 84
    0x180c4400b260866400090020803542e42c2e6517131610788040b51988545451100455a0038551546000300700d60360344280070404400941e0090030b002c2c41d5410071915148841d40918010502000a03d03413581b908052141030341d0381d0003c0540c1544452000c82d103020034101c0090141d009204400540d5101c607001002140d100c4400c4a620948442880007000511100d85984155040350400043c0194100391000c001d07904100032200004c000510075141c03040300407801604020100004007011459181002c1200d20f1081e0b5030b98104804256a49007604100080c0041c10014118151003007040f50080701c0d0240890381c59040524040c0d80e1601c0150040f07001d80111034000c10500c00020311a41183c6944d50700080840445400352203d0713010b0039054034041c0c801c00001c141d20142e444d220004000b181c00a180552541c24003d0407500054001803107900002c40410200c0001800c3d5628044100c40000342605c80c2e8005032070380c00c4492070510f803000b103146c030803d140491100d44008485 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 22183558 1250 22182308 22182311
    0xc06050c070501020606131805030307030903090801110a1d06070b0405010e0c030c0d0302070f08060106090b07080706020a030b18090d02070e041403120901050406060803070203060a0e0a021201020c01 88
    0x30b0300c850040ea05c1c0c80080b180d4681040030071034881300080300d076084030701c1000c3c43c1d02c0c18a241c201136032229400d5610440b1000003003902c89034103404140d403000c0c1c40d400030b201d030301d00030000b030a08880b8104252143c101d40c0c8003040aa03201001001002004100b40f5440040040755140550301d0110159101101e0a031103035441c3c9000401c140801103142801c0701030044c060309003148420104940522180405d6003180328880c4045641e6510520b110046e0952320000c1c00c035580351440c000c254440c5500000d19010050228900003400c0d5400c0e1115198014409606d80c1c074007140c100c004001082080360300a1146100d088641e4000004900640e40c1c5000d403004030002e40400e036500d02d49841580942d10307611000070041003040b01809002c01040007a02d00c0c005046014a40f482800d44207140503943d1b4030b00384401c0000500c941070050441c01c014609002c00c0d0340001e0b440354001170907000349540714505180c2d440001d00604160070750003400780c2000000200194002c0d000090f4031991507 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 22184808 1250 22183558 22183573
    0x60606020105070e101110091101020307120503150d0606090506060702210319030b010e040c0e010c0618050304140406051c03050d0e030309071401020304030f02030a0c06050c 77
    0x52060103040d21443c0d01e078440030804202c0009121a05c1c038011405420031070390024050300e0010900203006507200d115404240040642400d104401d0484030060566004120780000107141080d821090900c40c14280d4903503803403c070030060980f60038035143d502030007000003242008540d900c08016900420f038100324a658080610540c0c0c42407143c081d41c0507030845036000e5000794010508078140b08660550f400c3c1440c541c4820389018551f0203560109480d18800001541c0c0f0024604c5024000c9906005000103804040e0404030f00b00744842c100012000c0050521015070080740621644028920280c0c0140c00c004d030300c0b908a405900c0c100410450340540b24582030040703100750760300180b00c450a01d18840607902d04420840c4100d09228092203420000d028920416401c00094400703103669103003500010b42010000c0e00400004600c04004c09503d0760300105070385c1529130004084c8502e120310300020f4a0003914a03401400085080301c0801d00c19807000280038000345203c00c940300c4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 22186058 1250 22184808 22184819
    0x61505010201021309020c011404081c021201030605090f07060207050418020102070501050a0e090712051003111201020c0d030207050d0f020c010e0d020405070e0f0307030c0302100203040915030606 87
    0x741d21480140c411407a41e1044c0a00462405600900c2851600800020500c0c0c241091b003140031030031602500c00301d1011440c10070507180300600548002140c0302c11071800d4000c0a003003200b01410300000c0d150036503400018003000400c025054090510004680c0866660b0300c0003992411603001d03c80c066428841000001c2041d540d0307104060f40d058018201c000d0400d4011103180c0c005240d10f00800606848004254039251082c0d0f019020540c0d5880c0c8441c4d0082960054070406880c01d000803032060010130108000e1103c91059242c200c88803182280c0051802d8060b000300c04103c1c08a000e14400c04078003d805900904a440c4504180d034464194504103544a141590b00790300940c006440b4090705611803800b6020048000b0300d001405100ea80116044a00465640010480c81c662801d201e1420561184e40310300210000d011040c150307500c1c2c10708884107100c02401002d82011280c140b074020300541d000340481500c10840900340080d44d900c6000c003480f0030b68820b40343c404013046 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 22187308 1250 22186058 22186061
    0x105120307020a14010903060e0102122a09040b030129030d0f050d0e0318011209110d05070503190314270415090519140a05040f020607061505010201 66
    0x154004004041661410b0031840c1341498486880e4104040c915000c00000c034180b08525018586100040c0c840d40e4050b038085d003404000d44441401c0d6003141c034010103404882c448411441c040750100d41c075000c0e82c01c04203018005582c104c0380d01d9401d0264034003074120815004000c0714400f01c03200c411a8580000c0c5a00c1e1807681c100117001a03402080c21404900be40002c2c00300b21000c06e030006c1d2115151001c81d0954100000c28061000d14102d552059a80070f9040c4480420071502040141300039034070741c401003c1d00c100c0140a401ca00365a141444000d1154500502c0068213844180101506030b040c584550030044010400e10075a128141c0302d40c1c0d080d126110720110852410100c01000101d80000341180030f60301540310076210010305584102d00f0001c0c03041c201d010034a0304050b00e079040925040109090158581011400c1c10801e16038507680144a28000086a0719a070400f030307400e08503011000c1d41020f0300041c9041084a181c0c00310112959465203031446507140e400490 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 22188558 1250 22187308 22187317
    0x1802040f020703170606090a060f020106050a0609060c020d05010501060203030405010c02160b0c0a1707020406051509090c070b180c0103060b0306040c030e0703050c03060f0402011202032d01051203 87
    0x80000340002e14010313108401c0107046400c094000d00c400c4c14440300e007000402030001c0340c00102c005810703210f0a00c0015024007880001d8101110018481ca041c4a0001e007000b445100e013904000410581506542790141c0b41504190800d000380601e6844417070207507407039000342c03400c40b4a50721748400c00501910109a0b82049441040c19030212441c064500859401c4000c165010740100b042c1d20000581170940c03032407020180030005844502da80100021a40c0c20351090b030084a6400e0310854146017a000c444980320116101c1d1103d031540c0c00c1d104117a00801c3c00081c031041020087c800b9000986003800326404151040f680c034007402500460542c0d289114000c072100d0103001241940c03800750803001c0c09041034900001c0840b00d01c50140d00e03284190380191020b400c942044001380c00c0500030a503200200051b111054205507000a184403001102890807a07804408149850f40342c0b400509003100500c03104d940303542c100c050000d846400b0b204181c0b0515002c40c00c40c0c8000008019107 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 22189808 1250 22188558 22188563
    0x4050307032009090105070908060408040501030c0c0803040f060608190312020909130203060f190b060702090403031a04180f1a0a09120c020d0201211802040f0207 72
    0x106800e61840c1e440300050301c421070000c81803000c50544850a900ca2a10103842030454400103d41c60500301c10180681d00c8a4200e008660842c2082102055904041341c040710310a107000140c41c44810f0046440b46190400141700b80e20010900040c04100025804014020002001410350b81c1c1e0b00e0382e80d40c88200100408503a8001c00c14008640204880c91009000c00005860540c0c82000580c2a0a0840b80003071440847d40011003982010060144e2100b440015003c0a04280503d0040e0b416518541014180c0f41ca03903004480d184c1401f92090b541e070240500d01a03040604e0050301900c600c0da1341c5100700030f60424503100c624041c011074800b0350303d0980d038020204079a110140314003036581066a040c580c034655184864050401140b00307030810903001800c4603481c5418598408050040e400700640f0900190150780c40078440080680d0900f040c3ca4500250204100342c072051402c8501034524007914102081c5045034889106c910844003040300c00c028070500070880c060403801 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 22191058 1250 22189808 22189813
    0xc1f0b01021b0f06040611010e240406060b0c01021b0102040b0d0504020402040503060f090c030a020117040302010605041b12020708091201021215010e030703050d030f0204030206041508010605040503 88
    0x140c620300303980100000c04511001c0c00b450f07101880c1d20f0104a0b150b0180c1e1060002030210429100d00f15800c0c4200c010030040d1201070310070404114011468054140107a440084822000c0f8081107015408140100a411400e82d01c0c0d01f43d0184940c000c1d00021900035042e528407600400d010340620880701501d0304486003c1c18864910000740c000d05000b40300705d07045a400c1101254540c0c0c20000c0e07920459102922105903e44116410309201c6607522003800783e07203c2a003600050380c001c203a01071020400075240c210399896080c100e02400c49640151740081ca004819a540720801c0c0c2c02d18a6121240c540c0001c120714020204102d00c955203001e402a242800081c00610b064000e580c4425031420001d030502c4121040305150741c0080c5d8580d0210311441000003038551304000c442070f6100044002d401860310b1525032a803948103519902003050365601079120045000d034190303805180c0282c50180c58545414001c1400466980c812011440f00000003c050703100740100c03010386001501 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 22192308 1250 22191058 22191073
    0xf030f11060a020705010905030d0b120102040b0a03020306010c021806011412040303180c06090306050702060402011409030a080706050a0506030318090c0d050f07091520120c1f0b0102 81
    0x40b20029001010200e0b141c0d521200180040781003000900f213403000c02d0400184004001c02000f0311700e2001c40f4103440e241d0050204203c0c0c4101401514811440760070007580e01d80d101d10048401418481000390f000a00030100e00c2d010b40075548a81c07040354280c03201d050385414200710400c2d900507403800c0d00c184106900081d0001e44260000c2c02c820f80c425100d264a40c174560740700000d580c026004400021034415007081488680c0c011940c0186050028209604007500000d00742507071081000340c8014000303141c02840e2400c1101c0c0601940260040d034503041245058405000150340c50b00165081c031012454130b140100840e80c040c5444446003840712900e00c144111414014442000d42205101d400d40d007020030f002d0b00b84100c801108400161a01d0000038104100c1504209050304e036410300c4003011900204039400c10f02c2da3f10300d05900301c40295202454900c20803140c400041001c00d050650790340000d6003440c011854117194002c3e204c0340d2001d10031502030308103443c0168003040 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 22193558 1250 22192308 22192321
    0x150f0b010810080a0f06061701020d0b01030b0906010309020609031002070204050604060e0a0e031605030c0601060302031b0c070b1308010606021603080d0e1c14070c05010f17040f030f1106 83
    0x3c0e0041c81d114400c0c500407035140d50f96140b011309034445258000e07980c0d40002f03070030114950702d101702280309a09080c20840345a0070740200d224040000e111f241031560300c102c24000e6554280c260b820181d4014115a05008440d1950303010750441302049006a040402103021460b16002d2142680c110403010009503070303000703020806082c2e20032801c900750204101d4800821044010034010350b008000075a6107007d200c90280c0f80100c16800f44080510510600500200e0540814528403080d9000c42e1544030b03401355a824070700700d80c3c0a406180c40008908160b051301003040c4040f0341540008120f0a6038443c4107980311003400c0f01000902070120380510028110101030030f4141d01c00f802c0001c1480004030a1498840d6585040b07441443d180c0c40700030126442880e000c510903072100a10b080441903501c0c0a0129900e00641d410b1252480180f40801d205034026070070080c104202031164140350421285018241700e0682c0080d44510414180398044c0c8014042c1e1580325006203242e64804 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 22194808 1250 22193558 22193573
    0x1110c0f010c080d0c0503040506070809060c09010e0a1e080d051b010b090405011a06130326040332060612070302090c04061e0503040b04150f0b010810080a 69
    0x42504403005074060282e54140e94181c8180700407105952039407562402c10f82845850008022f28000402400c90304010682c4804150301d07402c14021142903480e001c0e0b400058940013008040d080e04211410000185090300b041e94070402000710b00c400c0501e0b078030351003d6a210086a00b41d03001250040002a000c2903110304400e6070031118800000f56590314400142900e10150380c1034816030345419607a010000915414180800100c42441c9444501050340081d603c00c0e00c800f9100140500c0d501c8107804001501510045040b0f503104d5546440703181021610301c101045020240c144051482090000035010100081c048004c000c40da813407004008600392810b1080c20140101000000142c440d0941140039003082d51555880c0e030b04002008001c120315410040e419410102000c06250f00f1004580c1c0250b000b503001c0c401a0b4a85c00c2c0704001c00d0501000e0506546080301105038110994005162074000343c0c0c4d44021621000e22070500300c406405140219041844c2080004018 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 22196058 1250 22194808 22194827
    0x30e030f07140a0b030f2e090f022a07050a05130509031606020c0d0206040b0c160f060203070807050c0709091b0e070206060301090c09020c01060e0901060501110c0f01 74
    0x41501072490f1300d8000440300380d04161000b0044440311018449800c0d602406500e428403a04072480912480c60444142d0500724402c002589903505402503040380c079501254030303041d2144052049124492039140b140121108844514095040702040e285000034400c42120f000402480001015030722541c010203000c0c00e8503071b03548020020a0310794140b4a22890400d40102001031319001210201410712621610501c00c640190040100103141041c015420081040310a902c428080b500070041d035a0710800607041924000c064802c011503500114400c485640e1545c41356101c0340c005980341c0c0120340c030041c4107802c005070a000e210a694000940c080c040d14179112585024014100b40c1402900140c1400001208010003030f60104045074000c00150003c000c0d0303c1190701d4540b18111280101d0b5a1141c0010303800040410035000302d40a09440c0c460301039542840c44115000744200d01c40c03070340458440d8280200301c0d0004904440600c4014000c10b100c4d010900046032013150 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 22197308 1250 22196058 22196099
    0x30402060c01090203010f0603140a0203120d0902060301171504050d0f0c0f08040e010b0304050a020103050c120907090b031501090506120304031a0619060e06070b0a09030e030f07 79
    0x1030b03d12041000d40e07424000c008401442c1c0000054840c00c0d418003c5c2e4032003410798030340c1c09580488591001a20000b07195800d2001c41c0075210380300c0a04d1840031014009085010354000c4000c00082452064841403240d500d00c040c00701c9003200007840241608074004c0314050080d812420079805c1c500d024a021001d180802e24246120300311030307610300364040c10008054401502c00b1a041c80b406030f092005902600d1480061070961070b00f03036166030783c403044500000d040689480c0840d140f40e1a28041d00c0e190100e808486426282c0182c489564503140d21071540c080781440d81c0c2c0c0200b810b000c2500500d0306074040c030202240c0e0030415000b003d40809024142c101c00c0c90390311501c00440500260000c0d40c491040c6001198000940702c0149102403c0b080c0302d681840c208548070704814400c03108640302402c21002d0400340c1e1002070411300a030135003e000c040920b020025010804d600006145101c0e440d035058080d072000a060f039a0725030b2003017102d00b503000100a1143c0c00b9039010080c003051 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 22198558 1250 22197308 22197311
    0x3030b1e010f08270a020f03150a0c0e0301050403020a0204061505072003030c0c09070e03060612010b060a0c0210020105070801140609060708030a0e060712020304080c0706090306050906010506030402060c01 91
    0xb10a48514a445484581310001d290045901d44085240c580e48141182d041140103140005104805510f00d40c00501150f00b41696034a08441712030041000d00c90307201000b00200700600c1e0909010392240d682c04da04a100b035190a9000c600305c805608a4841424a5643c90341819559614803520184405106117420007400d81c0381c5072950200001d281c44040030010b010140c4a00c1c0030711440c080090403000c24051503114110081d00c0000f20b140d0310490495148545c4281503508600400100003003039005403000500303002d0207030071002d401c044920a82d8804c50341203164104a00702c5006440340300021b0103040c01040f00c427460410105204800401c5503203840b03003c0c0300040c030560121000311400f01b004020051805680d00c9004103030461440a0b1000d0310b80500c000301402d012040c1e40b103c180c0c2c04004a0140004101501d88034401c08048420141c3c550320040c0c0140241e1100302c84860a140015903900800303e00d081c1205c0d000341025003143c48641c2000f01d550803400e40c5c9880c66 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 22199808 1250 22198558 22198591
    0xf0309120a050a020706050a05070809040605040e011a0f180c0904020706050a0b04140a0c1206060e151602150d051006020d0212090103050c040b040303030b1e010f08 73
    0x3200d03020000c00c500381c21500c030b165648211180181c00d000c01944058240034040c0110100590400115200b260b0f0244145030b54087c210009002071915070840d81e00b107440e002030100613180550108800c4005403142ca403c00d61284100f22aa030802c01800e0b40092040101d041146000244d00c3c1d040071030809160304002e006804201203800000082c1c4a040d120310502c00c092005100d000c5002c1e40039142408401b00c40c0312080100680030702500c1c02c03140d50b100702102c010f20030380840f00c0e41c1d01060707424031042d0341c0c1d0f0100401034605c8041c081d02c0782c00c0c03134200006040c4545040303900e03200d0701c1140050806482d40802048500b050400e024404042012241408040c0300d160312603400b19101c1000e80b070500100a1030440d4461044040d9803066800c0ca64031242e41d4240c0c0e0462000746004100f50792258003103030742c501944d840896048000300f804010517402d03800c034642d40c0703109441823300c0c80f40c142400b6030402114446640071801c0c00c090380a4013441200c170135a01284640ca0b44091 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 22201058 1250 22199808 22199833
    0x509030f070507091b170702010b03030c0105010e06121c030f0c02010519020a0905040b0307030b0c1e040308090103092a030c060306150f020a0b0f060a05150f0309 72
    0x441e44030850865190b0404181031014854510901e100000e00325a003210a6005d04c3d000f03894030a21540c03000110031180005244c5620075001007855400c081c0549884000c0c5003440d5000e020b0130b008182d0a6008000010b81c98288500103980100d0180018111002d280003035540105100c41650205034440401c6030311038440340500c441030010366000007658504031150322010301c980340c9a0600107004000344e020030b81d40030140c4410348000b1a40081c441e0498000a49010300079032004100c100c40740e00b0801921494070280c58040c81d00300700000c001c125034400c215a88550300000b0051241400b5801c00d65102c3e92100f04d501d80704921000c24000c00c03d4540100a09101c0c1350700d04564031481c00d10070440840205801489542020f101c00c81c14100e003842541c120b500d141042110012804c408207108000440d00701e90000050311440c104603c070310101c1c1000b00e80140c0030380a11400092207080151764429407000300c40b100c50800b0400d091081e21940082c240e08080c2c0305940b008000d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 22202308 1250 22201058 22201087
    0xe04020d0617010614240d0903050415030b10050702040b03060c1806030402030703030f12020406032901020303180a05030309010b090108010510090c05130602030a0905040b0f04050903 81
    0x90400024401d8440c0e203469201800d40d65640c01c40040c180080030301010300e4540b040c00d0700341c9015280c200700140e4209200c601d807c0c051401e50032207030383c10f1114100526401000608c2510803071007110701c1c441381c502c07400e82c1581e0058030016007200d00103030444240341c07144001c1c003000f0b480184046104a00c19001914000040d00c181c001a0b9001503003181008641d064621b122400741c2d03840741586060340000e51030345402e10015043c8540c451004603000e1042c40c10340414642c0172021074580c0c4e12210001c0052110300341081d030400c0c80803940ca00016401c0b41c48000482c05a00652850b0b603002140c07482c4d03811140a403403003449916086d0740001c105001441c405c4520b613000013106d07004601040031042c0b0607801075003180d140c6001e0002a850118004080d02c5807031070082002041d0b030008984501c109140044404000440170541682c040010f000c82c0e6010381d034208195460304200001c5900c03005e1030300e80c000348440c04151142400d4102c56401b04452090383d04141c02c6402e00803 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 22203558 1250 22202308 22202321
    0x20c19050601090c030b1305090f0601030f1a09070603020c0f12030402040b09040302100c050910090306110906040504111c06080d030908180f0307090608060604020702060a0e04020d 80
    0xd403160401c0700140000310140c41602d002000c28a02404008507441c086914111450185041039441e5000242c90001c10050401e442c3c9201040300d4443d1303540d0414440c11490090102c664040c1c40010444920b186601a40030300c5425005c2d10741a80313410700c03e03402944600c480c00a940107003410080042d6062200d0007a03c10340e036a01590300e180c40c0c410401220064060306115074594014040030036400a208501002040d000241481503e8003e031064019802e8156220742410303070600010b80d02545042c1240d119420034030007000d640c4100c484900501000c66040326040c8030800c820303c2c1a41005810f0004070342000d140940c3c0380718034085100b500c041c0c50486138903260201720042c01000014181072240c58200121203855039440054440e52000300004a5803242c81c1005a851301c2c0341c0718148070003d080b50341c0c696440480002030b050381c0c440c0d02060300400000801a007403500031500190740c001c2a00d494103582e001c1c26164082e2a000c0709401ca58203001c44182807590784038a4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 22204808 1250 22203558 22203563
    0x110904020a050a09060503010c031b080a0b09130201030f050603150c040306021201031a04031b02040605061c060906050901030b15060304060b03061308040b1b0a08040312020705060706020c19 84
    0x800c51071b045c10305144c20b460622500c07900301b616103000000661000b4465680400e503d02e4809202d03114407406c04003421384009116409150001030060040d41421140c0e1581e1007a01e003405002700032110001210070880700c103a01600703d6028000c0310924454090b503c40e1050f0700c40703401d1680320b864010407a0001c5103540551080300c2d0052082c440440078039841d08901c0c240305021442d05580080c007404101203940140c0e4040d100100c11942c1e1500f1010180102804050326500503000c0c0b404031006005c0000301d181d01d41040412040841c5c000d52064500181c40822b0300c0c3d01e1035441c4411410001d00303041c040b14103200c0c2d126880da21200118041c2c1e00881d401b140311301c4010101818010054001440418074450340000103442c102036404440b041e103000c5448802e007480c0203180010b4a4261002c9000300c01842080040b8a030290080d0303030090840c42c3c0d050702030381400c0c2d80d00e55090203030550006040c0500d500041e4290018001c603081003041e00e40121601850880c0740c0b0844404 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 22206058 1250 22204808 22204811
    0x14010302011e0203090607020f12010204050406080705030c090903070f0309030210020f070303050f070c03060203040512040b070803040c03080a11010c14090603041a04110102010b0d110904020a050a09 88
    0x4206540c1e2028441160807400c41403041400d2990002030f64900c5402180c078011070000c030b100c90035035907054044002900d0192041c1003c410344407995000b503009025592080740b0703100c2e000c50b1010b0002001419150090010442004040304029490300000c00c41c402c144020404980052040c1a100300b25a1086e201c800c6c1083c154070400940b40400c80640c003c5501c100900700301f61200142500461b034144c1403003640d0b401c03000080013041c410b445003c1c0800c081c00600200f000010303401148180e02a005590081c611065114014800c92003032007001c441c28040030011880c460015a000b41c0b04080c41e010641d640d81d40c944851f0460b802c80c50105180307c418040e0b114082c09034040503141f43c500400c0034000d006030a8124002c150183d4002c0c500400050200400e9040303210040d81031015035010b9180074a06400380320500d4030468015401c0c40c00015050400c0e401400c10360707501030070070114001304a051004201c0c004105a074019404035001440c0e40300d1324120307400742505810 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 22207308 1250 22206058 22206061
    0x9080703050c0c060a0c0f02120708160801050408030117030d06060302031503010b01092304060f06030e030a08160e09090a020901080d050406050d0608070608041101090b181314 78
    0x210941010005820f5a0040c0e00070013601c00000d0b401035442d02d04a41c400610131144020f1300200c0e40b084210b01d2030421a00c6400d00104202200048010551705041d42d03000301ca58440840d036087e5001550024240c3d00c00b40014861104164a1410481c219100321780c245001d036115801a150154085008070340d001061081000740314603d441511810350017031000c1402440024103043c0c2600c1103048100b94545a000e020b54444801106404c005109006103a25070904100034909841340328082440d1044100e50701c9000700940d007106e0400c1e12041d03401d6451003a40003000170103000030750800410400280c00380d550b10512a0083c0b0902c80103025100080c41405030000707040e0000003140d8085120600c296500a0403070302664024505240c503240c0c205254800b60245810452030340c0550a0086201680000300920130f5005006400200b050f8000669003407603103000e04040036004011050500007407405070844880040c00901d03640c15607003410b030300300c43c07085c2820100610f00300b0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 22208558 1250 22207308 22207327
    0x11202010e030a03020601050f0f03011b110d0806011b05071e17060403030c09121b0b1602010f0207031b080705010f050702100504080102070b060a0602011e0506040908070305 77
    0x2450045205042d0300400403550140c5010390303945814801e0a10941040c01d0f024030545030700700080c0c500d4201070001c0c0704a260740c0383e1171000084001c1d080e4000511854100c0006400000e2004400003507803a171003102c2c0c0318100115a04158403003403020b4051500c0b10480058410400f1030000c021101041d4414410b140741e10000c8519035001000d4100c020700c60480071040801d445811681c982030006030010401000c1d40c002032070794858543c0b0281c240c440d5083c0300d45111030319482800611100c03c00c0e911505a20890f0081110f4242c08942c00d80100c40154005c3c0742d078605500303150048603501c690742d41d2894a07524200c40454007010b05c80c1c4003040034a03010000403002d4242400c1c824821281c0040c0181540500c44000c3c4c420412207802504a074003560071540540f000800a660310080d03414284180301d07050394a036014031104240000d40078410b100d200d51018040d00e4050440340002a030381c2c0902000b402080c2d1181d50b0700341c000c4c001a10b01000701400d9100c0d403501e940baa000031 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 22209808 1250 22208558 22208567
    0x201030c0c03050301121e0501020306010806011d0108041119050405090307260d14040b0f07050f09040605060a080a060902120423010f0b0307080307050309060307030b030601120201 80
    0x3440e460a01c808180e1140010b40c101040d241550390030179281d003040003541000908410721070580090382c04075104440a1042c19002548a40e00a807569111522100e004452000c001c02252070321555601c5001050f600c68052950040c0c00707100041d10005440d00014505601070100c149444d6081c3d5081000d41028082e655014010101031070800c0d0458403941018000d0220003110b0441e036408201101110b1000e80d0780c014806070003000a17501c4105142c0c0701c4281514144e0b1090100c074001050304080d8800a03216180540e13a86003001e001c00f10a0302107070000d80c001584a41c9a01c000300b00c07500d420700501140622655151010305204481e8002c80314642c000020450040203d02c0a91104100c0c95421a50043c0109800100261a0010b5901e1208455415401d040c204500307207034650000ca1208030124190b51442d941e90b85410354030300c40c841d8010170540050142890710b1900f540550740c800d02c1c03802c0215007045044002400c0c03400036086200d40c60110a142819940d02 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 22211058 1250 22209808 22209821
    0xd0605101802031003020112020f0315041a150a0e180106080f0c070222051503010c031505090702160b1b03070f08090409060905030301081204030b0708040c030816020103 75
    0x1d001c811480e6081c110b45454414829000180c14484407130105426a0129411078042205540c082600d908110b801c00d04038070f403888115481141080401403409640304a48514400018240c200007060a4031091a40e0000c01519060000b400001584c3c2d40341c820300c06d4000c24040c1d135800751541c1003920103042404003501c0c810a5842c0c01c020011040180402c9481032078041b50142c2807416070031340e07490880c0f40601c21540058144003d0002000d0b00c82c82c00040c40300210024040c13140c18000c21802c0300c80e801c10803941110030030380c1017016042046060f41c001100344103a49000706001c1c411102040300790710007080d03c040018034080410105505221120095029502d00f040719215440c019940706009442207000095264060352203920a14169a0241044c04102c00340e08220f0b4880e0003d2084420a0203000040b03440c800125044805403940400803900944841400319240784004008039082c840e03048010010800a1002d001010f10011114480c250144001026a40c9 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 22212308 1250 22211058 22211099
    0xf070e01060503070c11061b010b01030209010e0f010c050d020706090501050a02061603020d11030f070302070510090303021303050c0f04060609060e060403080406180e010f0909020d060510 83
    0x820041c0012640102229003001440c54030b0030b402d48090401c00c0c0741c090403510b00d95100c2000694801c505038000c15880311650448001c0107400d00d648019800d0b4400e00300c4160004480083ea03001d10302e010110b000441c01d040c1344c072002c080300a60740e007880c1001101c0d0000c003590020204115442d80810118094082032800c2030406119101c00b0356505000391041c1406910a24107551051003a0305982003c0360b000001c2c0700790b040c031003003e071801d41c0140c0c2e80880c0f05038074400060441707019000302c0d908a980304004000303500121612000501407881d04404040d000c000001680d1010f05005000e140aa4003030410045402c04000184410030301d5580558280b4100f00200f40e0080d0180b022500141800159a1038003400180b051081d84c10080c44540041408500f940d0702042010a04500d92107403510503403111400303108020244500d6414041048041c01905481d0300600c1204d03101a01428040c5120743ea20000d580085807129403c5110082c20030032002d400d40840409a03 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 22213558 1250 22212308 22212329
    0x3010f080c01050a0c0303090c0b0703020c0d0f1b26190305030604090507150503100902040e04020f12010c0201020c0c0109080703020108060a0b0d0501152c03010603020301020301080f07 82
    0x1d000c480040e0280c000d903030f004401c0c041d4800c2802c040c54001d8010f80880c0d0350012080500a0b01c0701d100b112550084007065006100c1e1030000c000505102281d0f07016242c0000900c508903125503544042e200304521b000441408600d400200c108403460510201e0711031490030803082a04001e2149031501c0c0da00b800e6540d40104500e0004070707402504480e00180182d0300400c207aa043d0603c0c1e4a480015071000052820000d0320802096011018602078480b0781c05d044038581e075614014007a801030340201807090704070001080c014944010603650440300540b10038001580250031600715115038140f040980d40000c0c0010203c01d052050842d8204242450000d060030036507001d13520309541c0030003418000b001001c1034290741c03500550401801800e00c1107690382c0580c000c00020388020310402403680308500000c02c0740741c01043d24104a80c4030900c00c450100d00300ca4258030140000c202c05405558803035001c0b0147e10280001d50107000014000d0844c601a002d0f0940740000c0c40c0d02010158 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 22214808 1250 22213558 22213573
    0xc0106080a11030a02010e040b01090513020304050607080f070e01090302040f0b03070f0e0f090313080f10090308070807030615180905010614030603070e01060c02010201060608090a0f0609050105040803010f08 92
    0x181c2c0c1107d003100b0f001d48203890001f00c100102d0011380b0006d076a50010343c0d100350b064182c05900c5e9a00e80086200f180b054060342c00e5600c4821065444000039170f010f07041c10b09a075000800085c0710780180c201101051605049544d520f0300410704954844151044c1103441e6260852181410003000c4020080803e442d0215442c201c0556001c2e100500020703045284d010111700001c00c2001031700d40d0524111640c148040d55000c0071950341c641103202e0152030007044030400707540c4010f12420340816055100d40510b96200a01103904070342c02810001071666840d80495a50000702080f144240541ca03940c00030b201400c0070b1000641142d01c00c02400382040b00500c9499800540341c0c2c04080440c4400d52640c6601e00024200301c400c3e00710243c2c909824000046c1e80d540040c5034411a8000e0f002040201d40f204021282100700300d41200c3d0310f40c0034220500018221610400c07a0a0052038002503640c42039031454250383c0140d81c10349041202200611500c680600c00e48020300c20358000f80b818 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 22216058 1250 22214808 22214813
    0xa050c010503070c060b0a1a0d060b0f0301030b0403140a0e0108010902130b0a030609020a0f032913020d1401030c0e06030d0509061c051512060414030c0106080a11030a 74
    0x159111600109680d403950303146c0c003407600c0b0740307244502401608608a07100d201d00740702c0e1181a040540d0500141e41040300001d100c0d0049400c94180108c880c0f9240e15503030071030b1a41e40e040600500101c08014000c0ca480340425100b0001d400c03480d840d036031119070010301c81000500028040e041750350f5841c41007020780031f1041c884201c10110b60400f6034050b20398421107820b400400042c2e010110050001420301c1c841c41d400141301d07100c400d0588040000413043d041d2000010701d04071000030280e0720310013070301d00a1411a118600042000101501c5c0007616040306094030042042442c2e800c02c4403005208001ea075002e00360150001c0303101c180e418540640000e0b5074080c1e4030490030500c140090130500b0790302c0d00011211280003150004040d4003002404500420084805d17680d00c0c0c41a14000c0030034505000501c8485841200400054035152200305080c0c0d4842c8008995100403c02d6144a00007800b6260081c10a1000390800c3d0000c1d0078605001c894540300300344a50000b01c0d45000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 22217308 1250 22216058 22216067
    0x11090d0605090f011503150b09071b0204061514030903030f060105041e0927060213050d0b0604050c190311040b0708030919080d0c030615020a050c01050307 69
    0x24554100d9800300309601d50454503401d0840d80d14038540035500341001524003000310840707001124440c08014649000c2002004101c40200c21603a1b8450200808a21020b10481c000d050800d402c6603220066040c0394005003c58046a0290400c0740d081007191282c2604580c400c51000c0c0440c8000713240d03160800301c203501e922005041222000200300407034016407003a815030300580880a6a5400d1003442c10b403641d48a480c52050501680c100701d8108040c0400005199a04980003400382500c1711a83d0384c807020f03400c000060744141c002d80b040083c0503070710303a507000c943c190083c0000c3c521070500c10300f0300c0141c0e2401045099640700c104003209601c402e00118514500781c5260000340d00030511074140d11882541d100000c6c251022400a05100008009601032003e035011500c4483c10030b4800c101d140c0002030080c0940b8810305c425504145c842d00600c1c1008003e20f000141d458039215040450000010b000c80180d000386c6681c0c0400c101084854507040d030908002d411441c15400c000d1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 22218558 1250 22217308 22217329
    0x503010603152d0501020d020c0103050a020d05071106060a150503040f08040b13081c0804060905071d1b0901120f02030103080913020304080f03090f0604050d031109 73
    0x2007055621516115848409014203018002e0246003031074079500d902c040034800790080b01e955074031a84a540020a507000058510f040c44841e0050054032094038015002804000c256008040d0201f01058a000030341c1f054030f100b90f116840d22403038920f040c2c080318901600204414041c8a840c107003402a645d000707401d03d205552915010390b481d036070351030004003034144080020440701c0040340c00300345c0f5203006015140c998200c410a403001030b80c6403140f90b900c50070002e28807072200703000c410312000b1880b407801c41e64818056400815120405d030303113481c07400609502c9400508a583c401d0300c50040202682368126081860710009850001034152040c414420401d044c085064164180c010068209000407854040110f490b580c0d0b905104201d03070301410134248240e444001200724003403d882905e009642060f812814030701101c04c00c1d0030030ba001800307154940c807d41000090104041126070720444c46031001d030011a08030075014059460480c01030903260002d008856040e2208118038 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 22219808 1250 22218558 22218569
    0x70309050a1509060e071a0708090d0c03050a0b0601080c0a090b09030c03010501030f060c0f08010317040909030903051207081c0b031207050615100c03090b040311090106080601050301 81
    0x2e26400304004188001003116241c01481241070142d060000280801c0d01000c592090343c0298908181c985138001c5132060050040410f03405114060321303402c09101c0b642446210b00407089440b5201d48880303240048101d4212990250502080400d5a0003000141c001500e03004050400d150100c0203002c080150044600c0c041002c642d500c9140e600f0020030f0f000e0200035008009551312400c090380000344d100c0080d40d019003040700310300c0100c0c0308000c1c0300c0d09259250b80d21340303a41c5d00f036035a128124042d4090a40d07242b8070a110101d4900110300c68608464403075240c0403035152451400c079060204085400c109020300b480281c0c0459054001c940c400340b0040140703940c01e14a003905100034034900928a402d032040600c40c019080d92030000b05030b158080c1081f210b4958038102c0001d100e840d00c221481d00802070004c421620350081d187c0244691090514015464403580541d80c0c0741c00c07030b500c20368080301100712000c11801e040b5200c6015240c0362074014405c2c989040064a207100600c0ba0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 22221058 1250 22219808 22219823
    0x109050a1a06120606040b0a02060405010c05070c0e130b07030504060e1f0b030a21020c0307120308070909050709090b090705040b070510050403050307020f0d08070e030703060e0304030308070309050a 88
    0x1813025550482207030050f2a8031821242c9070202c1620003590741c001158111159803030464a039210340d01440a482805603c849271000c00b60500c442c807440c3d124050284a24070501c00032460005005100561040d00995400030316883c150405200f03890510450b0380381034003c020000120060460059000b030001c0d000130403424603d4001c03074034080007041e003d400e09112820300d088805551424815249960b802caa422206da40101a11000c1e14403c040e56480f1400151001900500c1e07003560110303850030a01002030380e401013801550412640d110001da0f00101c14003460001d4401e1900652044d20100484d203826030002d0543d2040e40581c008020000c1410070400c04104207070510b04003a044240940d051510b005003c642040d100f000241c01039082120199400150030030346280f0580d00c0d10381c25150719030b00f41c5803c11100d50703003509805058000b002103411401140c070040b011000455032503245060050150b40060044810141840d00e03082c04100b002906514543e0071211 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 22222308 1250 22221058 22221061
    0x302060a021b06040f0c2310050c06012402010b130b1203070809090705090f0108151903030e01090602030d020d02041d0702010501080c06041406070b0109050a1a0612 73
    0x304414803142c0c0040c680e00c9104200802c400c000341e43e440401041c5c40340100c6505652544500c002501c020f5001101d0b18071600d049113100d00e01340b40214a40000b9041c01da150041c0f0681007030408201b40c000f0f1460046585d82010f41c02240c070f001d1440d001c90303803000304003070700034840054640d80030a001000c01070f45581c0281d1443d501c07034052800142c16001182da41e0502442d0185d0140c000100316880380401100254005000300100c0f080c018000305a09442d03030003003006591f51640a000d0001212907800d01c80b1340c0c0e44038a401c3c001004094040c6003242031861034010601800c00100c1c03410404105c0080000c150000140c030440340a1803400b40c1c4620004070354100074040d50b84018001000741e02641c05070155945103500500042d4001d010583e01c55a10990b51520322641507004074040208004595401d107480d103440780001d01d524a060071540b81c2030950602a040f001c408c1d641c0301e042c03000341c5c0041d100f8002400a8201c908462200030000104a0b01511920480e694141d00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 22223558 1250 22222308 22222327
    0x4090203061b0c07090501050102160501020a0609060b0310020309010b0406060512070203090405071107080102030705070818091e060108060a0b0d0b0a09060302040f020301030b07050a02030d05130201080a090302060a02 96
    0x10b050761500301807030301100c003103d44d94040180500000c0c0702d85405400340241c0304105144c5203040400340d403410380040007854020341e1000010b00700c1e208140c070111750b1004c030f6503041e94050056414020750380704050b891342022040b03140ac40b25202880e9215a00d010400c0200a4016056441c0071003d114121202c1c1c1e41c84105a00f11301c0780001c183e9101d483c1030100b080594010f00034101550a20040303810306900c5a15050807848181e1b00d06010800501c0700800040d0342c074008150902c6591028146102d4042c04151841000d8540c8c00c150030803100013440400038074540700d921060910703181040341030101c0401d0304510b0600900c20900000203070706202c1140c54120418440740509192804c90340c030350200004280380d00040b4811400c120705070140c21000c0c001d4906894214205240079250703250251040d51000080310154081072100c04c0c081165440b41620400140d032202d1401d003000d02c0010700042d40141507040d4a464003600a002c2540028415449116654010307519034100703 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 22224808 1250 22223558 22223611
    0xc060c0f060c070b0709060203190302040b070c15020613060f1416030e07030206090603041b0909020a050301140411030f0105040602090910060c110406091802010e0409020306 77
    0x118100003a219010511440c0265400140409805001c1108064840190807201c11446104800049e441071094a260740c4c14045111740112480c00d00500d072a60f15403214640750030020f0190f80c00100100200018241c840030814aa6224405010903141c00511081940e0005a01070041035550451000209481c1d10021009000c030040c0382e1035180204204c400a402e69000500003030800801064150300000c42409481d402130505061042d00d03818080103400003001030b200506206040340c440003100d0087c90240c40103d501003501e00450041c014920382c0c0c0d41c40390740a41e24020007240030b803204040c0c181c3c00c1548030942054034a915400030303251600030420b002c103139460b090074481002201c2e0300900c000c50059401c80281e60340c3c0310340c1c5e91030b43d4660b1040d00040341144a1030000100c880c1c90410003501d0040000a00d641c6505200307040321030001c003d5469680040040040d50703080612030041907000c0754107018048035070f0f0102e030b15040040c01034401d0700904140310301c8410300c4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 22226058 1250 22224808 22224823
    0x2030708040614070807050a0201090602120906030a0605150a0806060403030509040b03010b100302070b0c0901090e0a020403080f091e030a02012129090c031303091701060918050c060c 81
    0x178402c50301c482e840d08155440c1c1c00340010490210342e040100190550000c110416004599415281080303035a40c1403141c00d40c001000098440d03235030a00455541c1e65091480c4811410b031552944442c4285405071102102604082c030448007070000700700081e0b0010840769181000e0740c01194848009002c03e015004240e00c690340405200c0710090705581c1940501059401044008030a44404a8207500c41c860400d6450010b40901d100b030108110758410b25070809003016006141690360745170103100750402e001031120f20800144c00c0400d45030502039480741703031041030b41445059500c00000e0b82d50119030b0402814400340741400000d0744541140d19a100c96126010321038881c018480b1304080da458104084030200c205501c10807814800c5800d0300c504c9508002030302c4d645500c2158200710254100880400440d43d601080e8108442003030151154410000f0400d40c0c02d154214040d940307a4002a81f40c940307001001c01c04034200046010200906591281c2e49140c0d51141a080504 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 22227308 1250 22226058 22226063
    0x90402010e0d02060d021804060b030c0c12070f110a05030c0f010306120b01080d03050603101e14071209050a12090b0304080304020f0f01080105100903050106090507030c0203070804061407 83
    0x100424105e0100d00650020040605104100700c1548061070810007115228026402071480910001e0800c20010000b80501a20442106c1120301c0d4030010785e070554091700c81201c00301d944100702c10811a03010007207410032100702d982c0001a81802d010035038170645811018400e07000f0752200e008690180d4054805019035071841c064804d0a03040c5590898800e2007950018850701e0300b03100020f4840c3c85018050100100038040101000080724060b00f248003000070f03071549856803000d120001d44130b4183c1085040d2460450b520300f51001034982d01140096031800341c108500c000000314085461814141d00c00003a01110709441004c070f903138006c1c581080070750038400424801408011000780d4840ca2080b50304a41e41c0c007022040c01241103080e500e060114005038010700c550302d0890003120074402d4619000d00910742d07a840e05800c1d00d81d150f21030000e4540d0748082c001c0c41070307042c0900300603210103000542c9025001c0d0f69444403407155219420802549030701000701e41c0c0008080307818194 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 22228558 1250 22227308 22227319
    0x112051b030405010e0c01050f030a0903030f050709060306050f01020a08130f060806030123040b04170a0305040203060c0a050301060c03030f1a13051306020304050c030f030c0d020606090402010e0d02 88
    0x15142c038269000b0955110b8980341c0d845001e01b140c405600c240b0440b44c0c840d01014503141503803101031618002e0252100d08038141522540080726600c41803040a100e50069900c00415a241403030150455074241c00490140e845051a000c8a076000101c00c1500c5520040c01c030703504c1c40d0b621a0a40300c1e0300c0c0d90b001300358400c1d0020400074045910a8581d401850b04400030055850346c6560f030781e4481070304a500008400521700080100f160b2244060380325001d0824002d1407400d404183d00154004050b501c04240e44405110550a00300881eaa12000603a001407600c4802c20f030103005400148030f030307004004140c007803881050720139000b0655101c85104103001400403620038182e021103110b041e6010740600300c2046140485c0d0300456000b0502c144840c041140c0c95101d1401039800100256558860b02c0103642a40c2c0b81000000480c0466030095a1548491500c503420060702c110080210b40c403c0080c040d450b503507800c001c0d80103682420400c0c0003403001d5011400c64051200e000c0d5205 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 22229808 1250 22228558 22228561
    0xc08030403151a1807020109060501080706030b0d080313050a0503030a0204140f060913020f041d0a0c0f08040201170c03060a09090507030803090a080f1308010b0112051b03 76
    0x501403015001c002d11038031050043d03141e03200c070854100d500301a80583c401074080a05940743d61100d9503a070000701c01d20001c907000111352101002e035803080c0d0007028940d00042e0304001c4607626100f1403100307800071220025034500c5030715542d1441c00003409020499103007070b500f40200401084280240c681c80015240c9030b1034044d6500c0020740052007051032601888483d1000d9140c114104820a00f00928541c2007a01c0b00043c0901300c410b080c1e4048000c1d03420041c0242c4800e0980280c001884c0d400c01922801c1003c60000301f40940142c200c1044500b01186080d24607001014080d00c40c25500d0045071a40d0340d400100c0713059001c20300500c58200400b05101c00000010029071144c0425551012410780c1c400c51682210003600016240e504404802e100040092000b0f68000100e80700b00c40d02200c00761119480395112105c513400840c40020084002d4110020360401440701a00802207040c0400000e410145e85040741a05c403503480000918514950001030070501d150481d40d03449 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 22231058 1250 22229808 22229813
    0x22805030106140310060e030106050d060203010303022b03020904090b090a02121b060a02010e150f0c040501021005040201030f0c270f030f0507050d0f0b06060406020a0f0c08030403 80
    0x2998001e020710b400180b000c444400411007048102c901036040c4243c411440c0e440c0c0502180c80b00c84c620f8661744d143d5201c080018451366401e000b100260f0042c8401662940f447c42c02916042c110320903406541c1e8001140d04c0b001a03000044a1040202d003805030b99211094001401060710f12401040d0320309160a0018030500000d40a403802d109444010000d50000c10060380e030030000804564180c0c42c0760b103104c2c5038100100070749048140d82c00040b070280645401300b820040b0307000341c0c040340030725542c2042020000340b98403e42048010082c1c500d41402c040000b901c510b4414040c440143d25003012800310391213580407a810103506101000400a07511009140000c00360782c03c07603030003280c8523480d010400010b80807040b0742154448010541ca0340d50342d03540310303c52103905840303a00410741e00203402c1e250810b00d030500c944951891484074050b4a440c50040d1000f8001502030308051000384080c0340c0015103c402960401d21441d031302c1c00c5a190400079581c141e08400c8003804045000000c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 22232308 1250 22231058 22231067
    0x309040509031306050c07090e030c0d0f02100b0907080411090a0204030b24010804031119030f0e01090924090b090109090c03020103050a2d0b0a0b04090228 69
    0x10f1108440360030206540e01c1320200c5240c01030041a8086400c2a482000a0b85555111001e810a6041540e08207444211440c2c200980036507070102040c00654004816507050206108a080d40c1e07404200240345140440d40060f00101004103002c5002c2c0481c0920a151814643c00800244031204502e861800c550107504144000c5619212000c00b095040c8204074912078803451080800fa80050080011144a04058030941c01c0c040241d4410b070030388a05104803604100b08a005034825640d510780103191f040b483d08003504102034026204172903a40107901c3d000303c400c20400428001c0c02d0b0b041c0079000040d0551002c44540340c501c400034043d01c440c1c209003a292011079020440382c1e40c5405603026103030020001404000911410300041d07001754844c0d5000026010000784086201da808488061540c2d180c8140441040c0600c03c1c2d40d40794003480074000c0040c0c0c0c050300c52521348090488980203d00800100d03580109601c400170102c0008400c150360740c03541051000815810182 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 22233558 1250 22232308 22232317
    0x10e010c02030d0605010804020d06020708130f15020102030907061409060310030209061f0f0c0f0b04020a0b1611030114010906140f28080f0609010f05040c0b03040203030904050903 80
    0x250fa25007000c100260720b6011303d064a2280381c020300f00c00350155895444000a5110050071502040c080c043c3c690343e182441000c2001d000540700650403a4100101c039903402040c2640070301107a0041080100c5580042004400c980440c2040b14091101c40388104c4113014080205400507004000c20a0b6045160359000480b8020383d86945142c40c0d650038072400c142d221501c402035440d09241c1c12009131041a072180c4e44269454072503448203103a6203d43c10f56602100030364890740c00c01c0500041d407406042600040a00a028928140c020100ba580c048107044000c0c0070f4201080034249240c5081d0001d070307640c1c046c0c406212415a12407826100829081c01010b208051703201140301c1905045450602c0100024843c405075210f0788840e45000c4898040c40c1e880702a084000aa041300400c4808000c1101002400c0a4509001c00c2403c45e1820004d0092490a0006000c0071400c0c060410051314003010ed0a65a035440340082480c501c40d0240e1560081d00c1d10080000040c0084081c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 22234808 1250 22233558 22233577
    0x109080315030a0302030412020a030b040302030a03050a0209030a020f0409061107050705040204030b0105091f060f0e030c090f07031104060e0f0f01051b0f010213171c11010e010c0203 81
    0x8140310307148201490790340d00401e140200564002c110521203440c02603180d101c01440204513565841c1c4940d241c10041c0802d84044015a00204004060035018003511b51f00c503582810840c09e041035440000d03995905203402a008002440780410203448941203130303105a1300f0100c20302c1a95800c0f5503011a80d40092020344a0340103030700011071185072600844040700d401007480301160742070408106001d04041d007588003200842107914024810151910700901094450400340c0240840c00b8102031001c0780e6403403090b04250750b030314150340d206550160807500e0544070002d650f60319041a002088140e0462a40d90804078000500651100100030740b5a800e039500c0c2156030b50f00c0107102d8148a8200e102d03020403818403008846208204c241d1440400c40d030111010200c0d0800c81ca400c90307009054141d0380307526220303091209024044000c1c0140c02101300410110070310394003503400f040c40b0070303045010088501c4040082103000d401c010714912070304000f04000790703010350065500d41c442c0e00e04 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 22236058 1250 22234808 22234831
    0x501020d03020c0d051804110405011808030f090604080604050d030e061005040e01020706020d020408010c0903030e060904060e071206050a050102072907050102030a05010b031302010f1101090803 86
    0x2160003451190007034506051040000340740c0f5104000040c0c8a580000c64507010102c00e40030082841d90b076600410f00550b52a02425568905200004105e1600180748141140704107204018441c00081104e0b810050b0106164841e800b45000445900c01c50b4001c0a4500c50b140170701050000c081104e4421021507107040100740b80c040d214540b0703008100d81c6003207440f103070f00c00400450401d9084041150950b200040c0740c40c80f181d6401040f46c0104e89015034840d03011600f0701044009100e54544a40c15052800c5480d1440da0700510a86141110070302030080410030180c16211034024201500d1200480700c0e00d0315103004000e2101445405000520741040c03400141420003e10301c1040d204180d024011140c200305090040c042c0d00c4840b400c581d40c0e909400c2070700e40308200240900c2407081c1c001683e02e0034032488503800d80b44107801c40307903107941e04100f403051205460301020b08103542802c0003c0900302e80101500c5051600c0a007240c91350800311650304204110000710b1161000214 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 22237308 1250 22236058 22236073
    0x40c0306050d0b04050f030409090606090915021c020304051c11120f0d050c12010503010606210e06100303030510050607081605070b040303020c010c0b07031a030115050102 76
    0x2142a26240c0c411103401c684010409030100f800e0034801d951141c000c00403111442030040c00685164040d81c05503616070344e640c1c1c100c0300b000181d001700380050400303500a018041c819100c0720460315040105483d000c3d4005041c00203074812101c1c808400c10160310440d01da2074a0f081c07094071080d0034451004030b040146501e60342d407400340316181009031b074000003443d1241e80060507107110b81c406403800350702100070300ca13035a50301135540a401c1c03180070384008680d29060190352491750b451040c0c0009201b03906006c8103100b003e0380036240006040200d000c0b804000082002c10004104a040c0310800d40281d04c1046009031840d141082100d1091343d00700015030700d0050b68000c2101c540203d6074840410803030100440c181c9400f40c207605e8086608154203000c0c0b40e5542d4035062481d881501d0b94600802c04205040e01031100c415000c40c203007400088500d840c0d03540351081d400207040801b41a9100c032055242062200202401040035000708112460140d005a01e4812449141d00520500340d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 22238558 1250 22237308 22237331
    0x302090f0403050f090109170a03020d03020a0806010e130c03021b010209101115070f110d090302041509060909020f0117040204051305060f010e010603020a0203030402090a0605030a06020904 84
    0xc100c1031059030559141400c1c451a251042082d600071100c40e4100003103d0800300d4855100048008440341010080c00c0f4400c00d481d001c0d0500c40e080b4110010b05206010041d62542c0007184a03078004024686041314155200004411110001220094a180002c1180d400b82c01d5802803841c10b0658003000802e165440c8114280d20406400f540c00003401c103201d00080e802034142074506844c0e08190380a013500880004442c103c01c07101440003a1119940f100c0305508001c0742207160b00c4901c00341c0010240410042d0420985100080c082d03070782e0b0401280154010400100a05140d003002c0c40000d540316600c901915400d54103a1241041c11212895580200d40609500010015204c119030f2560204801000c00901030314820815100480019070306000403813190b500300104041c00c0d41400300700c1500640503000b410915104001d00204c0ba600001038036803003a811155005540c1d0703405103480140c0403681c801038051254101950404c01c1d90340207080c5030a421f3710700308100c0c0c0006 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 22239808 1250 22238558 22238581
    0x2010f02040605070609060603050307030c0b060a030b0f04080412060b09070203030f0c2b050403090506030705042304021b01050f190906240509010512060118090c0b04030209 77
    0x140302d0380d000f20b0000c010b20320008005820101030300340501d80001e43c16a1340d0703c40c1421588078442c01c6000a000c002c94408210041c404070360060b5056401c80c11503400c5940c1c0088800c0f0181a600f494007424000404002c46c51040b140030f0300d04204070741e8101e43c80346021805495101d000328400c02d50f40001400700c1e48004103882c81100300c9084009151101d021080c880d61040d0090501c0c0700f410000c9550500103000352900c401c1e9641400242c0e0324103402d00800b000c2150b0001441030000f0030a000b200da6019050340d05440c01030080d00501e00c80f18980301440b511030040c9941140c008030b40d02c82803c5800074450305d03282200c030003448141e0380d4407403a85030104d0845d40301800f070682c0c00201203640720940c00b4056a5106441c0064806220b4040d1407904401d50307113280141c01d00c110b0a00090030003010240c010a001e980d044540c107134480d00107489420501554425025202d00c0300d20404264000b241d146402400010900b81c60711800f0140d903016000aa000355001c1011402c0703008039 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 22241058 1250 22239808 22239817
    0x12030c210306060703050d020a050903190b0c0d0605030709050405060c040303120b0d1a01150c021003050907030c030b010608070c0b1b0705030c03190503090c06090112020d0c02010f02 81
    0x6203060140345658480801681c0d4101810980411200f44501156000d0501c010940728001391501c50300d40000000301843c01126100c01110441c080202c00001003040080b03070740000c043e4100607104c804e004580402807002d64000d0307038140302d15000012000626442980564011000c3d140c0d295542400d80800e4406c0c2e12000b030008002600303071090204254001072000a000340b041c520210381d52907070401c0070012001554400b0341c2d4001004030150700010681009420305000024a145800164194a104a01000b4151207200142210790207000010140d80d005449040c519100d0a010703000420901501000c00c040718081420207000300c01c408011640081044c00d640c2da05958189000340c0402c140040345810721030380f00000c5040c405080c03450100f40042d92114000c402c1d035800700f480c80e101202405401c000703001da0700b0f0003c14440800072007900c803030341d03aa0322040c012511188034426806c0e0140c4046041a501e100580005016601c4d5900902c0902c0c03449074064100e108 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 22242308 1250 22241058 22241113
    0x21b070303090501030207061404050d031a010909050705070210080103050601051210110d0f0209091302210a02060c0a0c060306080d030e01140106090303090e010302060405010e04090212030c 84
    0x60b0780810070f41d80f00750010917010b4411b10b40031036040b0b50300e000400700c004255012141c5410601503c00b0060341442a0b44441400e5202503c030b004003c0d001920100d0a809483c6103281c0710720010b00103030302440448410b49c0d03018016042d13580c400705005048400070300081f102405903070000030b600e14100c80e4141d4820046009400c61542c01c4001d40000d182e110300407501000c0610880c41d0014070391091b10f10407a040180566103d25010400c48040740007003003400601c901200800150f204d508400317086244a1881c81e11802444a1462070582e03541002588850002881c1d0840e00002c00c0c40c264951003103c103010000e440c0d1500b070301a12514040c4284981c00b00314421119813183c3c00406034540c0440002850b640e00d00031440070984240c00031804079410304410000c041e8803915800c002c0c05000600805941190700003855485140705e000d041000391050086655900d52103d80e030140e000b8002c8041d281fa480300c0035100d4000c0c400c10149406003164a4120510800c807400e40880d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 22243558 1250 22242308 22242317
    0x30613020d0605031204080f01020408070e040303091b050108070305090607030b0111060403090f0b040501020304060c02010509030a110310021204030807090f0915080a0f150e030409021b070303 85
    0x488149a8000d400c8816040061901c0d28800102602c013803003610070006449405542d11401c0210051400403403060306412680704200401c4545000320f0340409403500700f5203541aa40725070500301d0182c140c041000e0808607030444611445600038a0f1034007242d2081c0c913031100c0c41d60344410550840368200c41d201719a40102000030841c92081d4480c60407080141042041d1014580d003540c43c0040c03c079011800311f09180e000f80131030540000700c03000031310f402050701c7d1903d07050800003500c0e4000d512a81003408080d901c504110780c00341043e0746940300064100c500c02d0400d800e0035040c101c9000304a6002c0d01489200c0b40b80004c42c0e000b1a0308402c000503112403030313440f01e540481710b50b40002d00789001c004e81080045500e00c55219914024003100002240150403c40c004803603c0321a4000c030f040d580580100b0300080e03405007440c200e07542c000d28008a0605118130020141c000030302155946d00002a001ca150300581e0301928170801184000c80d810380141c003001d0755170b6100b80405070105 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 22244808 1250 22243558 22243579
    0x90a0c05040525051605030904140c04180605120607120608062205030309150c030108061501090504090b011d010b300c09031203071b05030c0307080d110306 69
    0x20702d4194180007100c01c3c0c500e400c51400c0c140007a40d40c100e01540b902119a82c20000761450231b446c00b4041d0b903101c0c070010740e10a1001e0400c801c1d980c81501c140d114100314103446170318034005804154004070007020b01400d580d5010440030f444c551920750490304080072907000b0080440700745d0700d8814103007540c0003040140b1460300c4041d0201d0b4a400100742843e41000700e6001d10000031000d00c060344c040c4000303c004016440038581c803031a0f110401001100140001c0c001007054200015605400500907002081e4141041004a501685580240c2c1e005401d280c030000c00c001c4100181412a280030f6455800d44101c0b02500b070302c80c5400e00c01c01c8210a018000550154020301004040302681c0160012640042056601c0128100d403409005000030031070b8202801c00384100c000c00044180218654541aa006468201c0c01e0410b4408103207100e02c1e80c401c005e410421220700ca040c90003246e4460300d0030f1900c01300c03940c0403022403004141070150b00e14106064400307407401b03008001d2540414 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 22246058 1250 22244808 22244851
    0x1205060a0b03060a0902070f0b090604020a0509040f0503040602030d0501080c0603011802190c060c090602070b07081201080102030412050403120806060d0509010203060a060e0603060126090a0c050405 88
    0x942e080900399680c4038070040c0780003138122000d01c0200186841031040c2d948107181420507102001c0b0080c00040c070340c1c01c040c080000682e03903a00328006641049078240181c0e10707541803141c82710000380070042c02840000350102d400c64001020f401c0441c8a11014000750b0303210080951038041c2d0480e20f9410590520041c0031501c0e110207919005490039600604120142d04c440010011090320500401e5644d804002400003a00582c080e4900b02d09004501c2031806a00a40e00ca590b0703c2202100709010071300394100b00c0c841040f00c00c0280c0c0e0309081c168550f11344849034000e600039501298624082107841c54114014015601160b420580c0581c41485095054030642c1c00200003ea00040401048050321040d129603402101240d000603128604503050001c031b525a500040103101c1a099078040701c0d9510001c580d4091000e00e49000e01e800301125801d41c612407602c04441c0d0803030883c20000c080400180d041108c8d40580146640c1b1543c030800d00c81124070680c0c025007070b00c000c4c0300c0e212070 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 22247308 1250 22246058 22246079
    0x160c0b0c030c071506050f0103050405070312020309030f010c090816090c0e030607080402090109090c120201170c0a1409060a0f140d090c0501020102090913030c0b010608071205060a 80
    0x50161404015901e44882d035aa20740d040e064204d0300606460b510202800319062a84140c00005000c3c241000743c1d0400c0d4980641c0c6130814800200382e100d80d0280c15100d503100f40309841d00c0440c05000c41d4911801e00c00c500b40a004e040c51a900020107400c0c0000343d1040001d11000031031440c1d03d5084001d800e180b4180050641d44110501b0300800d40c1a082d040e85040140d28400c502c60f944e413108506151041002203031040e4044403100c0e0030706800d10f0124500150f20812034411a1015500000307904c01038907000c1c000d03409034082e00c142204100202024030001c00e80c80f8000d558000d154645210041414003616401c107070403103000c0c04043c0e2128091064002d00c030200f410312500c0480f0004040e15558480100305d07a03003d845440726020420854400c0001e44002d000941c00c000b0a40e01040c0c040400501c40600b80c420980070800f80750003842030030062070f00315000144070b40e1140d8010f0043c0d00309441110010360810b44003a65451148903c6015010090020312124949440540e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 22248558 1250 22247308 22247311
    0x3190b06011701080f060a0b1005090d060501030c14010903030e09060a0e090d09081908070c090c08060102060f0907090c110105090f120f12071b0b160c0b0c03 70
    0x1d040c09103103040515203a040401c1c4a00800c0414028915040e802561908281c4082c11b0300f007165080c40c04a104680d50000c44140c484114038041c1e840d52902d80014078102e440c410b0181840c1d107054004802e101c0041c02c002c0c1554410149035040040110046a40018501c405400200361102c0007015140503003520340c06c440000c0100c00c0d11510344043d00e801754000e482511885d030103529805032064106803408014641c0c1c10280c00030181c0c0e910315080282c07145e40020100700000415104110901210300050000c00c1000c03c40e1200f20b24024000302c3e420740e09a4050310071500010140052151981d101c4d101b0308029021003890100d4000180c50002c0d8203805200854107070600c4000c003442003500c11800c1c000242000ca554030b031460305000c06c2d01c8616140d0320b0104200e030580246901101e00c0c2d442170760b0303c8060780c0c1e8a2034400c95582c4038110407603412031080103011050200f88030400d400368025600a01e0640450581907d1040f9180401400d480801c00002c07000c010210265 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 22249808 1250 22248558 22248571
    0x3050115081306110c250e040c0909140109030906081315020f0702030a050309010311120402010f090801020d050108010506010903030e060307020c0a09050405010507030e1f0b060c070504050603190b 87
    0x36401c15006494050812101041003101c103404071039010030221030458448000c0a500011447c2d5007410b03166100002114002d041e24075072510303076180030070400340c00b501c030307101e040d100200018115880c00404071a041c1c0702e80b030002982440401c5d010b00a49281c544546e80c89043c0700400300b082211180a9000038081c10400300052085001585042c03001012040c0b04074095540c5000000001d0220ba001543c08142080f00f440781032008200070b0011a041902400c004100090b070142c100d40c0088290072119255002140290a030040703900458160781041000303200c03e079200001113400258500c00500041c01c038000441c15802d01000031600702c3c04900c10365031000c100c9004110301138900e0303021313901d410354070000c0005216080c0b203110307008035040c038007813018400b000358284c0d43c3e4012800c61034003450704002440e101c60003603201d1140c1d00e1000d00040c0d00c13000b11072502525801070380316580c003c03414040000d01514002c10303d42c1881803ea031341a0401031964450301da40395402042e4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 22251058 1250 22249808 22249841
    0x50a030c0509040204060207030510020910050c071a030402040605010806060405010c0c050a06020a03020d0806010903060c020c12010207020301050a23040503070519050d0801060504150513030303050115081306 92
    0x100842c0e860303a00040002d04001d800400103c1e107980742252505071240302050b01c240c414801d120996680e0903410380e086140c1e10300b968403070500ca0710681c1000b806620070039802485103005035203500c104000e075104500807241084442c0c0e49400541e82d82318126071060344000200014001d40d801004420704680c00703001c05230101d64880c00495001400398210001691102e24035100b00f5a0400c511300c500714040c500f04801b070801900190a8007901d02000b03280d00e0715100c503c1e2001c2e20800520040041c0200b07040028407079003510300e001b50301245007030303001b5401c140000e00740441c40e0107042d404030fa0500c0000310a480d01028421003d00140c4111174900040040e080420ba04211a104400300030072214120481d5251061400780d000c9140001c0c020644010070140790004162402c484111484450100c002da5040310240b0404185000d84045a100441811b0f455031141f816150416250007801c500c46409590b410b07411503101c007007500349515800000c1d080307801250341e58034a01d80 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 22252308 1250 22251058 22251067
    0x1060e06070c0b0406050310080c010203070303020a02031905040602100b1005070203070902070b060f090f0403030b18040b0a05010f120f0f1a0f0a020c150c04030c06050a030f0c050a030c05 83
    0x38900c0041c2d021781d00103000605c3c04020b00084071001070b043c000600c4100700500c00c001105002035202d0003403800c050145a40803034040a060300030300854080540300c2c0c03003408000c01c120300d020f440e5401c280070710001846030f84410f8003c8541445600b00c0b00b60000c180c01000c205449084810b9801184102e07058065404005500344540c005440900e2090300c0c001c0c0280b42010a1181140b43d00003a68810040380082c440c002c12a4910741d50800d4040c600413900740301041c0400c0704003040c044040c0141e403110042005101c1e012a42d640070780c44142084c0b00c42e0341c0e5032031078800c468154017900c5003480700f481e21440005d0428141d12a840d01c9080c2c203140c0c0b5026074451208004407401082e80d00c5504070100001912089080d035802100c0207030840c1017101c0900103503980c4140c003007000c0c402c10351800400c1142c10000e050300c000f1a84181e1760b0004980f40e10005200c0c1d0000a01e038000304c4e00700040c4a1103440c0a000ba040001c240e60f4515040c14000d90b0124042d03c002100c0d01c052040411 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 22253558 1250 22252308 22252319
    0x901021b0411030f0109200703080c0405060a080406060602010b150304030e040c050a0306081902040203060d0209040f030315120b070c020301020d0204050f04051506030705090409061b020601060e06070c 89
    0x2d02440c07080444c41d05800c140d6142c0200308060b590000c022001ca00b040ca990b84100000030320607031310100d416141076003055681c80809940c034891500155070100f00400d5025240750b1205010b03104a11840090002c47c2e40d03a0f205030709a031002e4041c55030150844040382240400704020310740c414000d240c41401c4024490100302154070880c000800500b00003001180386825000d40001000301c1c3e4000c00540b0080d401010100c5034942000384103580000214505a4801070300700e411a0300284651418203003864103001c185000c41c0110042400c1052109540c1c1c403c11181d0200e4508e005003d0601c10f2690361103a054500500c0c02003440400402400582c03001d202510100c180200016621400c00042141042c0114806885141040c0810030300c2040d200d081c410000c8280c415903247d0b00c40c1c450036a524002d5890fa20307080f0380340140d0101800080e410201c0d80e6044c1e1080c00100041414080fa1103003824080c0c00b000c074115401144160030036500410850b80600717420300b011610b50 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 22254808 1250 22253558 22253591
    0x7050607061413060e06090c04021804050c071403031303030504140601091a06070809010c2402120105061201060e010c0f05032203050a0f020a03150603050c060901021b04 75
    0x1620303c4500c2c0c2d40350080700c40820015114201100300c81500400c22440c007104801e54500f042c815a900403900170481c00d407402001800108000305c000d00600c800e242c9503200305420707044171382c040e076134105805282c84c00c2c2c4001201300c0340a030800340c03c0140030079480e450907000340502900c21121a120003581d00100039040c4076090113488281c40101e40e0100b80c2c10100d02400408011511424040241c20005014401141c901610a013003441c1c00d041d484c10050f17087d188180d60310808110210503178150041d1940241241080c05090390003d076200c1041c0600340c06810050007240c4410f0005011080c001c000301d035002907051400d900c840c06030366112846019103203411107442d840070551140e5440c0b0815106001081c8602c10002c2c00d107035444080d41c80d4404030001e410320300170a82c65800c0d0b403a074001c2c0101545d0421410307181503030f4803840d25008022a200a0744c0c01e0203440b105103010320700101224500841640181141c000c090f40c4851091581e00300da0740d000756105411003154918 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 22256058 1250 22254808 22254811
    0xa210c090911010e010f080612071205010204180903081801020f18030d11070b0c03040f0e06040b010302040521010905070f060206070203030709060e010909020c030702040605060c070506070614 85
    0xa4030042e000358140e0350000d0216000441410306210010703c08032909540111030903404041101d0b1600ca003c0460070160a02046800401c90032803200c0c114814010150000c008030380c48030540c0703074a6402c0f00928900f00c80009900800144400303000c01c15a440b00b80100307643d040d109000500d0310000705031401d0b603a070060f45411849080070556480350314090120940c00050350810051404280c9071403915103a260042c46210740000c6807007994500200241c03005005002c03010011a031302c60f6269a0014412a1103038400d0307051002442d1079501c0b0b402034408403400a4000e01a40000d0301c9421a580451090044113643c0c804a410224004201e8000100040d0b00c00c525101d0518030000d08080c0000e0000d0190b42c420000c0c400e84a500103891411200d2510b0045004080c402c0101c4060307845501c0640301e80c0c000300f042c0000340c01c048000e003492032081b107081281070b5541051183c540a00580340360b07a80c220700701c00c0195040c0b0000805280e4844e0000098002022040010b03c140 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 22257308 1250 22256058 22256063
    0x81b041d0d09181103041b0f0609030605060d02100f03091b0e0106030203040309170c0301090302030c01061211090c0c010905010903080a050f0408090a08031204060b0a210c0909 78
    0x12481c8204080c060040c0007010040203c04140305650b4005403100851101410040c62070118800d600c080000c200703102c01c0684450244148810f81e607803c00ac01141e92030100341c4941d45400080b84c0d8918040d1209007401c2d5000e00b8480748002d02250940b020003081d0303c604103054a40b400003000800040034005002030461016080504100e041e0000240503004041414070420078040800d4101d80313650104d4000072004615008054044c90601a03c59007e40d015030038808040e0806070080050030f42d110466000700802640d030318202901c07083c410005040110f1380c403068000741c02c1c0b0056080d409800303007080614185072000c01c00d08441c1c408078152810395640300480e041651002070180c104d05441e0083c816400c0101c139642c501c00d0040e000600c0c00c103000a0804c2c25481e500b803010010482403041d25141d880d40d1030186000141210216280d501d040c9a141c1c0c02e1078010008800c1d03410b082c820189a007041c02000c4a008102d160645882c4601040003400b0310550145044061 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 22258558 1250 22257308 22257317
    0x501180b03040f0302070e10090203040c080303040f0201020f031e0f040f0e090d08041a06040f020c07030b06010201330f06030218040e0a060b0f100503040c081b041d0d 74
    0x218103042c000e041041b241c02051040c0060801d110ba00c8220841410075141030301e400683e030351105d14080c0c1c0100c1c0340e584503241c9800040204014009515400e400244c001c1c5c09032404080d0220703040f6124418541005408000c1c403189140c44081c01e0041c0c01240541c800f03070341c6456100c0b074108010000780e501661514003100204034030701d002841b0800c50895282001c5202c0c2c2010350340c00c680c402e500d4200f1014812418001541aa1180c225800c40740c241a400c41d915203041001d186c0701c0c10f0078003094a004811002040140d4814454600c841e401d917040850001e501042c3d507103075841031801e0100311291410010071071500c1c3c01c8507c4000c26207510016a60800420005600508003003014400c1346860041c1c000c001000c910760740c0c0d0710340c030880014558002c40c0004e842a256002416000504001082091a04200198000c500809021618651f40c1483c1035440c440358a48024600c00003554440760f00349504803603856030f403403000b17030329032800203031009142503c05036686c2d0008 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 22259808 1250 22258558 22258583
    0x3050106050103090c0302040b030a0b190e060c072a0902030108010e0c031f0204030c0303050a02060901090519030203071a1b04030b070e030f0f06160f0206010501180b0304 76
    0x40024440e00004080a080502a0395180d8491585020140c40301901072901c1e900601a070340e5041c801402000e50200c3d0200c40b60034591950100d0a403a0038842458524049070180200303c00a2030714400e40310100710900e03001c065542c010502e40040300b003022441d2003181c1e0201c83e40c00382c00d8040c054260745030016103030740c54041c0d000d080d10120b940c41003903508192086100c0d84c03004607140e08a510803041d0703486520311f00c0c4592030092045910191141109010205c01c06500c50300509210380f00f40e080b07540701d84980508078220f41804400500f5540042d03000c41c1100d90400e5010b042a01a0050380c3c14030040b41c59004042c6410101125001048410002252641d1182003a403540d1140c5003802c0c0740c1103546140c140003010341040103001c0321502c03451180e5001c000c0220030100038400e03a502c410249042c0c40c0c2d59001640c00f20a02502c0c035040d04180c500c25060594603040c1540104980c6c3d10300350041d00d1254400c819031866a00651000c904030314108011400740780f20b0400e80610 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 22261058 1250 22259808 22259813
    0x60d05030c0609101d1209030a020604090608150108030301031104020910030b090106020102072406031e061b050702040b012a050f0d020601030303020a020c04050c031905070f030209030a050f060103 87
    0x1211031761980920032545003e03419115441c00100c00300c00b41d00c071000166542c0d01c07000000b4074100881c000258884000100480c13610081d8000c0412185004103c070b50364040e49090141800c400d0085801e141d04c00d10042011076042c81e020300490102420052400c1c4042c1c02060019014014900100740c50312040704190400707480301801801c0901c0210700f070801c16540d1301d480c01000a2041c1d00d0b500e00c2c001c0104030100319849000110362040000e0120b1200d00c510308c00000c0451019600700c0d24100740c0c100190515a000411109240d403200e10b026015803c010040040c0d1990904103c22500099030140ca425500024030300d9050146a1484151038443e25054a440310f120480c0c01110054640301d80010720703d41500d600d418056110005014228601a48a0b890b6a8060b00385000c0c4040d400300a4001e601404440c81840500e1140c002e001c81503e00645a040c006600c0103891060203120743d025007502a0001c040d10350060341501d805d46000c0c0f008000044540250004004 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 22262308 1250 22261058 22261061
    0x2040f0c020d140414031c020f0d020703080304150b090903040302030f0106080d0503091501060504060f0806011d040b0a0b12010801060501050d0207030201140a020c0c011403060d05030c060910 85
    0x2500d42c1d1881e145507907000340c081110150195108480a066840d10000a659814466080549610707000c9921400708500001d40ea001560003000d000e006607213154002c4c41c4007150031025079802035407091458682e9544e1520480c516520031100569a02d00c46030b00c0d0703840484580c01003229200030f5031a2030450040505201070720b4030540e9243c2c50300e90200a07841000c00e0184165000d030030302c40d0300ca0740c030240c07070303509001403844415a420360740d0002082c003641040c0a001a0ba1481c2d5650556482c4a00160f8583c4c0041d034030503000c103010100c030400d141015922210019401b4102145071481e0340c0c0071a5180c06e9a8004050711440890301049052440001500405080c4020300c51a890a00060f225129010312503c62a8001130840309250003500840266603400f50078003160303d481c524210094000c0c41001c2113501541c0e0b141d140035885501d2503800c03c902c40c80440d1139a1034500c00c0005524000348101ca06010070301890340c840d8003e000340c5100e985001c001c1d10200d90030081400 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 22263558 1250 22262308 22262323
    0x60307050a0f050f060c0708070e0a0203040507090b12010906020421170306061605060106081008030415020f0307061407030e030304021e0a080a12030204060c060c050702040f0c02 79
    0x14001d40099400b044500c0e01c2e03481e400c1c111102a0b030b03c6031001001c040030074890b04c901880d25690b4030400c030002400060006030341c0f0499034402078a801300d4545211041c203a00c819036014140c0d910550050000780c0f2141d006414941c0f0003408035941c0601e50814a0039502101ca007913a2059020808000911401c11450001c03103881c1240d401d10a8907680c4e19000e40038a5003030092080001c000035249803030720360031140715548a0410b00f9140d0a2450520b90fa40006d004190004a8043c0414054840ca44e055003d0b41c0821000e18181410000d10340c40010889155900310301c6080380030807032880d0500c003c10b0914010130b80400c044699a543c02c0c100c4c14050829003c040c1b43ca10180380b580000b0003034a402540c1154031108002483e154200c0e00314a0b1059183d00c25007a0780001460140003036200b070f10030f105034807000303000c10415030540880c025482034030081091a50300400040c0a603000301d8a19040d810541d0501c540c41d00400c0889000b0310081301e100d40d44030100c860340c540400441c07 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 22264808 1250 22263558 22263569
    0xc0201020c06091c081009020d02030a11030114120a060204060903050d0801180b0d0b0a0e0105090a0206040308030a1503060605040b040501050609060a031805031909060804030806120106030b060307 87
    0x1c050880c6240c640b81c5030300e100d2013a0002000104004030300a0030725140194001d00010307a0554442c1c001e01003c00081d4026038101c0d00389072500c251044a10401016a812981e03184840c01e961286103080c00641d9070440300044890050340196000624184090000751401d592180d54050451500c0c51a1030b084500300c0060203d19001040000014103a02c03480d01a0704102080c1c1d80440c402040d82d41008110040c0200e091a040080400b1b040e440707003501c00f09000092045e42ca03500d0b456030300d90f052420040d4010500304818808117195400558100c5a041c1000584880c03e00e110312101d946608203d985503101c107030400c02c034907040c0a0b426682c0d41c11202045103524000005006228402115005900102e801c580c0107000c0d601415080c20205810710007494145030094499101044404480c101040c3e050000e0341b00d00c030150256600c0b071700d441d10075450b175441c181c92142c40288016440b044000e10400020003e010341c00045200d050044902d040540400d41001f1564100 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 22266058 1250 22264808 22264813
    0xe0601030311120711010f02010e121c0204150503060307080105040f0c14011d010302070b010e041208090606040f0b0d0c090c0203070203030904022d03040303061505070210020705040c0201020c0609 87
    0x2c83c4042007141c215444171560908100391030040001050340546a0340141442a02800402c900120400c0d401070044401c078818103441030281e511014200c3c00343d80660390542d0341204251525500480065030004001000c480402d030382c85440509682c01207504907800300d00401c00340200051403402c2000342050309001e903e034160302800240020b00c0010140c8003510420b103264090b901030790454034650b812183c0c0c1e840303035a1a551b090040b007406a4040ba00d11901403100040799116455080c0070340a141d0103000507854440801c0041d00c075250b40f080016a440d44a80354541d42c402107005128807568041101600c0c0000d02002c850101071407000359007082001c040180d40100881380c030540200c4005854410740000e20207404c0a089800040881e01c0c80000680d00e0b0600c0a90b104038400e03581031000c55258400300740350300c2102001401048081c810500185400c00322103403884000c2c8100c54156603541e000a058804d45c000300701c0540d600044000081100344051035010009100 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 22267308 1250 22266058 22266067
    0x106030507090203060109050d20060405100c06290a120305040303050304020f04020c0604030801090513030c05030903060c0717070f0b041a0a020d0510050105070b070c050102070b07021b061c0e060103031112 91
    0x108004c1c0b83e03023b1030a01001050352961041084950120030f20f0601341500e180c0191002082114140849032218410004084001541c14a1440c6034002c07a516550715400c003841d43da0262640d82001c0d204a81c030254035a40c81c0b03031680b0b403440580352844100009003554141070402034410701060300000903503070800301004520700700c40c6484c1c6a070641c140750503846d0700803c1c1003581c294050914800d9142c05150301344034070780c46280054400306000e000d0050303801050005446042c0315111000700004d80408071080452503507071100b603225014040c42c44415403451944040c24070102e0b0b641421590100c0c0c07540c22000b4911a05510026000c7c2401c08075041c20006003190044110041c01c00703a03010001007119215000409a40340e01c0f00081d52584545e02d01540000780846000c0d0052003086001c1c4550039030803072451402072000d4120707031402e4031210205c02c5803180044148008c580364202504408001c00001c0c0c02140039948910700304810080103800e040900e070052071008010321 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 22268558 1250 22267308 22267319
    0x52e060f0f020106030605091e0d0c02011b050a030801080c030312040f030903080706020406030e2d01060b03090a03230d0b0a031b0e0601020106030507090203060109050d200604 78
    0x150480c450030850900c4005140e100301c089000d0032094000901075820f0400b44000c8210014964540d03080b141c0307294460404900140e03aa40740090070020006000090002c099401080001b001041c1c80b41c2c50180705c0680e41302c407403414096042c1200040e1080004011044c4148080c0850b070f40c0c101c014620707208104040281082000d4070141804450300b0400c010503000702640c4000311703071280700c2d82d42740c174502d040c90b2000350041d205280100707040050f64600098003042204d00204100b503e107134804406080e240042075074203180004d965803130038049101c4075544055407082540000500d044540d61400030200140400e140d817030340c01900d40842c0000402410b41c1c0d42103208070000249003a03c81c000400d03200c1c41c0d60014025003c400000f9400000c4034031402c2c251004101c188001362140c000482c00c9464901c0050b0141c0c001c0d090920800c40b40c0c1e001580c100d041450500045071321000010086901d11204131103002c000c2c006201e9540995404000c4400304544560402e440d05 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 22269808 1250 22268558 22268567
    0x20304050402090612010303111e101a040204030c090e0a02010507080a1b06020a08060f0a03080906070602120703060e04020f04052509060210050106051209030706052e06 75
    0x50260611070764011a8001d00c0d40c03039410070344d20310020304191044196542d0801074075850b98a001400c40e400b402d007120a41038800a4156120003011008102d5201d95410b081e008220000c0c3c0c03018450310b190703850009903481d400640051401456408030161900241c4011169010402016034000c1540000980c1e0000203803428290442c000f030340c0c0d91102c0142202c0d41410074005c083c0014507030002e0020721140c2c0e409070031b041056813100803440d203401041000c580e000c44230155020f803000034140001104003020f040c96820151803542400a1075440c807050742c101c501c200d442600c441007001555641070040500404241c840e00740c050070a9000301d41e000c1041000e00340160348a1020480010a860b80c0090840400b4029103034500d04080080500c000c070300c60301c00103214220710100d4400d02071280e6812030380e46841e494949407406810003c0e0000045c40e02500780800d115a031b0200d4454002c1c14425911100c010b01c580c3c0f40c5039032181883d2080a030643e04180a40700601c03509170030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 22271058 1250 22269808 22269817
    0x9090605031c0e0301020a050301030501140402130902010216060f023009061b010605040c02010510060c03110106030c0e0a0209010e01050f090a0e04020127050108100305030c0606010f02010603030203 88
    0x1081c1607071040c00c0b501c0c1081d034442c00001461605980300255031082280c0c003201444c182ea1181d4000d004000d45090744800441054801070b5018040c0d4030000c025a00562107080c0c020701c18010f84010408601c109204150280d001c4008100080c45021000e6410b0006600303a800001c08440a052900e090300e254413556140c8898000c0006000b100d0381c2d807041c0940d58801100c40c060041c0c2950b9818241c0600481e00c00d580c081c80c2410405e010090040c0039452103000c418182e6164549030181c125280c1c1d0020905030140106890040300110003030055002450192120b042c805103041c80810301d0b0140203005942e45441409814440da80c00700c034031b41103807200b40b07041d94644607041050503803803060001103544451075860014124642030132140c4600e00076243c42c0e4462900e81d442c1001c685442c0c0009200449810041c040307036014410042c0c1001c1459030144406480b41d84292840c0c5c049035100540c0e50003034040148540c0e00c10042c1180801a02c020310441d491660f002c0c1da40d028 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 22272308 1250 22271058 22271083
    0x10b09010602060f070302040806100e060a0506031303030605060a02010c1e020604320609060f0402060301060c0503070807140606040e0729071a010e0f041104060306050c09010909060503 82
    0x818000c5100c1c1d0123544c054442001580c0f02801c108503000107104007071195071466040e000002d4210b207000c02c4c0c400e0403a640a45010324541c0d80c0340c0441c0c00540480c00460034180d0b60b40020070641c5600001d003015003400d07000062102c80c0b5050290500b26280c0124021111542c800400507034082141500641e00800b00c2003681c559218280602c004084180700c0700c030222504290080c0f0028000c2d0244400009480464441c001680101c20f81150003075080001000100320fa50f111725035201540307004105582c1405d80b02e80d03805160b5408aa810f54410007026a541b010b00750500032141c000c2c2c4111001c0003080c844042407a05c1300b08600c6101d41c8540d9107901503021181c907280100301c0c3c0000c2d42401ea40e6449038130740800e4451200d4241940094100004a1951900320481d405804000c0c0d4504443d581d42c0e0704c1d00c800e808120102c680144d1200c90001c0003030528000e49000301c255242d050348401980000501c0080300f60710200303420b42811010001603e01203500d0700c1c01074 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 22273558 1250 22272308 22272331
    0x309010e040513050d0216080a020a0501080907050a0e090d08040b150303040e0106020102130f03031407030c12030209040c02160b0702060c0609010209040b061c180803040b09010b0901060206 84
    0xd650140000d0050346800c1c3c007401d5402006401d840680d40800e00300200748003560350703c011548494103556600b1118a00940086d4120030910580d03015520066000341041c00701c0345411788843c0401c0d044a40c651050703d081810700d00b0302411280038812007800b07007041d10f064000307440c00c1e072070395100c1c4600609008840500c4160041c540d8070300f401190702a008503c070880e05540e40d0342000707000754801c00e4641810240c1c0e1a021a405410f10103442c103e94140e40c41d0312084a440f01242d0007984412011014002240c542000180c1510000c0e14400e030152801a150300952040c48183c400d0072466a0454102e080403000a40d1040c0280b0151514070b0080c0707480b400c491000c18034500c1202c00f1744102d80f041c2d104029a0000540041030705d81c800341c50900408100c0001d11685019100030b600c1c1000003682044001e4601c0d511441c40000d0084200d040a0000e440303142807a4070a84e0f094696004000c20000c0380e00090080074041b800a07510407002e03626100c002522500042c01100564 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 22274808 1250 22273558 22273561
    0x306090b1e03031e0703080708190b0103021903090201030501120c0314030c06150a090915090302030d0908120907030b0403050304260304020114030114040e100903110f0309010e0405 80
    0x42e1400c20548007102581c8018401c80740700101005000e80189000301c1c005038805002441d0648203401590203001c522020220300c01c0318104a00107030240c00c8410341010350030b1105800c8652000480400710500b0b460004141c0c5070ba0000400f6548140c2000640c0000e00b2490000a80c0d0f603a4454101c98200311a03038020345042481341c0c00d40c49080301e224511302c100005d000c00c0c0d101981040148170021514203005d103640343e2203001552074480c406029000e05154010031040d580c4c10903406a4070a10680c3c0c6003040303030a080d42c21034008400560700e20a012030f445605460f00000d20342c03c481110000c0c00120325644d90f00050103801031000701006030200100c0c0c2000700d440d03e150710440c0401c5406210f400c00454201581c0c10407035050340043d24905040c40003004010450b4180c4000d40341801c9504450414000501011000c01440c3c2c0714261007410000690301c11886007038440d94a840105803c64882d502c3d0402035000610160010012904941c2c0c021002400050782524081902d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 22276058 1250 22274808 22274869
    0xa03020d020403020a0e07170f040204150503030c03090a0f08070510050f03010e160309051c05070501021207111603140307020301050103110a06031407081b04030609030306090b 78
    0x182c0a9580001d40180c4103007130100d4460000b0204c244200219030750482488045c0c0c000b00a0040e0a444001c64594104080b4001d420a50003a02c803101046214803d44c0c0c0d80c440111740340d544034000d080c10782e030000b141d006924500a0420001058a0ba041c41389950034a03226a0f00e50150340320305445512102c101007034040c001c2c0251000e0640050105e600c940c0d4030302c0800201d0404441c102d00000b086034446c1400d40c000c0c4605801150064020b20070031a5001844442c028018201410701100b40002c40008500f40010000003244800344101420066030190001c410b41000c4a42504a0340e08900c21404040042c011203400c0362458826804041090b41184504200a034265080c10000710a1221036003490f1002401a42c070194140d0745c42401710116003d030210000c1c0e00d07510321f01140c1800e1241d10032580286031403440386680b5000340020512503110b98000c070703202921081d4900c180340e0140f04000061034410350078407000c219000041d0026001c803440700b45040810208440 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 22277308 1250 22276058 22276061
    0x3071b08070503070209060d0f03051c0204090605090907080c040209150a080103020a09060e0103080702120703050c0411030105010f1815030506030606060903030706091109010b0307110c0102030a03020d 89
    0x4580e00300e4062980c5185a040003030300d990124030300342d015001d000c0214080f0706008c0081001c02c0e0f003000d07012000301d1b401d40c0c2c12940380d400310701000f06914010041d44501c0290340300401c004c18109000080b007a20b4907081c45850000100b15900d20b400089017081040404a050402030008842c01a5640340341d07070004015aa85010031003034024003103200252943c03c074402ca4144d9000300c40240c0340703603540c20303502099510b60700800340d60341100f00c0100001100000545800c1384003d0400039244801d048484c0b40c50015401036515a104003c2140107040511a031110904010121807444d070400c0001390101404071020b000304180203c0344203152801e24503000c05484500c0301d41d42171050440000300a8042544c015110340580c07400f05d203140c5410300032610154009000355080960301c1d2138610040c02414029564045a42d0340b0110780c1d50380c184524007801280c5c0d002a203030b00b02417400402c07800000c00722044543c46070b548152036a800100303866043c2a540740160342c0d20780001c03030b210 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 22278558 1250 22277308 22277357
    0x60903030411010c20031b0102030a0c020d0f08040614040302010f0c02031005191104060e090a0b09010603050711011401051219030302090112020f04030b07020307051617120307 78
    0x740300e008031082c0c0c400d010b94030002ca001c82c51400c0b4102d40361f5815102801200e900c40d4402c050150307108001800c0140d0140c900610143d00041c16281004201c6d06e8a02040c9220207003240c0200e400201070050b503412403041b541549a02080c10b05060469002a00c0c1c00c544a62003c01c0c400c95058107021954200828201c40004540138802800d040100c1840030700c0400300c20610605100801140c840010b080e1400c852903a5202842d160b4a01c0c140600b03d00094080e0099a80704c151008250f290b40d02c1603402800c8030b50300003030103140292004090301b138013228030000e0364107042124608180b4230044a05613001120707404040c8000350649490100400e0790302d4924a403d800500c145609903003d00421070302a20f8112501d40d000564804030310583e009114030000c14807060000c0345c1c1024140340e1000560044030f2a102581d140c0702e01d409100c1101d10134500000c3c00601c00c0007014a6200c0204003401c00034662140b440000c4001f0f4000284040c08025140780d0741508403600f140c180 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 22279808 1250 22278558 22278563
    0x30304050607140d020105060312070b01120f0606030503030103020922080c0712080405040624180b0d0608010b03030406021504020d0f03030204031a16111609060f0503060903030411010c 82
    0x100e40306601311002902900040314124480d004801c0044c0c003540301407048030407969205041c100e660b0f081208104401c4041c09050b1041d41044a00c3c0002480c0381c1700340000345000b03400035030701d030362442c4100141c1e06c0d0002c3c180c0e80a1040d20f492100140c150f40c03200d4060551281042c0e032100000c04129141c85002d03400075203450003848a60084c4098800140141e035015107040c042640c55400507445023408000d4400b00404c607500c0303d80014815048940c1c4100c0c1306103035002d030590340e02c180911342e00595003003e00c09546a10130411800248600e080300107065010b941001d203005006500c8065000003e0070703c0040c2c60010b011940d03481d01c003104150344004152811802d03801d00a000390018001141e0201481650a08004901d0100c40c46046140d00e9402e4100d00d403034044400c080703540d032011400d10403a92000803405000710204060540204c1c0080c02c0752400d14220282012903008d84c0c001e81180d0140100104084100c87c0e0203a0001d002484c0c01d001c101c01281d0031003603030b0ba01 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 22281058 1250 22279808 22279813
    0x40e0a09021201150311030109050a030e030304090509100b120c0609030a0b071d03010513060c0201060801050a0e06060a0518070207030f080307080709060917120f07020a060305010503030405060714 87
    0x1005061104d80b6450400d41303016682c08000c40c03403503800341350803a04000702c0a0503c0e8014880180001c0c455a032885406070090f00362410f05507281e115005a80c020f0b64500210740055010702000150f81c802c11018040480ea41d80c10200c231800e501c3e4881203d0308405010f1400000c092403141c07420400d003161f999002005030442d00d004c2c07200821580191101d43d0780004c050b800355546280501816024030b40103415201c414000c0d642c1d010041a0052001040d5500e070080022001828425148102c803114004140200c00312150380c10920f000303000074451f03074202200740455150043c19070000d0a00c202069a20b4450400a0349404602c2e0710041c09441b5101080c401c000c1e80d03070040d6020381e605440c1c07560503403200380702501c0c5c494039402100700041e1300c0d40c020030943c080c002d544e80e01c00500106840d41c2008d07a5000404542c081032040780580e40016120045041401e0208002c0c4454903042010b9418000003031f8503071045220342481030001107504010f0190116040c40d201280004 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 22282308 1250 22281058 22281071
    0x5240a050306090703020a08160905040219140109060302030c030601110a1718040e0d0305100f03081201060c050a020409080909040501050f09010b01080a05090703080703050d05060105040e0a09021201 88
    0x1001341d4600d0f072400200c0c0600d04031000080d042400140e4111a185081d802031184d60800610b4002000000c00903640704404100448020084001c0c0c4000341010301c07880b0800300c544d0000076203200c4660b400502014030400c2040911460003050320b400003002d103000840e44869036000c0d45009144040036010404d004512003a20b641d0000074002e11030f503090f001c10021191410081101c0032417841c055940c01100004a04c2c0d4841da000355440090090354400c01d03500c0e140054a440308a0700115035180c0c0019107658804c0c10043c6950041015203000746140ca2903994041c1c8641c01d21000038026620b84c0d00280030814003000b507407502030000e810210746150030308150340a480162485800d59404102003500d545041c09403c0c800302d03043e15402c40507255000d4940080c0340c0104011500d0050311000700014486000400d0203500035602c160f01d80d0820403c000868101404050500c1030820081140b031410700c42d416401030120800064862080c0040b84002c0310f85010300110303502c4d040d1b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 22283558 1250 22282308 22282321
    0xa150b070201120203090c040506040213080102030a061202030d050a120c1215060512130819080105090105010c080d1b09030506010527070c060c030507110105240a050306 75
    0x40203000014000d80c0c030003c45035440c66003042288000d4030220155002000a10b00d0740c202500050f8005e2000b82c030051426803004052803510910307820180c0a40d400000703118042c801402600c0203071800c0441c1c480c00000650002e643d9030000282c05041c0040410144595405041224280e000244090140c40300c1140024516010b0007440903a003454140880350140c0245048400d541e89902d800b407031b14003c40c01490004800410f000c4c92020019400e41c0001d0640c2c0c0604000c80505050f685180c03400d410291074074034140c21680c02100e581c1c0042046a070b001000c07000c10754100046654400400480d50098035011244544c124801000111200d6001c4281c0e81189d01950990350a17076228010402c1030100401817084080e42c070482c21024480100344c1c4e680100090030444c840145c0e958558003965615400031003c40c0e6079100f0000302c16001000c450045407000020480ca04e4084282100206101003034106080c13a0341c400300c0e0503200d000240000c2c101c003c00b240c040c3d01e05035 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 22284808 1250 22283558 22283579
    0xd030807080a060f0515040909061d0d0c030e03011503030f271e0e09030304120c030f08090304090509010b0f1008161704060b10050c060408030a15 65
    0x948010340020301807400102c0700503036407280341d09551880400c50800c525010401040c04050611000c1083d010803001503418202d2003801d1802c0d10600000c6070342c02e507048a1500500042c40960320a80042c0311011540383c3c481690500d0b554182070030706000c051040400d004211442c142c040700842308602000f40342c0c0003500400c540d50903540e0b501c0e801d12001480081140d1501c0019000d5010400c20302204c1942043c10b550410110f0441c820169541c806400790307071f000e484005083e0000024841400440303031400e91080c3c07050a000e102e22a490f94020302c40a40800d100c003c2142007000300b0b650700360900484000b8200180b0511507810101c2100d8000c2c1003110701c1611940c034100c0c440200b4240a42c490000c0701e8961941d440a640e08000d41d20940c90800030b03402040046240b12120501d0b00300718600075406514000f40d09280d540c103112144c02080902d5080c804280082013a2000014051750302c13070791140c4c1c5a0b440340c440e01c00703840150040d4400310380035000c8580d0100385030640 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 22286058 1250 22284808 22284811
    0x513050c0103090b0604020a0219060614010905010503040f050106052815080a0515060d1b030e070303140903060117151603020304151a0108060405130f05010603020d0308 75
    0x40054500e0180c10000640c111890100010800000354001910501d050740c0a80070048042c015564011910140c1c05494080b5600803220555030389828003100c48a000c0002e25030360b080c00c058000600340400a4158000200f00400a011180701c540c2044070a402075002040041c0002020240c03501243c40e1669600400b018009002c00c0002603000c440402c44210480c952500b80154648100c0700c40606401019200b00c0200041024002d80b40c0500800c290000d1490003e0840444840074010585c21903442e000c00d4144001100d516801050440c1200d50508106040d8454204800b400e4068842d080794540207403800010030700309518a21400c8a4004103503841601c480958100030001951054007aa00300da01c1100da00b80070307078002d64203c3d0040c5003c0c0c59054140341400e003580e2600031801601032070701461401550b04410b0701074010800712000e10051400420a03409100700e25070140140d102a00041c1c04d100d801e501c14005940c025003894042200c0e800c000c0c02d0283c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 22287308 1250 22286058 22286063
    0xf0c0306060b120a020403030f0c030c02031c0315052d040603080a09080f101d0109030504052b030c03050d02030903030f09010504030914030f060108071707060203040603050a0f0513 80
    0x720f01c0000b030038500684201c80c00e80f50326881e940450f400c00c010440d1721800340c420441c18007044a40716800741c2d600304540c0c41c0c00d143e8082000c06560780484003c0a072101c480000b5644800d080d0140000d554600490301e0b00c01500703259841b4900008581d150020800c1e103031640140c50954040140800d0000400c07652102d92201c10b05c99984030b40d043e0356286a42d003540a150410b05003406a41540d0700100c052890740000a04c00140c5280304030700710b90340c00c0000c402107900040c042005091114010303508400940c004020801002c0140c242282c484e100101000b07814210001007501a400b900c401d0504610111341340c2c6450750704603a90790700940300303850f60324450000160251414003803e8490f90307040d92006141860b121102550a048400190b85400b805101c0d001780300d0100040d81c000d00340d0000410b210b900c0c0510300e000c0850303940646070341d039003080c4014032001d50000101c3e800c070341c028503001410f50380d4030500800030800000082c035100d0a04051040603050701c5c4041c0f10090 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 22288558 1250 22287308 22287337
    0x201081e010305070815040c180204150807030c170c030702030403050a05030d1103090c0d06020904090605101d070509041b030209010e040b0a1202061b030705060a0212040f0c0306060b 81
    0x84006d008200074081218002c1c0f0291040e84144645a0842440c4c02081070400016080ca52911001d61080d040300074880b000940c400208601c842c0d050203601e000940f02c2c1000e8420001c950030b10720120f000108040704000000000c200d00c64802c10070ec4000b15000016214081e4003407800c5612a031220501c1d03251340c1e050180003c041c6040c0e0044034028107964004141c5010f4a0f4148075411402040c155426036091213011480c0c3c40c0da0050202c0d45204403000603581c42c05403544404000d843d00301e100300d40c0e48141e00c105542c0d01503c003140c01a209040294449107614002005452035034100e001d100c00c00000740319502d405402030042180242c84800400031041c061200700c401e070281542d40001c1181081202807682070428141c640068025442d209c801031351901d070f440080c00d0301812507100080000034441e0a005a50300400b58110652401e280044c40c100b400c4000f500c081e0021660340c450b00100b00c11600c5140c010f41e4800420b116169648004030069040040341c0203025 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 22289808 1250 22288558 22288573
    0x804080615010201060b040302090a09020909070302040509120a1b05010f0b01030f1e021b0d090e090303040b04020609060c0d030605030d020703020607080906040e010b0703090806070206040201081e0103050708 92
    0x10741c018005c00c4259a8660040d03414940b0315020800e80700780240000182c107980d040d5200c0980c0310a8803080c07240c0c0c000e070020160a450b501c140401c0300c900901162080d0032074103450081500080440d000900c1d18544182000c8018100c2c2e1420403400310010403640c64005070425298080e0480245904240c80c10064140d100503d40191901c01c240170030902c13001107007007201c011070358060485140341102c089000180001c440b881c0c411001c80d410b01182c481c4200f0803440801d00c010a5021103050080e60550405941e1030050803005031000340310b51701c0031415010b01e0300c4050a03541d94069480c12500030200d940c03005401030586002d0f15010313000d03001c04c0b03c3d20346000003543c01c12658007514691600065440c0c80c403941d003107180541da00c00700810000580d20300c0f011005000e80003802080e5561080b5140103400c4125551089040360040c1c1d0802500b02e401054440d03220b41c080c04c01d05401e5540702030b12a510340d00c6c0f40c0c40c0486040c400c1c0c004000e00400096060a4400210880e00710 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 22291058 1250 22289808 22289851
    0x30d0c03140105010806030d05031008070902030906011a0306060721030902091605030f0a0b0a0603050a060f052101020405030f07150e060d090309050d0b040b0a020301050105070311070308040806 86
    0x255442100c695800d54400008d07612030501c01d40043d43d01c240c0750380c4400200c0c0e403207480300c600304140b59101c401c281d41c005c010b0242414042c010346004140c038104003c0d02075000841e1035864000205124402d1001040100c00e10414050b03d1062058500003110030800e101c0011700140401a0700340c0c0180101d0000810004400160841e107407819180c003415582d406904000510006048031003150301c4110000054656070300d50300203094070707403000b1a03185055034820088800f01c1e40245010f100c584401c000e25111030310b81c0b049a001c00d07956840c45103661400240a84115845540c041c495003800f011018000b05041d0302340c6900881c0e80b490100851000c454542001141c154010300c2040414401d80e0140c1c000c0107050b1081c1043d0000301d64440029000005131401541c07000c21140400003009070f13020b10340d54090aa00421825541000d000030100d02034200d005003417004486603a02081ea00f0000007004503804000669034580311a982629007178280e450724451244200107014 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 22292308 1250 22291058 22291067
    0x3080f070207050f1315140a0605030a050411100306170304081507022505190806060d0501061205030702030d0207060206280e07050a060305040c090e030d0c0314010501 74
    0x1034680d40d009104607410002000000b08800340f886500500c0c1143c240c6289659010b06001c00141c0f05a4807202840c03c40703c400b0300d80480c2e01c498400d040d4914207100180d08141580e030003034403407640011165103030302d4130103c925904801075a1211110850b070710b003113902d60003003400c1c2c03440000c4100c026815041c0302583c1c0d0041d8050008c09821440100800341c020900b80d42d4800047d00c12030f02d00003c02c85404010564990003066401c501500611007810100301e40d6601c89204180c454030189044035003a01c1d100081e1201e4402c100c0d0004680c00e1100035084000640f00a80299a29581900d411562640b00c958220b0003405654121030101d4008a0140e0455080d60083c00c202e40c0c4600160340c8100e00350034902031110002200030381401072803003100c07940091100145000790414040205178007056002c5d0007018144820800015180d0390200100e58a14001040300c0030390506050550080b002c0b0035103024a401141003e0341d0f41900103203107400aa03e803d100741c0c0d881ea401100c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 22293558 1250 22292308 22292311
    0xa0f0302090a150c06050708070807050711010807090503060f0a0b0303030103050304050609040e01050702160f050d11010201021c0b040b010c050d0e010e0a0303030509060105040c0c0803061504090903080f 90
    0x680c000704203401004902003e0343c0b6484400d1003031802d500d044d5841e0f0350303140440c2e5080d00c1402c0007403443c0d000c02c074565805c041102d411040c94208a41003101070703526110240251594681000351400100351414001c80c0c1d20800b4080003020356400b89484a001d100700e9208540d0000503504007001e40f100c5040100449041e603803c60080d502d014203140500c50a548001da1164025a40e00320b01d8000c1c4800703204540c003035011079010304510108419000e191201030381040b0020003038030400b00300c5640d07041450178215600180482c4150080030040c1d009000d00c15403182d1150030000b031440702103010b0b88410820141154100f1101c0810401110341215840c001405a401444d840c880c0a0088203040d0310045c05142402c00c80889002040c00000b4580c4118042500d810034042000c4040c00714a0152200f903604200d01522184014009241048060004000000441c41d07645a9a10300c0302d8025000081d81d51355076a4100784002010301010a400040c403000116150540412a09 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 22294808 1250 22293558 22293577
    0x3031a10080c071106120a1d1908120c13140a050d1b0b0d050109141b091507060e010c050906160204090308040b01060c020102030318010f0e01020a0f0302 68
    0x5541ea640e4019900b80d40c021403003616030107401c140020940e95480000e020b80c403010118030b11036041c4010204151402164030146441c80300340c1400c9003c80000303181100060201d002203460125013024001c503c2191140003038400da0608101d40c881d1034030010099801d0072010900030640e141260003007688c0650a0507400074401d101003100d464426160340a60780940d8502955406078541d5101c603800f5035200501c40c1e600455010342002d441e218040c0103090004007840100103c0c0051482103400900900114810840301c00c590000703807013078607101c2e0f42c0035114400d1003490301c1c403020954000c0c04c0c0440d030aa0070321f040814200d10600a00500c4061525214285030f0b11f0420001550490304c2464882901c40b80d6420140e074850140411041c0179440380015400c09040c40610b444050f0041002d20550f266046c0060341c0c000100c03603000c4065010b10040040018400340909070024100c0c030210300349601e4202102041d402000c0c0ca20703c4d51681007256103181020f90590041500c1e1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 22296058 1250 22294808 22294817
    0xc0a021504060b0a09151e0302040203090a060e060103060501240e010309080414030106080f0c040203070905100206010905180703020f1909050601020709140a0e030408010903031a10 80
    0x280000c040403038061500144103070008141c5100b01004540300c0c01442d4071030b0400a807100b90812264640d41d13194000707007505481b0028803c451282070032450420b1300c402805658000000f658081e03003441034a03002c0e07500c0701f01401510a03010860755122000e00055130b51a1400000103981c01c075802004030030405800701000200c030301750800d43d80d840038210114141511002c0100018080708001c0c4064101d80880109554080c3c0c2410f0850b051038100021035800030194031111800022120803a0000b160090381c0ca90b03e03007034101c03840400e50b0b100d15088110008200751098010034103030f042e21085003003041260350f81e022034100c00b008029184a55009000244054103126800c0080500d028080b0100d01c0540246581c80c2021b40d84500b00b103940d9074060000c1c960341132007410014422100300307221074120828007140c00d10003e001210081d0b40d481d0040161041442030b6030003000c07008002c1201e5046400d0140c0580040c541c0d400ca0076541011508492404484442101e00c10f99117 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 22297308 1250 22296058 22296073
    0x80c03090a0201080a0e0f011506030e070b0d02040e010905090d020d0c02191505040306050a11040b0a02070e07020c04050f0903040303080901020f070c0302040b0f09060f010302070803040b0106080c0a02 89
    0x103440c4c034440034001c0600292100798404c0c6c400340030800e8000c1246401c0000a9550707403a00300360484032480e04034804060400301d8880701441d00103a81815075118008056440c0a5030903034074001d10481e403280c240410315900010310b0701d01c0c0b42e000e10302c40c604102c251000031721401c10490311040804aa0700100317500c828658090304041c000d100b81d580c1c0c0c001c807251481d070b00e85100340103a01d052184c0000141c0c00080910400506004068014861007428000300d03d407030381420428000d0f0301a00141c8500411008022031081107040001c1a04d400e00384214282454020344036002412111b0155081101181500100c1d03060a8400e00f1448040d6082a01b1035030210f40d00c0c00042c11181c0159000d00501040043d40303c002c2c01803900c1981d81c4020a03145106000075510340076101c901c0303103071a41c206401c0c94843c1071100364003a10854541c40c02c0f13030501006a0003802484000b45c180c59002c0100003c0144804103a03040e075480b52200c034455940c022241c0605e00c680c103407100040e0030688 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 22298558 1250 22297308 22297313
    0x210206030a020a050706090c03020307150e010e06120f0a1107080d0506010207150807080106080601090608060109030b010905040c17070302040902130203071206050d081e0906030106050a080c03090a 87
    0x5001d09405101c500e0f0151a00703d0341d1b112003085e180340610a0310740380301ca00400c000710324003040b10300020441038281002409420724054407881150074405c0c14006510301589069850f2400c5642250701c0c02079101440c244a09802c44010341160318031350f010329001000301c10030718500540c1c1200364071a0080345002103030f1141501424015251034154455070001162002800c91a400048415991111a850301c100010008207041e8001014801c1c188180181030343d1010103803050b07840d1030070a403100e0349032000125800e01c51a8805000141e01e0f90011580302c43c190006802140a03100340750100f500e032010100030528400d9507455650245404000500b05a08140030f01e60006040b103203070304083c01310701099034000c03501c40000490704d01e40030b02d2400340c82c4103c1010301800c1d83e0700c0803100c0c07565a4040303240c4a500041e0058113503c003850984199541c2c102d41c035200e8098005038480d6580c0002520700d410a03000030001c20b06590004d0440c0d400502928803900024000346011451034 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 22299808 1250 22298558 22298561
    0x120304051207030215070303051501020a02010305100807080a1a07080a0507020c060c01050a0614150c0102040305120a0201180b040308040f02030123100608012c010906210206030a 79
    0x720040619802800c50001c00340e40c0f6120358200403000122400c0d6181c185150080031144000c128601903260003400d0000b07030740e00240070031200340c0c203090011741c681f941d6140e0a814034040e07000b8a502d11401001054512001c07850000c80c1d07101d0818805200018500030030380400882e020f100244000000426950480c0c0000b50000c03100d0042d030b006243d8800101c0c0c3c41c1d070300c080f40c0d10429a44031024000024850b10500703009000803144d0f4040141c501001401d0382c0c020030308040c0166800300d0060f81d160002c1d4100c80c000d55001045402c10306511141c01015008040e050b030240d440c07c6070310b03000b08203202400740c040d551002c25400c0c290340b6036800396903002e8042c000b0386845015000c0c40e030058409200ba41c50304400c400c03041207141d00e055940f880d0804000c150204045c0305000400002e074002d28864152400614191080d01c5409014100344500355100d402182d0b00c0c800010304050542d10840c01e071031107880384c00d508003070001d41040a200002c100030340001c0204000361121025 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 22301058 1250 22299808 22299829
    0x100905012006270601170c0405010506030a02070303180605010312080108210d060b0d0c030902060901030e030c0313060305060303070210050f09040905010c0806090906010b070303140708040201030b12030405 91
    0x202d50036150f815000c40c1814034224090b00007102c10002c2c115240c0d403e050070040c1c01031680301100c1c10b020a604140c00b190241c0030140c02040c88035008904141098065000100f8040701920520400422410400041d1a0a00c0103652100106e050880501d10400c80c0034180c480c00720003080f11000d8400c40380c01e540c520118850f5185801d0003901c80001072030003000d00409224100507266100d4110100c103c1c0ca07103641301002c0c1440c08003008016121103055940952090800041d1400d002070300c20b086100d24403804c0d038140030008022210f2381d107444410041c1c800b00d5508000c42c2d507d800074140d6900c00d0000c0603512000d00024681c0c00c62089000b050803219032103116050110100104054a03042841240d282c0d44a100181200f036001044a60120049465070042d05006018a4891704103009410300484005131040034580660408516408a444030f2415860104001440d07810180c1d003c074006030400d503421a007481e00b500701c048032903911001340d07151924190400544049 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 22302164 1106 22301058 22301101
    0x1020c0108060f011e0305090d08040206071209080304030f02090703020702100809030f1803070f08031605010f060305030a08100b03040f11100905012006 68
    0x203200c0d20140d0000b070103503480751076601200c0040711005001242c840f18102c42d0003480008503071690007144658440340039074050381e003034180843e0025401c1c0c80c042e500c2581842140089541d403008038615a0072414900301040e0f65005950640e0050b42c0265002d030003511000c8c083d41411403901d40d100400386011403410710301e030b0300245004012040c1b00b000c2001000000b00114400c00880f00301070b81d000603450b21510000d00a1140d8100384142c0e5010b4000c01300000703000c1c2001038180d030656442034051820039800340005c88200ca402401a0350b65902c0310341c006680b2000348103d030081c0d40500082d43d82c030081107030040c16080300a0803075100000323030741c200300400340c050300079650456440002c00d0142d200604107403d1540c07072442040d600816540b60395950780e802040210481c3d5003a200c10b03406114400208600c03901e9100007103140c4c4c002d00002000308580c0001d50741c9100 = true := by decide +kernel

theorem cover : BRFrame.Cov 22122308 22302164 := by
  have h0 := BRFrame.cov_init 22122308
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22122308 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 22122308 ≤ n) (h2 : n < 22302164) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
