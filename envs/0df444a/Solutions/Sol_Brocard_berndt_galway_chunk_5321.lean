-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5321
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:29:08.517768+00:00
-- url     : https://prove2.me/submissions/2d6aec18-435c-49da-8305-07628e15780a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 956834532 ≤ n < 957014388 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 956835782 1250 956834532 956834537
    0x1b0906030606050f070f1203020306010e010c031710050a0f0f05010e09011505130303030b01091a120921130b0310060503070207030c1412010b09180109020418050607 73
    0x70041055a8210042e940003072528003450340e8410680c030784903100c1100038100a0000345401c0c036403890700380c1c1903010390311450080c0ca41c80400149640107590301b045850b802000550302c200030303061000100b01c4a40d001009602d20660813a02d880004141022a42000e550f40c400baa07001c10030032603100501401041c00307007000c458003982d00010643c2c500701406501e418504c45200404260305c12001c640401c3c413500d0309030065540301e00c0c1c02070141c0040c0e6440c0d8001003003c00c0208420442c080602c90005003000e10718a0503500e940700310400400100380219501450601e4804119801c009060040300d41c41c0c0746640c5c0d451303400e01a24a48254210a58804040c0104030781072004078034040a443d1141015500d990f19000c04a1610405800c002d01510324844c0c0061508c8214112014411080710b00e201003d00981c031240c200d403103907003803030368840f04034000b044008865000420203801d1400001c02c00000c140c02250565010000b075800d544c023842142400c2c801c0910900303403c0704051 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 956837032 1250 956835782 956835791
    0xc090b04140607050705220e060f0106031a030d180902090d030e120a0308220f02090601170c070314070f0201030513050604060c0e2718011b090603 65
    0x944035504010801c003215008610000d03200042c00801c200c52030040c0401043d0078180c512441050065600909080700c0c05802d040c903402d2618804102e10f4420b442407916518603a10300102100680b00340c44406a40202010700b84001d03880501c031000520006485003401c0c4041040700c42071540023940100e00480c8140007803151035075003001d4494200d0301886c01611020a00c80060008a09600c80344094850f80e500c403810160071409041c8140780380d081d100c4080c10048401400c1c425400d400170034588070204143d00514008411300e80241c418509041d070100800301309131800d00c0a07914801820b6005c00c2003000c0682c0420850a84069034900c1424290a42c0e50300c1003400c00309800a06240d102d50025800105480611524982040c00c807a001e01705811300f00d00a015841d500400580c5441c141ca805051043c4442a00c800e103660110004820140003469440081c114920101810101841c440003d0103145030714106080754902a00f030914018003051010352180c414941030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 956838282 1250 956837032 956837039
    0xd05090c10020706090315270201080a110306040f1b081501090608130303180305090a090b010503070525080a08070e1e03240412020109240605060c010c090b04 70
    0x20170076400c100e82c2e200c00b041604c20380102a030005840c1400703865000d110800c0400842209010072400624001e8036845ca658907203580d054180c3d0021080c56a603a00d080010a00300d007489d5110200d58103403000002130840355900214802e0700f40b03003105000250341800707101e02c41c0c02c090007405041d0b0090a18103031107071400402074001c52008080b03040322050986000305040c0240c00601140301c003501034070395481c214035002e00b003508002d216600501c00742c032000c81c805c141c40c0b10ba00b02d0311805031102ca045a81d904003c9a0a500400c05155403024a00842800d0b555800785188918403800b207840e25143d5000340140407010040850040200c1403040314000d41b18031011981d0008004810150f1070a550b011070302c3c05a0441040807004502920311714091500b040050065105e4400030f400c140008030101d00340c424044001d00b260080807001da4241c01d203402c0380158640d00100100d002651440050000d030003043c00901541d45481500d410907502c41c0d82003002c0c180488049040a09 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 956839532 1250 956838282 956838287
    0x6070b0601030914070b130807120b041e030914042d09080a0e010f0507020a0b0325020606010e0a0311191707030c060c0f15020d05090c10020706 64
    0x4040c2116040c550b84104410a00001e0310a42e0f900c40c4e0030070300300c03144c1503983e0090604662040106401c0b12103031140c0820980004502e030310032900c1581c00a05418496141c880401350090022a90320354041c85c90004072610038104080c00b4000d0b100c003e046440e0010010809100030001440b8600d0000340303000e0398150040840c1604882070300282c100c1941d0300b80400034081100060100200850900c9a4a6000000b07212400080c0d842945ca0000b14409031024010303010000d5200907010024413000000c0d41c0a1a407205807442a810307407110320081042c2032050300f00c1150040e0014020440c0d80e5800420700c0c1d078401030030b0300e40181c1070346903490f05444154890b8115101e955104080e084c0140320300344c1e02002d05070303801080c2e482402c1694203d5941869200480f4240c1109400091131809540e5605c00707183c0080119058840c140c1d40c0c082d03c2000c840454030107583c00d0007482c180c4925840741500c07550001c00104901c561840030408031028107500c6904661080310140078465 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 956840782 1250 956839532 956839553
    0x3140909010311060f161109040c150509040504050a03140f0319060509010f03030305160815190306090512091509220f0b0303090a060e04140903180607 67
    0xb070f0005141d0000506542c0001d401e8407544043c1017020380040780b4000d640d200c3d0240c509200b4840c65500c00c2d10189842401001082203c000d059100445803c001000071241807559002c924a0014640b5510500040480e0400d80341625181e20400542c3c04254110072034401350242d28040034185802c82c801c00f00c05200091054180c1c0c900c2440030f00416072150083e0000c0c200040c101d24296844400654044045100640009007000c001c5201544000c4102c10b0040443c0d0700c041e91030361904a02942d0399801845a50451000030360a240c6106450008008d148142000f141c00c10103420510328286224880e0b16100404000000041d0741c1c0300b208502c1400e50100e800e40320249100041c08952166862545400954500e481404181d5016044d000c40d400780401065458105041d500e003c0c01070001d4020f04400400d2103154040c0c20140d400f203d000384041404860074100015100c07064a000c60300e58000f081800143c1c0312280b00442d81c5e101550480d0401040f07440f14034004 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 956842032 1250 956840782 956840789
    0x905240604050d020a0f031505150d030c030915030209130c1b0c180f0c140406050d0e0d0f1112090f030a1a0105120a02031c0c0606090204030314090901 67
    0x26100441c1450840d100da4170108000e0101403c0802600c2e6203080003542c155401e5081b070790561070302c030000d510a81403427202d040084021788248032070540e50740d081e50909a488001c1d000c1c090501c1000031850313070b9003010341a1800c5e02d59000d42c99030a51014404100104c80c158071100f424451003107001a442242d114102004060f0040f9800460038003140000c41d940050601024010a0341c017104038513004581d00140c006010005482c0c40c0c201240d0f0500103030b074820284002003208121580c441c00c050300f00c504070007100140c446116024075282c078580c6801c120114550f5040c01d0000d40d08542d4401110508001400c423100079030b480c5010b2407040760ba40038462030940d5032f54050758030708111040c603042d8416a640589602c000c074440300060248605480340f090504080b0f5410004103849105684c00b500a018070308a0080003001e08020160801c10440d80300c0a14011036440d01507a00100301c5502c0050340c2c0c0381581401440d0210021809148420801114815458280c8500e045 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 956843282 1250 956842032 956842039
    0x12030d0c0207084e0706060e06060702212e0509030f07030c110301050a05180d0e1311070b070e01050a0f0e030102041a1c0504050a11060d06090524060405 68
    0x30304003d06620250951310680c00f03500400410700388108603295010405850307a00c9156480365950000700040c030312640600a4100c2038040b855450760031440300e040ca0700300741c0800b80c50180c0311092091040080c4801c1c240602400380080c000c02c2801031150a4026034420051480c000e4460078000052054400080030489110465014044940c1c092800b111740180244518106003800c04064881030312100c540b9502c0010b0091079400000f00c8510074401c540b01c0c100c20b0804501009401400088403a954a45910440040341c1803400102046480f900d504c548900301140000c003118003090400b03051020030400415041d400c0600b442208407140f0380034110341c0008004ca406402944d0002103c1e02c0d241c000b01c141010841c01a101054540c10420b944038080b8016805079841070300c001c0e102d034002422441c08140d0841628040c5500a410b0f07e1428000d00314034422986e01d54007540b40c591381c0b45c050003180c3d004003486141d801c81d404554000441842c00103850b6204a21400740f0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 956844532 1250 956843282 956843383
    0x161104140906160203040906080f0f061509040204020d110a030c03060e0a0e150c0a1d0117130b240f0901090f0e032803021812030d0c020708 62
    0x3d0340e10810071200a4540c641d4240078499031364501c903549034801071a80080c1d014a282035a02e000d00010b149101e4074041520301400c80100703080c400a1480035105a130400c2c0c080101411035080c1d4020b1003582d5144469030b982c3c0b40040e581c018101c901c1d00c0d00c2c40e000c040c107120041048440c3c40403c0d940000c180940043c000c0f03c0781410500d04460070710302801148040301000f06901036100681122402a180c20010030240c616440300034001c100c0d100c0c00b007124540421101038903a61410b50000c400035551941c0445512018107503001103890000d0448051003c0b4102117000e40704484000c0150361040403680640f0005003214014092552400e503203046c100b00710f83c901c0d001142901606000d80f40e81c0c4e4411800c10100300904480c0040210807171020304141c0d84207100301c4000c6a0a2440c6808607407041c1d0070020781540c1400811b100e0300c400d01200352010414400d29119034003503001040c1d01880d00c0c1d0750904110820071040916003c19034030610f204031307220b0500582c0541109018 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 956845782 1250 956844532 956844571
    0xf0f24090a0f141914041e06020d020d060e07020a02090703140c0a1107060e15040b1308100b0108060d0c03050703030509011808030a0f05161104140906 67
    0x24024070300080203442480c00d09181e03450014803918880c0c09142c052000181c03001c188404c1c2d0040c1d030070400074038076101d007800b0006010803c04140b0042118889103443c51441c05a10768500340d802c0712444c250455800101500c850398944911402003a00010b004400e03d40500b0103902c90f140c115002e8044c1c403038680061402c51191f4010004074182c0c1200c0001c6041c9100960641c1d0440c100080116400000c08000d071034000075003204a41582d03a40340030f80c10b1a50700303112441807900119618108281700c00301e02d5069500c05400c000710403881808100d490315545514003580390f2140c17106245405c65200450f640b0420721a48084162803403411541c4500c2c00401e40b1586604c043c100340154a0b000c010194850000d0210038401d90303410320f04d814200e2506403c7c0c0c81c01e205a2a095004021440b83d450055000b030815500340c1c1001c2d410290450030401c50289440c0044550043d031605080e010301e42845015480720841400c6401c51904480700c640c3c0380c0018000c2c04044000d2512407 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 956847032 1250 956845782 956845801
    0xd080901110f030a02030c010501080f060c0c15090a0204140105181005060705030706050f07052a0f03070b0f04020d0b09010b1003090b0a0903020d050c01060803030f0f2409 76
    0x1061445803c0b25629500d070240251290058800700c0c4071542407800000c0e00c0e0304002040d556115408002c0e054581b034071800000705074441c2c00c0a40241c0104100350352003d401045a42c071814031080906040c100d41e10400c0110b0b500c2494110811400000600603070312410031800396404100690607154a0f0050198400b4006030700403a407103840052103070204400130020342000d51161000348859101c21500e0502c04000b1500d03100020130903c001c110f0b0400140d51a4000400741a40c085080c524000301c0d401d02c0f0341c0d00c8910415a00010b400301c1041b019000e0a40e00103416840310300c3c2c5040c2580054201c1c00c0d02540035100c440c07408040b9042110a50020040d00001005e8000b500342e000c0740500503012000003911940307482d40018200c4030180c090144450341c580d0180c940541003920503a0982c021844c07003242c965840102003094117080005500400040150303007180c3c5491780e9100b4500c1070050820301d04895941002600a541003c142501842282c02c017060755104181d4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 956848282 1250 956847032 956847043
    0x81902040f05071d0a0504181406060609040207061d0601060f090807172802310507120f06150f050307120e0a0609060b010f1b020303120f150d08090111 67
    0x1032640140b400000230100b03a824440c10705030340c4c481c48000d60b030189040141c1d901d0300c104603540c0350000810004a001e40c5090350062070440c0c0714210008840000911342c08200390000290031681d40120011b010172600700c1000702c80d074442c40c90003d03440c0d0b091003001519001d0314805c078a0f0f09182800c40c00c4040800b03200d2040021110079101000302c0040c2030300b00480c200030724140d029071800314614541d689080702401014000c100251442050345094600410b0000c03c0c05003001031907680c86030000030328024009034129a50001c078249042080b60180c106018001c10b081c0441200345030f15440d00001500d51050803410401031080f210b48909001d0300c0083d5034070354a4091807802c0000c00800b5400036801c54003641d010007500e0848401516945003144407100071403082c001c507891058405100b8220755202a0a0b0790514882780d519403801c1106480040c0f20b00004000c01c8a032103d51603c0107240d8074121071b0624403013016180c8824070b01c40c401505041010840c03040140440c10410b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 956849532 1250 956848282 956848289
    0x20d0803040b0a1a1f140f251a07020102041d01030219080a140102070f060f0623120a1e0b0f07090b0a090b030702030a11030f090613081902040f05071d0a 68
    0x2d045607601443c42c60001c0b41c4c1e0221123201100d60944000708590b91440500d4420140d000c0003a0301d114010600714a0421402054402159000c01000c0ba8036010094610160f506101c480f951035411441008050780014600d0300402d60078680412450301c00003110118030750084140c501c1a00c000076058003900c43c0c541c0c09040e501042c51b0400c100000c070303401400c0d0f9100050040028a8440f54065054040c1030070314008200e454940041078a412841600c3c030028910495400c10200da464001c11109000100084440341c510802406240e00b42940d01500d114000d1500385440034010b00a103c540c011820885008201b000600340503600d200082d000d240c900d56128645460025030380e034004191540010040c03001d0000007200001501c08017607107801c03404d040c10000401d20000390007074843c820021080071000504080709011241103905000514100b043c4280140400c1e2425041d4200d141440c0504110703035140d01100c407980c1c2d02a80f0301d45400c070550380d200003564004940c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 956850782 1250 956849532 956849567
    0x2033007050c030625030501060509060a030b1203090307210b150a0b04080c03030415030507270306050c07200d0b0c0a02010b060c03040909020d0803040b0a1a1f 71
    0x303091003400c14005c41c420340f0b1542c84800c050a03010203070600700c099440a01c00d82000c100c0c244540c2115103030007400740c9100350544c80c0004010403050001000b00803464045d01032500001250103450a081c0f0068014265040809481c0175140c56010305041982e100a420a400c09002c03e0740c8981e095116001d508009100b004015220003007108550300174881c0040ea48180d207101c1290381404070035501241d090b00340c8a0b08030344004130290090003004000b40204075844640c3e06450300754000c000b035244c0d950b4002c41d0303250381140b91890403608050001700c80504180540800a14211100310451750308140c9d41d00310f03003043c2c07001c1807000260300001010654004108002401244081c00d00b2103540d50090080e020610180205032051650200d4503410401041c0941d6119030007607081a072003e46042919801915400400e03041a00c04540100e041418032810140c107020362840000546a44040c0344495000180c04c403144d02e4500c070517401c24503004800a03000340180c42d29880c800 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 956852032 1250 956850782 956850793
    0x50705030304050606030601060e01121a0d060507120524060c010609230702032b020c030d150807060309020310060807030312060501270302190302033007050c03 71
    0x140307040c50721100c4c125100c0b40640b180000018600388136020200003e48180c42e40760401c084c00710a800031700003540c00900c50000d045441442d5848030780030003c0c00d030300841000401d0b040c50240180048000082d41c0c2c202c0c0d0800007440034504030000c0c0b030300c0ca60000038110b00d100318030000810078034040c1c050011201c0d440c5c11000602244107030050624400300442c1d61142e000c83e041010b0314001d090b5407020050740248241c1d0000f02e03d10900b00e0b10300301e100f64160f060800c1110704400341d900020386898550000300d401c104c100c11900138402c0814a05107014009420020785d00e40c1e6007018400c0200f01510f80c031082c81991014001010251300102c800e001c148c0e113600c44140d440249210440c0050125154240402c2c190b200d4201921016500e16031069400040002114a18202034100c00b81d01c801c00030050340c44914103403100c0c002400b21000700345140101810a412100d041e001c3c101270044240071465039135120302e1030b140c01041d400d880f05a5030401c149840c50000104d50103108a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 956853282 1250 956852032 956852041
    0x5070b09071a041505550801090e061b0d06060e010e0d03081306020f03010306141501080103030809031306020f1603050304052809050f06120a0602030a1116030201061d160507050303 80
    0x7244941a8180c4040c0c4907c0381c20f13641c071000c240468100018a074010740090b004a81252441c400c0c640080b002d864106041c40c1d405c5a1850440f60240d00420100e00c41e80700c0402c0303a5800502d02060180c0c100d450049040117511301030000300b0000c21002e82403c82c58000820003110303505a80c0c929a44250f02c948940c0c403403031b200e0010000208800704002d040c2000031001050039001207841c01040e5a1306546034607568046c0c070360701000b5000349158001480001545a0080b1240c80280030741d030700070a14005c940c01600e04204a518260700d213890140310034008260000122400c031441078949210040003070702c100c840303000144d403c074000341019140040c507480c461300403030b01030602503512100684413881005480e00041401c0d80054200440460108041d54051175020b00c0c80100410042d64040d08000750b9800a034402141e2001c2000b400e0034503509100361f001070b1214000003500809460311403034040c04018103407011110081c545071200f92150058401490f84100ec4079100e050 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 956854532 1250 956853282 956853427
    0xe070308040306050708060619080c0c0d030603110d0804181812200a020f011b080c0f0d050403080706060302061c0c02010c05070b09071a041505 64
    0x406944540002c6d0110000ca40145000402c642220600e5041e4007010000460242c40e811402040310040b0305003405a07904000c018030440d0703601000c642d80080c2440c21481d140310015010a40c1c18010540c03800250005905c4104950554840040c0600000114103501010701205910030b0130141c0340e880c10104011031850f2214101e041510703071907c4502101e83e86410002e0300511008658810311100e4007506085901400e07a0704185000407802515555039150b2041299040320103440000b541d0340f1882060020f54080c0d80c9080107001b01650b000c0008100340240e002c081c0200e403001030260700f00400d56208000070342e0302414941e103481d5030014914001002d1180300b16001d08000032880c0b054818400c8107a400921340341c10b401e01d551900c4003d001c40f001130001002e4410301c0001311b80c40044165600504145000caa0b40d40c1c0d04000752810108001c2c2450400d2260070302002a410a600d4540010b04641c1414010a54040303080c6036007410400c420032201c1542e0010344194103c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 956855782 1250 956854532 956854541
    0x2c0408090a0b190c0b06041a06031314010203060102060c0f0c061302040b040e190f020612100603110304020409081c06081b0d0605100b0a030b04230403030e070308040306 75
    0xf0741803d88240c000c6446055440110402000344040c00351000901c2c1c03460a03510100325080f84459201c0850444004a01c1c2d80d07009135686801422500b06c86c80411051f1034903000504140402903080d810460000303951000c002e010001d40c02c0020451800c010000c4043d0381b0200004c104440e003a040c81c180c0c04500004401c0c05074012342c18056028000c1c1468005c4085152a141c01020200e00703000841541002c0408200d50440925583e5409640c0d04005040f1200e40d902c40c1c9221410038510001a42c0700c0c6501900600d400d1625407070031000101c00b075a61107501918081071800d12890001c0d0300b072244000c210101c0e1601070640e15a5640b6a010005442c40c01e41199482a04028103c0c8040e00482815600145035200b880004c1d015030070242d04980f244405d000e0241e112890580c0682001d8403a10009540e02184046072909014442d00d50400c10101c42c0741f8911a0340d01010104000c1004c0d05041d00c0300c00e1520b0301c45c010440c84000b9a0800290ba4a5a0300c80c6040030180 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 956857032 1250 956855782 956855797
    0x60a02160f2c01170102040b030f0a18050d080c040e0907030b0901151802090303361c020a050a0308030f09010221040303090f12092c0408090a0b 64
    0x81a500d6100c0c800e4810110051001c880c503028498580c0c80e01034004c0300c404652440c03200a54082c03000080c0d13080420040d500402c50302106040615091310500d085401182c00b210350880355680eaa000310718007184101c2503130f420380b078400510360726640072142e544a0399022a501c07062100811801e40c0010800009803441030706458000c0d00c0350400701e402d95094140c0d21182818004c000c020148076084205034038401c1180250030440d041d8006070854014482000300307004450801c030301c0106105020202005850760310740003540c040d40440c4607600c0d09030348811642891190f1100359514003001900030580201408d007903649a20300036260b43c006441d60b0080d480b030f83c2c01103002260107000756803140c4c04c0340c1c443c80703240f0b443c01c00f89240e0076030081e100741c1c240360741c0d4815000840e060318880301c82e6034001c5240c03400c04101c02c10028000507031940910b05440d64880711810360140c01c5901d04110420346408441a00c4609019215100c2c0100180e8042803e80c000981c03203401c1b50141407034 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 956858282 1250 956857032 956857049
    0x1060c02040b09090d050c0109120908010c03180b09010f020d1a0d030f0c03050c060a0603050f0606011209060b100c0506100605041505072a0b1305060a02160f 70
    0xe00840814040c8803d0241c2d0320240300d401035895002c0a501c1742002d880710000000010955410030707181e6400103000c83d140d010004d885240140080e460074014299211404d107000c00c0120503803410142d242c0352110340244484424008503503103080075000820b441881c50821076a66200d0540c2d18000c18980300d90508030f2038946440b101502c0c202d04000c8c80d00d905074a60640d040b9215004566881c00c103442102401424400e40d0000070003044054030030803030004005019800c40c2000b030320f404c01485480c0b40710f901010801140b660b0010040e52603582851001c01d050b07681c0e04d04407025010307851344150002001c00548500c1c50b84141104640c0b400b800035210355440d50303403c41c45075018500400c030100d18200800c02031032003100d180100321f0b03c083c9041810121280d031540300c0080e8030140241600e0071203031031707440c1c4403010710b500c100614044000301c0c50000261141e120b841010b120340b074800c580c0031403207011160080c0059011524070b200398101c890340b1203c618944c48510f0003007250 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 956859532 1250 956858282 956858291
    0x309021206180c030a080f0d1e11090a090e0f160918050a152d050105010e0f1005070b160e010f020a020f0307091e0f020f0a2601060c0204 61
    0x840d5030000c50f000b111910041e000d881214215240d540c01c80e4042c50308200700c130b101040307101e03a42040b6118012203210f00400b02c440088604103294155101c0366124112030740200100c44c480e56a2402c003c04072600401e0100340512080304190508500a00c01445402424142d9a0b84e00c170400c14041a1341c410241005801201403581e440a81000c000a042d43d20010925010504003880e140c03050b0059000410458015402d9880b070100f4411500c14052030325080d501005c0c8140aa54054402803810386013460300d101c00600040c04291140c0e00554111000310740b01441002154481a0001003d441b1800c21303602c9000080c58640020001030248104640c04d580308290049201c41681d005201c006140c1d003c016103104171600041d814810118001617008080c022910b1701c4800d540805081410320b160394041c0c41648030b070650013510410030350044150039000c0d00e0f003d00180c03500c100c04c060304c01e80da04550345000742e00791310340d8200390000600194880a003d029601c03c4d5003e00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 956860782 1250 956859532 956859571
    0x20c12070c0603050c1902010c1e050405280b04091808040b161b0314070f0315020c030d05090c0114040b07050a06060603240b0a0c030309021206 64
    0x10a405055002030400c10712290400c1040d1207904459000054481417914042c0810003114500d41e0020211025075121000c805c81c46070000d502d14600705911180705040e99003694001e00314032440c02190b01ca02c010f2000c240000c04d03110440070800c8000d4504060694444080300c14a400501c12400c145003481c0c1031303006200c0b82e08007801c40c42d540509600e051a08054038058a03400c800c8001c0c52405030302c646030010508a40040210b1952001403145260035070800704c13091507070a24942c80755405200204140c06640302c260045a4004004e040344442c901d82d00703c0684039600a03840c06200100d54078100030ba84d54045030081d0000405c591080d0309280c01551003041c1c4091b2440c41c400140400c100400e140b10082c0000c92107901a100340204564841e800c40d03a00d038000c803000960701e03c3d2800301e48086040102d0544090181c144506241c9101c2036005e2041c030f5058030400c01a14010805c00d8001d41200d0016503000300541c8000d445042c40941c1c0c1c410890340100c40c0c0080344000c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 956862032 1250 956860782 956860813
    0x120a02090c0c07060c03020a05070609140f06030f0405070806070932101403040c0306060e040c050118120b0a060b071502070f0807110910060f0f020106080d03020c 72
    0xc9142c424140041d00c15180b500105540e0200400c00035030070f40c0201c4142600040c01407180201404040c1c0b103100405051008040803443c02c41c420702e0149112a05187c055540d94040c0c80e0b00410369080181035998500d040c1b81030007240da0040b640c0b84130f0881800080b580195602d801d98040f410198001e1803400148660180800e125006003500003001000e1810007090154450f036650510382c59036284543c0341c0840b9442118103070355030214003d0a0003000b072507000f10401030140001c0c0041703a08003a102c00150340e11911655040c000701c10307a089100e01041c0304000c010844010307819603d24141c1072000c0010411503003191030606c1c0c03060102d58010703440103580c0440c0e00043e01610388150404004000d500c5004260703003801c07130780103640001103400c0700414505120b11003041043c0a00030600229140190620520112105081c800380d40e12803c4490001018a401518a05d142070280d00402d881d0301701841c1d0707002d1003842008080e09a0001d011165114044440e11103041604 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 956863282 1250 956862032 956862037
    0xc1b02090f091e0102120c0405090c34060605010503100b0c010b0a08100c091a030406110d15081501150e0a09141303090510050405120a02090c 63
    0xa50051050010800040720344034110350000081d07085880090840920f81e20444082038490004da4000800042006041403500c0c3c00c16035005c24903041c90f003440b001078050178000340501440751010031b0000e2104c080c042c075007441d00200801000e84101e140e600715580c850381401505d41c24100f0000091652050046900c160442c03402c0040c0f080c103007104008603078000d1000c51a9503403600320201c6681d4400c0d04520003446103400130148124026021800e507807001ca0381d041484580300c42001081c2100302c608030f00411101071347c1c0da81c3d80e4514080340182500400214070050110324081c500643e41d10041700030540702c21541180da50307406416640e0101c40f0400004e40072100042005056500b9602038001490410518010022000c00d1030b524a59110301c3c0036a07103603243c1104408043c410560442c039020044140051103440151942901d480740c18042c0441113580e80041c1e2065040d2000b600c0005c0ca0b10b9142d071881c50f907042d40d0300e03407000059200e0703c02000442c0c50404071504 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 956864532 1250 956863282 956863337
    0x30708180705090c0a0e13020307080c030403050f03070516060b011b080703032d0606141306081e1824010510030f0e06160c02030615030703020d060c 66
    0x2c140318030703584c0c40c201d0741098120704d0030081800281da44241c560f5962503100f201001c0040700050b2246440742c40100800d0000e407000c10000c00400c103100220341c0c883c046844400f0341c4004c3e51350701c1c1c46504085644d8130560729004410720840001a0030801980c0150303850640c01d80c4c5841d00d2001401d42450300744101d03000101405070800044002070b009030400c554819000c0b07050b040d2103106140c1c45d00000311800d01840c5040d80d0b071301c0610640c1d40100c403290502071080b00440c20444000c3c00c030003030b403d0b907401940300f80888100050013900180c150306500414000000246040030032110342117006c0900600110300404241403116256816022030031203401b048a00385034a000203000b030701281030652908164503020703100840d1001d4003d082003601010024102450402c000c05410101d4040860410a60525580260707400060325a00003a99202c110400e40b100d9000a161032001c2d44002d40000014180d8000e00c9810b91004042c40c115403101424480450201e2400c00b50321031 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 956865782 1250 956864532 956864539
    0x702100507170103060504020a0b0705014703100c05091509030601060c061107050f060a0203090705041d0106060f08150d03030c17100f0f050a03031b08030708180705 73
    0x2c0100081100c90300a190403500203031450141945a8260180540c422001590f01d41c0d1190380d0040700c0006400250030325a032011104405190f0240c8200070b4281e03200c8814180152111714126903501403085000b5141603100420484102220280c840d4000084251041802c0301804030f12501540445804200042c0640074507800c02c09c3c15607601441c803209458490380d503840e1503103095814004044481c066401000308020040416107405001400000054014001c0c080c540740001030501c240c030412240401c1d501c00c0766026400245601d07054a19a60a25100250440c0c2013090801051004d5a8100d01c0707a0700d01c22110800c2c98440420b03500f180e070301e10100c004244207600070b944200403444d0540b0111409550120010400e0741c44880c1c4100320482000001840c151060080030031302c0030501e40038540380000700201d480340f2000e000d0140c0d461041c0d9503400820045485107504c895010703128188400018200d0070125000741c051421108000e548207800200407003202e1005 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 956867032 1250 956865782 956865827
    0x114101e051503071403010b0318012c0a0204050a0e061e0402090705090d06020c010e0a05150c0706151d1314010b030601150f0f02071a09090702100507 67
    0x1030301402c6591008050200300071000c01c031a189031445500450080414112160b203c0c10710140005065803080c094a040742c0c5403600c882084901e0030068101804404034100c00709980c181e1540c10f080a08500940c0285003204020307143c0101d40c042000400714004444060b565091088803c403c0250030442005c02000001e00500c1e040c07034180e5000c072261410508004170300d804546201911001146d0680d008258011094001d01c1040c44030a0200000c0c044e50f49241c8130140ca461540780003204800c1d0340f0300020018880013046444203980240704000640c130904604842100138026080402c9101c10171019480515091134010350340a0712101e5501d8041e603500c41220b1040d000b1240654882d0304410050b5401d21145009041d6600c2484069001547c0145000c05030241842481010b80030300c024150b000503807030140c80d01102000798840c404d104903040c034010249510781c0908103808010a0f03550100340b25224a030302d1002072000b5110303100c0644802e01300755041090f0101c0e0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 956868282 1250 956867032 956867059
    0x110312010b0315040c020a03030f0b061204030c020d050d120c021504051f091704061205060d0210020a031d010c020f0d0b0709030b010503060103021807020114101e05 73
    0x324019074000c01400d410320b40c3c0320010008642650215680100940c00c81c0c0c104000b03154250113440707200303640c2500030012050400c001407083d020340541c00440440240000741050302400c0381a80b443e0f0010b000943c00b945528081c0c1d40c034184064441c0005003102c04001c15544035014030480c00303050340c000c1d19441030607039203a200d20400100183d0f400d118030000b1244040000094416800344070001280110080c2441c1ca01c242c1110040828100b04000c00c0004940c0480c0841c005500c00300301046684960700050744540700c00c04080d600c84682d6100b400c4040c0c0000e4038000007407294440310345001c96429084091040a45501c0c00b1070851900c0c40f0062422350090064100000d2242d060101e194640c0c1c3e022080494058000c00d407081020700c14810040c00d11030040004400a004560550f0702291401c1b6003107090114400280c40031850b500e00039000b010000701c5444102016207802105040030529504c21004601c440b0020342c0032003103a0b40c0c1c3c0403041e01c501401040e1105032 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 956869532 1250 956868282 956868299
    0x1212120c0f030c20010c031a22060306110408010e0c090c0a030e0115080f03031003150902090708070e03010e0303010303050703120903030b1c11060a090e0c0301030311031201 77
    0x800c0c4901404000202111300d0000030b03020480c03160105048000a480340000601030f04450103542a40100c0c6102011125190f80b40d00300103c80500400c401420801e0a041c0c905c0940400d41008040b00c0c1480d0710719207900315200140045408010003840b50303010030781199031a0310010104540118600b000550040410001030084004a150000d41c4e0206c811038682110a40072804a101c004800108507103001009000d40014028000c4e40c6582000f60b20a1201802d0f4440108001e40c404080040c103581d40d4400003074a80c02804015485c54003d10080500d942181c004000c0b034111003c3c0c04071424148207101e44c2c59031100003103203140d0030350724280d405400243d805c4041000420040c444c504141c05005403c512a407400b080c41d01e2280100071034608004d0006015401d00740001000c01d005800d012000340f02642ca40e0390740d0080070b000319a00b81c5d40780c00c144c24203d940003d01480400e0395001b1812a4013940d142e8800c2d0b800d030880b8a444c2d2150604c102c0d2402c0d161340043c0080038 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 956870782 1250 956869532 956869541
    0x30610230a120f090b07110d1803060c020601260c0f120a03020303060a061d1e041404020f010801051003020c070e0f0f18100e071212120c0f03 63
    0x1d6142000d0300c411456030015020384030004800140b00f500d0302c008400304203826040c0758121480c2d040c864821921880d03080c0c0e4605c65054203408004945943d50100d880c0c0000f00005160042c000340264801403c000e55240c800307120f40d40903c0da607011160f1420355010104c40c218402c1102410b9140035020421104000f400e4440d6031102400035421031030320080144d519000c3c0b0030340196449242083c20003801c2c601e581d0000d01881001c102000c0300540920050103108004c90301c040c1c0418240903007283c81c1c4c2880500700e030010700c0c26107198050440203085904c514402c40b03c01e400174508200445480e4001c2c80b490f908440d648541082007400b98001e0042c2c0300c0c10700202e0f00f0341340e504e0002c46800101911030030480d200030070a0001c1030180402250303000032142701182a03031811180903640c0c4c0311702c00c0c1a01250390b80c40b040400041800d0200d00002e00b90042c6400c1c0d8000341e13081003c0c060507600209001301c1d10072061112000d500c2d00480b482c0300c0d000d446080112200d62415070180 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 956872032 1250 956870782 956870797
    0x5010906030f1107050604060507020a020f131b18050f06120910020d021c0501260c030d0f110c0a090b06070b0708060103110702090a0c0203040308040b03061023 71
    0xb54585401c1c0100119040292240c036002c1c0300141040d04041c02c285080300c20180258046412040d1a071015848070300c0c590070007600c182c0315082c1e103007801014080103080410f0510f01070740c1c4035540c85428036400304071802425418500d4010315a50381041044001c102e03d05a0b81100040c80700d404010202405154064214001d88004210084598003240d01c19a505145540c0c0400c100c0c0c040044820745105074003004200f0480b6505100308208800c0714400c1c219240704a14060544061050101d03030007403c009000c4400140c640304000d0702e5810040680e00c00074101e040020907010000510300412040034000801540c102105000985a180c6076240c200004100d80070014041c080b8041c403036400c640c0c1d4030710181880300004058070200a503020380c526041c4410000741e610900340e00c0c3c001180c0400015116000c00f010317030a5010703591000d0030402d00802c00140c03061010000750710800c4215981d03501510102d506072210300038510091019040e110160503d00314003c01003881c1d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 956873282 1250 956872032 956872061
    0x1c111509060a1d01050c030f09010507080c131d070f09230f060a030b03070605090315040c1a0d06051219020103060f030c08060903030c0d1109040606030509060a060501090603 77
    0x40f020910165825a102528000c1298200004002e52482d142801ca40c200481400904c40c908164000a00c0030758050655290304030b00240300441114000f0281005081000c041c41d12004081a078200700c00013200c0400220f04044000d60750b02d0700c102c000000f81d0720390340c01c039500701c00e01e158401c51080c030700b0051580c2010100b80342440a6803101d003c0c040e101c0702c541d004240180d07041c040c1824080710354040c07010301c24144a503000c07030f58002c14a09580240486281036076a12400c11185c00310142e8003a440301c60204a00c400390f030340282c00800b5030031380040c2c0600038641d8640070710031010760441e4086029040f6048645040c01b4550703920844900503d800705100c0d03154600342c030116640380c0c001c94954454201c1004005000e21401e580100c010001c6d42c11494081c0302580c00340301e11054001d1031980c50b00048210a080000e488160202410810a060f16180094020b1506680707654651003040c0024504142c24001c0c01c003074880c180d4030101050b01c0c1c540305401812020121000c03 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 956874532 1250 956873282 956873321
    0x110307030c080c030f060c0405061804050103030c052b031a0604080f010e010b090c0a170408071110050f2a010516080108030406050304051c111509060a 67
    0x30442000807600644441d03030190140c20f508038201480c108080c0060314464001c0c0e0204014001d1403010f40b4101c660558001c3d030b454602d04c14103d01054519100741e80300349002c001005041d400f41c91000308520075000c0310200c40075a82c00d80e403c050f5a10300c0304070002510502d100310038426000a800c58080e2900002c1d80d644181c0099100d801580011415501172540c00d04d00100901450910450b01030007041065607000115000200044c0728003010080010100d401c10700caa2081d4031601c8440c020000c0a0034580f81c42015544100d0701914000360130308186102d850100014800d031503058a846150501c1108043d006400040c1c104299a5842e01080c0041103154280940c440c1c400000280c0b40c989101a407100388656401d00701041029001402103031000000c0307409440c03050402c1602ca42d86c42c58410b241005080c114007042d0001c05800700301d650845103181051a82206641c40003101e200b90420011301111032580503809003000c07901c80d001940c803021021890251212 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 956875782 1250 956874532 956874539
    0x201050903070e0a0c030203060a0b1e04030309030c050603090a060b0415081501080d050a230706150b070f120203070203060106020705030c12061b2a010c020118110307 74
    0x341042c010f580548054000c040420212095500c41c036030111213182821401c1d8203206010408046c003d0051000400d0001984802e5413074642c0c0e09100187c10480c80c81c0d9807600c1e0328005003078101f60f10003141d81d0f4152041c08500c0d440d0141c180c0c0d1261380914004c2c03051502e0b41d202c4001800380365030b040e500541c0d5004045c1c00020180b9808000e050040024248118800102c91109105a00c9282a50410005640c078640d0102c100c80a50b04240b0b40190508000e4a040e0b9150055000303078104130400140010400906400900102404805c691b184d15501d0035000c915204500000741200710070003101000130103080040000d1211481120b050134415800700e841c2004c01e070826000740e07004080800c0a0729080100f503140385401d840343d4408040205607075544d404040d11303c20201800078101030061101070103071001c4d41208406110031010481c42c0450000603440017000c2c2e5400c3c00e404203402d6005010308400c10310600001104c44505849184ca0706020030421503240c040d829002 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 956877032 1250 956875782 956875789
    0x2040801090b06090a180f150207120e0f010903140c061b06090c131a100f02190f030f03020702130c02061e070f110304080a140109020a0501030902010509 68
    0x220380340d5128441d0b074560390822008001500b00c000309040105402d00b9080100c01000c1030500001642c01280d42c601c1115900e007140200e103064140d0020b1038808100b01041c0011400d200c00c01c0140790301d41041000c40f40041c00201c50741001c11502041c000b4030104001003181600c0008400303104240d80d05518100c0c00600c1c04c1c1d015601341411540420104d0760458030500006801202c14401001820820404958207107044074004a0807035440c05608501200b17100407007426040100041950540380c800607100c403045100c4070005100b0b0400950241d62010700c030600c07507070b04289524102ca200b0381e0125825401680d002c2c00301a0203012450058071082140741c0c5440a072403001c00c911514041c028030b4110020036116021803840100b601c04060f1000740354000310b192600c400c0c440c0c2c2c802416100c0602140402000703102c00103000825900214070b00704050720a518148403a00410102400d840b807003880a540114450020000c0758002d0340300c021441d10606040d030170007d117034001 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 956878282 1250 956877032 956877041
    0x60f090907050408100207031d120624042a0228060506011d0f0609090a020301090e030f0414040603020d05010f050601051e090a170c040605120c1302040801 69
    0x501c01042c0081024415000140000030f82220145000c60074940346850041403151107005030001c00d9030030f04041e1103584501d840902000c600c01c007141c400782450ba900440030317503c800c4102800c03209013204180e03900e403034010300f0300e650700d00e402046040b03400c03020200381c040c0350307046030020b502c540c6c02042080c48900d120890b108020008009001741c5500b4850240c40d0010406410040d02c0801200858440d1805240c40385040d565000c140319500c1c0400c0607886420300e41503001c0e956000300041060260019410f81d0080c0310140016a01120190340d40d01518a258640c41000d00081c4035100c44c0440c1e180c0c0c110740090021031655a2a00072400d8808102e800b030b21640d4607a164015064054054960010004e103001454030001c40c210540e030070900000c4a4801000040b01d100d80e680d842104c10140c1222080032030700d584401c400c0d6980300306014040d801070341801400110380c41e0069000c0d0210b0022009841d0101070541040740291030322148080036a0309010220b44840244107 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 956879532 1250 956878282 956878291
    0xe03010501060912120e090114030c04180609050106050d0c1a09030d0e0432070908070905040f2108060d110f0a08011803090509010602120a050d050c0301181109060f0909 75
    0x2001c410850304242030504024bc401d065500890a000c80302d01040f184e4904154600e4003c180028135400d2841c041d800742a90f0f130700565020000f02d00754018413003030a90b800111200c03103101c01070840800d284050507001e42184168940c00000340c412229014607011801d005004000190300d00e90110007807448001a41c441819600d4108121006a03600c80090f0b0091480c0c1041d511300c03440e010707110380d58500c54043c80d4061504e03400420f0421083c046202c400c0e9038003401c081c1852001c0004200e00310240079001c1c00103480040032810f03500700107408200d0243c00c04401d549000b2018241716a50141d041442d402c5100c604000404c8082845406064400c4081e90301188801d4103004000d211a40c00c80ca2141184500410039180c000560519580045024a8a550130301d041a035080c0102c10351a10944c1c1418200b0514510001c0214182c0e085403045880d008601940a0200d8070200e80c0604159400c101a444d10300c0c080c4090002c0c07480401c81d903890290303a800407802d804015079 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 956880782 1250 956879532 956879549
    0xf030e03030703051c06033903110312090306160e040603080315060c0d030b010507082b0b0109050f130e01020304120221070f0209070e03010501060912120e0901 71
    0x101d08003000440002c441c1001c05e240c90a008850031515401510100080040c1c441c2c5444a0455800ba6010109808000c01c0704045440d843d902d040044840e50640b502c24802e004a07400700e000d145000c42540c007401e0003d03004042c107070f0b03480c00b07910041503c020841082c01340300b1103078074210369903801048040c504c10998981c132810089010b80540e40c6a09103240315100601102051050008075041c605813946804540180f4040040e6940d103d10100540810f00009130798041100940c4c02910700d01e041c104944c0301a2400c3c00c01c1c401c80c0c40804915002a01030b00c0204007514002c42c1515850800520880281240745900381c01c031400c10300c512246c0d0350040200002d100e0600744165218040d80050502d00c00caa4403800c4030300b0151201c480c0e0224000c01d0074000d101007440c6040e0351950250144086052228001d072500c41c00c040e42d82c1c425030a10b40003140723491080008000710740500d04088252003259407100900008812034a00300458245081840d50f1b600422900800c03007035 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 956882032 1250 956880782 956880787
    0x608072c0c0904092d0206030a020310050a0f0305060112080901030509010f060e061201052502010605120a0b060a05030a0b0910090804080d050a0507021e0a0b0c01050a060e040f030e0303070305 85
    0x1c146083c25000c44070703200202002c00d11100150702d5110403230741c2c400c506441c0160341e940c0e0302c003640b800c09045410203500169804004516080803201d45801d4a018070115003103603030782c0c1080410440559074001d181c8401405500300c070394041d4000c1c0740c020420701c0010030541d00da10304038422280c00350300c0304c0381c4000080e00340259801c0030001c0c00c18041c0120021701c02807501c1003048150a03100c40c1c0c070710340482c1801c440302a1680b00798070400103004000c01c2c219200c41101441951b4440806007a510f03c4130720404200e8610f0400801c1048070b0018010b02441070254440f0079407103200a000b07015a000e801ea410010310f290340b103903a103007d100b0300788613848a0810080d0b600c0c0105141c8100180542004514101a0030a00f61a00a030703041b02c1c8000b004089070b41c0c81c407092800b46401341c0c01c50b124820100300c0802d500c000e04040382c0140020001f1f42c0d111220300003a1425445100b000707400740c83c042008034041c01e801075001406400d000501c9940c600c003081c03940e8848082540003e001 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 956883282 1250 956882032 956882063
    0xc06030a1e0b1f0212030f070305070e09190207020a090501030b130215030613050f070216030b041e0b270105041a07020f0f010608072c0c090409 64
    0x1c2207400d590308a18000108400500c4001041403d00c01802840300c03180300c0400c2c0f1901610030003080d01c00c0b03081c40382225200d04080c1c80d20701200030241e50b201d000c00d06000010394060310500c80c103441400001e000d41c0564942d04030a00d0020700c0d07a1101e0031029002c0050401617101c100001c8001d14a040d400640c562541c1452406103802400500c1034912505104000d40c2d2502140d8905074400e5041d2a500e403249000156007400e00c072030700d81c45541400d0030440f009800e100c50ba40309900c2034003030b1081d80c8400500300d85003074103d02005102c20b000d40041408940108000208103184035080c40b80d404003032f1a03148540ca8201c0320000b003940c6200c00b42c0102c81164038840032181e410380003846a420203a642d1000e4020781c00003005d215451900140c0c98034030030030255403e4000d100640d049400c040464a0191090740180751540c801e03540001651100300c100c91190b68800c0c001850b40c03622603d8402420071001d404418050000e0051130039070b0388c682c0f0494003414070500d10340b0340c0400c8 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 956884532 1250 956883282 956883311
    0x1611011e060e01120204020a26220302030d0203180304080a1a070206040209040804050a14041508030f07320705030309010e0103091707260f0703110c06030a 69
    0x4842d0003000312041c1c02801000304030076614074a0700a66044034090b8886890f00e0b021515191100140e501241c4184003060380f0440d001c803c140100380011414410044401244102042611000f401039104128007140407a0503400f854101c0e490981c1c0c041d510750f101c9201482c50300182c02100550704901d140604000351032001103442e500c4004140d000d031030072440207520346400410190040b00e8035000201040180350031500900b2700100200002034480301a1035038110203510040c0a2842c0184441d0403408408403101181c0c0003000461515144142c135100c5600311a40441c0c0001c013005100c0032000408030030310343e98590400c0c80049605031285d06850102c065108078020380041244061a0f6400f12140b03103080000e0030080f50120311450300580e24001c002803000d40f0100483d661003001950105602014201ca00708a24140c1d000300030003d501c24405180304007241007200d4000a4041c2826401443c146825901c410700d802d40403070810b5000b2154140e00540e1000c41014688 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 956885782 1250 956884532 956884541
    0xa0810030503130608011d060f130608030a0e0402120103141c0c15090506070302090303041518061412180d02010b040f06050a0b0708160c0e01080d081611011e 70
    0x22030030030600b40c41c03403400747e040c05641c4001e800340e03014050010301c54400d510749003800e800c5100e4000040110503514018035480742c21910b6520000350308410104020b289c240240c6a42c01c01e403510f8104a41d1035540c6070511207003e0003100b01b190041e244801141455030740500103002c0382e6220002684040d14042c152100320b00c0c01e452440c3e20f03000c00c040c082403001400c0340e030207106e60500507500d4bd1040002441c0d401642d100c4646100141c0d03104c03a655074000c00c444002d07000c000307402056a440e40e8044d12516142902c16405203800d210b03d244102c1a0425150041c8031580c1c0c070709207001648240c0b410807010b42e03c40d80150303440e007800c00b13080d00386445010410380c3c2c0c0b200d04009440c100030005550108071b114460340a80301280c4c240c140880c20085034030350041d0181710b01c602c030540d1800024044040c492512900d03402e00c000581a003002c1b902c5c0813081d0003507507200030700e50300c84803441c0050300b10a107014100f00b15940d1300c0100f400c09200f461b482100700702d50298403012800700e0609070b4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 956887032 1250 956885782 956885789
    0x7111603030f03021317030c0604050a1122090317090a02010914010806040b04060e0703060905010b2503030b030f070806070504050a060f0e040504061a0301110a081003050313060801 80
    0x51042040c2c0c0e801d100a0075440040c1e44040c10001c00150041c40501d07c1c50041403002c2c01c2e54050074040c002003000003e44a11310620070405940c5540b0804c041117820440f03840605505075aa64003440681f4465120f01c0303040d8468100000500c0c00c0000042c0141012035200e0001d034000310041c3c040d036030030a901e00c000300500007029a80b1810480003c003040300150010b40900c0d260240840e107951550804809401d04ca6029034503880d00302d074002c001e0480c03441003d001920301000421300c621007008459103801c54569200c002006100b441544128006080c6d00300741d41c0b2284405565018403811080c82c4c000001002c400d0300f04101d0310300f4110090510400c2c008104420405901c44850510460f10b070740c20403654680c0381c0d000a17540401c000ca000c5a2040c80d04007000b082014a40c4080324100d405803102000d1480350040c50300320342d0308ac0c4001240b80d000b401801c800c14800d000700c50f4000d80b10800d40360a19502d0782e5940ca1a04801c030316a5468902050900c03542e6031019101c0e005 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 956888282 1250 956887032 956887037
    0xd1202090d0305130305030c100e07030b040f0c09062616150e0d030c060524041815020a0f0801060c060b19091b05071a07111603030f 59
    0x1490212000641c40300c020741002810701c040400c0c118120300078000ea41e00215045810350f0f540c0c844c1d10585130307199400400c88407182d03841c0030b203402990a070004080c400e50364094880451a00d96444680c0400c0500000320f900035017058001c43c50030800c0c01098010865642a0a0642044641e202500c01410400c20565001d03800c0074030400340c00000c0e20100c0d141c505c03600e40c03c003451200459002001020750b07034104065010030002c050780030402c40c20702130040340b04000e1500d60303030a020080b1101540041e41444110f1003903003035180580c00f5208950501c402d01d110041690388405e0078525041c15041c0c40390707010cd0b41b1002940c111384010303411207031490a1205903041c00e0700540900751004019000950324524020140c480180ca80d01c2c1c0301018609565043e03503601007001800700b140c3c0307001c1a4903a4078070501c98140160f040c1d811441c0d00c0107182801d010341c183e800c1901c940c0180160200700f42c4c80c20742e1039252010702007003940000e014000030740d040c218107010704034403041003aa004 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 956889532 1250 956888282 956888287
    0x10f0b030c070204180f081c0e0c040c020a0b0408070209062b0c0314010507020f0d120c0201240602150c0304171908060a0b040501080a09230d1202 65
    0x55161264080b41c150030b904590000382103c40b480d192800b08040380000303121b120700201c0310045c0250003020f01a502079030310005105e1590798000d001503e84c5000c103030003036510806a00182e45003c0d048001c6200c414412600e1100d03464880c07070b8000a09070740594441000181040640c00c05a524551050094071261149041c0ca44036910f0113542c5c0e22500d04c000e9070382600d0010407039825120343c01190080c0103081501004501540200710988049000d4070508645030f17010040882d00f000403599a4907040860f0380e400712040d01900e1902d0810007113560318840440e90101408600c0804031100020f000041d091001c083d1070305141c02e40f4547e0202c11502040f0344400700c07070200e130742c050392001c081088210700c00c080702c00078000c8900740340449040380c040d1985d50f40d1000506101345012a0070562942c0c0d0342c096051075120b039002c2c4d180000e50000c000f51840010f60029001e55210b031140e4805403540301182c0400318030340400d403042d0303070000c942032203c5550091000b110000d03407860071032 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 956890782 1250 956889532 956889541
    0xb030108030418110f0306040606110a0204090c051c060c0203030c160501060302100e03010612050304030b13080d0603030807090b0d0e030d02070302150f0108060a1d15010f0b03 78
    0x10750700d004602c104002401e481040140c420010703041041003080c40742465485a080c080090640d0300201e655030302a51900500060191040b03100707402da62000005442c0700c152030f40030b11000d000c618000f6540543c55050008a680312401a01844084020340d0082000b5625001c07080e5039410407540c046500c00d00c14050411000c50850717004048005001c2c0e05502c0c1860814090202ca41c000f03540403421a00300c1511940040780345504500c2200200002038a645c221031241c50803000240003580140010300014080c000382c1c1e500020710f0b40345050303008941e94076084260300060981c01c0d0207032101310030001c16400480450b00308109040c00c00d0110b0401da80c0f01080d000c2c110700c44215545592411a11031070034411528011105c1c581595240864140070390355415907076401080c640c0d01d1001900c807400c0c48207440c0c10b80f1510f41c013510483d0bc1c4c517220900644814501c500303000c01007018010343e80303000300811805600d40720405482585017002e001041c1e182c1c0d40c01070900311030800c10803 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 956892032 1250 956890782 956890799
    0x1c021e190501140a270503100e031b070e0103030c12020307240207060e010914030304110d0c0509150a080d080604090f05030711040b010e10360f0b0301 67
    0x140c41c0e041281000c0da00c4c0d580c00602203944d43c1c45843d145002400755038080440d100601075010580300300343d040f1b54501d94116007400449a0b00318001945400500000c0300300701240319100310f0911268115502c0c6500c59024030703500403080e40201d003c202040c091000304a0008041d155280203170024500300b103e10780703a0b030306075120021030386d48034007003034090b4900353f41c840d03415610740c0e64002e003040141c2c140340b04c65540204036602d402c0e15108107050414103004000400c0780e21940c3c1c0056540c03002504a000d0204107062660125543c000426021521707440ea440e40c2c522496010302d821100760954400d021510043d0b8000709266080580c2c40440c3c142c0000110380c100310240d0f0000f560070141e061500301c881d070b441001025404006036240c1400070403c40300c110710b003048600300000400c072401514140710600341d09411a4007400c159050500400300e0024804400a501c146550342c01d215480401401e48030124031040c21ba0103000816080101c030020380f01c040d0b4102d00c0d550400590303 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 956893282 1250 956892032 956892047
    0x2090307051c0201080403051909051302071a04050a121d03030c07271811010801030b0106230409060303020601080106060203030c0f040f0b18090c091c021e190501 72
    0x203414440144082001c140c4101c0c1101c018500480001d82700004455004144a03140d01c43d00780700c2c1013250a2071071402c0143c400c680240341d002c0112207400303040d0b01d568085020010816903071401a912402c012504443d90b81020b842c1580d04e9406000f80030046a14241344604002c1c0a54010b02c4500e16090000502303c05442512a40c0100304280200b01e070b40c1ca6086a0b03c04034283c0c01c100e54011013140b480f4070700c1c0b141803048020041090007039004403420242444050b00640200c03004001042c01414010028000c5018500c810581000042c0f4a0703801603102d00341740c6590340c20800501d076051280501428520009110b4145030542c02543c070300015082d0500d0040000341d04161001000854009089000c0c0e444409541e4460a9400f5080715032214a01c03080401c80b4030711440d00c0004648200038190205042c40c0c030300c4003489600117140e5241124409400700c030002681c0d990302d110140c0c400202891103034030380d0a002c0c85003002550983d103181006021060107580e0f0410f00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 956894532 1250 956893282 956893339
    0x609021b151323070303020d05030403090e0601051608031b031e10080f010c030f0b0121020405030304090c020c030f0a02060d0609020d050105040b030706020309040207020a17010209030705 83
    0x1102100101c0350300384049031001c652500504880e00281d8900f00e4400880e081c0101c0f03001c3e809880742c00c40300140943c1e0368407080b14000c00140d240c01040c0304590420381000c0e04104189851030900d520b0415007030307001520000503900604080b00b000003030000c1103003104071510031402c101e095040080e090380e1170620f01d0101070100501d84001031050088904000300900a04045803002c00450032864000e1650490200000342042c1080e1403070a00c0e40034030360001c50180d544841c0c03220809500145802c88900c0040d0307140c0c0070080000e00d5a0200060405000360307207000602c4035003089019141444202c03000e40a50811914242d00e44000310740504201c2e01074031040d0751000c1c210750300b42c000d01d803e400100c400c0e403000c25411014107a80e80658180c2c0e6040d01d0402c01307140c10404040d900c204e2131160500507802001400c0007801d04d5005012801e10160800c9040c4e40c60f0008483d00d20fa88000e2034400b80e50122f07030300d8840d18040007901d000b02010385041c098030007407490181c00c0114069 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 956895782 1250 956894532 956894551
    0x1080c070f0b0718120210120204080106030302010510061112070611030106020d08100f091107060c1224052119050601090b030a021003020d0609021b15 67
    0x6002000d0000d85031440e05150b40c040c4401d60507182ca0a00580b444190320035035010001800804901d10803542e00404a60350000e04410b9200354160007110030702a84548148040c2d0280800240f055090050700007031032003900003260b136107003051030010030340540c5e4001410882c0c040b00f4081702120200d5810415400c00a0a581c1c03120342e420300c000078011120003000700000000c00010030b41d90110302d448042910380e80d03000642d115450150030002e6240152203400800d04010481000180c0c41018102c0c1c020201d01d042030610344501c400c40c2d031078441080101e0307040b000a641c0c060b80c3d0b02c16504070400d0b0750034041e0324011000340c00210700304a0054600405404200d2074950f036100300c50840c0200a8401c03905040c46c2d140c0040c88504505404940c14403428002040c8030505008041c5024009402001050500e4080003500100350303501009042d403c00542c9800d54007401960003501640f00c0141c0c1e40d01c2c0d403040d41100038550102503900d9401561808420f40f0198031842e41005801 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 956897032 1250 956895782 956895787
    0xc070308090703030c140c130c1e0909090212060f09160608010e0c0903070902041e2912250206071403220f29010306021e0304210c0201080c 62
    0x340203d618160f500844254056102040000384090030340020127148841d82d03410b020a60181200c40312140c0c50140100490103800c000d01411141d41e01c5514058001031018a0392403a01c286a0700701841a16111a009146c00c10080d00a404000c2608501030001d205841a031901c040180034002c18003506200c90020f00101d010100c41c1c0081e222640c2009050b01c0e1455510154480258000d110700c203440d83c00610030442044082150384111164107041d08100b056a0b5550000c81c13910700345100500405011040481103503205c098842e00c3c07011000300d841c0301d0420b003074041d41c1c440103000403c55000104106000d540001022204c5890182040d1280c1710000001d000032028a100d10620002c8012502849092800210043e02840401d030940c60b104408612142d500040001200a42d80040001528550040c02d04e0000790108030225001e88402214a43c8161001d4442480c401651030183c0c0380480b404d4000100390603d0440c0d0b01c11a40040c051160040101c0c1c0c030395401 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 956898282 1250 956897032 956897063
    0xe0906070e010c0203010e0709060f0b090f0102150906010305150103082d0a0c060506091003121b110103110306130207050f031204050c0103090312020d11030c070308090703030c 78
    0x1944211080513070040c002d1040208148045544034010302c52031103800d0422200250082021046806440341c0d06c0c4942d00d007442c1041484124a4a1400b8904504c5080b40303a0100141d244565406900c02c0005000a9451820301c00e01c0c2c43c3d001151100c06403038103001000060b015904664040401c03820070110318440c443c000256441c00c074140315103c42c0016907101d013143c7c42240352283c0762207020b080100d9140e0074288400e90100310391503445c1c028010414001704403d58000d0304607261610b442e103440d0201d04403600b150000450101c640c038010f001d02105540e0180211030040060001d03050031803800300c0c00603425022243c0d1445400717500140260500c034040c04484840311031001282d60301c515800f6181c2d00d13102c00f21000d40302d074007845601c242e11390b20a0040e607800b260159980c000d40c0b00b9142c0d91034001c0d4044811039283c40e68601d000b4194a40b03110143d485140243d0301f060f11000c15040280040c0801007103c80b40350007001080c40020780101500f030050340c00101c80400340a4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 956899532 1250 956898282 956898287
    0x1050a2a08040b09090901060803031902040305030f0c010b090402010207120204020c0111091002010204060827060702061009150308130905010f09060503060618090309041a0a0e0906070e01 83
    0x200c010141203004006004105460700740e00504d250b0341c1c1620340e400c0c03d40d100d140550881c0d0085c000c0d0010764100f0004940480a039540c0c800015442403401442c05070307aa91f5031881c41d0f20080400d02c1181d00400e5200c1481b03000c1c85507524001099421080600d040d60000391a1206070003452402c01d91a6050f0007551a01c2e8140d542441c0c91134000c00920031142c4000c4415000016801d20070801c1c107840005291041c002d50381160107a0700d411200351a041c054403020428041e2490015140800790000b0340c6040003014010819a0060043c9081c14100075018000c90b1b0400b00b00707207003418041c0d0b24a501301d00200040b83d8000030a240c646601f02122192605a603120307140f49400c0c003001003004981c10300c506013120381205042101d65950024581c0740c01080381e00c00c1d4070210b0345a0410400301c071542c00f40c0c3c0c01890442a00c2c03510702d00f4000030302212a20f10081d282c2e000301261641450a0014682002d407107110310741102887c06844040e0389090082c11079003000190880f0041c642d0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 956900782 1250 956899532 956899607
    0x213020a020c0a0e0f010609030804061d040507080402010801120209010902071a04080307261303052203050601090e0307031d152d040b070c050406030f030e01050a 72
    0x82032100350f195100c600c5038074201c00303482c249025890b80c03000244250194207031000700c0f0b07445000780782450300d448401e540c87e0001d40100050f01080340c0c2545050f86d5144101c5d80716a03406e499400540c1003a0000400b09801600240d01c0c80b0003021480000d680d405001078119021114007503070b105414038007008a522100b01a0018000b04003e02003004040e02c05144610016074a90800001241080e280c06020006d15402000b2040c0481c00b01c14041055441d04c0d8040e0030058580400c1c0c0000c01e1502c0490350500c1c03004004420b05100300032080c0503039401801c0b40c170002c0c8262200500219200e01c070f414402024410f2442d500036030b04820262540c040b010040c403442c90101c00c0b0101071401d600c485407600c1c4c030820381f400c07071b00741010003040b10071502540300c1c621410182800c201207956270002400351030f00b0f007680c10005001c0d960b50207040d0285200d2032000ca6042b0345842c014000e030113545216414000d090100c24481ca9103c4409405d0010030840324980c1c03030384140f0035210f00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 956902032 1250 956900782 956900803
    0x913020901030b0a0f1b050703030e0f0106091d0c01111c0c03031508060106210c020c0310180209060409060509030a090b09150901050c030a020705040f090213020a02 73
    0xe040d140c00001030080030a05a84900c4071640d09121003140220b1580440341c2840d80a0540c11800c1c0103011564031400141c49803d01c030b81400690200405540b81c030789940d8071104013041e9107030710052003100602d000700ba00b41c4601d28601d10b084041070180a4461104400c840d041043c18040d5164084082003034a114074240310001c4108100e0700700c001d1561a880c0e07429404039007807403403a800000001491a0443d50b142d0082c03c001d07400d0600441d01446128110710145030614003c0503488904e2094180c81c0351660010001d0110740c90070705060071000703e03205105518060407145050102241400181e904446000b5656a0000080c000305a84070015094500d440e041100d000c0d8008002c5c070420600b1786401781d02c02e40e41c50392942e00d440b400680d650450952078103803002c5038840001d0b101503803050402500b40480540d0075455500304010620069009810410641c1800c2c400c8421302291208248412411900400c5402c00c6003194411401da00081d1148928802d20019041 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 956903282 1250 956902032 956902039
    0x121e2004020f1e190903020103060b121501050705150105090f010b07150e060406050f060f031203072319080903090d0201020c060f25030c120c0b010602250501020309091302 76
    0x10003007030a0000d16170300e80e90100701d0200303291400100742e01c00c841d0f0640e443e041015021007480d55032003e0030905a808541082d046c0401404044001007040c8012526500211000c4980d50301d45020401c090002516811070001d6850060211b018110200c0e2036840e005200808645041042d800c010320f4510b0125441c0e02070207040c0400c00c499a041240214980c9405a11945403082004500c20004402030380c1644005d0030310001c0f82c0c910000c1e40d407010113420080c82c40c201d541822049041c0035440c0303032620301c00000c05c01520403810250100c5104180340010443c68100d240650724480c2c3c49001d03204809a50300c3c1c008682c800c21481d0b6011801620300c1303445100c6a900304c0788980080c0c0b1166959480c014a41034440035440300c03c3c00350f0b0340651303c0e8078030821607489410094501000003010494850361701c00c04288448042c9008100b254000c0c0300481d00d103094941f40d0030b019017840000b5801e44c0390800c0560381c00416140000d104441000f4140c9a0f0441e01c1d48118200100030f42 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 956904532 1250 956903282 956903317
    0x1a060a0b0a170a050a240623030c070c060224310501140402010912080f03040f02010e0f210313060203120709030c121e2004020f1e 58
    0xc03000944c1202c0d01070690b031711050121003000314001d2854610009407041c4103440c402c04002c00752244419030741485a100d400641d03024226200911548110340c1000e0302c80c00080d83d48100820102a88001d1240344080d0440c071f08001d00241600c41d04840810700900c50b0130100346896241402089610002005012551100402845070300d1070b080098601d075103070803c1c1d04100040012520b20650341651460317000750425603103034040309201d2819201001c0c00d0054010221008000750300072400381c5007041e55407005100041c48807a01800041c02185075420074040c40e10b914103030500c4505d20500e4205803211246800c0c1c0346004140ea54031034190080c00c0001c041b500480145101065200110150f5440b003d080e1440c2031a403000401485059904010710703845a4407006426101d83c13850f40d850b440c02c403040c09801402d003d040d140009556080151078600000d155400c48003981c0030f40c00c00120f0300c0c00c41d00354051f4210350a00140e1404c00111040342180440d01d40c0900f40c1103412 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 956905782 1250 956904532 956904541
    0x2090f040519060609050f0114190905040f14040204021602190306050606161205070b091b0d0f060b06090d0303020d0506041e09030908010609091a060a0b0a17 70
    0x200c102c03030310311404046140650128034988291a40c83c207607034010b00300a0b0384290319070044451000d41c101e4845440c10910000020200f840c640000003c51540c030000c0c0f8a0500b4108021a40801c00c40381d542c0e4038103250140340002100b8a240c2c880d40482c0d00684500501219081c03e40005000a50251000d0445d00c04210801080c2c02564000c8008000960b606014441c0703030f1045030640c0a0940c0b030400b202c0005041b0041c003040c1c0c0e120b01d152080c2050031a503a1000000c006403a40341440c0c2000078090303030b00d42002c0d00b2200c0c000c5040700c54040c0102e06440300c2492500d0080042c0c00c041d19071790b8044494455400700c0b20140000b40c4821070000d400d0900a0080d002100d2100c217060034040440e01c94542400f40803400110b504c455400344861080110003040d084a00710144032282c40c0014113110b086c82500c0080207a4203000c1000c0000d89001403407448200b0f602c60940d15103205018194540405440c01e8541450105070b444114600c1074620211011503659401910400c01 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 956907032 1250 956905782 956905801
    0x12070303031a030a0203100e0c060a110c151b03040e0f070206160f03020c0109021c1a13030c030e0613051002060403052203050a03030506130b1302090f0405 69
    0x2090302203200c0c2c48000d624940d0004040d01c0d1801d0102c0694540e200c208400701903545035000d00c003000340d07001c1101c0b0125940008904240c00c0100c81c603010581d2161503c40d00310052210210800c002c40300c1c0c043da0340f103400001b252801404008000e501c0054280202000c04008031001f501c4820495400723481e200300113020441084071040018092080800c0b0513a40b0803c81030600c1e00340381c8840b10030041802c0218029008205500315564844c0381e0840580c07120684540d01556002c60381d074501d03065040032140c850b08076201c0d00004004204200784410a405040c001940c1494082d810f82a94241102d42c1404144c1c50b03540003500203100328031141c0c1d1701c000000f1200b050f01c944152824481003a610752408071000f4010442c10003480c1c0e1610b09803400c09003050b03074007a098a405605c980711146404440352044002c25540c42c00d0003024541250001ca2502005009100e0702e0100004250041481801031002c19000f052a8400f56603903101d0341d5050780040d10804c158034001d00c22 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 956908282 1250 956907032 956907041
    0x50106050303030a1d0118061a0d120914100f020307060515040e0313150909050c090109080d0f0302071505090c010e0f280308040b190306030f0209061207030303 71
    0x1005404075000482c0c03001100b044c047e40010b03518050448000b1162620b542e0042d21484860411600008050300c25650b144207030600340a0182c07a459a9069407040c000d05030001c039822503440c071841404801c0580e035034242d01c07079619403d624000088554000d811303461409040401041203007400e0800c0300000f005032501d0b102c0703a4119070034080b0ac9800382c00540c991003100c0311082d8812a0a0b0b09000108030480212010b1040e458982d04065865690408407802a927061036034280029141c0031640c2d210642501030800300e030185c0b640540749200501175400e441d4043f0240f64010075400300b40841101008140601103e003070202e40743c10a9051317102c0d00841c0b0342a0100720380e01c1c010812030a045140e03180f0404041d0800819101300d0710b142e50580c0250042c0310042c60b80c100003100003240d0402410040500c103035020348039585003042008014101a18004040c9401010004941703001c20328049580c064580030329a49441000c07070204c1e550296511228819420000200342d4954070 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 956909532 1250 956908282 956908301
    0xc1f030b060c2a090a1a0d050105100501050c1020040e09010c050c0a06020f1315091e2309070f14040503070303080903160809030f01110412050106050303030a 70
    0x2076014200e040781e1608003008003804003e60010f5038000094580c03040e40d4403c0c0054820504203d800080801c001a00140e111404807201e9440b0300c00d1000e54084002110050300b0242465030600306240003941c0d0781c4c8005c2401c00140d07038441d05030320fa102c1030311880048c04030341c0d0511295840d038640031292914501595403281640c80d00c0c0300f040c10b00b4410003d0b100480000c402800768800c5a4071810041c0d00301818602c05d0807400c200b5020000001801038004150072002c1e03245141c04a4009818200190300505c1001185548a200c582d40d0080c42c0e01130710380e42d441d110400d00501c04490405ca80d0f011300c99030450101400c1c00101c98021800e10100d5546030f8588200c0300410083c15028008c51148580540c40704030306000180c09800318941c808002c900310703420000c070307000c51607035107007180c5800c0d150b0500000e8000081e080a00003150308845020003480188000503210510784101d01c2079141d506a003420340010000290000300c02130000404890322400c15103410070080c5842c48 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 956910782 1250 956909532 956909563
    0x91401050420180d030818120d0c0905041a01170c0a030905150403030e01060b0f0403080f0d0212010e0a05040321020d05010e01090c080903090927010c02010c020c1f030b060c 77
    0x3030441501c6c40c7c00007501c11030052a05515418295808501800f50440b003602a0070700071401400309064030385225036404900a107018018109079400050002d0103070790b036603071040400c00c0208503103030400c201280d0901e01c00d441c0005010710301d424068201389070316440e114600141c009001c1850381c1504910950380c4c4503c02004543d5603520504c0e9a403007104c00040310010180b0040000c50459000b4152100c58014070910704816541c0030310803a441100c1d102d080d001043c3c01445034030300c04625180d01035415102040542882e071000380903115061202140d2902800000e4841110354040e5130442021000620103549c40c5e03132108030001c900340603030680d841c0740c203c6110040d841850400d00500803500614680100f42c2c0030f11000003401400600d006641071119040f5501011305051b0034800f9500000b421001e000000b42500c04012040b41158041d01c6260a50341c3d440c5080407202c804e0703004480b600b01700f601d0180c024020b6005991340c070050200782100c4800011911000041a14 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 956912032 1250 956910782 956910811
    0xf1501060908100e010b0d0c0f2c0c090a0e091203070f080402040b060a030b090108011a0904060f050403180806070c02012601091401050420180d0308 66
    0x109012104119940708101250344202c1c0f807040c120402da840349001042c4203001081c02e00b88400443c0b54000c10080c11030b9183c0b111132081120344081450a00503181c0412080c14090303202500d110348500340d4400450510107840402d26646604003150406540504403500c01683c442000e0145541150300d596540518407a5240d468041e0084070b01c100b0b26a10b4007148800d0444044540200c010003c030b81144c0e450b900c640e06691440c016010011141d580400d1038031590303043c0300500c0010391004095a060003620501d1420100601c10010000d5950803881ea403103080c0200a0701007505000c1541c2e181205000505a1210f401380d2903012003c15026010703a40e0700d5a5503079140c103d42d030350000307111010b0b10401588030b01030071180404800c00f4941d03403084203921038070040c20a0348040c000b20341e1b802076403145003002003034140185000c4804100784001c03081c070003008011401c00da2044613000260a0342445086595800d0008045c0c18644a0140b610307014099500503141000c024484 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 956913282 1250 956912032 956912039
    0x21f06091a01020a1202150411030d020f030313020d0804080717280302010212010b1806040302060a030203060a080f15010909050d0f1205090a03030e0d091509080f1501 74
    0xa0742400c04607801a40240707029122901c03010724149900c02500c045001e040b198020039030800030b403070780540d005403000c0030040c2030242090315110300e0702d010398250b420128036950f8407500842981e50102e141c45a613080580b140c40060944119400d0091900401090218804030700180200c15140302c0d00860610b0b00445c81007070b9450602d0a07480b240d2150020707481d5550254032400388841c0348203000241c184a80003c1c0c51072004401d802c03099240c01d0124010b640d1500102c01c1e200f881109481151a01d030654000c038400b445000c40c11024035400202164168460003440c60040c860b510030740e60721406065183d80c845001c0100c0b001c030b21407003200100f031100081c843c60600716400001484108601c500135910103012109290a0081140c45820f4803a621b004003482030072004083c000c8090140740290840b44015802d900790750014080c0c50300c0301d4109900c04144d511281c8200c01c0c240004008644201d826007203900039001d410f482003220400090820204813500042807440c0c1e89 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 956914532 1250 956913282 956913311
    0x120302070e130303090206090d11010905010512180304030507030807170c0c01080619060206061002210d0204030606090203160e1e0307030b09030c151605030601021f0609 75
    0x40c0e9507071940c520b02c202c1140003e8041d600c000303840e620190031181011135440c0014850b8501c0b5005442c1d00e20310310501d08566a018181030003501003420a90b0a20500c0044000da0b590014143d4044000101c0b09a12480f02002910003c1d80d0003000c80305000d4591500c049103401450741201e0381d0112054405601e9940c100742d807400d44a100081540c2034440004542122010b010281c10036140f100c1e504907510300340d103580d01900c00c60300100007030308210003449102e40200b040712045400c4081002d8043c41241009103403c418070301480c1c0c84410a0081000074822030340001d10151500c00001800000d98000e14807541042c0c60414070403240c00c509403550b0b0712480005234008284400d030b540810070940008500407026044420860302c0c2d550350520f00707406542d0441c1607070002c94031441501081200c0344440710741c803611104504081402802445409203040c1c00c0c048040001292a44204000700420000402c0000d00309519211030000780640d002d02c0d1840c50400010b0311813401d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 956915782 1250 956914532 956914559
    0x608090319031d0f010c080c120414010e16180e0601170f03160506150307090c0315090b1302130e041e0308070e030610060305060103090c12030207 65
    0x560441040d585401841c01c400400d00064402070080500511602260301040b4020100c083d407000010400030107400600700000040042c0c103c2c2504002404d8545202e071070094101781d00c004c0c13050112001c101d10034007600d003020084040d40314030100465000716080200c000c0360142810543c00c12800c0540c10261241140810a03a500c0040104040c00d8400c840c2d1905810340415203103d405030000003030035507111a01c001407410340c00e01103406001091180f240c0180b03d4820540c4119070403000301c4d40340c01181c032507841c40035920075015030f03200c2c066000401d03a160746840845603581c45200643c01410074000842c018015564160001c184510032200b05114039422403910b980b0703005a00d510384134024000c444800186e01d4ae00070307200d6400801980c052085e2070301d02e0b2925001000070046880c5680d15882075002d0002d100d1380c2d4207138401030420745400380b4000c80c060360b80100503401790243d0790004190050f80d82c400950018040c2c00c0204980c800d5091b9488030b5a038003020418803 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 956917032 1250 956915782 956915797
    0x4020a09020a0905060306040f150905090f1518012a1107030f080909040f0611190c03090b1605060601021212061c06090b180c041e020c0706080903 65
    0xc3d291483c24802450a04095a40140010320100710380320903003401e00079503000400002c0390410103e0706004c44c0f005805042d5001181100408120308091000781d034428413802d4056102e040c034004034120b405d07410301030400e07018003070000c0c06074a502040704629041c80b041d40c8401e504000c003460695510522100c07018043c01c00007000c115081d40c591464130f0b20240801c90714100c0811620360180c075581503035417080e400b50820001000b4141031038425a126111443c03c3c1d41000c00002640403000461076035240b20a1034043c00c4040c2d20726051ba000749090f009652060b00108a500c0c624a1943c40d1a014510650558505488241c01a81d598603a0702d51844624403d1002290140d9925100c0b54001c000604034400b061a6600203001165800d8081e1202925502484140070075110f9442d00305d00a901c207045100024113103da190245060500d21440e114091003007801406016a2900c0900e800219945c800d10f618445c4e840c100740c450700c00424260f00005103c84004011740303106 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 956918282 1250 956917032 956917037
    0x302010507050c0d08250903050f0307020d061805032709040308130305090a0b0c0f07140402070c03080a0513060504050d0308070c052509050c0901030504150e0604020a09020a 77
    0x3190b44e071a0b00303592150300108500c01548400d08048440d9048840001440e2880e4544903030541c150b04042e810b0070103a91040c91664000c10810005071907802c4020181500302a0004403080d0b100c84601c0c00d103503041006000341c80049640180ad150038100b110f0100c5a20080d03280e8100580d0034804921000c860183c041000c50b000521560b41050803241c42c1b178880d1601d41d1404510600007641c010707150f0024026210041100000c480c820020440588601001401000d290a103d403580411340080580540c1d000705000c420030907008400c0c0c02540c5e006540648034152503000a103150000700b4185c0380710200200010b9064001d034112426240003070301f5182001030300d4406803181b03072000c0c25410410a0b10301032100402d80901c00000021200c00c5031601201210000503100302850b04910f40d00307441d003014090100d0300481101c003003110030700b00410190303101c2c01c001b071a469118440c0c01c0c80a040c179030b8400c0e5828000c11610312891085030228016915070804c24224012145003002 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 956919532 1250 956918282 956918293
    0xb03060f04200a0504150c0b0a0e0705040f060308030c22080c040b0114070c0303030e0705030a06090c1211090a1b030908090a0b09041b020312040c051c0302010507050c 74
    0x1030003901d41d0b0003050281000c2c00c14501c2c00e6911403507070003000600c4c808030000802c4142810200486104840e8103e00d1503070f024440389142042c02602c40a0f80e110b030390301c141d54a10b030740e000e40065508410005d40d04103500c1600c9140102c41c01d400d1340e00c02c2407040705c2904000f02480703003d81500c503400d041c0c489140081c00e21303448000901000f0074840c00c9060500c031200741d001411040d118010403113644220a000d1032107103186005000e580128141c4401600011000d0045440c0018a01c1c0001c0c1c00600200c1d1891460034003611100054210b507103801c0c5600050300910103241084d80180f4000d4460a00c00d585081c0f07803808030745508007491420341d4448182c0354064460340111709402c1c040c0320020700e0400c0c0c2800142a50700700394000d102143c1c0118110702e20b4a03041c81511003905c43c1501161040c0c0d0811700007500c900c03c0b0410407030b080185401103014041100e510718054000501700c41006220484010100054454103c0040d03080c00e0015405900c02d20688140c007540c40020706 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 956920782 1250 956919532 956919581
    0xf040501062c0402030406020d050a05160c142509050601050f070507050603130506090307082b0212041511030723130303110a05061603150b03060f04 66
    0x1080b000c070407220303a100c0c2c046410740a0260342e10b9100550041d40300c2d010040c4c4e240041c003d000203540008180c1c9201520341810002e205600f601b803d4456500c034903111b095090a072070810b442d0040826190300c2031103542c13448410510b030070440150301619545150003007503a4403050b009858048039250f0000e0001e1012241d02c00140000c2d100c000d224a056501c110344480c0856001c0c1c00848100c01404400c0c024403040c01024003510350440c003440055131400901c0d031122a541c0c464030100c0402120700300212400400c6929020400c1d840c001820f40d42e45005e500c0901c2e40c150141c8050300e09100d011001c1c038010a035445246070311a05141c42d142162f844000c1a00c031140944400440c80324807880c1030030002010700007020745c825642c0c03120700507505500b001025640811118000e96200141c0c02d03002c0341d000510150312000441c1001800400c0d80b00843c05898482d40403801d080386a400450318801050144d071017801e0549203455440306030340810041c0e64ec6810003440303d019000201 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 956922032 1250 956920782 956920817
    0x110321061915030c11100f0b030a0209060d030c0f0807060b030a02130e24040c06051206090601110114010608070306050f06130e0112030f111c030f0e0105060f04050106 74
    0x514076000a0500b1203860401c1748004d410000d007412903000f055a680d0b03041031100c481d4031415403041019130051614909517408a0b001c3d98001c2c081c54072603c598682c010415100701c411102e0258001d01c0381c0b842a0f4903107004141038000d604115a5207092041915141c04c0000f0400c221703079002000f0380c00710945c4840450042010f10301e0035145000d4100108002e44003104004070800801307012061920303050900f10042d003019040b40342000750070005030201c0c07101c5009580d08040d0480385a0b00a4846c2c0005071020215001206030b194242000310143c079400c064158104c0310b0b02e45071040c0c00d41e9820800c40440d0300501410350b200b00c80065501d51802c0c15800380c6200319441125044d001d0302c608118041a409038800c0501d159500c50759010940e00c21102003008010f4205400c0042a140000c0d032151642c98210915652000e1840680c6109802158403626005820080152a4055113000c0c5c0710888080e80900c80711034904e02d0385c0c1014030402e81200c50f03640c0c518030390030480d801c40e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 956923282 1250 956922032 956922041
    0x20706030b28170304090f290f1302070317010501020d080a18120f1803060903030f0c02250b190c0b010e06120f03030711032106191503 60
    0x480d5901d11400c440894600481d200b00c03e00d0030020381c000c544552070300c100321007512440940f901c0903d091841c810004103c00c50941440c40c0074000b68500d264410340461145184070301e0b610f40c0241d05400004501646a0040607c54000d41d110f850074010f91242121058081c810030340164007000310075029601c074940251304030003c007e01140941060110800c0102800030680740e60036a24040d462160f040340e84d00f000802c0b01e00f052105003200c80c00e0505005140c0c03001820f10b03500c0d030146000301446640902003d00b001e1000b04800c10034000001c0d9500710700c407811801d201844c25031802d024101400c4600300c03517220199510344414403000e10320154030b6610a00a10035070b43c100b0400180109082d6001c0e00d10000c2c002407624201d07003013100c0305903084440c4100d40c012403001e60f45e1140100c21290b00c280796082054518902e50a00341c40d51041c071a0817002d03141c4105e0b01d406080160ba0000b07000340740846410520f0448a2844400c40c0070501c90010b44040460101c8c4045020381c12 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 956924532 1250 956923282 956923339
    0x200301092d0b190305010606120506010e010c05030d09060203010510030b0d020f0109030b090c0913051203060d0203030c10050603070e01120f15051b18041802030307080703020706030b 81
    0x16000344070780140745040e00f250b400485603a5110f6000713001d4254048600820840c01c802c0c00e00050500f200043c00c120a10080c0038108650400c01e4000e1103010001c0b201d0070309591000300001c540034109000250000e0290b2481081043e100c640601d1082c060400041c5005100c04e01a40083d820800c02501420060381405003104002010400142d48144140000c1002d0240441d98004002c80110002e0a803c144400c23041941c022400025000641c8010803960070340e01c1d151800003070407904842c80001e515100000d111003107002d020581c0c0210244480381400035840780c108041d1201c5050007002000d62520b4010044041c41001100c03509000324000c0c6031440194580e91050030200e400780070400d484000748042e8440c0c1d100002800c020b01000c6a041118a501c2c00c0108681100442e1150743ca40074031040046044299842a0ba4002e007240c0c2d40350043d00c0c05603415006a8410380260050010024005000c0d0003040e80c9418014543c001c0400d400004039030000300480d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 956925782 1250 956924532 956924539
    0x3111323060307080103030905010504150e030c04061701060b03240103090209041a0105241b151005040234061a130b0919200301092d0b 60
    0x6403001030744a520086000d400720303544022856055040c040c2441a03580e01142c1001010042006918100c0703205410064181c5804040100d00a0000c1d1401c8100554a07903c50b03d8a4400900102c000c0c407279101d0040450002d00150f6a54220101d06000459007451840e8a1002403200500c0d125070200e60301d001410f00007680c909507004110410422034040301c801c81c40b01d5003000130480350003580340140412200540d0204140b85104142d03c40a22804070b6100301096104801980d0480d0700c50350f5405c9011158034042c50500c030486000c050b0f458480c0c04042550108040c01e090007120158640f1001000040105003100615600d01d04400c2d420440004241000240319019050b0803101480c5401c0c882c50500040081c21459101029500c51030040c1c01e070036603210243e0b61540070007126440c0308441c0c078150214001d44090410b080042d07280d2501e03000d925514201560681e492034404011002c0f000f10003082200049540f078a00c02d2440e5440a400d241ea07030048001c485c4040c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 956927032 1250 956925782 956925839
    0x15080d0c0602071704030b090a053003040b010e010609150516020a1815050306040b0405030d05070816050304171e04140f100c030315050907030c031113 67
    0x39200e0024000c441c1c9400c42001c4c1c1c00150400c00d00000403200b507004044000500703c400318503a9040e5452401c00d9804070020141402000e42034280421698a0480c921110742e59150502d0300441c940001d000341c80c2100d800f5000841d0300ea101d64040c509407010030780c145240e0b411205054a50390003484040910044c011030076001600d4044d0000000c00d003890389603000794964585402920100d18004c103440411407002c000c5582d001580f40e800941143d86c0380724603100c5050103030441c40740392840100503050100f8842c01d03542c0404214450220302a208040599228040301ca80c4425a006400e075107060030002c005001c00d00c0140440c000d8002c0780301301c01c10004c8c0480788582059100c076075040d001042049503414620400d1a001904030399288051a96182c054650f030083c21000e400c05076548400b005054103500c6c00c0e0f01901c0024410f001500d04074071300401400c0101e04d1500002d081422104440b440c070801d40310100488502c0c510350904140d581c01c0364084060102810300c0d200c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 956928282 1250 956927032 956927047
    0x1a010e0426120106080112020303120c1603020a0b13081e0c01090602120a02131203020a0b0f07020114060d02010c020f04180507060c0b151801170115080d0c0602 71
    0x352000b004006102c89860205614040002d004a00f050740300403601c1e07012400c4c8100594010049411016090140380035940f03842644e20000d0207149184040248240d106a090603000159040c18034821480070380c1c16130b58501049070186400b48024480201803007103054110101508028a24417044081c1c18500b50080703c030b0071f40f070760410183c03060b55000900c0301700c0c414030b848181e074000044d5106504d01400c0000c040a112407074401d803030442022203122010035200380301f00150150004071200050070400504118480169044405907180c22158480040f6519626200d40402000070f03004a00c50703001910200c116a80481c0e01c0f00c41d041100d8010341e55482200e0640b0701c10700c0c4000d19858940340003131a101544e00318905000f996190b800000b01c803400d540794000c1700e0000c5203601c03544030f0000c0707007035510020406c042c07400c081000441c01c0c000d0904984a04a0f00301d0003401848914a0000303855241401200c0450300125081c0030b5084c090521007101c00d1041c44d005260080 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 956929532 1250 956928282 956928353
    0x5011e1e031e0203100c030b03010b030307030c11040c120b0405010305190c0b0a0c0302120705120906162f0a05060a020f1b0a0530150406091a010e04 66
    0xd28100c00c5c0a61566002880c0d16103905108800b800c1c030b0290f008001d6043c0c100c0000342e41c3c1c09000c8001f810000142c09107401c015100c40d2800841001400c18050b850703202501410b240a2407541d800010b00c0d040d030702c144d00d24090140e18100e03030700103014166100740070801180405201106440c0b500c1c0d03004000039400c280400070701108181d03a0359060265198680242040c1044901c58880c6000340581000300c2c1c008205170002c001420398031f80d42d81100c14042181070040f000c2140354005008001002e00a02c8040040d4160b40d4650049124111428940582a10101060300016849024041810140b00514144001c4e004070b0340d4090290100628200281c0c8011103100c60030a2a0303209400c0c005084006840c2c02c440302c005a24080700b1203040040070350024820308a200c4041b4005a00a00030b24055060b0304d00075002500d030074101600940a40d0200715140711035403c071b00840029003060b40703059540e00e042600c0903803107035204e01c080c46900c8c1610b00701c54114034140e500d2020 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 956930782 1250 956929532 956929543
    0x100509090114030d051c050a0609020a0215060d05030702190f1203030609020a08071d0a0f0f0609182c01051501082802040905011e1e031e0203 63
    0x800c030310b42082c100705841c080c1810013100100c1e0405005041c04429420b03501040c0d00d6040030b20b04480014203648604128024041c1130344424045440002d4004001e680450103d407014203194185499403201800d01600c1607506801501d01c1e042404414014500000012000121042d0080000b619041c45440440460b408103c0d80342d01d1700741c035900305a01805820000c143c8075008505040641d500948800001003100040040312443d070120715440340d80b070b0120180b02405018510340c4a20524010349502e000d0000103010800c0006400d5124110003419506186800c41400f510700030441e014006a00c210011501242489454080710300003a0700004601c40011840307042603c3c0c6100000c400e03c4450381000114020000c81d03404c842c03040707445620919408081561032060400090003140c000088950401e0000200c07140505811120040410003503000700340e5460303581c00c2d04401d403040c0d1030760350783e4140e000c001040c082c1c0b414504e0390300210440544080541d00181c1001c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 956932032 1250 956930782 956930789
    0x5040c0503072a0206211e0a0603120e0409230106050d0525081002120601021203071808030403050c19061b140604060606091a03150112020409021804050f01051005090901 75
    0x1020355401f0701907800c0402c1c854110019050801841d800d50302c0301002600c044d51190203020040d4004520f41c0c07203541c03040809540241140712040701544100c410f030703c0c1c2c000c1c40350080e40c2040c0d000319203854261043c0c200700b41d01c14020510b070104c000d04901042e990340740113811000310f0300c000510000d040c801800c070703103c074200010707501c207c0c1d003410050b8110040c1240e0f0444d44a02c3d0149040b40c40f0300d048a40101803414516403c2201300d038034200f94000c6800180c070358000032900108002c1d0010360740d80400c5040702c40340307020501401c0a80108010b80700b0007001981501100c100040d203c06107400c0c3c0c90042c2d07131081c5440030070414145001c8040d2001c0f10200d41d07845c01008521743c8503d400000d007940160b80c0c4c40004002d5484240c5000150001034500c102d1015140680e00403d035040f403c650300300c01951110b035a130003404025004610f194041c0d102c4054044143d04d0f091103014400e44c0500e02e10241079003002c0a1080e1b000c0482e650710207120302000010002d560300214640203 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 956933282 1250 956932032 956932051
    0x21061309050c040f2309160311090702121603090305010c0e032802041a0a0608070f0923030c0a0803030a060e07091203020705040c0503072a020621 65
    0xa1840c200f0f02c01161a80c4a1658805141c08107028106006442001c00080b9045001040b40c5662410f0340c1405a04a204004514089000000c02031124a244002d05c0215000940b0760f89603002661504154441c0000102040000c100c010b5055004280c0c0311b40645031406c1d89540329640da60841d6038400c08400420290b80390517410349410007000c10880d0b51313040100000a064440344010010002c00248102d413595801e807080034090780a1b08900c40020240e400b800c0c1d4465002d410540280c0340c3c68000744814030059a124001c02c9007004981d807003e59844440ca08100000c03a010903c11490381c140500404441e95a44d01e0340d9100c080e2503100003541d030b40c1c00e0007400c0380203c0c0c2d1182d1051030510ba26504201e0840c1d08203032074400316034151403101196181490304a003826440e03045203074054a04002c403200b60740d2110266105106980300c906a03504128062050344c030309038118007200c504140c41203005007040005040e5241c480e151640c698691440c100350030740e2046510408 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 956934532 1250 956933282 956933293
    0xc1203040f140a140708031206130513120306140d052109120606060f0c031224011e030c0e13022d0324031509070603022106130905 58
    0x500188001a6040c4d4600900030601c140c0b9005a09850340520074856450404450010b80c03903807100c0420f00031814100600700128a4681e0000e900c29240707810682d28125400610940503000c1c0c030512041e151101c5c1c0810369800f150007003120780540340100703d40d87d02070095100406a41d403080c03194449980420340c0d454140710818880380f2070346038040300c85c0740d88148240407494690710201c51124545a9405940e254459591851403203501c903440500c034600420001540100c054400d4100e4031048860044c40c000001100c29210029100198544e50b24043c0030640c0207a02042650a007810002d0810001d01d0000e106114a2503181d642e03a900003a2150f216446017080c1e4588a0601c0c460b03484186075503140b0090341c00f0040c4810721800d81c010041d040c11a80810603290740a000f81262420320008500a00031501525082c42510440300301041d414064001d40d04110b402c620031032131501c0000c942c0c00360060003408003900000ca5208940007201c05001d92513000740100000c02 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 956935782 1250 956934532 956934553
    0x30c1e03010e03041a09010c150902040e010209092d0109060f0803160206030c07061b02070510022802091e070302160b0709120b0117030c1203040f14 66
    0x6081d02d0201c1c10078181034000704400d000e0310b2400e07402e08450b070824000041e11503a04000503580210402800741402440945d003411280c000d42100c03c40c28801c0d2004e0244141810500d0300784d018035024158084841400184c90710f446c00c1e07545140081a1650420000103041c101c2581d20080c4c06c1100300c180c60f01014802d2b905010008401414000c000754030b440d0003c44030810040039024000e01c514800808034801182c10010345841c25081070707003089038600c880304113110f401c00c00c50264098000d85038001007d1501007880324600c4c400c0c0c1c001e011b60300c81c80f900b544000e0030400358500701c840001c2101000340c1c40e0b120019200c2d00400f00492170300388140c800071005030f030b00504c02c0301010300402880404a900303518119a09903c000d040c6103503115041d00340c4103031038581c2240b103540074652290800e01c078110340254122120310f1f01c0b0010790f00e14160702c00d407207108c1c40ac100304e11a070140700c0302858081d0300801146d209008110311910189141d554136400344034462140c0c0903500c01d40000303 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 956937032 1250 956935782 956935789
    0x905030a02040e0120250c0e070e0a080c01030c0f1205042a080c030613080a020c04020f0702210304030210020f0601090c0809060f01140103091502030f1612020306030c1e 75
    0x550724003078002c585035540f0480d0300c030410700a00c10308c041c1c110049041da034012021680c0b00d40c0c000b450801c05a8454031465550345030780c0051b60000781450f0709050031a019012100b190740c0d49596400c1c0588080d074000d400780101500440d00b00c500380782080b00d0841c1359941e2081031242c035030b8a072018624200c10185040c00c031050340c07846034020a0a00800c074491280300320313440380c0c48001d0a0300e6601d141800d03400c0018510485402600002e2110802d170b6000c1d00412030240f08444940552400100038030410380301103601481c0303510400040c130141c42e0504010201e40c03224411180402c501c08001c1d82001c00a9204444007522010384200c0d0315007200d400740e40544010000c280c01c0c80c3c00c041807103542e4418030902c07500c02c00c03807281c07030074564881e40003408520780100d40965802818201171000b03510448544000e070015102180c03088a52104800b9007160aa6a070400040e54440c0300700298000782c8502d62500c60080d0042d03454890750308603402059003280c1c4006440f14034060 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 956938282 1250 956937032 956937067
    0x70201090506300702061311130f0f511401030209210a0f05060f0106050c0309131d010c1103160807030903080d0911010905030a02040e0120 62
    0x34443c1d80003540003085400c0d0390004130780354040202580c81105100d0b908044401212040f186500100f0082d407101c40c3d400590003040403104200301c10016101c240000740c0848010003050303000c0c01a0b184684101030340758074880306600c1c4441100440780340d1050b840001100c410320600c900070444001003209141022100f405540c00707080a43c034003402540016803460b550000600725580200d180f500d920810400406469809021003142c1c1e4200e0400719070b1540304030b5469100d0450103001064452185058030000a00d030710065090800340d90400449083e00c2040780d01096907030401c0304003000ea107407a035030380e030000b1a000044c40c170f040d028001c00700003031b000010507580c0c410480c28003109490005c40321300b00c0c1c10000541e241d590502d011107481c6010750001e8007842000c90014558207596220811891107020740c800850078003001500d45500d5489640e5054200000110140c1055048808410901800001c01400c0e04002840060b45603004019290011518040c03400100c0311 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 956939532 1250 956938282 956938357
    0x80a0e030c1009260910020120030916060807110a020a03080705010b01030501050f040905121912110f0a2123010b03012723070311030606070201090506 67
    0x200040220048581102c01d807044042286c000d645d03203003421404030320030345c4210b0f4412030b051402d09514a074102300c071100b508141ea0021490154117a40000131180c5540c22044604a0f1100c0000340c0d249002601d0f252040000e4511364003900c0141c0005035201d1100c440910704c01c1c0b010a40302c80060504c80e08440c40c144145040c14074040c0148401d50f252440c400c000c03001100d001c50b01c0c18007440c00d10308190b010485852107100100d4107021809050340c01c231005050503550805600700424890068644100c211504854100040200e0321062002081d00d040242040404040b40807007414131500144d003403100701ca0343c03103219800d40000b2404100c0c1d68844c1803101082941000e650408621041c410001c0384018072a26900110300e00c512407044071091034080240740c0c007a04014581d0009001c0441d07102003900001451a4003e04c1103001d84d4a001411900303550f030714070501050b5840204260b05102d0182000183c070b6644c407000709582d80c814001c100019207016080c010564000340c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 956940782 1250 956939532 956939573
    0x190e060f3403270c050d02040915050106080705030c0a0f1b080405040b031606051b0601030f0204290114120a0f060b0c19020a0503030c0d020d02070303080a0e030c1009 74
    0x5010218106107404c20646504031000160701c100b5100003801000034270802040380050052400103506298002c904070350b4030f51901403c940d140b80d821200d0344400c45e1100444003040c00b4901e2035505c20815004401010704100a42c0e6104994440c2c80c40d607100d400b22645240001c0501060425000d10011418107500900304a1900340c4050b00c040c20034004d0408014010032600b00324408003840105600c0c034181615502d503145d00300403545141c10340d8240d0003907042102e005000740312040b80b2084003181c8000619402603030b0300112291700031208603a01c101001c7c4010003988001101d0300c0c0c002c80e40103000003040012038440c001540c550758071000107501c00303100e4065540c402080501605414400c500c880c0310403480054030a4005401058051001080c0d422003100c000a41014080d066021140e840964a4080741da5003903c0c00010b001400910203d03140c4d8440c1d80003881c1d414030f000c1c296420000a01c204070705c2d01c2c50150840000940b5840c1880504c511840a04010709181 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 956942032 1250 956940782 956940851
    0x103081204020a21111c122c011805090403200102161103031e03060d0c0b0711030c13020d0b030a0305040303080a02120c0a03060e190e060f3403 64
    0x702000003035840c02d4000981f13502c2800280c1c40309140306020400d0751300b1080700d0b5402e0004116069280d00c6080311001c1c0e0108186552002110741c03a03440f0341c01240c0f001008084a0742c0c40d613a0407601c2d100604c5810300071000141551180e104c00380094044414030000c8900b01941c0c600f0300040811903042514000e4000304401002030711f00c1c00c46001d641c042000341c00c2d580e40782c01002c030b4011400c0304000360410b00070360b41c081003004140008121150081e041d07611010100010162614840030340d150f0b1080c105400076901d8002d2307801610a001700c040d000140412850086401c01080c0b0307038120001080001c050042542050030150459482d410850170005d084800500151019228940100d4003140180025104e0b0308501d0181043d51915000c1e0f003091043c4940040030710903002429424842e03114051400025140e1151050b0112028652207200c10405d907102c00a1041100e03c0c4081012000030159126014044c03134940e4000a0389800d00c0107824103004c1c0c0f4100c1d4290068507 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 956943282 1250 956942032 956942059
    0x30403090611030c0102042304060f05010c020f0a030f14010203070905062a030a14180f030a12020c09070309020d12030f052d0103081204020a2111 65
    0xa2400041d2070003402c295880880ca580c1c0d4a14501401e040c414580d0b00001d400700701140c8220511014030b20858409041c40d226404100030ba07032060165a420042103102000b080d88960010508140007800c00c080c2214201d012541c585130607001a100c900201d0744d140200050010240c01c7c21000c140210f096040414008116030607604c02ca034481c000210310000402403100390810503620046d11302c1081c0000683c02d5840350004070503500402e13078112500c1aa001140c0407100003d81c00c400090003144200104024500c4040000341c041c031075600d0800c0003a4200c00100c0350710216400500030041607000301700440350001c01440800d0308008503a40181c0b205800941a1035018585522017143d2403000c50050058101049201c3c0c1420103028030411034100c2070400390b81140054a1880b104880345a130b102007880001c0c8645c004108140c01c1209054400b5007240c0f000f0512000315130348580000001004044001e056400f1011444c100841e01d4031000c100b010503a00203000081 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 956944532 1250 956943282 956943287
    0x131203140c070b30101502030318070b1303060605060c0c091906030c030c0603020a090902070230072403021605120304050c010203070f15061a0a08010506030403 71
    0x6603880b9019a500010610500c406042c01c0c00d1200000213100c0700a50000d40091a0725009040c0c40e4206034894101c0c0209806601c00c400030721068060b002140f658036903030641c001c45400321140903a107002d100340202d001c0c03880d50001c2c02e0340d05e02c0001d050041800c504200044a10303580c0400c0c0316080030407000030380010100c2d40d100c0d6100219241540c9a80d070f82e000f101c11688041d6101040d51610314080b04004180030200309407805030305046411900c03501c1c1a412441501c0521010a080d5101000160000d0b001041304510180001c0503e418400884103d9010200007000d0345020301c00c15030344100c0c1081020001c011180701c00c1124403115000c401c2d00c04603c2c1d00c007c1007580004084c903082c20703103482c20b01900e0744c02812034040412450b00080140c00c01d440c02c0300c582c090101c81240f5903100009a030b0700d040c0c0094184010850384d5417500102c0005e641711142107a00c5010004441c008043c2030030b810300c14100c043e60b03114003500b4000c0c4120340580089118540500c244000b0030b5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 956945782 1250 956944532 956944543
    0x106030c240f050714060c0d05151818010c08010914071413030206070602030f0a11043005030a030c020105010e063309010905010809060a02030c131203140c 69
    0x3803d0900643c2c4076601c0c01d09614110420012030228842c1030284602010000028459504c01450422080e158880601e0200801488080d413040111200315030000e05000c039550841c0302565500103001d62000000e0070340ea0040041c4001c1512078004112038083c40c060490030245040900c0d15a02d0300c132a018001448400c2105004040494004035118070030200c20003554006149a417200c0651520402a41c0100d45d00d01007103502c6c10216060a149001e006115101445c01da8141401c108109511145503920310b4200f0b94126400c11242a41c0017607480075600400186550300303500a006815104660805030440e89801d00411a400d9a208400d800810444410840c0c82248404049400c04000c0820240118017a541114100000101071868080c0c81d0250095501c00041d10030f0b10003213861f201980c00000009030301d504c16134002c5134040040342c1c0003070400b40f80d401007290158841e04030302d283c01006030807142410f8221020f0074500750262059403605107859102a15403 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 956947032 1250 956945782 956945807
    0x10507050d0f120515150406140a0c021c060509070e13030201060f0609080705151603092c0a23060604090203040b060405060f010f140c0106030c24 65
    0x820030300d012180180c4030701d807080c41c400c0f054a010f00081c1444101802049021040c45210300d25a01d00814040500030a4400300d0307402d610b501165484c00c40f10a0304640c80805400e00304414100c00340d00603a110701001802807040e54050b01c48824903e44041190409040c0d61140d0380311001c10080204c0c05011a580070403013038182c440b400b81ca4601607025102503004440f4a814504011500320750000201c402c48031070710200c8544c0f42e540c40c01d00c030602a0074045901c00e06820454500a00100550300139114801d1030a1081a940c546622940008884908521071a043e00c0001d50710a01e0329078075000b02d030500c0f04000302e0000606c1c28030000110b68a80801e8241c1c1000070742d1607540c540039500249020a0b0541d40c0340b50034600200a0001252071900c62450000401d4850074101418000c000041c0c5412401c0070b50104151000d002000e65403205880410200200c0b000a01444000b0b510480c1100c60b92030901c0344259468007c1041c42c00100c8030042001c03042c962102800b001c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 956948282 1250 956947032 956947037
    0x6070c1109042a1a0d1103010e15010507031b0c1503020d1b0801180209130f05130213020702031e03070b090607050a032a0810140604140d0f0606050a05010507050d 72
    0x540d6120305421019086c04030020b0301541d00480005014064141d0407441006010700710340e902d40c242001540c1da402202d101030001400102070000388544481d5188903240203068900409507600140072040d803640a0383e40000c0c2c0c003c15101d41712000c1d801408071103a00c00360800e060040e2300d8002440c2c44070501c02c118522030342c0603074007240c20650780c1207480d003000c0038080d10295042a12080040c052a43c1954003131303403411001074a00762103110100f401c00d0b4010507070520746001008800181d040481c003070364907002e4001d01c0e141803200445445402800034015603214001c030306000300c107054014081c00c2c1a4200e10308120003581d01c0422500003449a081c0050188142004000098100c00800d00090800025200927580021005101d001e07009039503003002c1c0d102c03400031030500701e02030740d96402403010300061251202444503011001c0014054980010054540880c3c40020030740c1602c085a0340e2205008038106844100c000d0002807c0807860070701141d54040e0350b01c1a80044508 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 956949532 1250 956948282 956948287
    0x309010e120706080402130c0906030b040e0313030209010e0417070f083103020120011e0506030d0314060409170703080105030f010902010206070c1109042a1a 70
    0x40503994850015050350040d02103610403030301c400f0080c0c100c80d01560306900c64428100f041d00b8000e450300502c1e44804c91a03a55550301443d00c2025005480c0151a80350b0150725000e0741d80d403000c001c2014025442c2072b01490038640f131550050014980040e040307804080741c00c3c410000400d40226500e444003800032001913584815003044140c11480c228010000100080c100440e1150b51000340e0b1394044c40306095084050165504a00001ca403000a022030700160903018000d00c0c000d202201d021407040007082d0701c8043c89800f2115810b0701401100640d980c4140400c0e41000c001c00140a40d841c02d080003420400380107842003041c0207100034030940d01e0314005010005180c1e160740c21181e60b2000c1d140c991003686170140c1800001d001e01e6010b44240380800010000500600c0c02c0503406801070711094540300c030102d401c070601d00e8050310350a100300c04411881d1503080304188694082d00c2e504011030080c0382980c1145e00404100f00742c0740c05d001420300c4581c0c50701440381d004d60344002e03440c1ea = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 956950782 1250 956949532 956949557
    0x617031608040f03080a020708011a010c1406313809030d1b080412030e030403030804060b09161b0b0f0103050d02030f040614070204060312030e0f030901 68
    0x20907220b5500683c22040c6420000000c100b02035014041d04182a000d80da5a981c07a40102800c071400254013000360529080e65100e40c0d40540509910035005085210782a01079600492410000b80e86140741e10a0307407140c0c0040d0b03000b40b900011f01204220010700c1d8202c010740300e5187c4142110300380107240c01105a00718444a414000349800300407202e011460f440c0c01441940c890301b00c0000c26001d2800e00011450310b83c0c06601d80c00030f5040649030340c2101d8545440d00071968a083e04c03508107040d0b40709046004110100301030801188030742c1c0c0308191490140f402000b61036030700d01414050300000b010300c0440351858502c1207014000c0c4ca0051154640b0740d40d10600d00080c800040e2500741007209004040c49622002c50580b4010b40c02c90f2421507410000b20398034400d079040606000003d11041c0030280c8038007841020030910440032402c2120a4000504844c0c19510803122013050304600341226401d406003450280104010b4007031a80307100081600c0e8801d5000c00c43c100f003107481210 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 956952032 1250 956950782 956950793
    0xc0f12020d0504080405030f01050603100b18160e01030b132f031b0325140c0607080702071802071e03020309010206250e21010b0406170316 62
    0x180c01c451500342080c4054107050529640c01d0788540245030290181c0c0c0342c0c48586040502540740500340140c02003203030303041000c1c10200a020072048a40c0c0040745540d24200314040d01c1c4100e014202c1415609040020340802910710703004003100c03034141801c0c085c00c40ca00756140b00444e81021b80c501c4010450144400600050704480360a4000560050080e81a2200e0320800345101e11a03180301c0c1c0f00b901d842403901038918002182c40c440980c80f100b4400709110740c43d00c201c0400000d0b86c1891440ca03210a080c140c0d0a40001d01582244d5100c44100321181c0e500c5035542e900111240050000346023851468000315510440070b03002581c002480d6810000c1b0074002507160f24032180f14420988681c44c009480c0d6000c1d011036401446840c2c08500803400f04d129502c800c4c1840d589112a41c52111010380703100e03295404490303100000555031064150b03401c035070303140782100c40b000080d92110715000c100840d0400d800024100700d4194641104440000840e04800c140b40340c2c07007503140c559243c030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 956953282 1250 956952032 956952037
    0x40303050a0b06180f040b0a0b0a022b0f180306020f0706020a180f05090f070212220f031e1104060b0a030e0c0303031303200c030706030c0f1202 64
    0x82da802c120009189803403e00e000c07a416208000c12140070b03945030381da0000c01007918640c180c9103904c110b04200c108540c1e80c42a005056581c40703070041e600c542c00158100c020f5803031184659560b0440c140c24228929070b10503401c0441911600700381444524000444102d441c09000007030009038000b5580b000812104291806282e0111055603112060200140f03501700c06200a003c2001301c01020a45050010f00700d410380e80042d181810310f59515075010b100740c0014041805601800d41c4410090f0360600c001d050b503981c0d40000e00d103030603260f04c07130342c41d900d0308940c004402c01001702000c4c0009203400d0488000301c940c58a100b41d0051181c14601a0070120401190b40986000c2001a10f21038031809408030260a8900300118080c810042d82c40d40001d800055140c0c204000050310100d50f0600803c000e40640b038601401110980c10400b04081650f420b1442d0380100c0c00c1c075400b85010004200908124a003c0c400070950340800f030010b800e002881000d01410300920900034089034103 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 956954532 1250 956953282 956953301
    0xe030f070c0b16030801151205041a0408030613151512050f240f01050d020706020412050f150c16050d0305041b0e041e05060901020307180509040303050a 68
    0x144507650390307012450711500d0011030000320017051170000000f50a4040b028102c0e00c803181900c0b00c83c10000c3c00007108004110041c0100c800200044650340740b5041d210010744902e00c114500d40d503905101041092045010820b1030f405428005815015410114040c00310b42058850004007107040f4020b50354000002d044600d5185401c041201d020381d10b00c121401800348001c080640b414290301305040919055459402c200032031000364131540700f9001803039003051040340141000c80c559110b5050764002d5201746941c0140500240501005100908004844000611a101d0060100f082000001301101d400300408078004040e491818540c0750070b298800203441e114a06001c0140c0201400e9409841e1000c104d402d20304c82802e114140b03002c0c0c4907010384d0780d07141c4c0e40c41c0c0c0c0e900c0001141d49031550403404810300810000407010843c0d0343c050f00400c1e00150b142c0c0342c4005c2c010f0010b020070100410b20304261408100316100c0e0004280c2094251502044a5072001c402e000506581c45 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 956955782 1250 956954532 956954549
    0x11040b03100303090b0708032e2304050f07030504031803061e1a0f0303070212030406170411011d031c320a090503121902010e030f070c 60
    0x42002010328660540d40c00ba24400d484d030141c4684c45408803492030003040c0008001640800102e610b1441d449210b80104c0d40701e018030041c48509022216101545601c01c1ca0b850035440d0b1182c1c01f117007812408038009401030350304200700c0c03510250320010860040c0001d01032564540102d01418840c280100e102e00c0c08441ca100c28581c2d9183c40c500401c038414074001c83d1008901c049941107002e020b02162040b4440701c0300c0702030310801c08019074450400380c03d642c5480b003001341200585804d06c98603c3e03810001301554440e86050405040e41c00d8001c05458140b0b040000c12000a0038010500351484080c60490041c5002c1050114409a0b04001c40c1e450720444104440c80050307002511038002d0980d40c3c483c510741d01011103180b120709441d82c0300c0548801143c0c00324a2100c401c0600110821403809540295542d004030b401c0100c916008a802036000584040420248207200700500141c03000300451000c41c2e0140352130340076081c2100d9900c6070004540003486500c00100c0054002138 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 956957032 1250 956955782 956955787
    0x3040614071e02040b030a11150927070e030d080613110316020f060c070305041a0706111303110a0e0f0601170408040501050703140c1006080304030206090411040b 72
    0x6105581c14640e02c0224421307402d1131030b020038506000c2040c610307660340300019414032540c44040041052400342d000500d03080601c00700c20340d035481211094008440803001800380900c1a200030380404002c00013424080200a428a5520300240c0c2c01008115031030200c0c210b451350341c0041c000481c5484000c0c00c003401d0030300001d0100001d0780150b019491855220b040d24403240340690300d4000d001601106500403600052400c0385180090102510901d0036902d400c0d16070080030a00b02c210700d0989002d40003c98400c00f00a07441c0310342000c1040e0002214240580c094003410f2150305030100803c012000300008401e901d80700c1d112400b07055041803100c91860040d600d64850700040724058000b41ca40311110130864a0121090b0040e504085034610702405d000054481e503102940860401042d46001109203400d44040d050035128200a0710a4201d00e829410983c3e181d50444c10040c1c10400c000c10059440703100326400780805880128000c01d01a80040e2940190b601104110000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 956958282 1250 956957032 956957063
    0x1050603150c030a02040510030c09320103090212010504020f0402190f1202160b0c0a1b0804120f03080705030709060309020409020910081203130b06040b1c1509050304061407 77
    0x1900200e10301071071135803003160450740c07001c58014cc0e117060301b0050404140d04080d4000c102a940d160144d1403011304000c01c1c400035550224004c0484030040744c1142c1d6550701480110f181c2003001d100007a104a5003507081c9101414a516850030290315a0107101450415122060080003900c4101c003940b8002c6444030f01d00d0020380081d030b14140c4100c6003c1007403800580d80c01d40540076100101491b5031490009104104148948400040151070100c011310001551401843c0d250711068410951f414160929190240c402c400160501d4148001401044a42584030101c04101d030b000d4035010030250079900110f4014514200c01035003000345601000507007000820580200c0e9482e10807245003d4242c42008820700080e2001440320700c4451101c0c0100d0402c1915070b07000680280002055080800099042d10700000c10b40104000003040701d0600c4408074821003c2400454240031451180e0394050320b070321a81c06004240841061009582c00b41c00040d02d1a05034462203030b00b0310b24030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 956959532 1250 956958282 956958287
    0x10c02040f0c03110a09150302160c06110c0f15121f0602060f071d03340e070c0302070f0f09060621050901022101050301050603150c030a02040510 65
    0x501102c0c0b0110f41403076002d5044901810032150312920f95580d06807214202041a04a081c81c1c0d100d1004140e0284402031842c000080e0301306009100c1c3c2c0d03086403100c0c03070440d000d0035003075030300078651074542040565038059180c0c19410b80011318119450031070740c55002180b034424002c48120840c02e0303211000708540c1e00502c4560f001d0400c2001522305006030b458200b01d81e0340d40100c03000000000306002056619001310b402c422012140d505101c001944800880d01d00203411882a49942100e40745060302240c2c481c0400c0c0d01da402e035030b002000c1070404289001210b0081c003840100b01c0d00c62054810304d4406d001c050301a14540824445043d980c1d50b180001d1660b5004500c41c8074500b5000059007030040e0350a015a108803448231180344130502d8440b0040c40001c020010300d540070814042c007982c1d800d002d510055604d00c95160f295043c07106050858034002d1406000c2c1d80a203442280300d50b4440c1c1c40692100c011220607a40f581c80c1542540030f40941d0380100d400082e0044208281c0741c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 956960782 1250 956959532 956959541
    0x2062a0106050114040609050402090a0e070c110a0e0f040c030209090a0c090614042432150d14010305010f0f06050609040b0406050a08061014100c02010c02040f 71
    0xc0b0260796a2000901c1940e0511140c880c1d44500d90214180b10010806400c00b40c02403c04100000c0c040b5941966403500c2d03510440e0120b40110000d108207101004005681c018821071081c1660030003006400c2503140366028501038030155100c1c00c0a0700007000c03c5125286140550350281ca000c500c0c1c20440d95155407102002021110b80c1240b800201c2e007a2100d12500701129004021240341d182a4014480184091041c0c898405441c0b0300300c8031035850980d981c00007450f41c90154200705040031900a04450541c99108031200310440344040c0f03544a517030b41d049000c10b02e90790550b038485922104000b40078901c08120f20740c01e10f4000200b4044194041d1a9000003010288650308408181c181112401e0060b1944041c0c1800145114100303a0303c810907000018100040641e1a07500003101e02c1d0147d841079070a94000e1080090320020048064002c100d1181003c403111134620020f10380003032401540040041c2c0141900070742e84141c40005075150050800c0001c0d0310060a144090b0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 956962032 1250 956960782 956960789
    0xa05060a0e0a0c0509090106032001020f030307140313020a06030f0e0a0308010909080c03041e2106050a18060501080d090302090c0a203702062a0106 66
    0x2440c0c86078074484004003140080c181944120f036111540e080804005a100303000e040200c0c60366a0321b40c0480042c0940d4241c40302064402010f000d1051230000080c43d10004041010380e0b070700700b0b0080c86080c0d0b400110740200069462901c5440c0e640310428100d02c1741e2440780c043c0d80589030030000140745070154001c100c40d1210b07010600607040f0b402c0c03040f41c0d5142c180c4001030001c2c0111004000408190f4404441540700303d503070a140070303240d0986c2c41c95500141c2111501c400e1071f183c28200419942101c03401040f00c2e40301404082d14840c5100225059080043c3c001501d800009145030f040358000c086101c1071080c10a400c214a04190004003407d001c0c0030014403c2c11590740c03100780070b58201d00440f0350040070060581d5a002c401d2800340c210004030428081751155402c00b6013041040780a11003041d0008149109428107076000d0b44076098100512003842c0c01d403a06100000a841e10400ca07010b6400716501d00145004042c60704150f411005200307110181507981010641000e0b086 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 956963282 1250 956962032 956962051
    0x151e2d04051c02031b0a1208090406080f03071725110a0305060613090b07050c07090207110d1515090b03060f1810020a11120a0504030b10080a0506 65
    0x49402e425580c4211200c003500a50701d030b400b00c41011800b44c25943c0d00040f05d640501581109942ea41402880c5844164101d45002010990300c42d18201482442d00504032540140005c034805034078140c481c424007001404519080c485141c00c141141c0448844e914035040e01c5141c00c001c20718120345c909840000b1600807098000c807103254507000c884a42039a4000c03000c0c1801e600c800c000c02c10310003080071214004507111001040404c01c8080100e22880b46a1181c9565041d28480d00d810800d03280c00c00817586106001d5500411a80c4005100c103541c251003071280c4480908040038020a02d01c012425607050040940d9103000c9800d14500b181c411039002e00041d55a0020561581811248403184c40761040004a481c1d0590381600c0c0429200001c0d600d0701810028400c059038400c051000110701c0e1840e81ca07041710010802400d40d208010fa00b5414002603a070002c109200b01d100c0502011195000706281e580c19913a400002c1203810121080807a40b8035100b40c40f0101111009078 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 956964532 1250 956963282 956963299
    0x50309070b09010f05070f21080a0911010c1a0108240f0f0c0405041a01230415140408010903020d0e09010504090f0f03030b151e2d0405 60
    0x9980e401d00081e5405204141c461031101c40c80900f0889140d00400c10944503807518010030004203901c1c400e02440c003220b504280c140195501809401140080c205d041e03030a19042c44800071030302641d140817040c80b0034070305111112580c0c00d10440010400640030390740325414000103019500000c0014010640c400700c40440c59010700309400ca40700484844020348035900c00514400780070f050065021a074210024105510707803010074111082c02c5110041100c4c0702545842c07030341c0c0013410b104a400c3d01348152250700001c01d481604c03d002c0c41c45604680c050f0319084000c1c0b28012420680c0e01280610b61607103490391050f01c14080e014418007a005030103040364802a9a1040980385079081002e02900401c0e40380c40d06000042a014605031680000880c0e18800202121208055140a82d40c082030410459040040345c5860340c0081c00340400410010100e1714900003018045140400c030303d40c072040580144000d04104e490510016000c034a0f41c0520042c182000e4019164162014039 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 956965782 1250 956964532 956964539
    0x601091103060609190b030c07060b09060d0b07020c120106300f020406180b0f06130905090708031209060109020a050712090510020304080c0d0b07050a020a1205030907 74
    0x100c0d01c0c070041d180c45030029401c00200421782040412000840314030500b4800440d6200f0303407010550016102070700d42d42c0c0f00291103418800140108540c425007140c0c4004039051403000112201503408005003041040c200059907a4000d10241c40111009049440d40b80143d04840c6d00a001a0050307a1140c086c0002404032500c02211030703814041101e004520424981c0c0320340c04400440c078001c81c0e025465441c08682c0c01c034442040f00d05401c0b0b001d00807403501c02843c100209080752004844c0100c0c014000c001709102e0a80e5040200d58030b8040014154072402511410800c140c0c00040c00d5200c000f490900c250071245049106070003044c1640c0ca81d0b62182480e02c20307445030301800c4000075000e001002c01300340300b210482d0b40281c2c181412044160356102080d590403011582d000540c2010034200020003052103c11070507071080f21800e414030116960140020000780540082140200d00480c01e10700070050403107020340096484807100c841c80c1d0010210340c8100e0700d15400707000d04031001 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 956967032 1250 956965782 956965811
    0x6030f05070f0312122d0e01022a0a05030a1205010806060d0b06040e0d020a06182f04021602031c020c010e0d021513080d050a03020a0c14060109 64
    0x700140c9500c8000351100041481c011200d0784140700700210601d80d1010b4107050800d070304940c6039001c09089020301c401b108000340d00086510078042c03824164010851443c2c1c6105890101200b0401d21120054040710a5110341c03a14900d8a8001c0c901d100000705460301c945c01079023041c035000c211802840942e0302d5000b030a454581c1035544076044644092010001003c0c00c0c1d440e580f101000d0000036008400503003007442c12a070140403101680000103500240016401000741c4940c48242803802c17101581c0c0c0304001000e04803088815001840c1420001700e22601d148080c6d042c000f4400e40d182d4140305440511141c1c5034204901c81d05c2803c9160482400d0a1807500500350b40350003808401c0c2c0c0c18801560542e00160802d680b1050343c488050041e510507200c0e01400c7d10711200551103043c0c0e541021f800d8405600400d03065402880b28440c9a0343c00001c5440494980c90090307105c0030320380750236a40c3d9980d200c0c0040c49001c254130b85580c000c10000b0350354101c89540ca0184241061078040 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 956968282 1250 956967032 956967059
    0xf07200f03040f050a0f060c030509010318140c190311060403150c09060c03020d110a0b0f09010b0117150f13090b07030204060801050909030c0f07050102070f06051b1006030f0507 79
    0x11f000100704444145e5003c00d0242020340310441c018180070480354540041d4019040068600315010851298a0507040100700051228103031300f980c80703c100c0c4500c3e00907402c03100040d100060000d03014556040d9192103c40c2907d00031079000640203900100100810050070003801c0c41000a24295000035040e44a407042c4003803107030503402500f00b0708001041141c01c2c515103016a007451058820407400100400741e060b1040d00315040070001402c01803811b43c20745904407200da0410010b695840c0e2401e10b0544a590800d00070980c0c0305c42d0390308a10100307915075002580554071401c0200c0801c0c100700c5d1600b0280d001c074402d4090070340701d6880c3d51040d4100e005500412000a0300c0d60014095820411500d0303410400c4801200c2c10800b0441c1d00314901055911603010f260441c00080015503010001c1d00068401980e000c4401828004010514014001c2140c6000c16489001c001c0c00000e1110007800444881c0074055541c50341822990795801c008100d85520560703d0004240090066 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 956969532 1250 956968282 956968289
    0x15090506071205040b0a02071401020601050102030a030c0e0607060207020f0603010f03030809011401170d03140a050a06180605120102131a040503060f010e0f07200f03040f050a0f 79
    0x400c0c100040c40d1a03010300354070b0408450050000c1004045013008200020b030100c0c041e294002d10006040071611590801042c81d80e0b41554400c000601c01a82c000c802e40d81c09581d20f00e40081d2012100e00100c4045411500c5560840e0b0001800c4043c842d058006080c074500945125900110030028800c99200c00d11450300c1068040300d05200091051140c0398002d0134890010900e07842c21031722100100700070380c000400204e1095500c074400314240142c44050140d070074100540465100c51003440a4000e00c0d40c050696154001001c50f21241e010341c1c0074080c03a03190004540420701c0c11600400003406107a10840320290700030700c08d04050080790341c204014480b0b001c403607107451030f0350f8442400312140490792501800045100d84041006034440c2c4080150040d0707070352601350380a002c00f1010700000300c090f00b41010000c5598224039906078510b02c07000e4450a141c032110308141400c0b42d04032866154000000e0020325141c0c00704900b4150345049864001c500e03551000401448950302c03 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 956970782 1250 956969532 956969539
    0x341d030a02060901111203090319050304080403020103051e07080613181214070b070e03011406060310180207140a2d0501090302060f0a06060c020904060608070b04150905 75
    0x44050984d5104d044030a0b10401c0007402c03201c11b00e85132800720304103800403501d031111340d40003241c3c41c225031005121449404086040081c0b85007032036180c1c0700e0702d44611301010381455101c4010810445022100381c1281d1070440a2129a0600d8203004188240c1611014444c00c15000784d83c011448074419607103000344214210603480f507981c1c0c0d9409014400c44000e030030702c0608805416035800c0c0400501c071f281e1140c0f000c07001914001001524901071000507d01a03072400c440781d0b064241815010f42c102100b190040e4503513803040d920f80f44030900c41c0c0194200f000c40c1c3d203906069074010b4001d00325aa10070500f84840a12466103076a40342038100c030142142c02d0343d80c5d0107041c0048045005c0490140090f4203040c21a43d03450b401d09503203c00d074080313005920400c00c224151110309001e40e04444140803e01c440e80c41d050340280340d500300c0c1f44064491b015150106042004507401040109a680107582481d0764079141450307550000c3c400c41c1d00e4a841c12f41c1e401002c83c401c1198005590005 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 956972032 1250 956970782 956970787
    0x7142d0c06040e060105090a0308041d04020915060c07030f0c0515040b0309011803050307091a09060f0d11220f030609050a022d030102040e341d030a0206 68
    0x3e500c043c8100300140c440c81c1801003c200340c10700e5840c0e005241d0b01841c020840e0a90f941e20708060603824108409080007000315200074800183d039900d00568000244c2101343d00c0c100021000612a8450404650050300c140400041008550841070741580d026582615126a0395000d00070301c05210a4541030001040006100d4804000c01031b51300400138600000300000c4440b602c1a020011003001e5001c0f0348007108001c1140d500100000c00307481c100001040450461010081038022802d8003071081a01203404a9030f51070340b2040e140480a80b4000744410100102d000c1c01a6200c0340040301d100c8075802c9810f07456440180141d0484800648c80040b040ca180c480c0c000501030140100c6090081c015000302507581c850013000b4580400307421400e10300014140881c0181c11441c183d000380d00600c4104211320056800c0381d4022a2a42424442c2007a211410410f1002d005404010002440c0329010f00c0d07882815a00e01601461500d030384540700c0420181e581460100003548100c08 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 956973282 1250 956972032 956972039
    0x4020d0f020c0d1202032203021920010c0309060309020111070b07030212030f040b190f0b120f0703020103090f0b011202042415050f030a32060607142d0c0604 70
    0x402c00071148031802303841603980048141c040103030201c2003858250b17108a01c1c01c070101d80311203641c100407036561002d00340071220401541e00500310101e2482070b10145076594807030300c046d6401140b500714105501010380e1030707850f15288091225001100c0550043c811207602d604660308000440f4002c010305040c5d210302d036586907500107480c800184185800c5a11f840804039039030f502c0c040c6545041003d4004980d0640100900080d89140c0c0078140da50b5000c0a81c0414000b4081441c90990b43c082c6400314040209050901000c4041c80c4014050440c44e00001100102d00c103800e07100b14800c039418031600c100c203d084421002d0103031208640404c1618104003080030910b220260480b00d00b0400d0824039800c49515a5800484243c0015900c0d04c2d85500081c0d00c42c50040c80d10690703016644801803020400c1e502000004100c94040c5900080120521840c00b4008000c0c10f805d100b140d4859810280d4070802c401340e1286c1c078509404030702e08125042408074200c1008500509014100b038038 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 956974532 1250 956973282 956973331
    0x6010308030a1103070f080a090b180705060d0504061103070e12070f0305070905070207061e0e0409030c12030209010516021c05070816060e04020d0f020c0d120203 72
    0x201400b52004181e40303001008011021030043c6100c0e05840c1c07558510b00324440300c060700414005041d010094030b06144040003c0d8010070164001600c006480015000248a1440c051a13a0007241d4043e10100d08a1486400c580186200e00e10a90b42404487c0d0b5105044103140400d0703c5070f030081502e10860700407600f0051554809030b110303502104c0142e655006406101c400320f820a0700e0355003141c0d20502121040c0d019158020b50756200400c0c0342c1c0c1c0b03003100c000c100100d008400e4005d8000e40c02c0541000340308450741101480001d1003040760041e2460040c10300141094212240414003c0590b5000d01910a44d0340124041e11aa850000343d0603510303441d43e80c0c1c0d0004a03444082740040200d8502000600d00859101d10b0082c5a2641030940031468094152400361944140b01c1d41803011031750000c1103116050b01074501589413484c6c100014064036100d008121032910124850440c3c00c800242c2c081c5010094032075500c050242c0303154030182d1004480201c920242540c0440a00a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 956975782 1250 956974532 956974537
    0x615121816030f030c0b100504050c071109090f0111030a14010312050d09140d1d0a03020904140a05070504060501050f03221e11030303060109061202070f0503191106010308 76
    0x113200c2d2030b160700395154a603541d00d103c58090f1403035245c040081d80c082c0140e06251062a401114507401c0900b0090b9598910f028810080c040c0c5004078240b40214441100805c84100082c80e200000e0018841280d005005c6070802c03550508400d003030260454a42c0c0c0d03160074503070603aa04000741486907030880d8826511075216503d80050386548514a0011074001507100b03520458843c041c00748000719910080001c840e0f621400c20b6650b10130105086c40d500c0701d00040c1200e50560b914a4583d0751424055800300410000100c1c90180085a00030018041440c0d401d485080303500300b04080d141c00044981e401409030b1480e074403c041011882a0509540301c8a0210ba050854540c00e103881c0c3c0c821242c040307810408101d045895a4100801c41c440002c008001d0003075000754107520307201000900300d03942c82c8911001d015014145281c0b0008030380441d03500c0703504100d080040ba00380c0c1c98500d50729408440850410080014049041d0744207072080b80308443d0f802c0003003190340d082d030300c40c54503c1c0e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 956977032 1250 956975782 956975813
    0x5070506030903160b060931060f240f0501120b0f03030a230901050d0504050727050a0e07031212092001080c070605061512181603 58
    0x144002d110308013207900c0440d40c000d601446034030802420300300042070001641001d03002c4005103854031101c0c0c0e0113401038045000e460700440d100d0420302e43c503401c04a008100441156003080d0802220f00c02080d5420a900b0058402440305092250b5804030800302072540c1c00340c2c41c0060340040c281c41c600c8400e50408101d00400400b00400100e040c00041c1c80e6920075003802c00820b0a17130401c04001c00b0030020308224802020b07000b82ca00541c20b00000c10340c0c851016580202c42c0d0322001320381032000c100002406442103a0388500e03001d60021b61021521401080418407504240001c0c11207040f60041c5141090050001c049440c11130740c803400c0c447e0321200701c5020031000059844840400b40035152507a4001d568130112501c040341101c0000c0c40c9010107074140321a0307009122600c01150103c0d4030340c0350008000102ca841da58005800c0c08040d1140c00d010305c0780800c410007004645400c07a4007841144000102c0d5000381c403000f503110480c8070b01d107041c0030361207900800103d4807100002416 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 956978282 1250 956977032 956977051
    0x21026060f092511070f0b1b010617010b1306050607020108070509130e160b03130c0b0a02150f0103080403080a1209060e0705010806060711180a0b0f0d0507050603 72
    0xc1c3c4a242a0704401421109407210014140c00c038840e540c4036090201c2e1000d0503c01c1b03ca10496814a081d5040b00c1c452170302400440072000028554900c800e40c403040152000180340703a00c5a902c50b80860180c544184401e201e00f100d41e000144c1e245484c0f260307404139803010700640e040020b10f800668005200074461000d12200700942107156484900b6038020501101000542c1024840c07281c1c60041c00703075402006803001000500800d100407090366440560044040c904441900c0c000990804650015009460204207400c0350b80d00403030b5440a081040f0a075181c0341d0750f10b0440501524080c400540054800c00042c00860035800040000390100e0500d11501d045007a0607008403400c41d90140c55190b0703500b071100c4003a01c0502c5184000c00003440c04004508101c00000c14901c02e007400107102c000c2e04201c601d51a01d500b1b013405500344003920b5400d13851030004000d0f0090802c42c0c41d118401d400c0c101d8405c4862812050408070740781c101000b03145490404040c0003141c0c2c00234142240 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 956979532 1250 956978282 956978311
    0x9062d1a04030b01080a0605010608060906060f040b0d0e0f0d052d0d060303020c03160e070320030a140411190f09021209070e040305030402010c021026060f09 70
    0x114180d030301441d00030580007005080910407428040208c03981070b0800e1003040b1900003800b02c25622481125002107080b581c20380d0740c07a07880c400c00046106560103001d2040001c81d500c5004135a41e80007011200c80301042d0b400c1d41d1000901c3d07a4a41c0c00d51034440000c10760a00c180030300c910f02d441f032000d0300c0c00c100058501e8955800d0b0010819030050310042044a03101c079002c0c02056410f00902900710419801400f011008080c0c0c01660701407070180d01d405500036800520003030710030740100180700c1c150070860003002094050342d070155000300da2601e411420b09042020703040003150300b6803080c4d402905502c01e20111004001c0251182c0d118402c00d02e0b020722000c11031880c032802da07100500010000690358281401d00000070300f070041c50071250b5000740340200a0440e60541c41540198145802e59a950326480180c440b0512908043d4106040040c1e001129803c0040f480c0980803804807003a00c585e65065030351a00390221846038025800389155a090f0404900c615002a0790303062018 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 956980782 1250 956979532 956979539
    0xe0307050d05070b16020a08030306030c01110d12060b0703050a02070605270109170102040e0c042402120a09090b040b03030d0902010302070b0405150106090f0501081e0109062d1a04 80
    0x7150b00d20035820904149d0800801e0121600d010810061100d81c28200000d1070301255880d02c1e200ca40150014062001c2d05c00c2c254120f00051340010050300c80383c1c80c50b9444e0540d5040040c0300790800d14114025220f02600440c0050040007611950200c5a02e00d2400c400e92141900b160001030400e50305000041401051148103541c26101c400e41900005031110714200c0f101d520101d01919004030380e081004203105600240703554641000714500600440690300500301d00e0502d01368840c080f001c0d800b0410034083c9174000c40c1841201e81503407045c4440d41d0301104220845142c1c1e0b0b0080d61640c81080b85000d0641560880710442d8014100181041c42c540c0320380c010207000701c1c0e04941c1c0d0b4000c84900350b00c000c0008101c6000d4485071034900301e072604009520075405018080c2a040c020f0560015824003607144052000c5002a80e03001f174203503540c09412005d84840d001da42c00640500e20b2140301d250b050762841000a100f541c540d61200c0c54000f4846410081041c0a84000c1c410072020 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 956982032 1250 956980782 956980789
    0x90e07120212060a050a0f0e1b030a080c0d1d010e040f2003071b0302030703080408092e05090f04050a18050c090703050420031006060e0307050d05070b1602 69
    0x34442c1132602d0340490030303142c00444181201d071014201080d042c54041d609010000003d2000c044040303585d01a8090f500000010340380103802e036401043c1c81c600080110340354401061450804903141c4940c0c648081c00c2d5425a1401e01c184a003a0014904015190b07107840c0035046101c83e5084581c00085051642c018007201890024540074a0840042071100c810360281407404070115051140320007480540e0020b4503441a54001781c100b11213070340898140000030045032a448002030840c00380c941484940c2a0f00d80d2404412241400509a44000540600c0449031a2180100011100f40c092410000200006044000310b580c3d2034220304002c0a11501c80ca0f90740d802007005080d081130380bd04102001c00c2c01005201018108003e1000041c0410491f83c5800e40a1003031402c00310075080804c0c5030030720500615404905010b00050b0868000340e0a140904c030913029200110b03200c7c82402800c00c0c140400412503402110700f080001c9140020300404c4459010042c01d91540c0d4000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 956983282 1250 956982032 956982043
    0xa0f1b1d280b030d02070e0c030907170d020f0316061d03071a01060311040506071a150f0a0815070c060c0f1706061806040317070507090e07120212 65
    0xa081d580d42d6036040022081c40d0800581d4a100003900c0141142d9017480c1c6050b0003410090400b9068180100c00b0584480c41800402d01903c0580b07550300030a01017004103991941014884c0016005107040600500e01c040100c4424100e070165000058803a07954840062400a00d04140c145848901c003100c0079040c8000c00e0300318044e600c0a015441949900e588140040c1e101c0802d2503c7d0007000d0079a04e85802c2982c08445040321015101c0483d801d1100418034031600b00c0882c100c01008000340308038541d19043c80c0c00005c1d21003040380c00e00841803000d100c1642c0610000d941c007403803903480d421161402e499440780007031900d40b4000c10726907035049c242d840900411020a25603c2090301d01381c1d00050344078001c802c40f960300d07042d4101000800d01c0c901ca00041c4020001020700034201d01e0f120201203070011075201800f20701c03804a4200710021a08084802c450f680500c00001880300d919000c2c000d01490003502800001e4034010304030000b00381c452012138105600b02c5041d403000f1001e001 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 956984532 1250 956983282 956983351
    0x13030e0a17060a05040213020a120504050d02070b0310050d050f011419090209060f0d050a05030702040e0a051b0a090f0501091107080d1a030a0f1b1d 66
    0x250240318501d0484031a080001c01030201d811a03103007400300805660345ca07040710700846445100503511034846004588114410400d450b406003000188800c000f0002512110107200e82e0903185856120350300352046100a580e03082d105011200c090000345440c05440903200d1291080b150925101c2000d6425079440b07103003411050040d40c08008840b002d0884020001100c03d00801002030150300107621420050310701da008910802c50880d042d2a40044800c01540040c02c451100c400380c5412541ca910540d0304900071030034101500800340c00003d2390811581d005001d0400c02420555695444000403002680f0440e0f15800080809540c8517045155941d5800400c42e517040c4410041552800035507030032172550403c258004a0080415074070800079010003c200c800c074500c580c02c00e101000e40a5980340c003a9400380020000e010805021701e51003130311000701d170b01d424900e200300400d44d0b44110845642290845080c8003541e5080725030100e80080e0303400d2800c1e03001c584c0d003200d004800c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 956985782 1250 956984532 956984549
    0x1c050a1a010303200f161e0f03030302030402041503060c020f0304062a05161d010506032d010602030705120405060712110a1a1e13030e0a 61
    0x480a814850404622500508056801140355142d5940144a20b102c04889008902c500002c00c0e20000e0a0009800004807402101d644200040b14651901c01510600c00c2c1c80e2000d43c0c4e00310501c1403d01d0380e00c040341c002042c24402c0c9491924158007030750009004980c80350391030703002582145450800e5005180905000140b421f00c240010345040c2030900801003982c028041000565400515910921703080c06c0c400e5520400c00c11408056620032500a000d401485c6021043c1071030b40314400202c8510f03003400300a280780c05800c00b07480d000070301a050b0446010000a1051204440c6148141800000b800648204048036130500b80c030a0704100c3c010b820028803901481420003601c1803030414006940d14151074500050103d00c03031031800415140741448500750081c050f8500080b003035410829103114500600c0d044204c178550001c0c281c0c00b45d54450102d111200078a45401d20b12020107114910ba13100c092800c40088204c0404404021583c8050700964840600d91401081c525 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 956987032 1250 956985782 956985793
    0x8160c051905090a15050f0f0904110a171009030e0d0302070501030b06190e13060b042102130f02091f03060501021903051c15030203160f141c05 64
    0x2c04214a02c0d40140a1030760381402c08140d4441c029041c40100111201118811403c0f0a05d1020132900704504428035130150180c0104024020b0a40354500e0081c011690012200c0d00c84203207010303000c2042c25406240d449600c0482040c0304a40c00510058024100b00c0a10321403100010000d00c0c01c0b05084006030808101045a0b58042c02000b40c0208100c448a0504505101e80502c0040541001e000c20409803184140c0e901c0380008010300d05048402440500c1e11280b60000c1139005108040c4c1000d1300c04403603100d058004258441880c0d0090102005018020381c61010b0b0030364400d182030f01507003008504c405aa071074424210031024a0071061810000803006800c07141d107a40b0450540d00451003040710400081c0e0080741041d41800d002d9100d60410009002c401e44580c04020a01d20f4a24041c0c0041c4500324040100c9208904540444240c0c102047c0c01d603249100341404040e5190f4244814200c016085240802c040c20580014142108141e00d1140500c015201030b04030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 956988282 1250 956987032 956987039
    0x31306021902060c070206070210030e060a0c0e0105031e100801020c0124050a0b0309160b0309011b1b050c15120105010518120f030c0706180308160c0519 68
    0x1442103075803041a41e41344506000158010861074846c940001740304080328800c9512035401780e03000543d1250901e045131101d20306000140c004001d510380c4030010400c2101d08108542c42102203038840e54407110302c001c25045008008066a0001d45036041c0b0954503074010a501000348064244802c00390004910401c0e6412104170100ca0501c0610614129403003d0000c2e0301ca50300854100c0e10001d442958039500c0c0c1d00d03100d061140c00100c035008000c58400c00200b60103110040e6014030ba9400c020030031a0010071508200c1e2411280100100b034956041d58401c0c1010039081c2c0100740074000355102081b0400001e4850f42141c0d00c02c1d980c160012401110049092a0f078601515080c20f140d403405040c40f070903c080c1c2204a4000d0700c40d8811141000e1000b401344403400507923000344100c90b291031020302c8840e26041c10303001c0c0a002440e00401041c900071403040f5030007100c0e00003c8040ca407005001142603080c94800080d0b0300d180306650001840e840b00f030003c0703d000d0341c4003030311034400c504 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 956989532 1250 956988282 956988287
    0xa050303160e0d0b010506070305090607060504150e07050d03021018150618090812010b030601030b040b090115200114070c150e0c061c0b0d080a03020313060219 71
    0x40c2d402c154041c000003843e00e40080e10b207403a241d064a00880d03800ea2503c2c01440c04948502c13a030011242c1041d00801c41808020154106500403171260080ca000300e216020294103c9880d565054250340c0a10f40030007903420f050100e149040e0003441603502000c2d2b14100c0006030740d800170f58410421020081c90081c0301042c0d0000b42c4074240c50b0b2003401500e261643c4405070000d401103101e951071b6296003078000c0000361400c68540d40300c4181ea5514941e525000c0060035041120300742d022a08000707542c0d84034a002d11404031344d102c1c003c02001090b42002a201d02510703025005000384540244600424030081c40399000b521548000402d40706a100d02d14402414003500d1203041c0f203442c044080c0016581c1c0200707001c4c110300080c00500c0101d5598841e1500d81c07414401d941001000480500c1640300c80142c040d601e070161401d0140307000103418080c611000e000040d00c102c0d41405103602e13640c8070f03800864111401700045016485203403254012a03002c0061007120f40c2c6400e2140041c2034 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 956990782 1250 956989532 956989547
    0xf01060810051903140d09050a0b0403080a1710030606090b0607060902010302131205120703020a0312060b0a0c06050c0a2003120f090f03031003030c03020a05030316 73
    0x4090310305896a03007424200d10300400024024940f040020540003001c0711291500b2200440c4c20035003400c50424442d46a9854190740a081c2c00080c402c04408613a5041441da10030456080702103c5203002d01d192112a01c030707000068000c00700030110292400b030980380c42046015815490601d12043d02d585410000c6880e240d102620302030500000b01c1c0d01d50758030010b80c0d460940100b03000c0340c15106840103c7c003d11900540c0d84007416100000b082c084080c4003002e040ca0301c41e00071144641403643c0944c203180140c00b80100180e03c203110540000384207080d40041445141c9010130340384c0e105c8202e03840310340050f03801000182006040c030080c8056405940e40000213400154075050041000801d56000602184600041d00f0f0000c0c0306004204101c40d0000202c14068a03d0b081010269402c510f054a804046101e041c3e03030a04071030404070803a409420300c200104402d03441d580e02902c502d10078120030342c02d500840c19500c02044080c001513128246080c01c5a162100c103940291491 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 956992032 1250 956990782 956990789
    0xf020405040c0206160f0c110a080105010816080a170c0c15030609100303021207030e03060a0b0310020a17040f02040c0519081611120c0a020f331b060f01 68
    0x4000406d001204a4001510303001160b0032201078000e89011502040070700b845070b0300946980d0318000c000910a8000314405008412485040e01904d990304595a0f5541c1240300c09440c039401c40300484005000000101000d120f29002d40303071045880c0d07000400c04107801d52030188805000007045841d18001c043c40d981308801c0000050410b043d034500941c0c44030500c2442860300000a0b4042c14503028481c42400f44200904403031081c40d118824002800e40307411600d000e48500407106035001854001c0d1090f00c082d0f80d9038208006000c0e1362075660904090030a075004000d0300c0b00c04000da00c03103000d00780c501c4109840b05d956444040886440e40000701c0440c000300440340d418840c405440c201c14070352200302441c0c00c07003010b103c082c0f03c0703410607034070048100c00c2c5080002c1c40e0032101d0021421043d4a40200c405400500c2d112041c041004100740d42c3e03c8240d0510b540707040350302c1100c2c1c100900c0c2c2c04410040d58204483e80c0c00c0b07404003005003030000c00345600c0b0804020424a0944204d400f5 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 956993282 1250 956992032 956992037
    0x10306020a140c0c130f0509030a031b1218060c180801020720030c0d03110d0509030a02040f150306020c010b030102090a0e062e022b030f020405040c020616 69
    0x1c0400b548001d41c0c0b5181c00c410110300c0b405c828070318080c00c0e2120b5008081c1425040e07604024030305013180103580d40d510043c103070310100f07060009000c80200d4140810f41c6001190720b46800c0180182103a9008080c404035801510220003255000b00b03036107200c0c80b911403489446c1c0d50640f92540c240340801090952090100f80e00400403400003541c0004420103001a1041c1405409501d1000074100408070488a4201c004004614289940a00806c042e8bc00074000c0e20392032001403800300c3e02807041400c0c02c1d8242d4400342401e001400c1c50f0b407165822007180200050407411226008007003500139031007a10300d0303078001c50150f40d00e52081c4a642101e0a04400031072030425403101064261305a403017449090181e08000540d42d4842546c040f400c004811038001c4044460781002c0000c580c000140c1005105583c400c094003d0309200010b0048030252201c4480802c02d64118050b000b00c1542e202c00e50740030300000917217403503601803940b160201d80c000c2c065030300c5c0690381d02031080a01c2c0200000c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 956994532 1250 956993282 956993287
    0x40902071716020d020f1f110d1b0606090e0109050c2b06021603030f05060102060921040308070b0115031413030c210f02063c010306020a14 62
    0x2001c2c11003506900d4020780c140c0d600d61906095000042076074810f00300058001038494111048114981102808654546c55015003641d510301150703642c0c2d00703c070704031004662444145090045542c01c20400148180000300d4420b44a611a07401d4171220303d000c26060391680580c00c1000024403121106050654562008400414081402c44808102c00e41c4204803105131500b8004540c04131221400002c00320b1103100c0e0180790080c010051800700c0c0c040c440c502808134900e0744c40881d40a01401d51074005160000c403030310042c481c0c846022400200c01c0810040040001d0541010313022290054201c0c20032581f520081070b20440300084004101481c02c1c42d03a58030500d000d0a401e400c00122a4401c5030b190007494140c0f45a56150f40190004030503064001c0e4060503001c1c3e412140c084d40d540c51000f00722400c0181d80d94602034580c04429280543c0e01601c5480b80c1207022039030703401011549141180c40e03d286103c41002c0e0015a800343d000140a950940c1244130134110340d03854400d591 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 956995782 1250 956994532 956994547
    0x120901020f0c06030a02072a03060c0302270a080703121403071b1e05010902030708010b0607021e09041104060b070302031c0f0c08160201022a01110409020717 70
    0x20544d00c8020407042140394082240070912104000c400c0c021001001e40200c0707080c03042108008a549403004448840c10803800c403125030310a009417050990601c4200c41c22910704200c141c469040c80800b207400010003440001d456a00308610720086000b10ba5400701100004030007030181c141103035100c42c560002c00a01001960110102c1c10b80001942c080d0048001031400f0211540c0e0080040c500400600c8440103000041d0310085a09200701d044580070396442d85031909803241d8981a60b88510700f40480009800c0c5215603520026080d4540da0340c1320350750800500621016901500c5443e01512043c0c07060601d840340002400050080604020256900a5683c070818201c0803075000d0703070f2105010700c1e0702c076800504128111841c02c1c8022020040020315201c422144100c035400c0600c50102201c0c018401c8444d01403417548000d4080e0b00c030001a5400c0d16035400c1e181c069659451203440d0344601500604058102c91401507600e03110707410610b94180715900d40b42c00d441001c04c42d01 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 956997032 1250 956995782 956995789
    0x1061403031b0102040b0a0e04050f1005041d011d0106050904150b12250b0304080301060804030c0204090f02090f0106020709240906031401020a0804060518120901020f0c 75
    0x3124a8005481c2d24098030500540c0300303000e8081c6502c89540c0d2100816030035286504442c0c10302030b101003507600f08005d503101c01950030180b0f01541ca03058540711030b400901c824200b075004070004841c0c050303400ea0f00b41d11016101e421122075038402c02c102114030301d215295100078003860000305070840c0c2405c51030603c3d484914002900c0a07904400170340d254446031481d1503076030020450f1500c1109444100e070584412060041d001604a54010070780342001c42c101081809a07801590001c010906583c2081016104c095010f003094007030080c12540343c1c1c0103940f50f0040107002480b40b0300c4030b6000000c40c41408018003000d0403641c0040008001130000b95030001d03240d412145c80201c0800c5c0c5616240781900c108518159607401440e05400c040b88055030f0340c2254044911400c6214203451001042900301d006841661000030050004100491440d400c40383c1c001c01703074160100c00a081584042c0c64040c0c240c20ba244465000f0400c60030301c0d030701484015880b11850f400b0380384404044000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 956998282 1250 956997032 956997037
    0x80103141c030902010e09040506010f0603050c090f010c08220504020910080711030304051518030412020a0801020a0f0816090315021b0c0f040b09060108280b030106140303 76
    0x1d100030566201800e805580c403d4080704013807900503200801c03a0910381042c60300d9010074092401c0e107001400c00064814407034401c071407181c061407041a013011100420481001000d071503c5041000b010b0795000440c0d0208010302a20381d05051044243c1c4402c81d40c0f9480085030350180c0e11440c4184801c410342d49a45501d805607590601d030450f600d84e1a032100341c45908080c41c01760810304c4003000b0001000350001d0b18410219007070300040010b65400300510003884040c104440c60390002e02c0100820900e150682c20382510050040c0703140c90f15129940c3c00ca030080e1a5600c0000c0404072820ec445803c2400d90b5081543c80c456060391206022000d1701d042d11030303c401007880c00440f00885c410382140d41030b01d98400400c0d00654090802d5861a81e139900030203580c0384a0000412481402c1c500b511540780d254801801006941d6580c0f4019100c00320010041504080d0002c44987e409045450800e082c0d542c1100005034060360300145400c40c0c25a4105840e15101001998204d40d0700006 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 956999532 1250 956998282 956998333
    0xd080919030201033b0718020726120601030204180219081012140609070608010905040c05010e03010e1218040c0503190605030d11150105090106030c050c070608010314 74
    0x507000307550701c030070024a11b4010b450380400441d000c004d0060380b4041890300180709090081d04603841d802814560f041030802c0c081c4c1101440c2c4002c10210140c4074904804541c0030205050050815540d080a05510101003482c03001080d0300085103055040c00c14680108081c0520300080c051400a0720003107804a14090303822004c0301700b4110340400200f04131255038680001e050f42d00f18100107414642d641071501031940410310201c001720b180c1c140740c804d05200b607420450850819103810010369590201b01e0480360035540380c4408541c401800c2028800d814540310f00150745050101101204000703210140c3d1040d42400d0900690f1503020b000e4a07001294904a07030340c410b18108209004040070f81c4500c0d058045d080244400c140c10050403c00d945480c41a110488203c840c4104100000d02690f03901c2011000144096440380c1c0c0041040b2026003070035407a00001942c181c0c9021400d5100000003010a00140100608009000d609041c1100144980b01d000c1e00018140340840c007 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 957000782 1250 956999532 956999621
    0x507090b040603170405011710030b04021306060e010f020718020f13140915011d031f021801051309051005090a0b0103150b090d08091903020103 64
    0x2a000a0741d110740c4148001e59010140302100c03a105009a801504184900c0b80455001d0748a54a40720010946a124510418010034580c1c25696440d0059802910a0b80c114610540c0d08640008500c00d203409851329442c0d07990001402000100700349100350001045402000c000c00420302103101030400007140c088096200c94070180140c6407800f8000004008420340c6d800010700c42c8646814540003d4240d40700c3c0007a0303031644a07140103613514007501c0d40000da0b025038840680c40e142d06003680001008003518003800d00c00140b003110009274524485000d500003400b03140120f020b840741d84210b40a08182e81880403040081c0d078514294400c02c981a5212000038016081e00c100c403001901d4010b010729a02d080c0802e01c200200807004401e80400d2501550303003003c5040c00543e00803511526801450003040c882404901e6142d18411101004c0600084019a86009521101800000164440754a18000181950002032480c2403a402010f42c4400011803610942d08114004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 957002032 1250 957000782 957000791
    0x106080c0607030926031c0c110c010807030209130501050f0102010507050a0f050f031306060b0301151202040509040807060f15051002120d06050a0905070503041b0b1b19050709 78
    0x21200381c12030013446a170403405000c000b440024000c501d051b18258040e401d00200681d07054020241c40403005016101c1d81a4000c00b14040298440c00880703600c030286150150805038100d000c52088a00204001d00954940006218505203011848042c01c001d03c028001801c055602034202c0c0304003800642045001d0784100d81240c00369003124803100242d03010302e0f500d160406040c07010b242c80410031a1564100080040d03441100c2c0c082d80c0c140c074202101ca10412400c4d21054602c0781c40080e0302d8070a6a000c0c00700065039510b22007018400c1d80aa0003040c2c2d0380059142200466903030781c109414aa28200750068024410040c94040d03540c00d03524900000150a0164500300ca440060003843c4030001c0c0b070034102080c81c0c00c0b00045801c1698210040c5460700d140f04251507007202c0d03c1001810030300001d80403a407240740130100002041070a4000703a4840d04003661a80c040c002030003141c028030324040d0044004214152522078000c4040b4200d55680e40d03802d40b00c1c0e4035440380038180c80c0c45c0c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 957003282 1250 957002032 957002069
    0x60b091e0912030a020315030f032a0102070507032901030201080601020307140115050108040206030403200f151f06121e09030206070c110402030709170106080c06070309 75
    0x10400000c2c42c11182d2106620707071030300c03400b410040e40c4110340d01c1c0440140c4040c40c180c01d08000540f80c8d109034000004d1420201c8909a01d4003a542943d400141070b00c00440d5005086401c3c0300034031600b8091409401000e00314104070001c5040c008512404d400c0c8000304602545512810b01d055070781c240382040054862400407861401100c4001d4140c181481f10350300e030381e0015480300d00d0011901e581100026910b100546a041c02124082c2d0029810000900024450380303010b014188160080c0440c4140455114545445204043c25560008442d00010014840b2059000490088810f89281c40c1140c1d00340308102480b5440078025901c802d108043c040c1e4101700800540b21a800503400c5918240c8000b4208a41c0c0030b030094000e950100300c4061042c02c400c90055040741c22030400081510070b000c000d41c001004013040241800003c00e20454080264500c21501800880d01a0414105a04000d0038400300da100f008100010000290410a0142201d003102034100d0394168 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 957004532 1250 957003282 957003301
    0x50307031b030c0909140c0702180103150b092a0417071a09150d23190b010f0809010617070612061a070f060e0a060b091e 54
    0x292070301d0010111035071001c00036810752003903240d207049030360f12000180d40d1030004c4111012445003060002802000a0b41c2c2803480d402401d14510103000b108109458901da04800f500a07001102c1c0262200310001c0c00e000c180c011120710600c00c440c0c0d0181800c00b0300f408040c9864684104403206101d80204030030490107020746005103075585169100c013410b84c0c1666118601c60089005500e5121030b05c0d0000036540040e110198805414203240050424030402160031811b0701601c1c90307032180a0b126485c1c9240120750032811180000c0c3d103003421b00d000580e071007610811002e100d880c9002070410300c0f40c0c1c1c0004a8001c401445c203002c256900c41d101c106001d4240c5810520f250300d4082d0540c4080c5000240140454030a030741c0e0910300e03401c840407860580b8000d100d10a08c03180c0c80175a404100001301e0081058074400d80c2c56040c459034a43d2840c040d58440a42e0040070b4205040c610203200303030750280c1422030b0f10481e007030310952a022440625000c0342c41040402c8c178041da0000b806112 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 957005782 1250 957004532 957004541
    0x302040b040e1b041401060f050309010e011b0e0d0b06040b0301150b1308011505060a2d0909060e1f230103060605030402090c09060708040807141f05030703 69
    0x11407000b070700d040820721070f03000c50407034028072201d4029071420f060701403411501c44e92070341038800da99100c1c4100321a008007143e1980004c3c00e04001556191081c0050070b00900c6a400c0c4102160841c0729843c40420014141000050105010320302107507080b000500801400c690000e02282d002860424050100380108002404c0e0002c43c801610701080150804000e003001070400d0450490960700c411500b4240e40c0721034000c8458000b2564140014a440300c0130b0044c4540c14a81521315441e0320980d000448024480c0d05442c2d840451202c903043d50028400d00504641c0800340302c00c900d4440180403554006000c075108900d41411594818900780070304c40105028070300385c101c1c0010041440041e0500900f4240402d150650028019000d001540c2c410754008017409002e65600e1040c0342c1e40d502880c0c0542c1d10000030400b2200040a003400341015040010007400b1103410019400480043e160b610340c07043c0d001c91544011008640b0100c140720b045032a10350780303075102c030701c070650140 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 957007032 1250 957005782 957005801
    0xa0b0702030a0e270108010f1107050604020d0602090415030c060e030303060423010e0f010f030b0f0a0e03040b1c1107060b0112090510110a17090a02040e060910150302040b04 77
    0x400c140c0000136481d00705401c80301c685049230008104400303214400c1c40c0c40c0d00c181080100741d03400c00c0d40010007500e0700750001c0c03400c2401200b0261820b02c5000001d001c585a00801000041d0700460510600080f41c0c3d644000d005541000d012451785c5a00181d070341c0c00000c040c02d1299448a82000c03103050b504001c054251402501030545584503038031031103016411100ea503811702100c000005d00901d101c80800c100c1c0e4010900e91241d450f003020031102a40010414102a5101c980c4161031540c01c1000744020000c006445894070b007050f1040100e552200c0e20803581c10b003441c412000c80d003001e6080b00e0055903c804005140f0000e0b10050310f0403818000002c42d43c87c0381c0b81c2c29409122020503a440d003a251041d0800c04c0042c152241c400398011407902c400000c088000041408025146d442e4110310008116200a4103907800507043d600d4044855850f5000081400a0f0503001c00801c149101070241c107008024011f0515400d00c0b905120203403099031150b45071991234803254004c2510 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 957008282 1250 957007032 957007099
    0x8070e04052e1a0a0e0306130602182d09090705210604081b0105010605040504090503090301092a06021b010e040e061f14040c18080a0b0702030a0e 65
    0x59907007103020300105810661060303000c10288144017040d4a40820118071840407508901c00c0c00310181c94000003234000d00c5040c00c5130402e840e8982660717620280c003d4070140d0042c1d0450034a2003c11205d5030508031000b00c00d801100b0810074001d07082804200e0805452040d20b03c90400c2c800180440c01c41d440094040d903141c040e04040c4428440340714001e00e401e000f00f84400300225120003007a82281c000340301d6800000c809000900452509410460f081400740e012a4200b02c2080002030840c1c0c50b144d000ca884201844c0110181d8090700303092200c00401c10b6201f1405881d08601948400514004454403103c42106101036070140380201561000500b04100e100030300301c81c45130342e4041a90113110140c210074900c12081000014441662242509100d002a0800510002d8108440317031030140628880c100c110a1030001210008040c0b100003811418402e084c0310f190702001401c1d600454100300410440039402021059456206403540f00c5015500e582080100ca61004100d04 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 957009532 1250 957008282 957008309
    0x109061703070f030c02031603150c0806011d040e031602041b0206071b0803100e01090c02100e072102100804030219140304080f06060d0209070c030314040308070e04052e 75
    0x2801762b8510841029043c0010800c1100c0d1010310680b803001040b9080e50000b84c5d1f00b0021000c40d02074240103c018000a170012400d000c0c2c00508a042d0b42040710541c0364030003950084020b40c070300350182540c04240c014400341800d0581034001d4552800501c0310090010141044030400015a4010716094002009a449050000382d00d001e0781030300c4c071545910b11480c80020036036070901e10502518450300d030010217505441c00045005020000480440b6000301040012907110000890380500404030342e020030718801f07204000641920050040410040b00704000001b5000038a0710b007414400c451408145e850b80c41d20f1150344200820a5000740004a80099070b12000600d02200c4d804c0b60058030215134510381031103508142a0341c065800340002021030354590081300c03580c41003400303850041140d02c14509030040400f030948086000501203030400c52225800080c01c1d00111084505111a08104c00d00304000014070728142c10701c2c01c03038680d00e40b50201030303034040070081841609504 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 957010782 1250 957009532 957009539
    0xb060d060b0706050615040e0c040f1518050f1c080d0207030806270a060b0a08071206030c1a070203010905010605090a0e07090519050109061703070f030c020316 71
    0x900907049100d0844845080a0208031580381a06c10314080c0c803c06440c2505040c0b5041104014031030181449284075802c00010980504210080003c1c0500f840418040089250024095038040c040101c0b249207940c0280490b98031441c141c26503190486c0e110401107070302c8000701c1d003070f2034140b2000700007980000700500b22001d5600038140c030034000c0d115201a070383c41200380646500500303000d05124000030802d00786600302c10746650304003018940c0000ea081e100d403d02010f40e80200f520034040756402e4200304085500079800a41281c004409001c1c003455652402e45080c1c1900640b00ca10709004081440103000b541a90300d074a4000b0001d010080250510500138a928080c3c18090800f00d8006045101e45010340b5154080100003000f1140c54100c240000702000741c0107100394110418080340780c610b10300420b17020389107015002400381d207042100c540090746c868076400c03030743c0080c4400c001041c901e40072440a075801d814030341c1c0e48020510001e802d25902d200d00103030030031800b000403 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 957012032 1250 957010782 957010799
    0x110f0c0d06290f0306040f06090c08071221020709241e1d012105011b020c0121110c070608010e1302030d12020c0706050c0c0907120b060d06 62
    0x1051556030540e4243c0008160400345a00c40e48115805010220191038120000d03502d5400300f52101d0040c141d6442d0f250700c41c80428200361055125100c4c08103003580c2c800901c400c0601c3c1115480300200300c043c0c0810010806529842e80b4030581750216903d0044010680c00b440d012101c6134102d080c09030f1b0381e54492a8079180c2c03450207900b0510b1420710388004100c80450304104025600001c03a40482c2d60701e441d8942100040c0c404060b070a1010669070400003802c2402003500c000410902c40200d0f121f4600001c0c600703031143d41d140341048024003054480c0441603860044190500304082441da103c1c41c140c50480c0701d040112121449803070302c009041a441901d00e41030f00c0b100d42c0007524548031041711013412001c0c0f52001c1d506402114001d0100d41c09029000c240400b200409400c1085200700c440c02c0c5500c2d03600100c08100001810f540c100414008085200c4040340c6009a034185200000c10110710900416810b90380e035034403601c03d0380d038141c00e5503030710f0001c40c0e01030002a03241c03200e0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 957013282 1250 957012032 957012101
    0x342403050c090d151103062101060e0903070203010c0906090306021b03040803030108070501090506190e040623030703031b1e0f060b03010e19080d1b110f0c0d06 71
    0x8000c4c2c0d8515210b1110240603079403049900548005011f43e01030b100d01e80c590b14135140d83c40c0d002a0503640c0c2e4800010a40074010780d040c0704080c42400f840d10741d82075005043c01e42c5c1d1014485010050b200d0b100b48103540d0410000790949801c0f200c0140c81d2042048502642a12254000340342e10001c5000601343c88004021416161a08141c074800c550701c41c015a0401440c0c000c0c0f9070302000034800f07030200003105481d2505114580c0741600041c00381c2004101116080d41001e4800b45600e1103d0694030000c8010202d001400d45c0100005803558800800c0116210b1652022984144815042c0210801286260540366072156100d070100d240403080c030f0a0200d002c80c0c1c02404d00c200d250342c40c6418400c6920b101a00000b42c488180e00340c2c4900c0908014100480c0c44110500102d058800d4a102c1c3c0020b007158051641c680c40b0800a0103020351403010804c40c420b034084e810199108402269403898440140e5040c004104140f0b000b00145c407050014000e040c8407219a0320401040142 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 957014388 1106 957013282 957013313
    0x2131d1c050d0b150307021504080d050601050d0c020d08090f071415130503010b100c03080a020706020a020a1104060f05060705342403050c090d 64
    0xe103244404a403d060707040c90101c10000451f03010041c0305940c1c550070340d1902c003a20b807a50303d1404502c500707005039510646500119200307902401c19100052880c403028000c1d00302c0c44000035580c04914190300006015400814082100850031030310310b00e0b08501500c115801e05444040202c1d0b42c014850300301c40f030024034804080094000c1c0c010b1601c02602034903528501000c050a6460048a0501c03c18284071070300c0440e03800c41541c1145981c50b0900039415614400303080700074021b01c100070744018000240d14480542c0858110812b6100d0f0001100031254003080c002200c01070b024070f15500126103030a104038540840900310043c440c40c12034004034911020001910031840d200d00c000190104403050803038969241a0142540d050100c541c400c41404508032107140d10550300900d036460020401200001c000c4a4015001a01d129900403141c5011400b03035032000c0c0c = true := by decide +kernel

theorem cover : BRFrame.Cov 956834532 957014388 := by
  have h0 := BRFrame.cov_init 956834532
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956834532 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 956834532 ≤ n) (h2 : n < 957014388) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
