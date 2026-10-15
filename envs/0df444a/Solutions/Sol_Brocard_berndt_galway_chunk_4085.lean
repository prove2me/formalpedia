-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4085
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:32:00.646513+00:00
-- url     : https://prove2.me/submissions/8e018d32-5765-47d1-8dab-c231e7206f79

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 734532374 ≤ n < 734712230 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 734533624 1250 734532374 734532377
    0x6060607021809031c1806150305190b01060503060102150a1806090b061f03150905270c0d0605130c1e0501030b0108060906120102270108011511100c 66
    0x128a83c1580b80b000c1c80c4118000e070141c5d108005807440d080084c1c4401e2084030003c3c01541c0c0d070b540407607040c02400d42080040c641010845200c628078001e4441c00500c400340403200b42069400000340036001d02d082e02d00132103058015080301d1040012600d40318000805403018561a046410b02c0d0351603c5a9180c00b580c06044040388102d11400d003050b8500c2c000d42410301580c0388200c107010035203c8a03a10080d0500700e14005c41d1520480900b910504070f143c0008041c14a800b00b4030070035603c010303150651542d05814001d20801c10030291500c44c4480d95155400039103c0060310001105984095844420226102034140d610380360403101c44116003003540003c4482c61102c80b024444400f49000b810b091805000440414000034444280940601c0c020609040841d00682d20300e07070582a41526403000315140c8001ca84215500114074500400c0c40c400c010701a90207510540c80213050b06d403060107503144054000b01c1220b41069003000c540e2640a080c0c4005003082d182e00590f07024644a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 734534874 1250 734533624 734533627
    0x60f1503052a01090306050a1e090b0c0f2a0312010e0903032401090801020f0a09120c031205120a0605031015061112040e040b01090203090606060702180903 69
    0xa150b42a503180101d10100d2100c0b001c840761199407684d00c0f40382202642d5000e0b0011a1688035a0ba960029041031030800c1001145000380c0e04808650740d1091605a014070004151030300c4d5203040042c644103480074000341141c10401100001d807034510031603d00c0000641d011601d200c0b00706482c1181c100d102a080207507403003001001105003143c5480e42000384c4001031465400d00c5441c48108140700c040851000c04541c40303142c03050707000e0382c0c0c1c4000030104c060007555189040c0c500c900302684200c11210105040d40c03004109003103501c0d050030303d640d8040d4040d01640d0640e1074040d008024a01c441d410021704201c00502200203244003805002d490300d010031100d05020805050002c40e003502c0c4203c502d41110380101c41070300c28082d012035a240c1411200d8101d000703041c5040c00c0e044544000b03600310000300010010211401d03644180d001d02010801662a800001c0c140d10065504c003030756912801c085109440d018008250080c4000c0c01072842e0307903059484072400300c4111040400d1340c10 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 734536124 1250 734534874 734534893
    0x30105211009021201050114040c022401170c0d080915070b01060905061801180b0c03030f06100e092d04060b062a0106170601090606050c0a060f150305 67
    0x103003401c3c0c034101d4184d5038000380712030f60400c1c0d0120403030326440a0f524807958036003445d600420700a00003203110612400c04040100000144612110303401c1c4034508030301003a1404540a0340000c511600c51180003492003640d030700b1544030340c5860340201420590045105500e80844103d240081184034884d800205046d0701d8000060300c4207426501c0140a03140801c81c14440c2070344100d0304081c4a8017400d00c036207000e04950030f00c1c51a181c1130300030780560400018034503120080040034520414020f1824012580e408080c0b280c8510300e4411900401c1d8140d000811910301064100c0e0310160072140e849500b07a061100e0100116203030362440600542e03100307103c00e1060074050420551426070305a85041d4407451154001c11607190340b068504403980d00312001c0c1c0b8003908a18000e00518a07500e40b00e98850308210303180c480a128a0501078646140007400d2409201502d2880410318058100f01c2103030380311034000c0c041d003070b182e001541e49d5201008100490020898041d5000d8001403200f5007 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 734537374 1250 734536124 734536129
    0x1203090506181c2105092d0f03030a050a020309100309030f090b18040f0e0d020c1503070503060a03020310061719030f0203070c271103010521100902 66
    0x688410704200c80701082030f5000c0881e90451524800b00b001d12140c01d80c000c0c60b04001c46050140140b4141d00c0b062244400f0740030307054035513802101664200c1d01c001c00741007081005600300300880301980540062200188103800799014151140260054911b0941e001d0002016a02642d80900100340c0d100500d50500d60320810440740c8070554182a41c4080c1004d800c0502801204151084400601e4038503c0ba6203498010640035602010305102c024581d00910381c540c0107068001005200d5580901e25520381840d030503890581c4481e4061075a10f035030004542c190320080841c0d4104400c40400801628208054110480100000038200341482e40100300040c9401130540a0390050040c240d0b503000e02c1004050b015031504207105041c0a4100c1039046001d141c902030115403040d08001000d1002c0a44c0c0014086000140d00f0b070506050010412a290200348901194090005028604000600b00e00032400b003104285549039046000c1c0c64840003908601c007203900e5041d01001c50 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 734538624 1250 734537374 734537389
    0x602010b010e0604090c05040317090108130804050d031107061206122a08060705030601110d080423070b0a0207051806040209041b030c0e030a050601120309050618 72
    0x2008246030021540810704000303141c0707019a004d0100c9859440c100b406c0303800c0c0101d048034020740d030010340540d644510296410340c980000000c940428140e0b00040e40e02414807031201e61166100900c1c905007070402c42403140124150034228240050784590440110040102c03800030070f4141d40d010b440100700340109090742c2c0c6503408108440030700f10744000011000525418480b00a02e50060340755440c20001d8640d981c207070f2122829003c3c00c0b0a004406910400840c03051038280c031803101e80301c401e1624998030308030000003400050b0914085000114844116444004400c85159010040021460512605030701c002001c0100080d20040ca54043c00000002c1504440000286204444c1c9010140d030040c142c80c8900d13400506003201d41e40f1a4404102c1a140c4a612100411210700c080d0043c0345869013140801c80e004200342840c03400040290445603c0f0000d00038030f0b4a000d620403c0c40001360b8044043c440760303802c04121b039242c44018010007026419070b180000350103006c3c4002c1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 734539874 1250 734538624 734538641
    0x4141501150f0206160306030f03081b0c0309010804140304090509060f04120305090307060c03090b0604020a0905010509040209040903020604060e0d050a0c0309031b03051203090a14071806060201 86
    0x2800320000050903a00d0f000f1854950040c1d40d0644d40f0a2070b15260030442c0106200c0e0001480d0101e91008001031550290721148905407110b4011076044404000e82018040c0c4201a40b00c1c3c1d00402401220b5403003044000d0b0818840c564001240001030307905410354210740c12070b980711aa98410072110722401c00c0000c0c0c00071442c402211140c10305884081191002410103410303d511880815803511040003251045908000304100c0c601090400030b010f840b200ca02038950340541c8010856514007882114800c1549807109e0141d80d1a04005445c20340107058031581c0f0036402cbc010200682c403030303014014405101e0380c0900602e18262802c00121404504140c0d1150301490080021a40000071901090403908014980386240e143c1200d103016640c100400e0032441607e16841d442d08a003000e400d603417103401a6031000e00704040c1e00e406804100c3e900c07071640e0300881c110400300f04103c2e4510040e07080342041d03030b55154a46e000d0241c03c14420480c42440c4d652020b04018090303080c840c5102 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 734541124 1250 734539874 734539877
    0x80d0908181c0804120f06090305090f03120901120b0310060e070216050d080705100606020705030c0307030b040515090c0901080f0c040f1e020408070812120414150115 74
    0x300c0b46039502e60b04118011030080715031048000100350240a030b025100440154004400d104114480c503000b80a50403203200359028280070301c504c8416280110792801c403100440f692034106010b1400454800721303845800c0c40059235400700000d040c2c60500107500030002072580810f0741490400d490342103100c01030040d02113410010710030440c007407050111001c03510206c0c0c0c116042005070402e0035051040c1d020080c00e40c4501241c2c1c0c6460013050300030104665182c0c080d516066607a1040c140c50b4136a2060182c0c1c140c01982c014030020303840406032604503000c4c00c121050040d2a80c08082c030240306480009465111006071016803804104160241c50801c01800e9850b403012a21a600c1341040c96540c40740352212800e200c50b81aa51140f50340c0c0b0007108251a0b43c0200a052000035400b60184850500a800f408900050000340070001500b003c2006440c3c421ba4070a0010884000fa008940f0130740010300b0310240c00820444c0048001c500740310b40d500c95244c40348084800480d40039250 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 734542374 1250 734541124 734541169
    0x73504111c02040209041d060708100609090f0e060103061505121506010e030a080c10020901080a0e070b070602033c180a150e0106030f080d090818 65
    0xc8605522441e421070740c2c1a18056111040c3c0c1c00050064105d213401d030810480141c0310004480b100190003800f070359040c2c580600325102c0340f51414807110f541c003d01c03000c254248810030041169034031000d40c50ad41440d00040e031072181c1c620305007001c40a07441528816143c102c150200044880404020103007120703c501807507420300b070241e02d4402c03541c82d104844002d20001025a4040c030031021030341c9001401d031250313049207103020f1f0180c0d04603891281c80c0340320301040e010f1407010380d108076007188105859210075540c0b10001c0e100500300e440d1415500c0c0c01032410014001c2108000380001e244102c4000d0385174a1300144800351325900480907803c200004100c51044848545111101c010720b4100d9021781d55483e0f901c2d16010100785100d2110310a0f540c0380001e206c8500302404154205401c1405001504800182652602d010142071103c45042600006841c60b0080c030b442103030b20b007011880107400c0c2c071907500301d40044400c001c040035011080082860004031854031128021400c4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 734543624 1250 734542374 734542399
    0x5010602011b2706120b06070c03021923030c01083c0106020a140d02100e150405030c01060911030c0c0708010c050a08010506070b07350411 62
    0x1007501d20b01d00007050706100c000400d03444030800c52091a5401c0208814441105540780801040c04400c4c01040940720f00e81495003034546410000c0f6181507421040500b40d5a05503003c0100d00c6088080d507541c0444407400015080c800400600e801c0304142481c20003601c00c0c2d8081c5400d01070000361090420140004000f034100040b103542e0303c81c00280403034051225514030b1500c1d06040c01d50f4515940f4503240d00010380306600080b00802030780b04140001402e03060380700c3d81c0c0d82c3d007480c03a05a0000d46c000309803000038514071f544803043c5101e4030700c221403411607480301002c03c402059400b550f4503000082c502007580f0090080c41c0050040c03200410040120000c410071070f010140242c4c4414400185011084204220003000380080340b00070840c9220280300501264030050702c1c140402c03c00c20001810f483c0030401c0e5402d003074000210700140c2c1e4070400c0460b00040c103620041080c000c8201c4060bd5101404440f505025480c1c007521190704044c2004061103000ca039005102d8070030444407 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 734544874 1250 734543624 734543651
    0x120606080f0a050717180604260a022a090709080618031605011104140901090c020607230409051b2104051002191205061c0503091009090501060201 65
    0x10041c0009403107000d0039503191502c6d511a111000b40205082d172007080140300078804250030840c0c990001c07a14443e90500810980410707405610480c00140e044200c4d001422400420b0350780303d00c910094500e456070b451200041c2c41140590b0311900040b0100c5041c8180074013005041e03000303101e084070704082054110405a807031207a05201c062003e15041d0000410400f5000041a42c403011f140035129030711103500340c01c2a01c582040134807a100b801d00002d065969441078042007202e40d8082c101e1a50361074030070b80d2100c40c1010441c1800ea89040403000100713134000908040c08581801090358140404030715040d02c0e00400d000400d050070480c3c400528020710300303070209099060321a04e603070f80c46e400c04c1030422240780380d400c5216000141940440e489a021008400503a0b12100036541c0000d0504048070307070451b4515049420524500360000c00301001981c018890000c0384e140210f100003052104044201c04408101804010310425545001e5036000d056a44002c0207001d11030600b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 734546124 1250 734544874 734544887
    0xe0c0913030c080c060112030e101704020a03021002030a0e03070e04150f060b0909150108060f06041a0c0d0e060304060c120e0606030106090b0a0b0307120606080f0a0507 75
    0x14028107010b007440342c900800c4043c0b0143c0301e501c1c070080161071896035114403004a1460740c0300c04a000134060011282903140001c0154580002d40d99580640c000c4410a82241c2201800980c2e206501440000050740e4400c11842c8400c0c881d4007642c0c44584d415800740c515102c504081b4400d400c4010b09000010000514903071081d000308404001000b15404000144003039050741004d60b041c5240800d04140300c4004003c0c1000c10f4070f860845503a0884940039481d211035806000648404c0861b04604d00b078004465038102c002d000514040c0d81d22a0f903500f120f0180e101c80342c4050003046000c008403045c400d20840b0200c0303007440c00d02c61100400103001340c4001030004007501d580f40b412a8050b44280c150355903040e003114042002d4250691810b95030b0004496041c400c1d800c0c0800840c030382009000b07000620002602c21504079041c9050794003142c000901d0b8000f00056206001e40b511828000c1c03030000d0246464000040c1400001800d03100c900030000d004084c1880c061054041e0f1000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 734547374 1250 734546124 734546161
    0x16021f021b241b0607090e0903030f0412020118230f060718080607030501090c030605010c06090204110d0207020103061202031b0114071104060504090816020a03060207060e0c09 78
    0x650301c28072040001070310480800c402c0c0f0315202e0f0800300700d9400d0300310801d441543c091561300802d50b5129401e540c1d8910080301c0d65214543c1100118000a8000d0786405412a460001103401c810100d000f24200068010907203c045140010003001c080c40d010b410307241c11a403c068140c0000620501c0e9460802038524010041c0e0030307009640740c14181c01c9040c0034004020540707620b8104988001c026010078080c058140e0314006c1e120f18028024490807048400603140c000a043c0b079500c4500c020040d612040e600103440e01c50f515548542c0c08028800c18882c0407005031101001d0000400310307201a042700c41011b0f50042c00e10090b035800201a4002040c8200001c00c1c0d038040801240d101c480c010036801c10480c04500b1a04100c0f400400d90f444441c1550104100ca42d283c003008259104000c0250001c0303400c0018002c1c0ea16580300030090f00f400034040084840e41c0703607694000c984c003456040c1e402541c1c6180c1c0540000050011282e668011601d60750390f410b240708255000c80861 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 734548624 1250 734547374 734547439
    0x10206070e0d08071a0f01270b040204030f030f030203192c07030209130206190306050307090b100c121b02090702010603051e0316021f021b 62
    0x594410959580007000c0b040790b407200005864080600c2c2c40031002514000d4207000081202c0040d41240c2c404010504031002c4000d01c1910a0540c04030982c081c00c0e07500c0d90215181c40b074402611300c3c1c407036000a100461042d800b0b15544901030900a004030006004001050f0040080c844076418407105108012120138000580d03544c1101480c0480305040e0100c80c1a46004000303102c40800400e40c0811603000b5110091a641c0b01d07040d0148010407220025440030007800003404040b440f41c03016076001c1c50ba040000b40140c0381e6001914080455204004190700c0c1c0c0396510040c01c0500442c411428642486c4904000b81c0d0348500410b09030301004401c00c01c6c00f5200800c0715a001082c041e1203500906901268103015000901a21041c002540c1c180324060741e107800400840b071081c60301690b081c05141028600b03441c48540040824003070760f008050b041c0d40150000481d800840003000f0707030014a000040129401d00074928100038900c41d0108004482103123400050035040030025 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 734549874 1250 734548624 734548637
    0x10f0303111c140d060b030901060e090318031504150c020f07030b0604060e0c071e051b0105040305060a050906060102010603050705060a0302040e0c0705011107120e0105040b221401020607 83
    0x42141c0072001d000d10a80302407613a0400100003010751040c1c0042d13000341c0e1f80038020711a541d290310148010990a403500341240d481080014825040d03101c01c090b125078000c0560f00c4444041c00786009214054809448146050118612103903561050805a14186c005030950f5040b01d10a40d48548040c030025029200a42c00036400e41c0d121303030101001d02003200c022015410020b001c0c00e40358005507401c8603d9054440c0c040e105030000c900f4030940c540d112009003416028030309105c09000b03d03e0601c0d4140b0800b030201000258050003020301c0f91114000c0051140b81440c60249855005002c180c150392620702c00340085900403400005449059aa40c1d95461042d0000c500a10459102100c0b150858040c01540340d0680000d10907640148000d2040d03412000740881c09204001c1c00400085103c07030310a0290f4007030400b924203d90705040c0305003480e955001c99201548001c0062000113400b0b103540c608001e0000f000405480340300301a000212840300080d60350302d8068284c1d820310a1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 734551124 1250 734549874 734549897
    0xa060206071b2f10030204090c051204060b01031b02010f060e10030813120308042010030f0e16050306010e010308223b060a0b0d02090306010f0303111c 67
    0x102c884084031207480181010034401c20340344d801802074020f8044c5920690400c000020360a01c140192010404803840307202003903c0b01da03038620040035040790036410315840784881d40c41007400f03680d0030400078104d4001203045002500148200d952030303003000d00d4409280d400e20a20342d4518200109a0341e10500311660f41841c5070b5400700040072580810a4550580b0320502010360200000c0d020301e00c0f5441c00d030191401c606004080845600c3c456401020032621354030094403e410404881d401c50740001450041c4080d07180c1443c085540303001c3c002c071140c441080107080c2041610b00600f04212080c036254116a1a1002c9120350a014444035a41030f005601650040309040000c2030094000c0502c2c01d000d0641104030f400055100d8804510720300e83d0520b408000d080c182c0700313103801090300e542c083c2800b103440c0c0c042d04a4850310300310503400d0080507100c2c1c50402006000c1d00c00900c0c040d8210745145001030003d0a4150450080d4000c07203040602d1100c18080075a1000761030404811091 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 734552374 1250 734551124 734551193
    0x10824180a020417010e03071203090c032612060d0201090b0d1b030b180c0d0608060105030d05160f0201140d0504020406060c0c051903020a060206071b 67
    0x1040c940100c02008000c1405041c250399030061045400103c003056100c201264280e00321511a4100c4100350000c125010000710682d4400100c41c1540c280040e01d124280c4920a5182d015001100d0152642da60031a02404010b9291f400e815012000c0c0d18060045803400a40040580424015081c5c60103907011617005104110280280b40f54407519489000354402c0581058406040c81103024080f16150ba131190148200803c000350418000c00f00c2000ca08680130002003a155850301d041c455805008114003c0704000c244500003480d0b1941024105070903e403640d580d03541403040070004100104a100210b00da03080e007050b120010b015080c001a560011001c01c03541c05041d001071880103524896024038065802500c00b00140c586174602606e142d961004050058107025908020b05e2600000452500140520000c4c6896503540442d03228900c40c4c0001b805608000100f1010315030000c00b022486c0e0130b0b41f080d4000440c4c2a00d444907565140d0590200c0110150200502c06 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 734553624 1250 734552374 734552389
    0x50108060316030f061107080909010e040807030e0609060c0f0d05070f080f0d23061909180c0806040311070e07030507180605120901060803030117010b030601170c010824 75
    0x400d1b89210343d40e10308a43ca086400e07076001c40c54451007040e07214004942c100200e08514070696003c01e550f46090500e44082d03030700a065628040d4001ca0402040c0300d40d40707440c000b070102902203c0c0241080e103003403180b071410617002d020000300b042030a21803d400700300442032050802e40c0003043d041d990f81400070729a0442c80707445580c0400c5428000b402d0745580490345903400c0a0261500c000864640c4801c10410724592869a124070503205024001e000e070031390180340d00765225030401004a02a035036998019500340e2041400d508124208818140c0019070281e0030003a000190030385e0360910b5000234562502030800020169130702c000440c100e0240d4108103428210380c2200500b00da0300c810052039640016084200b690520000c0b9071200e405000744426125020041d5046a0034034081020f0300c20117118003c0d080d925681811101d88040c0102406083d81c3c100d403240060345048003c0c40c00c1050710082d410000e280701003001403040809080e0342240405038115041c1405400107100c03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 734554874 1250 734553624 734553641
    0x60a050f0706091a07110c01020d032a0201021306090522090506190e010204120f02030715020601060e030c030705040b03010608030412050606100903080a09170106050108060316030f06 81
    0xe1049139944403001e280c1c00c00b0210305c07500f807541d0380100c1c080010703100644407000b85203c83c0c0940d2001001000a034007980010280c004212400d03500072003505500000c07441190140c801607540060150541c9688200e220060101410084003462070103001c96120032070340134510000f645802211035842025081519480c0e08038003100c00c0b81c1005e030b0b008410352540707a810359821441c0c4448040390b00b006000f641c04545c05d2401000202c0340d1074855495403806413404a03454003440724040761a1140625103400240c40d42c0c01400a58100f03400541800c54001c0c41c2032080d400703460721040036540011504152903099401140019801c4042405410242c0042d0081c3c00007080214142250310310f10801c2500031000c40301c0d651105070030b1000c040e4140c1440c1002400c0c04a050001c07440c80001070400107151b2500038552507940d80503110006400620035826516a1002c1002d036a000703195a80102d422001340200b4a40a10200b9002000b403200400c0003008200c01c03018000d441d1b004c0c001 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 734556124 1250 734554874 734554883
    0x308040e0c1b1c0e06030c0c0c03030a111005040b13060b0a03110f060301030f0816120c020315010510180503011d010e01060510030b030a150f0b060a050f070609 71
    0x380e210b111032450b489240d01901e0060900740c003010b5072041072140044104510f00505010701d1600c03114441c002c640e001034101041489048a00316039030705d00b00001c4c19030440b50303901c9050782d0810040248c1440f8860015098070390070301051101003450321560b0b0f03802040e1142d80008c0341919241c20005000c1641c0d401c0d43c400314403000082030001800710014003034000c65602801d01c0c0c5072030800c2a280000c0c0009000564903a8003800011442e900500f6a0404025480320b000c01d165545080707074501c01c51503070005420f800c8100460408003c0004141184008031a81e036060002241c1c44920012402042000074200310341007000103011607024090140092145003000e05403402c01303010156030481c1940ca82101c2a9a00300113105150036036000030180441401c0c1d000c0308030054000f03801e4440d81400b60704d042e0f200281030502e40010804c100750000c0f07000c2c3c1c08007071f404041f982e0700c01080e8050003080010401d5280d2090071240c031414512100d640307a503000e081c900c004100c5010000d0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 734557374 1250 734556124 734556157
    0xe03010e010b0307120323070807060903020c040b010e06090a090c0c0c091a0607080910030b010e120307020108040512040b0d0615081512061302090f010308040e0c 72
    0x10014041074001d01d10802080e01198066580e174161451100710510029000501240d1090503410111480802c0700c000300d20410b04081c40e9480d84c3d4400e50143c03404550190362200070004050701441004182d20048504100c2030b0800d60010381252403408090f0710680002881000a41d5000c1089003e044121000c00c058100194043c0210040a030b0a0b203443c02a0140040ca490301170042c00310319002c9115401c8007900c410107002c1c0f2a04008821200d40409000a024640b1661101c0c502d1080664010504082c01c0b0005000d001c00d0080d400d020762100e0b03041401011000007162440780e42880c04108030f1b0f6075410450700300003142000c004111000503001501400c070b00090311076015541130401c01c084da140c8080780645c404486034008a80810700140c401205d9940d80d0110110107484030a00706c40c420510342c11304030120781403449503004407216010b50a0501c0c4082d8403102c141903090855056440f44c02050090b80305504c1c241c5101720006002c2a488000d86510095409180 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 734558624 1250 734557374 734557391
    0x109050c0108181903110d020a0c120308160207081507080705030f0619091805150105091f03020a150215160e04110f030910020a0f030c0e0301 63
    0x180c5841440350103a0008a00c1e03000301c1c1400200300403154030030500100038501d01d0682181c4445503110303c201541070041c00340c2000b80400301444880320680465001d410320100520341452248d00715000b15945c2140e07101210000390308060129045900442c01c0c5400170815102245846101e8004000350702030902404450201c1e050006d024559648480304295142c48040701c0b40c3c00100c1e0b1076040c06102c440481c1c92814105845403502c04014031190165444000c2103007914207950380d10001c41500c0200b282445418401c10741c04202074104000294541400034418403806003090440304100c2c2014209520282c0b8003000656000c0d00c00080c2036981d40309500c4860400519001500540c40032401c4074650301c107028030510444140701c4000540c031600700d950540150b4800d42040e40d910b1032080c0450312030b000d8411004a440495506e1a244d00310500b80500040440f4501e4014804101b00e503400c100d07034a6081e040341c40c00040844100604403400707004480340723503055440e20094 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 734559874 1250 734558624 734558633
    0xf06030a091406011d04031709120406051e0414190e0a0b040f06241701091e0b090109021c0906050702160f09020a050c0d0903030314160806120109 65
    0x26103048810406081008070b500170903d145012044070001d00040b1a0b4111008520310b0746416500f090a00040714803488641c0c118070b52a503c00d402c0080801c4022070301c00001246d803012803104101c2021500c1c141850701042e42c80c07060f052241c0360706c550440183c003001d400380b4019400040a84100c1c0740303290700345800c100c0010442400094000c6051080000080e0500d010304400c0321041144034000300b0f00041010501d50b041e280c82403c2000c0c200000d09000d00c40c4a01b2130107080300d0740c000296940015013072881214440c140c4121107080440c4203145550b0240c0242c110390780303030320090f80d034a43c820b4410101410105040e07031050b00d0240503605201c0d29030311062045510380c08036141040c0b200c002d05072450491080ca0041c40354100c0c00d000101254001d441c03100c0031801d11a0400c0300d02800d450501403c521800d00203101000100241a0703d4050121220b251a004e00117600f4019100d86195510302d41d08002d1005890205c2e040351034001102c044501c10034005c00144881e45003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 734561124 1250 734559874 734559883
    0x40c03020114070302100e010b12101410030204090212151801020405090604090f08070f0b13030c02010e1c1a07030b011b05030f0c03030601020607020c0f06030a0914 73
    0x420380c0040c80120414070901d584108503a845038140e002000c50340d801115800c050070381e061920401c0d54a0708602035a54880100e101c11400414015100c0c80d00c0030b05150048441c3c0080980702400d02c0380612100c81e4842d0a180305490701954007140800c1c240c00458103541c0400d18200061041e2502074081c85072000342540104180e01e039107100d58006820070703130030b070700540c01182c0d07101c82c20380081601c0346095481421201c0c0f08803049041000c01d85c903500b43c0c9400c50306003601c03501d0014403800208028840703001c0d8084078809200c10b80c1a101c3e1001400b65104420090500101203005446035941c030301041c0c80410403041b46e40402c0640e24000ea0114115480c50039a0038000c800302c1c0c4118000d001c0e2004000f0b06030b4801c80640080640100c1e0010801c209841e030340003c00409034107602c13020040c00054410780017180d507820540002403404000600040071134103c1e07000c0745226030b030309000c5d00a10b04088804948076100c0c4003004009204842004050100901d4907440420000c40d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 734562374 1250 734561124 734561129
    0x1e030a0e010f1d03010b0d08032e15270306050a0b010519050d090b042003101e0c0e03120309030409020313050a050708190c0b0c0f06040c 61
    0x30350301010045040015500c0300c0d42011400c010403040d115400228036010301c80c0d00261001400480c201c0c52481c042621342104113001d0f503458030004104001003112201440e101c0708030b0605d101e4200c40074840341800c265680145840e0008949083c1800351080d0540f0341ca00c1048841c0104411912080018182d42c91201b1511942060000780040c1d4052240420700038042c1c40740e91400c6040200810503e441e04103040c140202408060f9698205219071260a0b20450207192030703080ca42441c01c118410007100600d10703504000300b2070781a10301241c03410040c1c0340000041100d504400c0c02807601002501003c070700c5480c1481c648002a44801c075102022826000c1c1c03040006980562035040c401100c01041d56401044100b241000543c02183d100c044074403400300d42c05030f981e5280e003050000b440030b84503a40465006e1000300b1062007a10500000a00c009520300c01d6513840214040c2d540c490032800c6400070404035650381c0c082c0f250503003806082041d510710f4901450040f07100103450 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 734563624 1250 734562374 734562377
    0x609061d0c031614061308070303030501031505160e0a080610140108040c0b07030306090e3313050708070303120f0614090712090c180507080c0307021e030a 69
    0x180e030b42c8078007940c020b0754201910980310303207504d0541e8980248a501c0d80048001a0600040f91000456660a100050146110341e0300410a9490740c109840d00150755030111106916040c1409840480b5400c03100d002d43d00b03401d10410180f0a03400248041505034084091402403c041040e1105554411003d40f51032130315415444188500468103031608440c01000b54181d8a0180815002100078281841c403074540810042c1d12040306d401511160003c401455126203164000c545445841b00c3c2e04400700b60b0568115440c004802017681e4020340407041c1e42c070031121400140b0200348503038400703008850121252a69203180050180c100d1203414040e803880c21441d0b111401f5030f8040da0040322080202621038544010410001010244c0a40b051080381c00301d400c0b4103000c40c00703002c01c081c1c054050100e01c03d19100400540c69070700c000d10040c15281008020115420040700ba81000c11000f449840c4d503110041a454403800c10680c2001e110000c180e010402000801000760b10502d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 734564874 1250 734563624 734563633
    0x105090f0105071407080412060b120613080c03040503010e07080d02070323101e06140603040305030702160f05010224130305090a06050a1d0d0609061d0c03 69
    0x80c1051422658107070341120000da81206080c40240d1120082c100450244015500c2c10b50348038843c84154a407958208c03500c1d62142c0413808513180ca810030102d03840328400036002916261448801000000d58000c16043c4042a460820a01082614003814019008000d00ba515150303041d42e40f40710380700d0360006100b40b2943d030035002c0c40454a413045a50000b46040380200300d0328407040c007800581d50806148110050010781011502036414044810341c0c4200e4103941030503811083d1000340e082001c3e091200f28022490b074075540202c03a8400e8052500329200d8854660481c2080031220700b1110120403100c010805c401071207802d03400c80f50241c0894810428030031002c9024007501d0902c5081e07401e00000034020b03006030241940124030901d03204d41f0303207031807100064080e016035046403000030b8001c210f03480c105030400005181401c142d4404070307084560000282c0b500d40d00340310082c082500c881c081820080150000700c28030340c1e5005040000d4454240c0c0645c1d03a2070094441e80f20380716 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 734566124 1250 734564874 734564893
    0x151203050c160303020d0c1115041a03010305030d090c030b09010614030f0705010e01020c03011410050612281e05100807050907051b010209040f06080316060e0f010509 74
    0xb850a051002c4070340c543c01034600c075200107100361094050b604066560b08803c07041030045960b190040c903080c0303800004264a903400c0c4041480682110038510700743d400100010301c08600700105030f9404c14607982c800310301c20031b151910084505099000822403815281884034500d41904104180d4044918002211700c600041603903035103c000752000345801246080c0402e501c9203180312034000040c01150002c00398840420308460810b481c03010b214042038240054142c2016400c0010501100c4450404001c0c0041e170303560f400098030300c0003503c40110a220078220311070302c0803843c07c0b00c0c0b00c000c12125682160140170301c031201417604080d03031a00d0700241e1040000c90004007511112002840c100e070500c000d00c41c0c20200642440700340b1105002c4440100014072224030000c0d454000036840b00800070a000965080b000042d49040c14240f00340019070f400000d850f1518000e194081c5070380e006040200c002c083c48400c0b8842c034083d044a0340404c05054100a000e000c815088821144 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 734567374 1250 734566124 734566153
    0x16030f18080a02120717011b1d040e0c061803060c0f0a08071b06020c06071404060e15220518130311060a020406081321260a150612151203050c 63
    0x50140c3e906407105161807070f901e8a401d1a41c0b15092088800041b28cc181035200f0000d503464210594000d0510444440007003107040c2400711a03004041100c5490500406d00480041c8d80640207ca0040140c9140084c03440e03480303802a00905400b83d2011020280341d030900a0113544036001c08602c3d031080001240041e8840ca1903102602d0b240c608003030519051103c211810300c225280c40780e000c03098000843d00348842e8002403c103221407054015a0395040d1544a030a80f100e0350010b4071940250080c1c150a01885907907a6000d440074aa4100b0f502003840c00f5a07030a0b800c0543e4441c50310441c0c04010600d50194028000e840e40742e12030510707a0345e80c98070400c03600844110040084000043c0802c1034031814203100500c0c4498100b07180c400421106180c2c11480104121500440f00e800740700c0444414802c3c40c08051180f9198440981030400c0681051404190201c4035642c800110080003e200402005042605280102d01d9100e08000700242c004c0c0042d0012402454070b0740c504034 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 734568624 1250 734567374 734567387
    0xc03021009031a010b0d200d09020a08010c050403021c170a0306080a05070e072109020906060c1b01030906110d1401030312050c16030f18080a02120717011b 69
    0x85d4030754031080b4581a1213030703407550141c00fa0781868802e078942d103e002c0b0301810600f00034049401c981c010010b0981e00c07500403c4464001680554088d9240100110400703a0140c111425250141d44588a103034441681803a1052140d1020341614218040e6002c02c0184030020112000b056505100c800e40300c42d10140c640d00c4211009102e0390002c1020090041c0c0c80b1621513019003203050068003011140c1401d440c12290343d14156100780d8502c070210440c030341990400c0d0004416135074203003008540643d540e999090001101076240341086d1314109070384280c0002d62416030103d82400028034403403085010780c202c07625441005e4103003010000c01c0c0380c02074031450490750141e88054504d590079030f444005110240110020003010001050b8105c440815242200d10a581346290344114440091075544010f80c8800c108514403010424014001a00360029404690b003002401000d1130355850701d207256202021600110346c1c440e5580c0010743c4032343d088150001500510321481c90088421 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 734569874 1250 734568624 734568629
    0x301060b040e1506091c0510060302030d120b061b0706140a180b070f0b0a050c0403110406030605090601080d181203030905120c0f03250c03021009031a01 68
    0xa2442c080005903100ca0a0405400054000c0c1c071545c07528215001040d00b036040d000714501c0c030310038460450303040290070000f41c90000440e400c20002c080c1154006503d6107400d222078004c000c4020580303054444143d1241c15100d100508650b0f0700c050000c1c1c58001c5a0315a141c416aa000e18080001e009015464081da001d0349038144a103056160700c0280c814450300d0440c000c21904034070380403178800400002412501d0186c0c0500d0913a00491800100c2110000c200325911402c00040c8070395442d40c441554150380e030000304d00340c560b400d440104004007460b503c082c010030309103018464007000100320036050310741000c151503040c14400410f0b500510200c106020442044404025070000e14000800381842403a000c210704c04ca40c1c40c1d0300c0c42c1114060405120110010316840c1840d01000039100302c0d20310304065400c0a190003070050301007048500050740290007031241000c07c0442c08030710b0059540100120020701180350010b260708510b0204440340a2183c5100940e009000d003001d04 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 734571124 1250 734569874 734569889
    0x1806061211090d0f12030509160303020d030b0d020904030801061101020a0e0108131403090f01140d020304050304030f05060a0605190b0d0b060706021207050301140d0309051e0301060b04 82
    0xb40610060500000003200001500c5980c03c10b11104001030300904642d0210440d5980032035103082021f8990304051a512601d15142c41506041002a4001c61040e030140101c0c00d0004070a20707280c010071201500004001d500139040801c01040640094803d4182d5140381d0f1900e05a041d0403500381d00300d00c60403140c039021524901c10b480d003a620034542c0301d60209840c04442c0441c05680d41d9500031441441c3e030141290004a48420706085c030140d0000b00c941c003480c00b03d0f260442420241c1c0740303128188410301400d80010000b814032100b041150b005550005581c40220b00e14100b8544520056900c101d503d130800d400003985283c46680d0103819481ea581e500b01c014030301001d80003180c1c01280718003503954503080e030130030b055484c50301401e00c142c020440940d030307034501e4849003c21840041261091100a10040c0308001c030003040718905060650b1564447d0b1480c0c1400e4520003075541c0720a038041700e080380500d0090001413606d52440c000303500a202c0b40c1e80b90361507032203113002c0c9005290 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 734572374 1250 734571124 734571127
    0x110a02010c091409060d080c0d11071a0304030212040303170609090d08040204060f060504080601080105011a0a03020d05010b0d14160503060d050d23040302060d05101806061211 78
    0x80c1131030690981034000c03d000f412032140714015900e50030550080100800c3c1a0032614070070140303a41140b0440000c40b0342a014060040c144401d883c4840b00303411407955081d10120014040500800c80b0b2200603044c02c9281d522103a0b01c2c0303402082c90300764214403c0078074403000100701c583c02c000c41a103026590540103050605c0c21102c0c00c4900c0c050040050707034803580303460001070150281c235405c0700944887d55400d03655500744909589040b0040e400510280c5c94000104602d1045040c20740382d50399240b030160790301d0081d0002103020740605401e401c50a4a080c000144030303040350b00140101840014184581c00501040c807515a00403600c102886202d043d803600d07154860401554001e0b0b00400c44041a1a1038880900e490440c01e4900d000c129240c502c4540d00d100c00310700d04811480364030110714043c02e550200c0d000e8002d401450b180151500007250419032041b400c0301c094020015409086841c4034160300240650744191408070703e803160141e86080b074600450960000707618189 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 734573624 1250 734572374 734572409
    0x60b0a05180a0510021e0c0f09190203010b03010510020601030203060a110d02030408091c031e051c1508070f05060f07060e0706140a0f0e030304050301110a02010c09 73
    0x81c8421100d411481d903000056400c00705990780c2d0a401c8095074055640207106120119012082d1880c0c40442540300703900144c261242541c4070381c20400041d2040d5100907868544282d2090b00c0b890080e110a1170a00120002c00d010341290041c50494208950020300e030380030342200340d840301004c0c0400784d010340004002030300340007c640024000d0080808101c1ca05106078802404a82094404903001c103c0024040490701c1c1484125851000608201c40d4030340d000d03a406815211902c009100c0a100300c5842c200103402142503503400040c003041101400f0402021034001e000e5038092001c8020b2646011070310b00c200040e03000a07900303a1807014581500b040e08014590300144000600402c003000640001490f80c000d5a03144d0200d00000e0007110304018015000f500c1c0000e04601c0a00c0a1081404455002a8042040c591801d00841d01c1d4030040201e41980305941210b5090740c01d004100142030400002000d07e000c841e4020440a091400c040b603000d600b40c420803480440030b5004 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 734574874 1250 734573624 734573647
    0x270c060516050708030702240a0e0a030b07090510140412171612140d0b040e030406170a050417160f0b060f0609010903060b0d0206120a060b0a05 64
    0x701100803540c002100e02031540d96600d890032805030080411a080800e180c011410804501d49260040c400354219500c400541d4060324080c02032007000b00290311042079040c0d15116040d2001d0341c3c1080c030f4541c2d14904844081c04200c65846603500a0000c40d080e07602052041c035501c1e1803060b019600d90b02c1c013842e02c200d4a44c1d11500c41c4050311143c0c81d80c1c826400750741c0307444021301e43c41c03801000038400c4801501b400c0c2011034040c210041030007192820f4101000000044608041e0801c0300081d4454600d000f0800500079140501043d1000050125105800c03105a44440801c0d411a0742035541e801c030180280d400c29030700280711003014121002c051248001a018295800701c007e603149100d504c0301103030707144010401c0d200504080d0501c0124148035010b44040342d0150360403031403c49418002000204940702c040c140f07660b80d0341102c1c419900d8a8204102c603400910258a903519044000c0100905407851544d05183c4000007510707014081c26109403c10ba0b40b1024203001c0081103 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 734576124 1250 734574874 734574877
    0x160b060303041512061d0115020102030c070602070510020c250e0c0c030906280305040809060901020307050607170f060315090f010e060108150f0c07170301060201270c0605 76
    0x4400c0ba541d103a64000c6801d001b503080c0a003240340c141070071b40704a51504d403140c00048080101c04085900400c10019188103580844900399400100141d0301c0352541001c2d414400c2c4e030308043c400b20b400002c0311440303040001005558211580e07284422048603608007618802648a03014402030740500040030401110040c145007070700c0300709a0b460050030500092442c1d221220f005422a10103880f4001054400c0e00084540c01900303081101d03050645400085020b0306400a108910001d600da034264400d0094400b090390010443c1c3c110700700007001411240d141c094800d0344158840c0007074a2140203d04441c003d103006009420f20098114038200151170003410a0100d1050502c622403006091250304402e0320400f020f80780c2075040c1451582007440c0c000c040346c00d100c005018445030107c2040110b0304000042c0c0040d5031011107280ca03004158a058503c107000402100020b100e0f0780640010300b811110900d40300403214203c880d040b500c4401d0034050300c0c20020705001c3c040b1500640 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 734577374 1250 734576124 734576147
    0x14100b09061303240b150a110703140c0a181802030f0115150918091a0106020c060703020a030e0a12061b020109021e06070602160b0603030415 63
    0x4141d0361030b0a9080c58070105034031031603000300c608442a051001900850620361300c06030303124410078003001c40c0d50307400106003650800719401c400750006010f65055018107002032a019030300050f81c402550f80c0c1050110302c012114508464080c100382e140d600d00c0e0200c2e102c02903032042c8114011500d1384941d00c1c8000c0c03241d0074080002c001a480e01101594041140c810520713400302c00860541c0c103190b01a00c0b41c240030351000c181d4041d07036030000800681001c10030083c0d60000019a0302d50900100800c0039006000f0007030070442d103c02940c8240e00d000103042d03043e908980c0071034503160b40440034002c42d031240c1c0a004d0700580019141e40c0000e4031929001050340f1b0018601c907101c0e511003209040210640c28102c1740c1c56952039950f4045200c0002c18181000d042c0000c00c4481040e0f0081103000103c00c010304403c010703021014100b95207281c140c90110b40c00032002c41d2948a42c503010200b00c40d8908c030170b50761407242c003000034214913001003110705840004409010740d40c21404242ea4401003070 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 734578624 1250 734577374 734577379
    0x106060e151e19021b0f06032e0303230f0c0c12030a031a03060c030a022b0b2e170a060326090f01120504030e0414100b09 54
    0x2804000503a840000500f4142a10072030301c481c44400d804010b4034005a18441841d16080d0348184103181e61880451540c11505490603a0349542d036001c0d901015400e01440b8101110040d00525190700807015503094030321035250402d0f211600080170010341e03c1e8900d002e038003031010070005039155040383c05404440300c210300f1a6408404a40010891100011105260352011402c4200f0310740c07500580c180455100c0d21030a2402e05030000c01d890710720041c028868904c000000c9460400c9550454104600004144c000a03030102c08802c3c0b4420101000050a03042c580074a40030f20b40695001200c06607401c0224101644601200e4580031613000081801188034039045079180c11800179124141740440003c0d5181985000c084800e200120060020f444920440580040c8070454903245000c882c0f10b605d400ca1900105d440e52282c02c25801c00500308002d110425404c040703000c15010040310103103d14100d07554050410038045032240e04520709c4030b104203c1d103602100144004c4401 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 734579874 1250 734578624 734578657
    0x1712070e0609090106180e0405060609100b131716140406030804080f010e3009060a110d0203070201051e0903070e0417070210180801110304050106060e15 68
    0x1510001c1c120340426800381740480c1d8200000d080d000d50110300070000d010807060310b00050405448850b42d640c00185018014920f4201042090201840c007038018146c140b40c0d50750700c0c6030301c000041240d1003500c03034000d091a9204a003c0c50007004225150620005414855828600810308400c0342200034100d40082d0f42c0c1d480400458542d4008101a00038180100905c4c0824410300342103c20b21158020550001c0801070798407081002e440c5442945000d802c000340d00500e180c3d44452156007011907010b0b200045554450f60401507401c0b0000051003520312410001006980300d01c64018000d00255080222101809034049007001c410000c0d03d030310f41000c4203100030900e484d40c17580003489004d8071101004100204403c0502e006e064079004079090000c9603000c5941032150003496024481d8402c05080c01c01c0c060300c1204010b003001e4000740b01c1e4815442c0460f0391580306940a807015421315401082040c02004c0440e02c220740500b45440707405600d02001102c0d00444283e500786000c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 734581124 1250 734579874 734579887
    0x2e0501080303070f050d0204032d0c120816151401050a21050a050610060e090a02031801020406200102180108040609021e040b040506092e0b071712070e06 68
    0x41e8802350000d9803140c41c091803102c00040c4000364102c0108410280d481d461034000000420b10181d900459080d0b0000d0341c201c40d2149480c2495020341d0304103101c802e0b101c02079002800800d4040b52080d4000c820200075171555031011680c4010240140b0f070708102155005c000c030b0550080710510b03500c008241d0400540c12981c445041075180d8209580c15401141071010022261000c2c0f001030105050501c00781d095900072072201180106461201035000c00018100b81009808840700709007c4000c55896032108005000858070386031016070000529501e1403011014803c5075490341191420310303100b4805000441e41c4481c002c0045800c01d03110001303040103849000b04c0241e540c50482404419400e44000d004c102c2e0103c00c44c042c071a600300000e00031107444009282d80c000318105002452142580b0380640e038561001202c1e06060100b0b040010b00e00880d034040c28940c0c3c8903c040044288100d00075000328010380440c224104451004121094024401d040c190600507200c141000e2 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 734582374 1250 734581124 734581147
    0xa1515052802070602071707150203091305220b1305030712050a2a1e1505010e0c0a02061f0905070c05010f0e030403170c2e0501080303070f05 63
    0x8041514507070150b4007500003880716035014420075014140e03540c07114003c1d502d031100300ca83d204440e224100040c49030030100d1181c1c0b0720074404c881600c0c40151035030310b80720082031044d07000304011a201c0008401c0007580b00180c94507004003104507900040600305d00e85821000e0403514054400440d1103120400001c80041c00d0111280048105d60700c0322512120842c8003d040056100d034107011000c25902c0c8074417034000c01042203580c00e2b0828220070a004410709400c1c03810729025405040344030800300d0f00b0501080c64003d181a900008800b52842c0ca600c05400808d0080009070b50268114000064a40b03404888a02e11003d070f11070403d1806903900d0301c2c40100c40041c1c3e1900000368840c0c503103c0c1888024080c411080181480c1004940300300200c082e1203001d10300000303110740903024001d040302d8641001c2d01c5003c040704040d0344144008003030714003042a44031460b04010480c0c101f84100d900591050358101c1c0c0542c4055451640c820400320380041d21507000c203050000030b008444010 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 734583624 1250 734582374 734582437
    0x207020d060c030c1b030f02030c12030a060f03050a0b150409030201090b1810090c032a050603010513020c0106030b100503010614030d050c10050a050a151505 70
    0x11801444002800540e02c00c2c0142a00c200c1c1516400784003008071402a091000d40c0c40045d203680500c0c20701c20320740b10800128298071a0740908001841100580c44e013000c12440154020840e03402c003001496903c0341250b000042520014144c0d0708680c090801003058170f0760b0254001940740c00012100b6040b0002001c81e00b0302c00003900140e41d03441006c0300f003101080440da0421300a000154501d048443c5840c0c2d64003000c5c0764911019260100842006282001e00700a140d0024440b0b80b5180e85100602c0c2c011429a0402800001c94100084509205080f01c2c1609d001400d08248070b402c110418000c0d500c00d18562107a0b66981341d000022418841d070442c0540403503807107a49013078035110816003503a00d1501300c00452514440e1504c0709950000c0c1e811103c4105041081c0c84a10740020241800d4a8060307414440b4103240422602660340d5010506c80e211050302008603101190840500b00a0303400b8100c1ca84405d030710416081800f846c00b034006070302e40040f2640c00c4643c06c88e03240c900 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 734584874 1250 734583624 734583649
    0x120f0504030623090105040c0519080106090203191406060f19210b0307170a0602030a1d0a030c081b25080a0803060103020a030f020a0c0326040b0901020702 69
    0x2004011410840001c0800f1200f0340180d04280240000d0405849003403840400d803250034401c0981112203458542207183c4a0010b0001c00000c02030f940e030f221003031800780d80201c82c012005003420724108001b400c0e9108445030b001884800549075541c000c1840b03142d030703c40b0001040780e0409100302c03030810000c400c14441131040e59940c4848027440503000c428040003480004079482c1840e00722011a200001c1610499101040300100180321605031030904030203810182585000004000940c0c9058004042d0340801c41c2502d012010b12040380b54a9004c5c2c0070000b000681000144030210705100054a00607150010000003140030075440d629040c004d0803c2c00c086048511201035445c1e0a0400d41d00815000000d0110001543d684812901c0020441e0307040c190301041254445201c0d074000200f16800703280c1155a4052030304041c1075250f04000840006102d15150031014182d035440c0d9021020704000c2240c1511141d45402040320000d000810790366080c485000581e0f05c0e41c408440 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 734586124 1250 734584874 734584901
    0x110403021306050301051012150b090f0708060a0e0a1e020a020109060609181b050a080303040501110f251b091a100c050703080f18030703120f05040306 67
    0x30030b6840d00c421306003552001400062159404142004101800c41480d0455940b01c1202540c030f40c19052140000c0016840340380c0c011340d2070020003c086800d40c80050003050a5250708240340d03a410100400e41c5031500507019640d00742070116001c481c103500070001c240141d842c080042c01d00b180c0074000300e030030a05282c0300503919188840281b00c8a80302d02009031a41090511480d40001400700c4422481c450041180f44c8490805440d240403450304009020028161036525643d800d00750754903002500c0c103031082d520f08410200102c410004560503929109025424010481d44044c02d881c06d00b82d09600340040d41081f000000c0584555440c1201c014540307041c51130038a207520301141c40d111100800f140380240c0c2081c5a64036802444c3e02401545404a40d660f054a441030400c40107a000400a40d004946944200406405070028000c5082008280b440e14400c040ea02c814510002d418890072201c0020740303e229000480300c010007030130302c03500c0c0070795039500c103030483c0d0005601d840c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 734587374 1250 734586124 734586131
    0x32030c040e090c030c011d1906120e0c1201110c0601170f070515190305070f0207050d0305030405070b0c1b01030c1409121e010c020f030403061104030213 68
    0x204110201a8003030b00490884014103000036210086680c40580c0c0141505100c00c201c01c90252114210180c3c800c0c0f04007130086036141090181005140c11a0b009034400f00312040d920707485004c818410030031075503220402805581c0301078041c8410000050703544001c035500c468152070110305183c0200007504402008148640c58100608000d05100c82440e4198221100d60000a10006482070a84004440e04601120000c00104d0315214440c0b00ba50001c00c1e2003002d0141d6a0198443c41c071510140c0c69001520f411484100c1c0c44608030300800f41e10101003030780d04002c64402c82c0915400b42c030500440e084541c0b252081c100c0d642110f16961000c0e032141c282d610300401c080d25401032600003800c0900542e100c042c400382000c031100c40d0700c5109140115810000790350b1a0703601c040507450101030711302c44c43d01c00f4019240700220b00310445c010342c20441c1c4418100c1c40046d100c0d103640004009107040c681540d940030090000b4440440704118240000700140e40d941d10207814002c003514001 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 734588624 1250 734587374 734587379
    0x150e0402010e010207060801270e010902130e0303010e0928021e03030910180b0904060614070f0f080a050703021e0a061e1409010e030a32030c04 64
    0x424082d44403005a0441d000507508100158000c40d0385815150710000e010704000500007000c500c16080b80840b0802414408401e2482c0d0044d48a00b07100e60090b205007249a8203440c2c1d80050354030146e02d5035010b500401c0100b000b1000b4042c001d4011498109494031141c44e582003101d42c1c082046011300445401040c8030031480d1401060f03000249030610031021400c1c03c80000c0c2c40f4020000300385e0140c0100310004080c0d521400354100801100b007894540c55407078460103030568100b100e29502552610201040490080d20f61649200700c441e0054903251055030707080500c032807500c42110300300e03803085d007140000b60120041d002140443d43d8103600c507081404c00030720302071081900c07048141e4145410301c4008000301c2d401d10020740100020074841404120a003207002001c80d442c0c09985480380f60428050200703031040c006d0341044001d0168070703083c03005d6607124814208000045101150308000004001c40c1c41c00c200040050998000405040c420405030300484807114075a00001d001e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 734589874 1250 734588624 734588627
    0x1906110105090109231002030a06180902060f1308011b1706131e021306080f060616030e03010f02030601110a080409050c2502010e1f080a150e040201 66
    0x280740e0710058520013031080040719140c500940c1410380030b403031540104c0d011000141300d00b0460385144802c4014215520702d4a03200c1c0358002c0c00a4040d0205904400358090075075841d038023400d80340725001002c080c40d1811503d1000c40941c44907041c070a90212007003000035a2a800c1c4a010400400c000c070b480c1ca10003c0c4680100301d8100141100302c090115410312155844000740140341b00c200341c0d00000c1c4180c0005100900e0b890401803c1c1c1c0460002410001c21100c0c1c01c183d10455010b501c4020706522010700c250200c2070101e440903000401444620001c00030481600a081e02a0070940020308184000c20f0a440c00e980103807000c60740003c18803503156405074500c03d0f83e0b071707149010301b0181c4015910040c59104038803c2600460700c60011030701c3e00d4990b8007141d078010040b80882040308160016032821a520540c241d0100e09280341408460030159900549001c540c0d50f0f072000000000000d0383d15034009800d00109030354441e049049078000010400140c521844907040500d4070380f00 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 734591124 1250 734589874 734589881
    0x6150f150c0d12020a0906030e0c0a180e0f03031504020c0624030706050f30270309191e0510020c1e010203070f03050d0c02030406020d0e19061101 65
    0x30a007003e4030402c0b101c07100706d900159860030fa81451401185114024404c249484e4401c0c1c0c0c41a40041e03c03003000142841a4400310098441240c400e000158035003140c241c503240518075070714482e0410000541040342010003001035550040c4014100700c1380f00c7e040d9241a404030b07444031601d500c142c0503d1000f4011880915180401c40082c6141d50600d10000d10500451011000c490f80100b00c0d001a20b5040151501001881d520003845852001034003103010710545660701e4a90001d940b1506034a0740d401c0701c241008004000b035151009540c18001031301040020303c4200b04d4220404101c20084881c9003079030302450700e42c0000b500d04140411005040414410081d580054410080742d11800541d105124035907003664406c600280041c2d085204147c801095641c90003241401c040d0800d014040424050030304000100e92420240d030740f0702c43c80c0106000340e4002d400c1c80a809200320103e52102401903c2d0100700c0c29040c00b9081c080900750042c0e00855080d505c20b28180000340f0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 734592374 1250 734591124 734591147
    0x16180e071d03060709170309040c0203360105130b0a0c031b020f09070c02060a08040b0f0402150c010f0606030605011701030803180c030703140c010206150f150c0d 72
    0x4000d0300c244d040a10f000360440c0c55600c00c00084144501241515000506c00c1d50f5240002400c144080f0f402000025180d40c01b0074840401e000c995004818101d0400700d0084980d0071003a25908019072040055a00c0d42140440041c6a92056004a0850320b03000c0070f00100700b15034035244824049854003511410f4110013000e070780e00c124401007025a07103614200074038150a44404005844c0c1c0c0004464980a8000c00794000000141802500e0360124480388914020054001161101070301e40f0811242a10041e5102425508841c10b401002004005080c5880000074010b461040d5a00c19200035a0110002c0b079503922040081c2c0d6085203252103179803031802e44c0c009190704540c0e0f01d013a5800702500881013114004000d20381948100003241803560000d04071a40c040c0ea91600d0002185803c2c055603150241042141309940002505401280e008100c001a90960001d210341400c0052009a001000c2001d42030642c5018001308400025580074010302c620006002d8000c90412 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 734593624 1250 734592374 734592379
    0x903011e1a1e19030308010302091501210b0d0b04171905071e0f1218120206090901080d030b0616060908040810020306120616180e071d 60
    0x82400d54540d44580422811500789003203900107111a50103d2480c84500c120040030344603040002c005d040e005403640d03048074402c480124450795445011100c000c028a8418003007518007a000b4042001c4140c065120200ba40c0001110880200003c2044414400c240c9100c0703080800e00050054064038105024004900b241c604203141d909c800040c2e1010a0260410101007901410041c950090b071041c0340360304244042c01080c0b802c0119002d04514070403529640e0311042c20900f2130156050807500f201e82200310314500e24140450305146036500b022607000d0005c1140a1a503520301031200d0103026540000c4c072008002e11400b40440d42240d101c40d204600078010050603110b50a591884598081004503441181c1c0c46e0060b002d010329089081140a46440c1c03400c416103d44c0a14414001262405800094003804580310101541d10001d40c000588480310f00c40c5c003826500a030ba90314128030075505a618203000c0074808003038600c1c0000540407601124540e00740746c0280304c0400304 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 734594874 1250 734593624 734593661
    0xa060207061404082b0c1e09050a05060705010603240b060306090c0a09080304080a0204050f0408190c1208180d0f0e04022503081e15060903011e 64
    0x50302c820002e0302903170380200a00a5208010800840303e10904202c0c4403102d01d05209400c0c6510002d084281c20b1a040e03010b195180c50483c8110344070b040d0380c00c22258090b169072120390422041c0503c680c002c0405880c07d640f00c2d840080004c000d292210317100c0f4801c2c0b07140310f43c041c501c0601c10142c84410108071f21480c018000c1c88003c1d40d0b0240c0042e0000d80d0018400e03640c441c43d0b001601c11400c55441154240000b20f0009400700e0040340a038a054400c80f010891559071040b00a1010350542c3d010b04516030612810064140321082c81d04220404c0c02d20140a02c847e40d190b4103007039103014111001860300d1050003100d81000030501d9000074200007030f00b5003214518000300310001811522040080410344920303c0d4469904a80c411100500500d0440c8081c0c424a0001703992140118000f03098100041d40d19035600c81f507101184070400410800d81c46801c0700080d103181c403102896010400704000401960244501c45020583d000605c0030000c1401c0701c2002c6928910b00c288030f8081c0b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 734596124 1250 734594874 734594881
    0x150203070503070302070f0c0e01090b09151c1415061c0303050c040e040830040b06040e03120402031018080f0417010b0312040e070e03010e0a0602070614 68
    0x1c101080c2c0340d00c9501482c0c010780301c00503401c01d030610064282e8084d00c1d08089440c040398140c04688028143d42c2044418419004442d040c8401c0c40011600303c2c014502114051896184c200f85400300c0c0703403450301d070010a428142c841a940141354901c0c50350a5200c040e116032035010541c2490740c4100101c2d41c0180f410350304008008007080e9100b00a0070159103500055024066005507000380004886480c25864180380c080c800ea03105103803d00c6507109102001400250050408640100c0381000b98800d8486039104802180081e01a5a109032101038003e10300c0c40030806401101080800c40348903040038018182040c41e08040c581c80c56091032454a40000500c12907600b0503070100306290380d0012840c0f0101c1a0095400052004036140800e490300401500880a204d1003101a640700404c0000291414807503441015500c01e49400000c100d14014006200150710150010501a0b11402c00c581072100c000002c03280107a000c1058401d10685106501c8000c400d10103490740c4c2e05 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 734597374 1250 734596124 734596127
    0xc0405060d110a12081b0d0f1d060c1c03110912010b03011803090504050103030f0c03140a0203040303110303010f0b0d0f05151801061d06071a010315020307 69
    0x20310000c070182c0b40c40044020b2401e5903c2e14510310b4000d101014030040280c8803460008810b6218400400602c0341c801da5849030082c000c11500510071392916003081c034203030150003500c00c2c003902400c2c24004111030002c3e00f410f4643d403004059188004000e840039150000886603042c01c83d038001030400d4600035480d13136100307441e00450b1039000c82111695110125241064050038402d0b2100350103502b003e09480c1e0303900f500c030100030320148207494056040c1d07181c00c2032000302c0700240b0000d0001041d01d01c50300c052038010900b09880c1d901903d04500441c2d090480c08030359922032000c10b0010b0348002000c10506501c1003040c09101d5828010b10314652501d224400c03900c8090141b01d00201d00040c0420050103560b10401000c070b500c5005000b01d28007144c0c40c081c50307149460058041d00c0c0e018020f04140503d032401c18142e1b1010b482d43c5111407a540b0460f0049112240c0c500d0700410b003001140b01280141d440b1a01d19400340d51111003035811031401e030b07040c108481c0d50b145415005000340300d440ca = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 734598624 1250 734597374 734597389
    0x50d080a0f0f1b06060306090b060a06030509071203050d0e100e0a0c0911071a0a050f040b071b0b0f1501020604080301091a04020a020a03020610050d060f020f0a020106080c040506 79
    0x44514500f880400c4041e0a1050040515600c010b0130b05140104013810013200d44101e0384190310494a88801d83e540e40825826150100c92044450700540802d010079906680070610080c007070f1400a0030001c103203501004454003c0e01c1c00c45580c4c0b10000310a12102c0038041c4515440050001d451514002da03a03100c19501c0c41e00540c00100c1e140c9500b4140d108960095541e42600100c10060592581c2e840b202c0c01103003a10807144090a010019108101d6184600c0c0100c0d031200f001c502a035075101c812918081080c0388078600440c2a103021010034051542c050148608c988058241e00304900030b4202041101ca001d410740d0061000c03c8007003642e140aa1781160892000414084048400d80031481000324107143c3c01031010a801f8a80c40e40092590f50882c420f4089401c6520342c1d04c0c400c031103030301c0380e1050340d50140c15100b48400150b090b810030720000808a1000d07051400c03003420304d03500c0e4205019050051307560304030802001004000080d01d03034800355410001e6081500110361031 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 734599874 1250 734598624 734598647
    0x1d0a030804090c0e06040608040b060a21081314120708030418060902040303270506040512030408060103120215070c02010f0c0803070302041d130308040c050d080a0f0f 74
    0x3034942d283c101c1c261450040c070880184420042c402a5202e0311a0740103070a40d80e00b1b950681c2c1e491201c1c0f002903000e0034040c12400c240c41000409a403c3c0d03500c00c001400c2800f007003504440c2014140b10041008040100c400081c0000551001078039821205111408585800130782c0760390f04c0002c080003440d80110854040da901803028060f00b4104e01401d201410740c0c0c0e4021100a03100060001c18140d120440400084085240d400e0804040c400c2c0701510f0742a009682d4480c0d400c00c020010303450628900380010b1a070710182c1c2c0c02c240d42d4894550405070242c0c07040d1420340c8000040340143d54184000c0f00b244101ca402d000c82d0381012000241a0344590000a05000c0f0441181000da0f02408a9282c2e540c0d00401640d520310344014000d0281d000361151220342c040a01040e1800400020418070407102d0440035842140c264808584500000e8416603424000d1000400c0c42c1e03e6085041c0b07203117130042280680e1a5941c03030000307202c20702800b0003008124141801550059000050a41 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 734601124 1250 734599874 734599889
    0x40206250503030c040504180c090b010309020907110609010204150c1a090106080c22090f060c2a1a091515041104030c030602030411030d1d0a030804 66
    0x540340d504010304040408510000d00544004010091030003240740c001c20681c1c10681d0180180c100d50784821058101d0320000400b242c0c0881e20912030818079900c080c0b8411014500400c1e00d12068011840d14101518280c001a07203001035070b01c10038010000c240c0c00840b017800841c039013072a002c0703404001c1d0b007600f0b014400c1002610104061122805444c100e0303980790341910781d940c00d100c90494000c02c1c0c1032007540014011000c01e04510318142c5c1310b454075540f1081810110003201c0107188010030b0340c0c2808803604125000c0100c08101d0b28032900c26803041c15201c51110041d003144925075020020f00c01540300c810803e0400c00980b0740100783c040c041d2030880c00303a515114418100d042c407c43c207000e0b9440a51003420402d4500302c11100756034482040c1c60800030b00e074a40b800a0400e120b540009004407040308010000601e0f10b5004541c440c0c02800c081610740d4841001a04082101100c9800159800c1c088100d0504000035a20004012101e0b107000a1940c0c1d111100c900451284d8071 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 734602374 1250 734601124 734601157
    0x11e0501120912080615070b0f1f0803091309030c06090206090409031206090b10111504080705010b04020414010c0c0e0408070c0803071e03093506040206 68
    0x84220580c102e0103946a01440d80c11030700910001c001d10304081260000d210320354003040040c0b84110241194102ca800c8030b181c050310796075000001c4100c40003800071042c0300d40c025503c0f10010010010603010304160005142d0751103d580804c01502d00100c15041d99030314003400c400c0000d80221090b003c0c07607070000000c142c14a040c0002402c60103145500358005061000304400c0603400403c1c3c00c18660703210405c000b401e45a1070182c0460fa072842c4402e0308080140101110180034090848102e882401150021401c00117000c500400035038088a08050105035501000020302890801d00025907045003483d2822a0800f000f00d004d52050b41407143d80c2e04040e051007143c900b40b0001c2c240d140407a00040c02c05140c0034200b03500c41c0c03e044e035880d01c40c50404035072018084100c03802d542d04120080c0461a4422803000311120310301d012418098034010004160441c441e01c2c0b0410b00e0362419207582c031036028211903c2d60341182c81c1550300350007050070040166264000d13200003440d0052504c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 734603624 1250 734602374 734602397
    0x9081b04050601170106020a0201020105240d050a15050103050f06150411070618050609010c0c170d15140604030f060e190b0711061303030203090109080f030103050105011e0501 78
    0x41c1c603280800074100c0d961004ca0300020606a800040421425100f0b900070082d66407600c810001141d1035011031460b00c10342c1085049285004d035003600940c0e0040050740d024403103540d1004211031184e03809940d0240c88000400030711000307002100f561120a80074055900d041280000b01c1440a502c140c0b05d195904e440074503441c001e1041d80d1650342d00007801c22100b04031100164a400500104039254440c14000540003003041c0602c8001002c140c9642942035800e80d11444c140d0740340d038032400401c0407e012200000c4820b004040400320944036507503145043c02e0103811307070111004096010702c00c100700420020700c540c020040c560390000cd001036681c2c060300c05642040c640a17520140307500121541400e000200c09054024032164032501501d0341055201c80d03c6e400e08491780c6107202c104100032004a40240c00a55101c480b00340006209602070381c840da4907401c9842c4501880714080014170030408248a16409070240030101425011500591114041e950064504100c40741021 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 734604874 1250 734603624 734603627
    0x2011e0210020d151805060d0b07080703090b10060f11061536220b060f0d0b101a0f07033f05090318120d02030a09081b04050601 57
    0x114040d061a8154032159910015000114180c4103024501713840c20b004030714180f40c84c0200040b40c560020308800c0079600d40d40300303641c1840010000010b143c1c0f1901080c000408800040b031003048410402d250b601d003821170003400c085035100040180041c008003900850b00c0014102d6001c007801041c0300b101c03500030000c911088140d00c240c03110003402010050f00c0010195004010910b90401c5c0701140d5200e14070310142d0b20fa500140e680c81c264041c90134010808401d42103901c450007801e80802c01101501180341017119031005d44c1c40b60703141c10500c41004044080c0000608c0341c1d03640341ca400200800707400545d214984241105070000209007003014081c2d1000640c0c0f061a0383c8442143d201041e4100c1e00340001d14007008980b0f44a400503007403803400d115440c040c4600360300442c00e1410355901c05617114402010700707034071050100c83da401d10141049011010b802950245480d079844110207810300a50b0f4001d01c004e030b0803403002c00140303428006448502c0001100d001c50991941c400 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 734606124 1250 734604874 734604881
    0x110f0a05060306040219020609011506122a180f030804270f021c050c030105101106090307050f06071e050d0e0f0d1d0f060f030103060902011e0210020d 67
    0x1d1144e40130703007414046e01038140c01080d0540701d1450100207011807000d1703c9840945003890b0040c2070219500000f20312940031254014010039070030f220f0040c00d01c4006071480c1080b01580301150000740e803070501100000a202405801802c280c00703640403490643e512004280130380d0081c03925180b000000c20f060964405694901d2000035102000030400900c2500080d41c040b004624030202c0d06a2001d403401c856100f460700c11491143e5160030340c0d00307080800c1007c42501c0300150030031002d681c221441010501401e4018080a0300850380c03170351540340403402c00e003030040b402c05281c02400030003901c2c5402c444205904041810f1000c0d40f200b9041c0252054002d4004c90364100d45410380200300c50900040c1800311ba142d90f01114050440d421044441010340c209040c003c4441c003104001c64103014428040c4094010407040c28080c8681c4105140d4000f40c2c4141e8038181c58103c10410741d43c000c50361140a4070070600c0d1003101d000006000c1e41e51501c19040500c80c0d58005800c1640144590 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 734607374 1250 734606124 734606137
    0xc040906080705090f07020a060b030c03010f091406150607170a0810150c0209070207030f08190509061605100e0105060901090603120e0406090612110f0a050603060402 74
    0x22410031009848009056588080303005242c0640c0c6900003084001140841503880340d03000f980288050720040d40c1d40405007640d001c9a0780c040c4079086003034059a40c01c0c003440c0d0300c0c081601c0c4001107006541c10100c0046c3c03500c1c0622a2a0707048903051004200c8149903c6028100944404e0303502e41c014502305480441c045079907160310b0404982c00075400d50003a0414045c10344050151202c81d10359424010b482c410001c80c001260b04c800c03070803006003414000181d02505600580e0a1240d480c0c51f12540c00d24501000c03100301c0000644000a2040e070800c4080010403458a241000b1500e001301e50284107000c4444150021a00c9807410000304204180d00030340c00b090140b00b0000341c0041e003030182400b9203d5501c940350400001c6103400952254104032a00481c03400b408001d4803e060306c41113504590250069185d40780400c07004031900174031004041221a0041011241c202104545285800d0074071030301012080406581c5c0300b80c01842a904115001603480e05ca80700000c00910911 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 734608624 1250 734607374 734607389
    0x5060304060c08061c0212030903060117010c08040f140a0203160501031a090c0d0b03070303050903010b0f0603070f02010e0615030d110316031206091a0303041a030c04 74
    0xc0100700203040d0410b5201114603110004140c0302d02c2c040040350000c0201c64403a400100808201501d030070803142544640c6182503d14007450354012900700310003600409031144800092030200740d024803984484503a58035003012282010f50b1280c0c84842810400341030403140740c4814005000a02c8180c0100b0380c010200d401c800361480d0007480c0340c8610b110303550100340352402d02000152134244a01c00f01c03000a189885170381c0d0701c1c101a105500415140c0e0b00141d5688018a00e94604008010145001e038680e182c98041120406080d24071a41c92240160040c01c2901c0660300c8400c1541e41084040c203140c8050b01040200304d0043c00400c2084038079101d40000e10000c1e0384a464007041040b425000d88000c400700000a5441068150341300561354404c02c0890000403149002d10f8465111349850001e82c583c8c403014905a544036040111066566001d1620848411304201208642500074600300303494841203c031a903645112a241d80130000000905401540f0200c90150448 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 734609874 1250 734608624 734608627
    0x10806010f0215040b010f0e060d03030e210414120a142b08090d05120402010c0204090b06120c09010e0601180b030114010302190f02030c12030402100309080f0c070506 74
    0xb418200c0c1700f03d00c00e10030802d4a2800f0400403034400d030900c110b10722842010f040e42c080e01146540813401041c00d10304180c100e01509922800014602c40501d14546020012a4440d42000d240d107402c4500800c9092140c20660030720580800301040702c0b074005400030800c9050781f00d0310090070f007171030100c2400040c402c2c070325414111040c102d04915074003081c0c01d030f071603d0081e641d207a101691100b17500080c1010540504c00740681000d200b011035402441803410b04805206540441d05544180e0000ca5411801c1c20404c0418200000e40005028210f4014a500703010007011a030b41017418002c11205148960000364507900450805502201b001e18540d070050369006443c2c40c6801c20700901140c010340010303c158540c464000d407100c071451040d90301001007800b4025201c03009238480c00d00641c0170900c650000e9020512141400c0048680d001d40d5a1a2a10400c80c9200d02c3d201c90806140c60310503444042a400c5042d5107452060540e80f59072801c0c1e6054103403410a030380c0e011030341c00341c1d0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 734611124 1250 734609874 734609881
    0x80a0309090c0503010303050706020306130f05090606011e030b040905031c0b090f06010c03020c10030e10150b0f16110906040b091311300705010806010f0215 70
    0x50200300030045031803000040200c1000c031542115203110a01c805000078000b405013401250655006580080d0000e10800015850344c00706000d03a1400c150004121340d0301d00400416640a020055001509181041c5417200d80210044a110b5140d903a404056650007006030940381c0741c8c0140000d0781c00200b00d075243d03213803030200c600302000c06807074484038a09103440c1183e2030070014003460041d012207034204451b40d982001143e41608648040d4114440c4a02a1141c2d8a44102c0c00b40e1404560b034012610280108081d881c1801d60704e6042d40300340c502002d006000445c5142003041e6020300061a0351a40035000d10181401500b032801c0381805400d040900300035206050030014601a14039080503075442c820131046544468286410152a00004805182c4c40f07041c070030098482c2c20610543d000c01800300345880109e6180107040100d00e44602c1c070701c884082000001c10324604c01803c045051034002018258088c01c0c15061001c0801d262091500a02c00340300c83d40c00e03034036214403e4039 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 734612374 1250 734611124 734611127
    0x1b050a0506160f0f1704081201030506070e01021507030c0c050312150111060a0f020706020d09051e0a11150a0c0215040b040b0c03040e041a180c130204080a03 70
    0x101640400115060902090640703004113100207003920252100c41204d14102030440240d000200215074007101003014040039a1045680c602860007000100410b260002020b030140324030780c240314159444603400192044d00c00c19416032100d500d03d070224500307101a105861184500c07000405501010400c0242a40c80141107840b80c4000c0303007030700719202c2c0d40d100540d490395403000c0ca1011b070380045002400b580345a802880e41004464001860b1040719280c1004036004100031801103602c94101030280f290070003c1d891741400c07503000185031340c0d5400202c5560701c080000c020074007111070b030108131650f0303880103070902ca40100c064280e0b031600c1d40d410013054520510404c0344501300b504400c3c103052080e0b43c192002c1e980c11841580c50207050880c04a00c0b40c000901c9000d8502c0100401300b0140c001e102420b02844c0318081581002d04010108011494010114a856000d0142c0000e41c41000584200f2220b0305a40035002c2a4001569201038421504034005c00d1050341d22450426 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 734613624 1250 734612374 734612401
    0x151b1b030706050105300f0d021f0e0604060b01120f05040218070e0d0f060608070905160e010c02040902091303030f02130b1b070905011509061b050a0506 68
    0x60b1094004022a0b03032103100708006001c0700c507406000c08070b20005060a042c038030340304517544d038440f0070071175128010b040790700b0b89400800201038006070010701e0201103611120b10350756000603c0f01000d110131941800c400b56104d00003400905469100e08941d8016401092894819040250180070a01400441c14081c01040c2c400f00e01815040c4c0c80d5843c0c148070105010f0280541eaa00c00c07450060610030483c1c644009001510724170f40349403280b80080c00d00c2c45540003c02d8140d0260084628003040c5000f101c01c0101a800c98040c0310701c1c000c40b01940f0034512445040700b400c015500d4a81800820000c141d00103000350003101c80000d116500041d80c06066105100f580c0130302141c44c40c002c01a0507800388011016443d00e261400780000060300c80505043e50000722181d10301c400f40c402c1e15151042683c070a02507150785a0051181d0442d01da4032891904080c00d102501a15114004205944049014419201e460f0b015000c00909004902c46650040d00701d0788203003801c0c3c0340141e00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 734614874 1250 734613624 734613637
    0x150408071a0103200603070c0c05060a0906091712030a2019050c06040809010c2406050303030601120e1207081306020706120207031b1112151b1b03 65
    0x20380c003000c11240400f0624800c2c04201e00005051503046031100e0fa002d840070a4000001c5640003d00d2718003051a445d1200179002e0a8007940d100c0754118a0008003034400d0089400c002d0159041c0440c00221120015002880c0f60b10041515501d64450300c90800500760a10f01e00c1416808503100003a241d04040600030304071608181841c00f0f00f80c000e0944031031003401d00700011754220b02e0010380455032410150024403010305044401e4480b9586e070800b108145400100142c020f4401d810450301688644006000150010362541c18110b001800d03900781d424500c1076060315021403810810090045c900c03594025500a03031a0078103407a1940850700220300c0e0190340340702c0400000d4180d01c002541001c5450640383e880c0c82941251802d4080e47c4010410740038082050705940c01240740720700b030522080c041c100041180d0800410415417061100f08210340d035001291281c08000c4d12a11180c00100d0401d040e03034540303a0b00b084c00d401806031542152a000da04180c2d20400100031000707004 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 734616124 1250 734614874 734614883
    0xd090501060303091e051201090209040f0c0b0708090d0302010b0a3305030712060e1611010c05041403120304080712091a0a020106050307082508150408071a0103 71
    0x2c4e1074650f00070390b543d01c8000094024035542c5a108000c0c60801c20268040844440004128045070fa004a40014000e407401c42e0440018101d6600b4401c0e4220000c000e00103e0300d890f80f0b00a000d8480d40b01314051842007501c502490002c02003098000d41c05151100300290440f0529036456108072800c1c04268030309600d5403025407901c00300030381500200c6000a61500c5050940d1280803003100c3d00801c440014160716541c00022500d2503254110714801c0c0540940d000d0709442220000304601280d52500c03440380e0500c440410740d81e0300602a241070740c0f03443d4820b004403164480064a043e100c0c2144407440c020000c1800103001542c0c2c000c04d042030103504840c0030b85010b103008030341e0a03119110346180b442d0221910348482e01542c00600701d664080c0f001040403601d90000034185035240c1d0103c10b0560040f4040d002c040c1b81440c0f0f04814030a00381e20001c04920b82044203031901100c940d41d10360f90b44c080c400107040003819402d0f10320f01c5410a00040b1900316000140745225000c0c0800c1d607 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 734617374 1250 734616124 734616137
    0xf060c0c0c100f05030406021201030f030f03060609050609040908030a0209120c0a060c110405010603020c1b0a0504020705070b0a02010209094204050c0a14070f1203020d090501060303 81
    0xa12402c185480c010002210f0340e88949443e107206040352190000383c022141c045d020407280c40b025001c1410640a5806018042106401450302902c1200c031060340c04145814030a0811809410a40b010121103081c0d40d00341d0b4400e07810001400403e200700c0c00904d100000f00030700000030aa5400f81450803c25501c49507549240070b50a503079810417507282c0e544800c1d00001448914811202840000e02c5898411b09a004002c009802c0e1103090b001080001e6000c50f40d40180001040442602c4050780039040e8003074940004038000203041c0c01f03082d0189400050110811a04000b01e40080c8000d0381c0e110707281c9541401c002d020303501c005070981c072510007403011442c1d960410003141096200240c0301070301c941d492803c02d00c4840ca1103410010500c03040148006940b07aa00901d07100c0c0c80d1600c07a140d59844505006018400d032450346203c030301400c1c0101c0c0b00050118001c9020a600312000c00d01d865071a00e0700310003038401c031000006103e05081e0480c0c200b0505400c00170580748a034a0380c4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 734618624 1250 734617374 734617393
    0x9040614010e01112508190204050a0b0f090414190b01060306050d060b0a051003150e0106021203040f2909030f0a0e0a050d0f0b1f0312020f060c0c 65
    0x44031800441c0030880e51503003240b4102110400141d4962280700074007005c0004556844085038204441111466404070b801450b4070110310b498450b0300d510110f007400402842427a0340106507107205804400d0b0068606101040c20f11510440c0305640f28040c0048583c125400c15a00503240d00b652422135204240d0000850345500902403c01500c0d40508030910440c02500c44001400f688a0000d8020054400108542c1c443c014850f070044c07103507140414240110b10380c400d50b002e0300d54410981122407000501240780c0c0401ea00b43e4146000c08c01c41e40f2929582056200313801c001800901810751181c00026521042311052414400020000a680d07114001c3c0c81d00c2c0d100b41c02c144200e000c81048140d680d280124562000030702c014125920042e11030021540d0b0b40889041030342c2c005c90800d0302c8001c0002400e480d6901107450307c80080e81105c071203181403607803030540802070201c200f207082515218420400804075a0781d08044a81c20b09103400e81040030b41c0080e800301940c0c003581561 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 734619874 1250 734618624 734618627
    0x15070611030f04080d090c06050a1209051906020d02040e150a080d11150405280807151e0e1905030406111002120a0b09040203150c09040614010e01 65
    0x607240b0480e407000e044101503403180d4590b281903000f40801000d2a5a40ca85900400e04401c0301e03001415250700c88640c0c81c45020700241c400e0f001ca00442100c903040c0221180040e101186840c09540d00b2078083c400e00169182410180c004c03200810300c482d10100740010f00312034010355075010b44101c01c503501c2c0c0d0407081d1007400a00c1c2158000e134206580401744454400e4403d8541c2c61002c4c40c0390065454624940c1420041c10009548c107030340300d6100541c03224402544040a05080100661903076150060b555251214040c02401074000e00000c22002d4905406405c508a040386c80710348404043c24a1783c2c0c42004000480d0000b440e8400c245001c030040304001c040c00c0090b6007210082d0b08091800900703c0d031444441820040a008070442c02c41c80311002d001800b02000c0d409a22041c1c1e2814096071402ca411808140b0b10901140003404003680f0040351180701c0c40700701e42c00c4140d182d90382d19001c0c2c0c981c45101d108981240c80d00100089148440e203402400d1202640d0303900940d08613000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 734621124 1250 734619874 734619877
    0x13094b061b080103110102030d06080f0f1507031a04050703050a0c020304061e09030c1d06011b20150d0605010c030915170106180b04080304050105071115070611 71
    0x700740000c9400400107001181c600c0c201d4410100051040700d04c8c1020746001d640680e14268440c074440d0380300000c020b18280040c0034810701551000018855010f50988a070030341d0310064580c000b4076984503031110901200341448030240704051f0040c4458240303140c0041c01070004403031045040c1c0c684aa5001302c1c51001c4120303000ca0701c0654a801c00440006d2020101e685030000f9141400940c1f000040015060030000300100741e81191080d40d4030b141c11b0140e15001000f0a42410000304020100030140d601c8072101036580c0020307050701c1d02032038859004c200c004003055895014607400340740007001e4051b00042c507481c0c0121509002d010341d41c80c0155541d1241c41c03c0240820f600c401c0038884100803803007044000b166071a110480360741c1e495506a408401782c00c032600280910300400034449883c1e0400c40100890f00200d07250900e0310880d01e441e8020b43c0100b0341005400282031003801100003100100d142e000f03001c0040c004800080d031109601c4000201e03403490512241344401e098000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 734622374 1250 734621124 734621171
    0x1091202100b1e04020306030312040f05060f01050901090518030d0c030b040203070813030210090803010501030c02070f150e0315100e0411010c05160e010513094b06 73
    0xb00c9800ca60b0f2030241000043d40000308421f4262009004090403004110343c128011801482c0018520300641009400c0000c0200080d18039081c0c68010407980d1215911541100d08100300014203444028524891740850b41030754043e480046060551120180c1c0980028041034030b00300102d180810900081e40030403030f4401c1c04182e0560004003506a400801070388503100f48161004e05541e601c4141c00c03900291000c3d500f10001000600c519601031040b465121243d0004088041c507191480340b0041441c003686220041514096603440d0003407000340312941d001030564034000d0700d4200e80c286c80703003048410980d18034a8041c0000c07107403070459025010b980c200e01c00d540e107441020011344261480007021a914481c0d9100d01e040c00100100406c040e241c015521a070765450031080004404010310103068451511034454001205400c04400310b03040c3c9944a28615504050010303031594000541d9503e880948402c1545449075a8241c11030303114034410009c24840784d076841e1007041c211 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 734623624 1250 734622374 734622409
    0x30f0712081c050a0212010501300603050304081605010504060f180e091e010c05120709050a15031b0503060103090c1a1809090706080901091202100b 66
    0xe245031011907029002802c090303800c401011180000b2040074402c6840c100d0b602d10a02e50301045d00031000c0b404080d181d004090929080300109242184007a800d090703402c01c265220310800d1051300000403a0452801140c114058a8440340e0310015291204418000494000d08296001c103166014409981c00d41d801d50f60f4803130a6102180d002d41d000c0c51000040c0b0225a00c01300000f0302c2c0710b00d010340a8031400120f809030800744444249181303035014400700c9070a142d041c180c000b01c403140d000b42514445141c2451500c03d076241e185040d035070120207401203900307c07060360008614402801d0020140e0001554100f208203031b0319007811444a02c0c2100400041c0d01000420f4166100750007005000c5c0c094030b44151915540c003e0000388081c0f81c00380044100b0007007a291519160281160b404030001c2d10f1b0183c040c54601841c503156141401341030107000e509404110b41084c25070021009650081401c0d04800041c0c4010703680d81c0c403e00b140301000e8181807060101f814503c0740000400c4a5 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 734624874 1250 734623624 734623649
    0x9030c031609050406060504060b09040506060a0e0405040218250207053304080d0311040509012616210b0604020c0102161a0f060a0603180605070e030f07 68
    0x20860381d00c0180601038130079240b031500c13071304045241d5407a48203010050040c100b441d41c4d2406100c0610041e01d4006010500c00c0c1d0051102d463b0454104641c0d5160784411100003c00c1c2d6030318400540001e41000c0348030106c01e180b40801816000192950f0190103801c4035256009040120480e9507182c18001e20303401560b00d402884040c20401000e00c42d03640b95198030140710450000042c03440c5c00507803140d0400e034400801503000325054403440e950062420421490030b42410701050040c401880303020040c41c4203e0411003045209494030302e40231503140550700484a01c8644000c944614080e841000d6010400c42d11160b031000c0302042c2440c1d01071000d100c02d0b41c03040304020003134024148401031550204041141e003403140141c046800e10848041d0541503240c40201c000f00401004450000401000d0009540e15102807900720f40403490089042002c0010440130350742c146400404072400c00051180654100100c09210039040e0100d51181060f184400d5583c5168031072040036524 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 734626124 1250 734624874 734624879
    0xa05120c0921010e0d0206071b02100507080418140a0203070f030c050f1209010b0316120804050310051504091a0406020408060a0b030111043804080309030c0316 71
    0x140b0700c0b040c529a01000c800010f00c07407400c400300c600340500920389000580100c010081d96a0700103010080018030a0208103101c4826408100240c0021030758405000300820400704028074401150068560507109001c80e0030702081000280810700c0712592560b103c80005007040f007040c403d5a01c240100d07030361a00c21603500e0400750010080942c4500c1040f0703040008121181407580240442c030f4200c0130070b00c481d00d4130881250840d40c1c5a103008d8881d0300589038840401141801c1842500c841020782100c40050740360103244c44c03044d680441d401d03001b00d2141000c0302409a103e03610075200c1219008025800104000889941903001880c462540002403508007031100340d26441031088000514241c3c45125140c41e25908881a40380c481d00c2d1241300da0300342428003c000e00c44001c1c203401d604003400c0c01c1c01c1a243c240566550699651046400c1c1250408140c0c40d102240c0704480e120b641e60303281c4494684075031200b07000782e00174402c0f424080c150f4200062108048203141e41d00c0d0003260b0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 734627374 1250 734626124 734626159
    0x30c020d02060f0a080108010e0303010609031101030906060909020f2706040e06040c2c070305090703020a0b040f0807080a0b0702012406270b0f0d020a05120c09 71
    0xc0c456501603800400900008072a4030b03405006026200d050345482c1c1076036252449680c00c1d500100c0055503150030502c0100812a04000d8810699600c81080c0c0848006400100e000b025030240c003921705400d1000000d400b0440303030b0100c2281c80c002d66039540798075089030601c0242c0b080144030003c95013a4914227054054400d02107508140f000b80b0205030640031541080c5008400d4038180d07411200c001080210210514045500d0400e13102c00a01c8564058010f500381c40004250205140c2c0b1840000c103c42c0c410321503071000c0c590042445004c26101c88035562150010301a40500141705c500204024000282180c12580c541c03004203000341076651640c44043c00030306190305564894800c042d545d22a402c0c990855440c108120707000e203241020007400354018040d92030000b00c2000c0d14071718512840c090b000c182c5920480090b0703034202003030010030644100c16044a049102103400d8110a41c040300401c0f038020b0350b101110351511b8081c0207880d140300340b080182e84104400710588045 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 734628624 1250 734627374 734627389
    0x30b22020f0d2303040e160c03030905100905010606300c0513090f0b0d03023f04060306170c2101020c0604050714060909100f09140a09030c02 63
    0x1103104207248032812190b00c6082c40070210040c1c2c03d60550304086000c1c1310301950300c1d401907803101448200c40501103035044003a15100500001904040e164140402449000c0105c80000f50401c03208008512003401c02a0080031b040c044c21001850b106082c81d47c007d801d0300b444a0200c0000010a2800e49500355000180a00e0b58000305000042c86240702c1e41c0c043c015050000c060070b0501058101a07071007004200c60000c0341086c1304d01c01c02c000c8100425030014031182c4121010b0408605800311028401c41b0038503072294000c070020142000890308031240050401c40e821510148210760716a0031009280d48011007a041c1584802c1d0203e08030324180318081500e685116003a2a00c5007045400ca0990b444004143e0481d4000c1d1305100820500700280801000b0300d07008548000c098100080030391249502c0c50784908000008541c100703204031604e9005040d0704200c144410b580744c8061025109543c1201303559034046000a0400d031a5000b02480268103035aa400036030810350811228 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 734629874 1250 734628624 734628649
    0x2150c13031a2a07120509032a030604170a1404060302071505071d040e06090a0b0f07080a020a09051504051e0f2701030b22020f 57
    0xc0c11520340007000c42d4580c0e900c2e00c15080440000c00c00c900e000f8403100982100b54403004812000e290208020012280c00d50305071542c440140500b0300010f200481d03080c0100050030313a141c0503244c0c2c801b811180a01c4684004042407034204c07031a220607000c244d16054116800350115a02409040c450240c20006004007840c60415600ca60420105240690025042240031a600103804030501c0400542c080c3d0f8a1500b0380302340800c0c40e16038402007000c41b0302e01030003030340b0503840105584554950304040b614611000885000c0d01c0c0c80410300d0381d85e4003c1e00d01640c03201c9100c00070444141c42d44a035244100200c1e1904412900c5000750403009601c01d0700640108503c0e04c001042954401050034808035010724429151800c000c01c0007460300000c139090b10704500d02200c0c114540c480c2100682c1010048580c002c4228a0700c0041e00c1d400300440c0856142c28a22001204206400b0346c01030040f01c45519a13203484800c211030803441e4120f4180a03500c440d0020502e001d500c1d000045000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 734631124 1250 734629874 734629897
    0x1401140306222a0e0906060d05070501030f06090f0c1b0f02060c0a050706050306010323010905040c080f0318011d0411040f140102010c0203041a0f1b0105060108060102150c 76
    0x2e80078010320090f12001d0242c1c01c1071944403c81402e22120900802c04160411011104514001c01c00c0c9c1e241036954246100b8a814541c4491505018807080d905c00001000701110038446401000055002030608c02011404141d80c1040914034407000c00b07800a4003a804a00340c1c03a070501c20780030001d8603003160290592074411246c40000240c0c0c2400350070300401e003d031990354072801d1940002d0103994a04801080007007406941000a90b580300d04541142d142c10320010362610303681800036042071142c02c18035642c4500740c0080d0060300000020039035140380e01038410f140100b4ac0011243d0321f00705030340104442d4000c00710401c180f0705580103150b200010305800e86065551070800345600c64640c8855050511000780c12050f5030280140c002041c0603102a501d064182001011442901c46510100d04004158071400445141c121800711020044112049800503c441d0280038103c60140c00105009e0100300306500004080e103030b01060180b068202c0d0340358000d440d80b6822041692b0f8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 734632374 1250 734631124 734631173
    0xb0901081003050c0f06160606060e060a1706062b0f020306010c020135100b030f04060e0307021806040c031b050c0705060f0a030b01020a170d140114030622 69
    0x1240c0c440d4500480e0310b4508c1280d0100c0d0075071070044050010801002030a00501c1c00304a02c0c1e5050f94030203071080c000b45078240174002c0c030745032030007c203140b405a00c111a0700d999844c000407098031040144001c00e050f0801003800b603258100c170706030164041560428045440319445600541c001c84100242420907009030b1015103581d00310601c0242d103000c081c0740a599a50034070120030304048020000d070840d1072a403403460074001c0c0c1ca0075048400800242c030030f0360340b41070f4040c8844080c0100c458180d0003d1040080c6403034030f0000015180142c4405202d06d291103c0345500901038040c540c0030b040d002419441da00014442610698000105040304cc00750038004950341d41c604018041e09441035138101c0c2c43d03541da51000b4003241d03101601c0c02e0555005c980d00c0c1c00080c0c1c01e06141c038445038840f000f085e00c80c100c0402e01e001501d20301119140c891851400880d003491200051288100304604075107958a5025520130b4581c420440b4101000041e60108041800c400c0030002562140ba900da = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 734633624 1250 734632374 734632387
    0x50d020a120203010b1e0c0606060a050c0102190e01030e0c011803060e0a030f03090c0504020c010b0301060305010b0102071406030c030606160510061e170709060b0901081003050c0f06 81
    0x150203d9000340c2100c0360900340481c0c3c2c180e0100c0000303200803403028410905403038050904041d554034903000301142c1c890b640001d04004603501c2007041d41c0810841030002d40d1103401c5150300108840c03040b800c0c04001500701000c05c1c40c40d032090256854034051030000d8a10442c40c0d900454880c00e000c45030310600c80c07a03448000000782c014410326198180d10405058500c0091600402244440c0340d40000c15041030000300110300350320342c00b1084900c00c48006a548100c0c0308994007422071001000e9041d4a13045d00001488011740242d24856400d0b401e44070851f441c0c0960040703018652a6903a0132907002d00010341420380440045800420003007410b810300e060800700740c0701c0850684040314260480c040c6075085c00d2850007002c0140c5242505c1000000c009041e03e003c03500743d0700c07a010100046c4070350b1000036071041c8080e901a2417045000d2014a031100c804140382e60044c0c9003070f4000f81152001400001d009504502902d9010b805441032011140400c5800050800b200342e004804010a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 734634874 1250 734633624 734633657
    0x61406190f0309052d07060206070305040201110109030c050d110a061a0303071506060503010501020309131808030415050603120307030b22060923090f03070b1801020703050d020a 79
    0x407014912944160107407088180407617070502d20b580310004549644080000e0203240c0c2c002c40c11940c080c82626001549544900040354251380d148006100c40d440c01241c00c05159000032804800340c0104110b0340744071010842182c408400314540c0070b045d0000140440041d020b60442800c0301650780c01c2203d90418600002e0441c0d002807400c075400d0801d0703418042070348881e0295000920b020708140e0304540c54900080c2d105d208005aaa02c0b600c98400c50821000c8194009100d4490708500d01042c54414603000741c1d00da00640d42500c14100c020640c1c461005a4054903102e40c0c000303009030000c080040c0c401c0101d078101400c00818540c840ea030040560b240c01d540460b8403841205440604250098803204680b135980100000751304055184070321440c0d5590005908010844041690744d0390044182400030543c140311441c00300244113001c0c003840b5140c180c050000021058601003900d4259400c0b4400c2a50040c00b041c02803249015640a42c0d026024a010320309048402c91000581d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 734636124 1250 734634874 734634883
    0xc2d0705010507051306020c150d1104060309020f030601050f100e061306030b04060e1b07080f03100f0303170c130308180a050a090e150109061406190f030905 70
    0x8000c00000c00100e81075507845425807115001b0101400540f20070090f607408103d0003a0740e50001c1a5036040050142c00030b04295200702101c9002c504015211600c0d120020090215440c099210b4050260707101c0c02c034600415503904a03503000b82903c410102803010b110038541012464000c1c802c01c0d8502c602a034413800000c1a402d071003c00403000d441e040140241c111440a91500d01a074a0440c00780a9040580c05441d005a05461040392000065641c0d403c00d01c1411070051424002062800709514107001031030203040000e01d009111078481c10b0103918510310b444040e00103502035400041045194043c01e4008591040031490310b048814096560f211542c4121400c00d0001804a40c10854140414000504640b032180b402d103418001401508680175400c50107a8902c1c910311000c004100c9510750301c2e02c1200f1000d00c3d42c0d640103200000c0ca0300d44140c0c40e0010b07041c4801c40541c94500125421903c00d1381100c07800f0445030340b01721164080341780710b80d061558074101540850070401 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 734637374 1250 734636124 734636131
    0x806070206070906020114060f0604030609080d05090a0f020d030306051807030501050d110907020c09040f0203010b010c0213051f0f15020d0504030839060c2d07050105 74
    0x10001c00d45420b1180000b031101c020359101c6411039141000c6040400f080750300c041c4c2c02c14000c450f00e110707800801c000112940b0455100501c0701c1d2808910b041000040d001a140d03025030040104000e59400b0701c1d05444202960b401041440c845600c0001440c003040d110741c0c660302910713001805035204c02c00b00d00040010006295075101c40c0b01004140342d81801503a002d003009440c0004e0420196450746221998100b100e4810707002a80060400e61080041c00350300b150040150503070b070509083c6660550700302101a8043c0d403c00c0450b20701c9500401c0040300155000c0c004401d2602a40c1040ac0201006000c0c400c41b0440320300c000c10600381c0d4105580c050541c3d07400c1c20101c00d1a114203034101400c92030190041d50883c01070751038229044800c0c1e80803a40c01103007140d92000e900d0301d0b05018451240e080200c14481781c0d0b01d054562101070441040f85118030407103815403105000c031045400b0708140c0d0610580f00501c0d801c40003141c40038000410408040460a0400c140d4945003964000c9 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 734638624 1250 734637374 734637377
    0xa020409060e0a0c030c020a0b1b0f0c060a0504020108010b07030306091e20040e18030703080604140f01060e01020a0204020301290a080c210708180f190507080607 72
    0x1c2003070045000310f034442d0401d0400b10b41810042c41821600194551609113005030001141d5000103405040f0840007880b4104098040340d030b1524a61000200358014522a0080d4443c0e2000100c1008580c45054051a016111442d9a0703103407054414080c0d2210000320101500c8140c00204101103004620a28030150070411071514080310386411541125480c11401c14010140d4601c000d44800f120181c0d082c114101010b82c2e00c0702040d00004d00c102800d00958840052011305059020840e240a0b0b0b0301220140318075031400d0003690b0030000980303c4090b030803107100041100707a0040300920790f00720060055815005c000d40014013280c2003640100e419910140981042e0854180c1001943c0e01011060f8181100d1036002080814000c040088075103000600b6502c04a150304002408950700240d40301d00d103443c1c04001e00304c500903180707010040005000822046404258280300102000c01050444d80d400e82c40d503900d602c0c8580c1540c6901904001154144041c004148691120b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 734639874 1250 734638624 734638649
    0x10602071a0702031e0f0c100c021810090e0d02101a060d02031e04030806090c0702030f010f1b0c06050601030b030a030206010509100311190815160212030a050a02040906 75
    0x5c0c1c00403814403c00b003c1e441c2c00d070f8010b109509101d9035101054881c04202c2c1c43d1070610069148089080c2d080364141160f001d0301031804200300960b040440c41700b41c0e000580140304511240c1c015a030745450341d940b904090b801440c2108d10710315450b84000e4441e00e480b20046e41741001c0401194544c0d02c0359400f03402d440d03000820041482c40d1f0980b48100340e00011701301c10310b6181c1524024031002002e4240ca200303031a2000071800c04811101034880b41c0750001d090710003101d92080ba4900800c000340c0700071455814149600e40080915003101e0241c0c4941d00c400c03011601030760b5030b03030001c1000400060506607070792420016a02d08002400c2c0341e600c00e4000b044103504120070031860301c40041503207052219020703007800010341407192404006e0b029a1131008060790042c2200e8500ea560700401247e01c0394031085135024030360802d0300d4001c0704e0031801803094801d52002261100100c2000800018080002c40c40c1e81070290701040c0d004000c81c80050074142c42d103507841d0a0f54140e902894403102e9 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 734641124 1250 734639874 734639923
    0x50c0d1104031205031b07060902120a0b010b0910081324060b04140402070204090204020a0f080f09031b07030605070504090b090114040c030e01060308071a010602071a070203 77
    0x4a6040d0982c2e8141a818401d003141b402003081c460703540c407181d07950025460100e2140308102042d00450105503000b40b008125201c4050015a215501c001c152400d4100a00014484500004070351088601800e902e00b6540400015541c01001078803c555040d03c10020002040c4c0f01403021040a000034854000114010300000c00d9174001c2d001650070705010401009659280104500c1a0105983c0903840d2001400050014072a901000e904075000140c68644586c5c03008004045a00c103440301c07a801d4580d52250700040314100c0c2c5021071039004104890404c0710500c5410207643d1090202c40c881516035a507002a66420380f291800b1900105051040038818002e06080001c1641d24400c5076141c00c08981d80385201030280340c0070fa40d6030010b18450610a8103c02c0001a01c0360080c088642d6a02d8602e510743c1c8a40f00944000c0011101e4544040c5c51080b558121480e0f40d00030030b8014201050503005000d04821020b018908110600058500307008800340c0c90480c480a03005a070 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 734642374 1250 734641124 734641133
    0x6060315020a020307020904020414010b03010501030c050f0d15031b17010b01210603081809061207031e14010507090803070f08070c0806040f11090f0a050c0d110403 73
    0x1140e141034920301401805030100d000c2c1e000003034402d040e80489100c1c0361030f112070010500601847c0c460002640e0018004111094104002d40c100c813800e0b41c0800805650000441d001d000e940001c0f0048a01004245a007550b6508021003170680e543c034101c0c401d5070303a69074910105516000002200000903041180d400c10002d01311603201c2d40e42c000c0c41204044000240114030210152054958080540e219628580d0250b005107038480501c69944109500001c54015124200b40c81034401800040c054100207401081011828000f003030140d05581c1c91860708021000c06007403600040c800180454001e61804401c6121400005030605100c500106080542e821420b19070381308000d500001410401ca0804454021703401039250502858030550702079480e440562140302da0400d00043c403101621f14a25188541c01000c11607881d04140320141c1800c42d40c0703904900d0804000342c8800080d40080d1b030b00207035071402e00b85411262000c0c130081f00e0032072030b201c400403c0103e414002c00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 734643624 1250 734642374 734642393
    0x3040519050f0913060e280c09090506010b0a260f0f09070501140903070e0a05060d0201080a0b120609101a090c07051c030504060f14060d02120604060603 68
    0x40940300601c0f00d281500f2580841c080b82d000052006030781d07000518640e0070138481e010030b5000c480703000d458400c40903242c00810558501e069400c46500c1c0c40003e118540c0d031242c3d05909500c4005001c0c030f0b83c0ba103800c2c6a040e070000300b4418244100954606941002c240300c0b02d856540070301c00c1c1049170410610203112a44001c0c90708145506401c1071002c2c286000412504590b42481c00c9a03540540c0802e200160250b102d1650301403140e1072000c59040c0c5d030503584602c0f1303a152500400840da50030040020b09040b000c800390224034450049041e8a400360041342e805000a4811a0900e01c1034464614254049481c1c0c42e154101d04141d004208641c02000110a209000d40100949850001c0c0030064090141180d18000090500403c0b0090001c48100400118068614241000041d02808086074126522031401d0644c4410410b20300c1980c00c00304281c016100380780e0f600e20510840525049090741d0100c002c0794000084241000f0f024412403249102042d07103480c51414402c070 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 734644874 1250 734643624 734643649
    0x90103140d020a05190c05041a011b081c0b091005121b09040c0e01080313050102031303150b060c49030b030307120207080a02060d020702030304051905 67
    0x45410142018001c90030015180a58450940f40d60381038402c0ca10301100501500d47c4555007050400b208050040500890301d9816842030b207500020001c860800300c0e4030107013190000c10b40d40e0140710390440d500c0141c482c1450400380300742c000741d07000310b0000184414408441d1041c07044200c2d9001e1140c6d0402e03150003070b8414513400c010503214015103061120040482a07040c001c0e2000700c00501444820300c40300340108906642c1010550b122140981c496001000e4204a040300c00301c0000d85510010868190580f6100d000320681e05680d201d00c80c5149510221540075105d081e1600669148002804030302c80540082040c41c0d04d01c60b1001c2004aa400c0800c030b40b003031a021011541401c076001c80591050303160300c0700031400781c04001e5008103203210086425200210b2000d0070000e4030358011781111455021aa900c40d99600c0460f5550704000d002900308000340310000c0c10501e990068484107100038241c030705107902c0e48081035820030541c922407071080c0c0d0102d0400c86800d0124141c0117 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 734646124 1250 734644874 734644877
    0x3173c180319050a0b2502011406060301030b06190b04090510170303160215150a0e06010c0311030d0207030c0c150f0507141006080f07062a02090103140d 68
    0xc1c540c80700d407101c680703c00d07004c40d001e800150440700090480301c0284034220b00b4501c416006541384800407000f8003e24901b185620a8000030740032448070300c0d105059030b04032a40800748111179551481030001c0d842c880d48190802c060000004240040444041c2c000f1b00010300c0c0004880ca4101c0d6010700059103548403210441000c80c081218500120441c1e6108903c3e0800c08040d5010410481c42d100c4100102e076040d048000074004400501040250740b8002150020152604d801c0d0140282e101a51004e0100785400144000280a8029a00b490000c0000d03a41403400c0000c040069074440f4a086001641c003072034050800c5075000301100035000b5050700c2081c1040e0f201c0054460000d41c81a5024400e002c90801c0810907517600c1c0c440340f04004030544412010b522000f03000b07440140141da400740208440010310800003d801811589195120300800c0200700d541d00c0c0710070f58031348014884581591824056241c5100c000e00840c881c0c041e4070807a6284270001818020700c0c8100d40f0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 734647374 1250 734646124 734646163
    0x18020a03051f0b0f070203030d090b070305060a1509080d0f1d0306040201030b030f071502010c0e0a15050409050709300b0601030f0504080403173c1803 67
    0x12000d07441e03503001d0300c00c3d10401c1c6022aa1240390040d055001e0282070350082d41441b0019201c900184590030040d84a8400d5601e410f107526406010790545600700c403a65001041850200403e0202040407042440e69061101ca01503c1d04c0381079052207803000210f00840e41c4500c220081130ba0280d0300c800f00002140c04200e0f941c4107000000e49075180944003071704054a139180100e4542d000e2001c1030001c0c200700c0881d0344059664030a00078000750301980c0d102651901d950800404e0080d940700c1d4040c20020907200605040440b0009251022a03c000400500b03000c04100d91841c3d12406000710300b280c0383d9114092525024461042003844002103140f0910042031b003009450290392581d56010182c6074159440f840103c001380425901000b503d82428180014803900c000180141c90159078940000c4804c81c002001c01e103e83c0030f524401071800440c100e40d03060101c54810302018005580310038042d5030216414030750010728034038407415150100401546802c101015280303e2103544c14 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 734648624 1250 734647374 734647411
    0x3061e010e072f24010f050105030c0708070c0602071e0e0622020a121b0f050c120c03030709080c030c01111608071404290a18020a0305 60
    0x40c90001003080700124001c54000490f1080111803251102d0a024411210b14034100403905540284404040da2000c08810000c42c03201014854941a80c00c10b856580c59601c030700e00f001038640d015081c1610320314000c0c80300f94005107440001c0c1e0300401055000301104c50034180c68415400d00080001a0700440100030000304900658555110f082190403030300c201d15114800d40611816848440d07481d200050038603a00b40c10030b407404501c5d50300807805c000350359008800601070407040004070041108400000c1000b403107500206015150762083d10135503001a81c241ca050303004a580400703190804400c001455a20212510080c440000204110b8458202103a01d4161040c0c500f41000403212800c000030100b040440e055041e0111390314005d0f030ba40e108044d11071905010b1021910a240405002483c0c24013542814010110108010618107240a0400a070307070b0742d101e500300c5c10580c000900070510544840044010444c0540e45812a0400a080342c07001030281851a5807400360 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 734649874 1250 734648624 734648627
    0x1507030e07150509010201110d020705120c03071403040806010603240f0611011503030c0b13080910110d020105090706020f060a0209030304090905010f1812050306040b03061e010e07 80
    0x80c1c40c80d04000d0400f40da940d1000d0300100d014001200e4800e000d000001002c07070040460740d008190a50107482954003484241d42d1105861045c1a01c10500740d10034005240070580e11590014844042000c40345010756606c09241824800da0150300400d6035207107070300304411281d03110340e1085090340000318020b8105461380c4404160390007403070104a0105031174200d50000354854101c00b080185441005540c84c81c0c0140900400c00d0226911800d11000c2113904060102c0301e03003125804210301e42042c00390400d02424808010b10311040000281035061580700510005a80214941c004100d070b1800101c050303d0107800b83e2251045612030305a0072040705011072995040989800003681e140c0b40e0388006461400345420038802030b49840944401c000d4154803000821009000502c2007921181e404044020000c0021700100084003074840118460002103611542c0140002031035906500840e01c0c1c000121100c102841c1c02002c00c850590b0310010460040a00407501082498000780 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 734651124 1250 734649874 734649899
    0x1110180c171018021903060e03030f130f021c060e03041a0d090b07031e0b060d0b0301200c06010515040306110d1a010e0f010c11040e1507030e07 64
    0x4602c820103542e00c0c0018440710351030404405290b00100300c0140900250121801c440d0325100440f02e007071810030b51008861022068a1260301044c440e881903641d120340800e00d402102c4001c03111254a00c00b00d40c01a85c038507a000080c2d0402540005090546d8504003080325a28041400640c2c0184810800c45d9604a002100c00302c4466401d03440c1c6100300f05503005001010401040c0d036a0300c0d03041000c007a606906c00c070450001c1e0306140e040c218155044c01e0440315080480c50704031100f0000301d141941645c2240085550183c000120200c0300d46400c40d030300c4007000b04016960b80000e605c55564170100301c0c440c09000d00700c840040030f0281e030884200d54411031100074400e584402d1040c1c00f4180500903504a00100d11050160704003129071040000301182020b4041540c8501081039070500e035400d80c030440c00c10317101c802e070070b03074031034680b40d81c000d501c0c282a5501c00e13105c07801d1541c9038800b44140c440510340740159600c2400c00d040040c0a0b583c142d5000c1002da407010300c2c20000c0003a10f0310b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 734652374 1250 734651124 734651143
    0x50a080a060b030c03010903020d08102418122001090302090403050f070c092a030f020409151d0609041e0606032102070b04061110180c17 61
    0x20400a204002c0c400420b0502d26200b82e2603525520f000d140c0010306402140007818004903554802040e600c014500c821440540916080c401c1d16000f85482d0020100441a0f10000f500b046115a81d46580d42d416036100c81d0041c1c101200301030407d42c104680c10b001d003085000140b0b410100d44800f440000c12162031403101030f02c2544010f0100d002d15015500300ca55004000b071b0020f07600c10460411001c580c1640c0309680c80e241c0342c91148060750888180801d0030f08280501130b641801050021070186c05001c182c0b08001c4d07420400010409214496418a0541e0920480e800da00e0000d20305000200e0b8503800c595801c1d507901300f180079544c0e80f20702d50344103520142c0d0205842101101d80d801011003040100028900600881070001c1d40725007140448001c180040c2042c0b243d41c0480c0c68029522401d80190340521040c044a8060703d00a1071400800045520054580103110240c920104400400c4100039403007605001e41a80f10201825050303800f003601040d9582602d549502a0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 734653624 1250 734652374 734652383
    0x40c09120303090212070f0f05030114060415120606030302070632071e120309111c0b1f05040e0c042c0114070323060301140718050a080a 61
    0xc11483c000c40d654400e00d0b4200903040c4003200c4180340c4a41080780802e0326405054140120366600003440e20f814010b0040c0035101069016141d01c9010034030010348880500c0d000b03610189140030131503495016003003210f9070003000003280491a42c00e01034241300302a00240d00308440844800d0010021144020035894902c0c6800700850b00300100c1d4040d8024000700422890310f03450b452400d00b00702d1400500184c041c0c03601010400c00c0344805c1c4d08481540b03e00070f29802035000400031a10b46207000c40200c04141c2c1000600035a9640c40c00b0110783e0441c2e511660341c0c142c071074001c0003a11402c103240c082c1400750f0b070070441e0075001e04e0f581da9218070f131890451003152909031440d08548814900309410400c940c4000d8000211082e80d8060a010800340310200c489800142009209009101c0100d50010852445407036040c010f00742090000d060f42e40641d204e89955842d114032001561003141345039201c05014040b4140b01c03050070020350190344a50b40288041c450301c030300400c1640c81180c0c0b0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 734654874 1250 734653624 734653631
    0x70506040b070c1503020a0206060a05012a02041d010b180c09031c020f060606030f0103081e0a08220302030d0902030a05010c05030601170103050a020933040c09120303 74
    0x1d51504030406025604144c07003641d42420024082074164014111141c866000d40d21569200c10902c030588072184200c5d4000768000c2c901c0c0c410b400340960500e50040d1030a0040e20150b500f41c0118050711540b403051301d200c0d103603c0140340d01c40d10207104108a120085403a0125034040c02c01c004000da5010384002c41d2040c0009845c0500d940810201c2e20a460350038044001410301c50019440c0c1030582035001c4540502c0001544901d0710004491041c100c0304071083d010303401c41d15084400d0700042c04010900c0f416071948019480c402019242a04856589140b68039000210b4855017038564400495000e0b01000100007c0d0044203880503400c5100000511400c070f030000a00d00080c003080601503503c0c01040001c2c00303a12800a40c0724180a0f00c582c50142011107184031001c03801d02c8084c0450b003042840b2801460700300440340c2c01800c840801c2d030a9110b0f89001021601449000c1345510b4246101c0910b00d080502400c40d0340d41460404582051a081203440d060641c040c0041c05c042e036 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 734656124 1250 734654874 734654887
    0x170109090831060203031618030803270610080604020d020f030c06030a0c0216030305070b060438030106140d0305070506070207050301200a121107050c040b03070506040b 75
    0xc2c0314410240e041e001c00071180015548100281d00c0b03030710076076034a40c41501281c0000000c501072240c0c9031301c07502040e844c1c0b0400ca10b103484030001608003034000d45e0103407004c10198030014061026944501c0c0001c0250405082180c1c141c4c100810301e50260300e4076080700003000090b03607807600402800c58056502600f040403900c0041e04260345840151385c8020040144481c0382c40b164465006503070140c0031100d026101901480c042044c40c48004c0014004001c4680010040b40f1504e40203a80070340040390162800c540b840c90104130004ca003611145011284a21103540344014841c100141c008210300c50524011110382000d0503001c5000d100c20041a400b018459421210b545030020140e520a051000c00251115000d00c5050300c01d60034201c22001650907504031a88441035107240900d0070b00c1c00b400a50b1503000000c0d118502075550300034184001025001003600318481c0d00a05403d0300103c00b00000c0704d0080b140c240c042da0141100303212588039402104c043c0d031a214001a00d958 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 734657374 1250 734656124 734656177
    0x11d1e0102010f11070203010b010e1302250b09060a050c090904020f0303041512110405120f240c130b130f060504060f03140a0f0e010c1701090908 65
    0x20f1998125422880c2c51000400401c00304040c008940c42140203202800b1950011512041c25020080c1c1c04104043d0f58017484415078000c01e805101c6202000e0780b814285c1c0040026040514240ca01c0107424080141c0f003c0f0078060603610100d0040100010f0419544500e000c2c0030741c01016018a001e140481d043d50303a00c02c9050b6001d00000d0880b550345481e0413603188542ca5402c1c4441c041203c5041d1003007211020300500c151140e604010782d0406161600700412106541d400200ea80070b1041d5028440340c051180d12301ca100d040140341240c00c4114145420450001e08005802c0c009001150100d000c3d03081c02c0c811a40e10356401030711004440f5015030581d43e603600800360a0781012000a0311a0000040c1003269505d03210404140101c0300190180c2e602e40b031410b0100c8507404c002400210350390b8019401207050040000d42c0307400303a110b4503084821665414010415488602c482c14200350780082c054040520203200004c0160354800850250f03101d90004d240540003501d940c1f0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 734658624 1250 734657374 734657381
    0x4050c06130b030c0a110c010c11180906100f050907031e2309030723070306060b1909060801061202161a070e0607080c2109011d1e010201 61
    0x1003460191159503810004440c1320740b80c0c010304416010440c0030100001c1420042a4603d0600c0c044c2c540c004240303400e030740f1005240f0405503019031040b010100d40c40e00d116490f80d003078800c108a4006019504082c6005242d20710310303510540648128160a108580300d01002d26017021481c00e02080c410548405140014042c00da145511850b00d0103c005000481d8500e41007203d543d140308482e6111920744603128400c90300050300c000d5031071800c0c801025606800084424613107043d1080e4684aa070799006468481c1d01440d4990f4000c140c00b420060031a601980c030b04994208102c860345011406004086e05200d213609000881044015000e401d40441d07140180100660412038194901154080306a40b0307404a0341c036400000401c140d01400d00c2000768a401418a410807030107a56103d603aa000245c1c1100e1070150340d0382584090541d055100c0d9008140d02440d0710340940c50001000401c8142003078410003511031600390b55032100c404016501410410030042d00d03890300d0050707015 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 734659874 1250 734658624 734658629
    0x60b0406080c060f0a0c1a0103030807031103070e0411120411010f170703060e04030210050c0c0712050a1403030405010f0203070903020f010309020616110607080a050310050319061404050c0613 85
    0x405056152181d01d1a03e41d29006060781d112f510341c081c1d203856180b81203044800b850440c1098500c100301180e01c0341e0003210ba04d03241500042c00812603655110101d9400e4210304500000d40d40752000380300c01c000f1010380d00036090200b8030340f0164141e03504400400c200450803e0b00380c01c04a60000c600120710a8000c040900803076a52840c040c00c207460001e5407081c42907002039006241101240c0c0e0100c0c0001224207120911004022603814916007070290551007070104c0d20b612842080300c4c005081e01443d208500002c0002e1512858141401800d50f0b0f0310807600c0c0c0700d0300d1040003049911508030480da420703a038043d511108808103c000513401000c1003640a5840040070841d50229805c111194405510070f030b00003400152184280f00d824020707107000520010080c0700452050388104055603005600282e202125070740c07280464140300408e100c43c2200f980c0c5200c150140455805102c40c1c803e5504101c5845160030344405407039110141c0c20b02e220b4200016030742c07a44203441100300c02 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 734661124 1250 734659874 734659883
    0x7050f030610030308072c01020607030c0905010e0402120405030406110a0b070e01180b0c010e0105040816050307172a06011703130902180108073009060b0406080c060f0a0c 76
    0x106a02408050001f4030712020150062240c0400a03440314403c2c02010300c1d00f81680c5480800304c0c1030a0066170b22004998000d50050b03800d000d17007010104a80856402107003d2005181e0360303424490700070150510803002d03411960043e010310300020f40a0315061740c00001d515186807001ea000c80129221031141003442c504c1980390502060140011005111080e01d0380020018465401030f450b00f07840381218040d0050505200250a0390110f18116450b280b01d0030540c2d24044499980e076000c1030204c894550500c40100308840c001c5280d00000d031180d0848111040200e413070120310f5540724814041c0741e049101c0d1629000c80500100140e40c00b9200c1e10858080c41915184074400a40105091550a0341301890107081d0354021056035018107151781d9440c01411940002903c02680d901c98851609039080c10f55080040b2031281e584114071407440450403601c1e0108200c03d461640c0c00c01c50235a0407d01d401545a41c0d08011203510308200c0500344d490b2030b10b0000596820714031440252 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 734662374 1250 734661124 734661167
    0x315031504114c3f0e03070f0503030609010e01030209060d2102030c010f020301051f0507020612040b0c03090d0c0f0c0305070f0f180e071707050f03061003030807 72
    0x1e074441d0400140f2904c0c48103e4106041c00280038105291303200003aa01c510050843d070510148448141c004c0740080d103084040320310701201561203040c0d00061850540d040d03007020060041503d090082140100b0300c8908070030300d80d415900020340c00c42001c2c10051080c400c03826940d0070065070b0300b100b51401210600340580494046808ad4a0303601c4060b03181c849501e00084107a500c00342d442641d0585402501c800c00903200c191265a44c000150418001d2010507c01d04005035105030041208000d046080c40c180e0803c0c0c50240b01c50040901030720600c01060082003603040c0b0000705144003213800e00d4224003824041c184004060080200076044020304c0c44080188000000e003103044841c0080d20810303d170703a5034280e0701179144140a46151511444802d100c1c0d5121794000025501c4c0c0d00041d9a03040e0307070740c00c0c407000000c600450074500c0381c115003400c121a1501821100030000c050300540094a0b1001039900801c515000041c1481041c60100c0e40301c2d032003046240040100d41c803005 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 734663624 1250 734662374 734662519
    0x4050622020408010b1f080702160b3013020a030210050306030d18030b25021f090c03020d0f060504080d05070c021302031503150411 59
    0x400a0b51050040500941c2030014a0f5101c1c1001a06800350f0004603021900c44000440112a0410050709003411441842000c01681100307d6a81c0018100141019501c1020000903260b07402400726070a9a948401c0909440c80d40407400340754840305006100707078041500c0c400540010607640010f90003911800480541e41d0f001001140640000c5085503410f10b45140c00b160198402090b03443d8000c5082c1c2c04000051140781810b40042a040724000b40119200502c01104880c0c446030006910a180f40ca4101100c0c1951201c040c00d242804d110451180c1c442940c4981c0510000303000301021031a1000744a056858800b100d40e011805205605240c02e240c040ca400640b4910741552611000c501450b0207520100d19013507001c0c143c100b0588080400c0c1c8000d420042c00c0ca042e500d80e041c1e240703406a809000baa800e5001010345801c050829003003c6130a0100f1842c501c2c098400d542482020340a031040c10101c003840d000110807810301d099403480040000c01c030782c8043c1c01e0f03500003103 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 734664874 1250 734663624 734663689
    0x901092927040309080d020706080604020702030a030e090702070605090d06110a0806030c0d050a031211070515010b0307090e15131e1806150503070e09010506041a040506 75
    0x501e802a40a07540b245402502d6030911500c035040035040e03901691189804200e207038040c04020303130b0203140100f0042c10840181c001c02c0c20034141303050403800100802200350681c64101400c54101c4024070060000ca0f04140c005802c52042c0d204281c0304e252034104e6082040341c6600041d4003403140740302041e1101d181510250030754801b03444851082c003603114520014109040c0c2e0410050708080103010f4021551030946246d1319002200d400075448032028544504200700902c681d0340305074000e20380c400e550085100109810b030810b10340389030200203001c0f030306502411460a50740220b12504541e100d050100e01055042559590003980c000c41406200c240340d80034903049140c2c2c616003564241401030784030458000e034100c0c00404d408402c0d040c0100390550710810b203100d50841c0c02e0b2071590301c031800079140c0350040c0e1001880c0b103411820411980003c0c01802e0b044003003901d0034490302140301542070754005421060380c0038607500c00c001002030f551582c044110380304070420418500b10000340e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 734666124 1250 734664874 734664949
    0xa02130e011403121c06080708030a03050108060601020618010b09010f03060b04290102031b0f120f030a0b01031806050a06060c020d0204020f22030209010929 70
    0x91081c0b08403080754410321824042a5105103800485985140600e040740c0050040301c1001050b600c3d6554120100d070710101040138034098003078030004644039102260020242c500c144c2010031540c00c0182403161503600000c072690001803101d0410455400400864018440040201c0e4050a00800020464010a03141d02540e000b0307001407107107141d218140400d4071410041c1403120034a43c0c3e2040702c005c800c1c05a06201610510503203181902c11243d6a40861803440b0b60007203a00b000d404906000c0d070410a03030b20303000031141c503140c00c1007070f5900500b0680c0030081204e52104e80b680341079003450384a0f03802281070701c1c410380c100c1514014505202009210031074104402c4d41c43c10030042005801040c40c062025401003645803141140e6092101940082400142c0b410041c07003903208402e51424200c0c6180780308148241c8a130310f14010882d201d03006a10902d55185030041030034060f444076407558a4540c009110300c44800c0140085a040d200390080521403103000084150048a800d6 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 734667374 1250 734666124 734666129
    0x13060b0a0804050c0406180e070b0318240103061103150111010b0a1806081f020306040e0303090609100e2104030206030a0207051c1b0519111203090a1401090504020f070605071b0206030a02130e01 86
    0x902004700708044403003071446220640b01c14002e00130610a01600b5032281e6860600c1d2964000042a0320180d0404201002d241da005036000041d0310034110b440c3c0c0d10511411000b00340070340c0140180c9104140d00110701032000c060361820303600000015001d85a5400c0003180c2003044040300c0c0d40f4901145041c1c0c841d10706680e52035190040720030194441280380a40c44000f010040507001110012030036010503000502e4106648034240400800f580e602c40c06140b00f40090351300540d40300c101c0c7c40d144c0e061019072260450700002c0c8602c64040241d00449011004d4800000391500a00c1410300c1072a02c0502c0350086001001c100c403000c10401d04541c00c401085042e00c1070868100d40c0001c45440340165003110f03400c0560300301b0401038111031442958101c00d040c1009110641c8900100c3c06a0344201d4584515032400580c1404000c0203118140e404086890100c0c2507400f021100c041031100c03c0c07006445000c02002040030044160b044500f1440d814500c08803203aa2a04000d039240001d2 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 734668624 1250 734667374 734667383
    0x2703030201023c0d11130303141611040e100624020d080a020c010213060e190611010b18040213060b0a0804050c0406180e070b0318240103 61
    0x509410280320020030500b0100c810f06107140e0100250b070f0445212a088030881c801035030b44074100481448500802000d01664152a0151180c194240904840400038013096070355810081d0301000a100548004480e90184440c0c001c0c81d0750a001402401c0e14510840c03d90240702c8400c21410080c0d8480c3c003c07035010794160383c030003100080d19025607800202604056044500030440061042d516240e000700e031ba031401410071059405960881c3c00c400324411400d0900c141c00d006481e001918070b101d0040c1220f148507901c41c004000341c1411501d12a2001340700c5a0241c10700203110a400005000b00d0140800d10881010070070048500000d0350140c0c0140020310446900d4002d6010b010141c0c1c0d40d07400c1142c5003401e200703000ca6410700c0040040da014003035415030102550310340c00b603d4000c001c021904007080020304011021203211503808122907000c0f007000c00075084d0210940354010b89558025496103144030880d03040c4504c0b2751020207425851409094558401c114881c10381c0e014 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 734669874 1250 734668624 734668657
    0x1c02030f010c0503090c01110c10091a041409060a0b0a021905030a09080f06060d020a05041e0f0218040b042703140909040f080f0d020c0f03040e07270303020102 71
    0x20540199505000a899213449401089d801220390070300752100282c4144914000030815034407005494509d46104810400d09400541041801c0070030824004001045a810050703040a20000f05014558401c0001080000c40e880d0b807594002c0c00280c2e8101c800c0030700403040c04800e00d40a904d03544a0400e48010505070003012442450001310130a05403005001400c0d01d840d03484c02c1011180b20700c0030480c0e0105201030046070b1515603000702068084034a401e04403880c00c0e807191b0000d441542c130b01c0d0000d242c41848506600d5201a91580e00d060040d100000d10321840c0d004100601251031020014100c0300080e10840c010381c070000c150701070090740c411981148144100e11244600d00f4002c1c0c2c400700c00404200820541504028464400c4074a14030b0458421003d610350781000c14030305038040d07000c28111460074080c00040c1c0101d5150016501c0c003810000c98041c152800340010003001000c2c1034060a80e40c41140e0702d10400c1000170320542c1d4940c0da02d0024040d6011045030481c13101c1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 734671124 1250 734669874 734669893
    0x709050d050f12041206020f1c2901051c020702220c09050d080a0c0b0108011e0608070e070c05030315130606050910020a0c0e010e01060203091c02030f010c050309 72
    0xf4242e0a49050340c0d925643c800c0c1c90241911a00045d402159520404a07001c1005d01b07400a140aa07513a44d4048410300402c01802422039101c07180035800f0014101e822180c1d1000c3c0f107030390100031610b0007100d51541d500c0c0c030354041036040020702501070000d420441c1010046054000f0b030456504820300b990060142004140d0100ca05121034450f154001d240030603041d0000b2020406004900001d2410b100c1e807010586a42d11090f0003030340002000d0b5940e403503106903181c0d070681036116401140380901586160010303031599240c080c030414a0b520350150126070110322420003004255000403caa86a081030f80c5600303224804145a0b910070fa004900407507411a440c0210021200c0640364103060802d00b500340b0240c05210340c8074801314003172684c00400154114a61001505064203008020341c1030214544a880e4181c1180043d5030080c03100841c641d54000903010350102c0404448800c40700c500c0031074030b00040007805100e59420010905503032903008000d18420300f000822221241e6 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 734672374 1250 734671124 734671153
    0x5150c0607030b060406110c09191409210c03030103050d030b010c030801031e05030304060b01020d0c051207080c0f100c0f021207020d080703030b01080a051302090709050d050f 78
    0x781100c583c1d6030411024081000750341d0040c03c03003a014007505e4042d20402080c800c00034011001c11156040000282100504c440000e0701c1464001113a00820180505081118039a83c100031500715548400b403034812080c0010880039075022104100880303031030b540c40e442d049484a00d00c040040001785030036800b0300d107503110f9400e0741700040d01031300ca450303d41e4217646403c0595051211641d81d07020404091000042c2c0400055108501400c40062590b151a000904007d01c0c040d07807408006030744000c032012802c0818280c1d450064506640e55500c00d61602c00c0c15030003860061000d030300030256444446070f004900c0d60b03e07003520208104410900924261182030035104000010703404180301c400c15040440050480c180010080700c21442c41d40e41d17200456000d40070440000e901d82c84042c1480d40c0000301160020113458090005140051039841000301d130150103031140500c0310104010b14050788109006e4036019103c0c00020140f810038a90741c89001040c0646172042001c90321050 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 734673624 1250 734672374 734672381
    0x304020a0e160f0521090705031905120405061801030b0a0e0402030f0d05090411040308130e0901020703050d020a23070b1008030306060f0d18050615011b0c05150c060703 75
    0x11790942040c2500129601c10795961984000c0183d03d05106800000c1a980c1c2d0400c20301415410058030b07058490400c2c540141003d0328103c440d607500710240400d03c00703a0b071008155102034000c420030100f0903000400481c041c040000070b00da040805001c01240309030558482d07600c0b49009600301c0b101404021a0180d542c80d080700b00a00051040c09880ca0320300c0c060f0000400e140a0043c0036007016180c1d22940060b0381704000c04d4071800c204000800c00140a02d0125600c01d006400031414180c50780c501500501c078200d90118800e900140d1151060b00880e0001e20300e07070555001c032407403545001d0150040e512005d0203952245001c00068800002440320358240c0e04a6000782d819621030106018550b0400003041c62000c009108005070314800e442800c00803401411911100b10103070400710f0030b080c0d0243c04071031119204140305c0c03550790700a00341e08542e88454a4462100c5817a00f4031104030070310364002e982e00c91500c2c1400c500c005c0c00e0320003900b4141010070035203250340c454000c141c040303 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 734674874 1250 734673624 734673637
    0x20301090c03182d050f011b050f07110105120a020406030f1b0c210504051003090317270f07060c0c03060207150f150501180b0304020a0e160f05 64
    0x2924100e10a02e81a481c0c2c492602c6076481c1c04d09241035684040342e07039181c10715806d21092140c81c0c4d03681d40003d000c00030a03200141c01061b1814928604480700100d0180352060b583c01505442d079002107042503034400c4044a2000c000c0591002d460b0610b148448040d42c8640b040c000001c1c105002c03000760a100d845560a1000d00101c2c0c0c05481c9510b080982d01d8540d41c420071356041903a81d403030b00010b00030b0b00f18101440300c159407102d0781c8a052108000410399004900c50400d86031001c6240003070f0300084003c000308640140000580d60300520060780c5903078a01b8405001c0c071500d001044405002a07800c90092043c4d01360340302c40d52502000c566140d80c410016100c010029402c2000c900c041d4010f0050030300984404602c3c00c0d25007001402d4644408444800136668000c250000910a0b00c40001d01402d1a01c443d4010149070081000340c10f174000e40302040d000001150440d0b40d01c82c4510010082c1c00c0f03402440345440201c82c81440440103000000c2000f0541c1c00504034483c1048490 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 734676124 1250 734674874 734674883
    0x91e06140a051e1201060612020f0d05040c1505090f04050c0d05090109020a080604140f03070311070527070507081b0c120106080705190b1804020301090c0318 70
    0x141d4a01810018003030786161295400c48000702200302c0030b86502d585405100750f80030010894600c0c1441c000c010100002d52003a005c1d00c1840962860031107442100e88c0303d100180042115180e50500100194041d44074050542080c4040012103411074064480780004507411034450800505200030f90340b00b00c900d0380c100d000c04c010496600d6443d5000b250851814000011030f41c417950301080661111782c0003140702e54403010800c010480780141040d80d0038216805032100f42e40101c00150749004021004003801052510307001161820004080200802040341107080350001c1d00f008001e80c002c204000c2401040f001450f01c0340103004075004181d122000078070b068003024201100c415040214501800381c1000c82e2110365440d14524041e40000000054161030400c00500e1f0910b19071255000f60003094825502000780019138045550341c3d41003035540c1da484440d80c520001109452a4042d1010002040c946142c2c2c0c4030107a40325040c1c4040051041700500c943c0d42004005c0000c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 734677374 1250 734676124 734676139
    0x806180a02061b1b1314150d0c0b03100603060303080a05060d02090f06030f0c030d080405100905030a081302130e01020403153c0b0a091e0614 63
    0x2801810702c1c1d4020042450b0501c2074011a0806880c2c035424a61525001c114066454015104928202180180c201251542000203200450f103142481720010f01200b0081c003690303050b0310191100c000c06a40d040c4d1240c0031802c1d464484a00c40d4943d0001c0e60b085901c0c0c5a440c070007007501c6c1c3c081d1040c0c4082e20f4060321449070310b5a4815501000c0c1100503c0b2940024408503400010b1300c443c1d101900404404800c0e03505d610707000c428035181186414000c0724543c440280318040f40c43c0494502000300a5240c0700300c041c0c0d5241812460507642403c1d41030f18a140c140c402041c002c001c0003400154405030384008a0b91940c0c110398922029100001c1e5208900002e00e201401c000d502a8444005600c000340c241a6240c0300e000782d5108000d4603020564440e19280c0c0880302d48101a0b82d00b2501031141c5404044c0420003842c0d010341081440340443d911584007004d030396400030f050000d00400c6c0042c0014011030003441078000c00140c41c01c46560501d0800700b8081885030790b4409100c00908102e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 734678624 1250 734677374 734677393
    0x308070f170601050c06090d030e070b0405040c0e180906072f280605090105010303050315032d1c1d0a1d04030806040c0f0f12020a09080618 62
    0x41000300e001502c8141800020041584c1c118002c1c41494800c6411401500300c2c80104c80014090304e010101d081c01d40d40200105001007103814040e05c00340c1e40103403800603020621005c155180c5440d0209a85e10402040000e008820241c80a5118000c8074080c0c400d00d454401c1e0598491220705d0342140300c00008884c602d0800e000920303031083c0b080741c002215414640000c3c095110071303407407450ba03455035014a480350900481f070013501c0c0c200e08064000c0069614545005120380005041c80820104440302c2041581d8108100040138041080e10607060000480701c4142d86207810400040d40142080da40c0c1c0b080d004211074400c0251901c3e210012110408080b12031400d0800300b651109108501181300304c403042e544a040702000808460505090502421882c0c00600ca98451810a15450941640320000012521043c10903506545074a181a200b0082c00e8644844091020070303900130352503121aa00040b28854402c0e24469220841aa00d44403e80000ca100c15400401c03807 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 734679874 1250 734678624 734678657
    0x1020c1018440a090b09090708040501020c060c0909070c15020c010f09030e1203041d060d0f030306090b01050304052104080102040303080417130302090711030c0106030308070f 78
    0x1509030982040321440c1e0142e5112000e001c0265200100c1c0c450620040303515841d00f500034685002030180401e107241049521000245110f10060130501004022404036080003801d4040e52240c0201c1c00507a9030a141000c0580101e81100031060700c01e0081d80013050425002d980da40c007a045d04a00b4480b400100010000040d50104c4009403031503583e04010100c000b081d12400c01840e110355100f10152408100300720b003010001041030440d0300204010030000400c80554180034154100c1142240d641e2400181d103100e1046003d0829800e55016808241d407580c00601030720b0b07803480c00300003007446000112404c0c001100e00401c50307886440041e6070399034413010014500140451461410340c0356601c16099821951044000c1500c0700244001c121b082034802d541448004003131414449002038500c62603100e4270003c0d0040051201081c240345c49100c240ca6020041e004481e507030003054203824003d003091b10045d400110400c0204c0c405601c01d42c2a1027442000b41d5801c1d08180700c4003031 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 734681124 1250 734679874 734679923
    0xa05040c050702030712052103071b02040f1415090f040c050d05010207030833040b040908130611060711210d11040602190f020301020c1018 62
    0x30401481400e01088005a41c200b00d400c0141040c41328501442c2858500355180450f410780780c110001e03442940d0040714038180156540440c0720b152898040c040303609120b518055101002c0d4005041005a82d203414a54008001202c5041c60400d031580d074400d0001d5081000780c102592180240d004a042d900c580521140c0090180d80d003801d51039074a0300000c1480c2584102100c059402103641e000349a000001035901c5209921201e55003915403003080c4818442d0014090200c0128110380b07600c0d1100c0e44a0418440041c100b00a144800d00b001042d5401104da0301c002841907400100f02c0911450b08040b01d281780c0b200a240d55114058141c891041180d403c0e01e0510501822030021003410400c00b0010540300710035030b0349a20046800003510015481091105004c200401006a000603500c040414440c00b00c2108c407114901800c04200c000030283d815800451401c48050002c20111310f0442c0c2c02004110080186480030070035054844080c190022198201100d5202d102 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 734682374 1250 734681124 734681141
    0x21603030b0a090e060a0c0e0d02060a021501080703060605060a1b150903120506102715082e061b0b010306050603121903021b06010e040309140a0504 66
    0x411031480d0381e446803151003c40d461013909494039449041403044241e064410880c01c1041e514000b00302c0c0340d01c0404a9000d070800000240141d00c0092200f0782d5070f100744521030018126000e121080d580d12009659207030b100340002e456140c60800e0000d403924103031046960b0003446444821138146500d040c2c5040f4100c0040c1030341c142d6002a192a2842e00b18498140c6143c0701b621600d00104880c0c403600112a00100782502520340115104006034014203140f1018501d09040c0c040c0e4034406020b03ca481b05941e109031030701d10030064034036002e6800850442c810341d007400071030742c812340307160300c50a0920410b0070a605001c0c1e00020078080148910f440103080301d00c103c18a40c0700b1b4a15070740c069490038241e0007681c803a940c030000d0090900c0d0038020004d20441a40e5600c0c10180401c8112101d144600034030424164000b54064001d0040185072030062921003e49a8541e9a805071144d0720900700c5044000640340d1501080000703c654248040c058054042004e040c206002d0000070207066 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 734683624 1250 734682374 734682379
    0xa020f01050c0303010b03010e090109030e0f04061d0103051903090e10030b090109060501080321130507090f0507031b18050307180b0625030519051309021603030b 72
    0x20802c0500c5041c0801c0218024002e86084940d41d40c0342084507104584050304d020000c1e414045160b0110354023400c182e21045044a075401f007440b1303200005008181e150f01c81c40c50700e4010190411000d624880c018100e13030107542980c0707044500c0c144110810002840090110b8410b0300c05105c280e005e5502e80364040380314036010b641c26483e038940c1408846c044036202610780d1100001e1040000d0b901856006102050065040c2002c0101c401081110080c11841c030040207000141c48450342c1085100e0720b034100094400403501e41c481480680803103035110080d1410107010030b102c28860b10070380001c01c00d242006540d05c075400ca0b08842c42e042d0b2070040300d03c4007940c000114940d501404200c0061920801e802060001d102c5050299200c902d4100d1103890244280d50701c00c000146000110900c00b07180c6200c03c2c070240f030181c8050042100c2d41011340b409000614410303420800501c1c0700700000382c089110341c1c1d4508503402030b441101e210303200c248900d01505c40003074040d0f0010310700c00000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 734684874 1250 734683624 734683627
    0x203031c0f090f05160b09040209060d09051c081006030218030706030e15010305030a0804050a08210901062102040f0e0705011b0b010b0a020a0b0103050705210a020f0105 75
    0x622100426201d900500f40d40c0c11520301d502c0010090100030307102000300801c80e4200d40354a0300c031140d0795a001c0c41c504a070080390000b900420950326001120f11001040008124440450410300d81d24100300c4110703d010921040e40b501c2550080030307a513218110f02a682003a19080001c2103019400c00342507141c5400900314408410342d401d02c40710700503162035900011001c0040070340da454015a030000c110642204001031012030004001c68103117407100d080a421030345032403070003602d04621644090b04d66540030881c03087c03c404004010360780c1c0381c0300790a000081c0c44120441c2d0885480b481000d1103610040d110503003080341c0c40245080240020000200307070901580c0c040548900c076055100a401c107070b038180034568200a400506030041d11040c03640c01c071aa9114642c075101070082c44822500031503c8041c05208101441000754000304540c00e83d40d4074607140741d55160a0242d40d11401541650002408040c81481d040940e80308c02808030345496024030000282d514402810083c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 734686124 1250 734684874 734684891
    0x902152215021b0609062a07093b0f070b0306120706050307031515080627060d0302031b0a1101140d1e090308090115030203031c 57
    0x200d100000d002405101e041c40d94121150307800070f00300004184005410f0703c00200b021455140d0500b520340d05481551600c3d580c01601c0254503420401d024107000107100e089884c00d10351404248881110039980c424040e00100b0044e09814004069120036440340e088860700b0440c94068402000451040c1600d52040a480c48581000c0d215008821100f10000522400342400c04d5500382c44543d54001e809a02e041c00001090b030300c005002d83c001c1584940703207481c2402c60285800c00401070303004400c07044005020058400030701152010b1042c0744a850004460178003009800000c5a0295a01c02c40c2d501e80d000c01c569104010001e604502c030602950060700c0071079042000b2021000300510b81860589003034804100d00c00b003030b1070400c4212106100500c0c9040b041c1c3d10700890000000caa05140e05100510b61003110802c1c450650608051006250f0030000041c0a210482c0c000d024105e1000b000031845c0120740b000a41603842003007054511895002040c94802900c80301044908 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 734687374 1250 734686124 734686177
    0xc090a09050f1b0405040e0312132003010f020c0c10080c1c020903150f0907030c060c032106170a0803011e05030a03091d0606030705210406091203090215 68
    0x20487d50b1510025800019015a80f60300100ca00741c0c000c80e208001408001c0550368000c11504211002c2640004a465180965000e41002c042084802411504d0340c9800c01c0840e17a81e840e20700300324021813076001c101001c81e218207003c9104480c0c44054500c2e10000c5e00c1705100501d10006100303900755003800042c170135550501c68440406e920400365013050910031903015103514080c002e412264007021007040052040c004000841c1c1160601d00701858440c201540d001084041c052240c3c0f865452201844c2d605e81e205030142c4400c402040d0205820f188115a5030200c110302400c40079003400100120b03940c0d0b001082d540e048490010440d9980d40000c40d04e0b014000d0800c03804642e8901080c48003210201c100404001e03820701000711400d00c0c1004c036506d884058058020840c0000320030381102541c400744202d00c48800c0d0480b40f00d19140c10160010074200c401212121242e0000a1500c0e100c2c1c021008043e4000700110107543c1c0c00c241c8082c45a000c84116200c00c10454000003000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 734688624 1250 734687374 734687381
    0x2010219020d06110901091d010e07020313080115060e090402090c19051c05040b040311010207080f130b04030506070810180e01050123090c0f030c090a09050f1b040504 74
    0x440d9131031056925055020009425199107401c4024200c50805190303003d0803013814207134110307a29207080040300c0d04d0310a82241188100a41e03212040c1603031600040a8105500c000349130754214408410868444400315800d0602d8901c6c15440990350010401501e441e032421a00724580300340765071808541400c0c0501420300a070900010400110b804071101040c0e40006440b4900d0304010002803a1a1307407140036500703000d40081e040045040f020156040250304940440350458240d68171200550302c23200580c2d0005d10b504508404001c0002070b5000c0741d0701502d0550f0b0b44900600b0b0b86035a441c0c000c55007002c0c0141054a628501040081c0564582c080700c1e54518030b448012034101c00500340300742500c0b0180c2c404900001a1100c00e2006844400786000002003110745030107580b50a03000b0106400f4509201201c04800003c0c020224200f900400d814501510303d01081da0340c0f0072481c000c480c02160300f4019035031120700007005548518130b0f00f00c40034255004a402c0039101e50208044 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 734689874 1250 734688624 734688641
    0x302030a03080609420301290102060405070608220b100509160c080c07060807021506011413091e05010902071101111f050f1302010219020d06 63
    0x42140c071424030105003048140d0135444400e45404400350445201070700e1810304d40010364540d035030480c08407400c80c001c5c24a45d0840d034803008000f8081c80ba070140b641c1070000450002251100840b83c480415940042881803280c1d40081c0900046450940190b480072001004050001c8a40c2681e41039254179a91a01c805401130f082d42102d460030802000d4a101150051442010100e0400007200140c02100c3d040603050b1a10044072212031400e613205002d900110b06e10360186c50740c0495080e0340000e050748112099400c84101d0002e20340407013038110096400500042e1a0140351003201041d2006105249603d44030159490b0784a800208a44880d01c4080c02640b8010440d813000e90140100c901418404070214600b85e01941c07118004100383d1700c901d051228860f040f8403020014020701e0009080014500086041041b03040002e05040340c0703c022403031400b00401c42c098030405600d05002d0341078005103c00420342103206c074440c07084403040380c0c4414014650400a2014080e2000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 734691124 1250 734689874 734689877
    0xc021018090f0f150b16210822080901020a05010608100e12041e03060c0206100e090a03082e03170708030a09020a0e090708120406090e060a0302030a03 67
    0x20001c0301e000e04034081c0c3d105441d4900c003590400d00c84502d24003400c0070b0b0804492140840540c0d8008080301104062601e0784007a0a002c1e4480040c10b0a601c280c0082d0032100250303032410b080d6507031040c1d1102c69891819014264000750b507465000600c01200400541030b0500448228043d0b50b92501d00b90f410035004880d042d0403090210746080020300901c05500d0b8080042d0000c0d00d03241c0d040a60714003640c41144e042164602031112403203540030800001d9504400140310304906003501030740d14001a00e200c0c0380c28641040000720841c21190080c0180c0141000e40300b10421602c044940400c003501042ca15289010591140411400300c1c090a40455000c120014a1802e090a036140d45502d0502e2141c410132003040028118000c50341d02c00c9601c0b034000b424859a0010818809158210f103141d82c000f0024861300d1540040e641e42100c0c0180e08440d1348035441c1e0341d6442240a41d204140100d45243d2051142d0300150ba030075a405140500f0070031049a8a0300082d250982c0b08a0980 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 734692374 1250 734691124 734691131
    0x1204030918020c10020f0f0a0201150504020703230d150302090a0615120207080f0702210a11040e031c05090d140903101a03060a0c0c02101809 63
    0x440c6111000700040c074682007020450400103c22a8191038488a00c42040c0701c40d40000d000e001d000c02c00c2c041d00ca844003a0800e07141c603102440b502030300034640d03070500402202d14542c001445251600850303484950507643d5200d030300360b40c2d440554108480c0c000c2003d40300050202d000c06440c544185d03e0b0102d403449121000620f54010b000c10302002504104000382040020301500c0e24924448080c1c0034181382011a10039108481780090003202402050350a0019641910243d06005804058021206039070781c15502031410044519200c0e0a48041e0041c03100c1001107081031132813140381c40000e0808140300180400319801c5500000f000e5103003a1001c407284080455a100d0243c0c801400c000424420350702c4d00d00505642400f4000b58030410000400210030b0b142844030025407503e1880034000800b0801480c06600c4400d288035000e481004002031104080b4001d07104601c1407911507001060b1281c0034000c034054040d500100b80700c000b44100c1c0242044d40851f2006100089001 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 734693624 1250 734692374 734692379
    0xe1006030212010c0206010b162001021c0e28090c0206010602011e0203040813080124050d110d1a010e0606091003020306030c040912080105010c08030403030203070512040309 77
    0x30100c1003400d034101401d60700d040d80d04c030f9006800049050645007100500c0d6160310f240c19030640d02c14127524004100d00003031007800c0e4139101502942c140640c4240c00784c1c0e082000103074490512035851545480080e0545180c1303407943c14080d440d109162001e40c02c1c1040c5125007012484080800d5003c200301507683e111401070140c0c18482d86002d4052403009002d1a41c0c11206603001c11024040d144d2210b0b40000400c041001d0401120401c20103449550441680c401311740f0700800c0c18001052483d072039a0744540420303007407214040503242c000300a030700750740d070740e03407a091003a141d009009904000c030b0148441c0803c035401251024480d8020750040203604104044844140181000b405007a0902502c0301983da128036942031245540340060b00d95a0b810002481e02c5050004150001d1a000d8890144040351185202d041c82640b5142c000740d036240c00445d6601010760000e400d502d014030101e070004e40701c0d40085802000e140b5159007003020f040142d0b290b5003030a07142200800c3c4004000c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 734694874 1250 734693624 734693629
    0x9150c0d030b0306010303051e121816290903120d1a01050702040b010201110d090605070f09140d060e030706050109020a120b0a1d070e031b10030e10060302 69
    0x64190b03041042d40501800d514640e00502140611080c0c1c05000001200000ca10075026041c4d80341c6003090184000c079400c1c5188030407418154209642010b0113007804030035030144049521b20485042441c005a1031681c8802054031441d01003038180d20100130011a2020390b0100f0141d01003109251034540d0341c0c5c00190010003101c003180c0003081d03101509031010011741e070880c003524095901990003003901c00b050b1004070300500400c00000c1941c0008201801a40040d51091600341d00c0703024104007030303110710740f040e1240c04204900100282c0035103c180001d0f0031222810300c9114014104030501d0000c7d945120a994503154a0750789603102185e0b00062140d5805020b0041c45c1c00141103203044a0500300902c43d140085022481c20340300c9a40c41c505d511011101c01c011322601d602c0030350b03405e903001011400d0442540d01000007003904400b01c440b460f01082465510b54402e86a11080c5001402d0090980300d01c09140705059031a191080e0b044010300c052100d25600940001d0002c0c1140b04 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 734696124 1250 734694874 734694881
    0x91002040f090c020109150b0f04050c1206030109020609012a0807032709020f04030b0c090916021c0302070204110c010f09261b160b1e09150c0d03 65
    0x550011a0305220100001c24441e1f2611340c8455044880400d202c0d810201250340c82d81c440741c040d034115140c0742c1041054413141000c1c1150078030402c0107540c9138540701c080500340c892900d0060351181003001101860340c011640c0310907043c00141e44400070003101405680d85e15103903505440d450000a50002050f41c1302000301101c4401103030303c0850300d178021717071640507a450390042c0710049074000340c00c061311500c202c1920700465001c02051114500709000030200e4010000c06401040004040b03500030542c40781c9101210005d900a20401100303216110090140c03802c03401c2450707401c100340300143e102c1d8050780480800d0708a9417030352510601881030860714148904400c071407030324034010005000310b19003090f4030074940b1464020341d207445606505ca2041c240950900c840300d08000c010768a0126840d00a0012581c0d15130f18556129801202442036203055406610fa504400d6010b4080e40040e045118000e495042085943c142c0d51503142d0080315004030b00c1e8010f440301c00810b90303d0301 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 734697374 1250 734696124 734696141
    0xd050d0216091506030c020c04020409060801050705030c03150409080304030f0f051804050705040f03060605041109010e040911101106060a0e04061808070807032c0108091002040f09 80
    0x4403c00240f0400ca0300d444014080f805030b00105a11071145a00c5103100b0484401282d0700142708640d5a50f48200c0c0e40000e0401c0d02c9000155401c00c0300040d00240642c00b500c2c803c4001404151440e078601c44044883e144811845074041e80e981365100218030781a0145110354404d481c0c003d1000207030351001c2c1c41f4001a01030b04040040c1002903c000710b96528424150390750950b400300c0c0320381b40c0f00030560300d45c090381e0407039904000c07583c1d400403d004443d042034040b64000d41741007101d0441804080010b1040d8120240841d10b24803000b20389007419403003880f54502681c2046900b841c1034002a0490214640f42000150005a8844840c5040c8880d50b0007560446010781294501280740d07001c00740041014000e03940c4d5a1100d00f071600c00d45042c005165200500c2c61b641c002503d405801604600001d400040d0001c049005056024240040b1131000b84051080f0845e160011120850010240455030141192142650100303002401c0502510350001003c1030030082000c0c01c85402c40c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 734698624 1250 734697374 734697389
    0x506090f070515071401021c0e0106140906181603150303091809080a0503090d112d010218010f08040b16182303030c19020d050d0216 59
    0x1000308000c1d61108454400e41c905080070f56181c2060b4240300c0842c410061049503194000650004d241c804010003082c4901110b40422500e03442da0001422104039000c4d0301c1d0541c001000000c40344c40c0015403143c1c0701c400204031004400340c0c00400c151a003016100f800540c280e05108442e6203415005245100340000d0380c23040401c3c40c3d510700038000ca0191283c400c00311b807141f240340c1080384550000c004281d00207450756603640000380c2c020300303990007110090745074040c043c9100b070341d5480360414041c0340c400c040050000e0826141d103010729000303103c5111102005055051145502030002e800c5084013070b010f52200d00e100318005042c1800c0d880c03480c0f041000000800c00015480d9040f16000303203c1e8050022494a807403029580b040840d001114001031005000446204800082c501110b03004261040700da984400c0c16075071702550384815015041000036000000380180d40c40c00c01c2d40010f091f00c80000c10341d1a0581080c851032800300c01a0040300a100403480320003c00c10092540307 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 734699874 1250 734698624 734698633
    0xa2009041101110708030705060f0a2003060607020a0807090c080f04110d212003092e031407080402030a1704080d0305041a0907030308090307080301030506090f 71
    0x10381d0398008000c0200d2019043c000e203180748003007108040050201401c084821079179160103038244503691b000100c5404450380b078414009418501a0b00036400c1141d10a601d06004070000081d41001e50002800130381c002c81c0522683c00565290184100208110405001d406081c000158103407460050707005d0138000400d05100308003c5d030006907503100703400c21034402071142c440b00040c0304030b00c80000280489114103846059080d808a00b08051003003031321141d10140d41050000310045c19010030000c590001e104640440c100602c60b407800000e590202d07004128107800380307850158411035400000c0e580744150040070080401e920781100441c2094591071070035600003a554000c000e80105084100360b802031600c09580c0c25100900710038010340c0d81800c0c0100000340200011202918181c058074141d03000c11140b1560746004000d03100241120a00b03644041d10402170180030400c10744000c000703204c0810149405903010b175204401512650a014403c0ca240103142004d50029410 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 734701124 1250 734699874 734699881
    0x1401030b0607060c030906050901050603150c120c07081303030f03060b03071d0307080d120207390306141005031b03070f03030c02090c040e0a0f09050a2009 69
    0x503054180d031502c903444880030030766602d041000c401400c0c0c040030050040c0d0600707050225690040d00640d110350020f90807030788090a080040d01e031660301500d071004541c40810560400c0404540d0b100d900c2440a03c0c401c4c5028030954640400b0780c040c10a003e420000082d0510030036600130034401620f00e461806200140c1072204035049031002904420034401442c2c07401c0414000e4421168607601300800f91807086607240080b9403a01d1039002c5c4640014600c900028209a59100317403050035400200c00810060304c1a40e041410410b06500c880700e0001c21109e030324402c04900c4640156109040c04503080c10900c4008008000103801504a0401850184215100000c00440c0d0002c0d0b901125503001440c0d012908160058220310724031108140007200f496003007001150300c5c074030980d2401502c0c0d6420000740500c0c01940607001034407450402140016000c0d410510441e80d11700303c002400c0c00d46640d80791500d4030b01c0c00112980840d0854103620b040c403414400075062070075581c001041c034 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 734702374 1250 734701124 734701129
    0xf04032f0d110d0b090706050310060e19030809010801060e030604080904060302042a0203040f05060f0c0102030f0402190303080a090c050919390e03070b041401030b 73
    0x400d4200040e00400300010300d401880004600709500102c00381901c15140300700e04050410120840301c43c1e071a44a01c1c0e50004800b0301ca001201e214001c403418003212a800c200c02152041441d0b4411b6620200c1450304841c0e541304400c0080065202d088290303540c08801c0009064440f059000e082131000d1500840302989021a126034802d0340a00c11599a4641c580001d0080c25140c00c080c1d0450f10340220900f00020460182c0c00c0b2465241070a00c1141f00840c049903644500c0c0100d02c141001076038200190308202e4060688401c500c0680e6041a5005603480c2c2241c000301d541440a04940050005505046005040b41c50f010410311044c09e0840c0c801901100303000d000007a045e580c9072081c5061040f40c4080c00068600248590b100b0b0811018400100341030101919529180004180c107241c0c02c4011404d01d652141850050711904564118040c0d1202107520144130410480d1320b0103030f13010300030708003d0150405001d480764140321405050381c001614890606240011200300c55 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 734703624 1250 734702374 734702453
    0x9120102121e150102100f02090a0f05100c050a0227090102030c090609031908041419031407030b07020a050f010606270f030605011403061501030c0c02060f0403 71
    0x18201c3c200404991000d040100e02e0048640da44441062a0030115000da40c9581c0050803080f000702d402e041541e40b40e5204486001040c480c1c180c0c071044000780a185680a25100282580220306442000140e900031480c4140d805104458443c404008410b00012845a20ba0010101c000840c218545502095814030400c80114450003011401d6840d45d80d0800c0401ca4091018006c400700050501c0d0508443c2c015004480924212041c0940c0301d0800210180420400c3d80900c0700b402d03c1c40d20b440e121203035829085451800f03039100c080f021480c881c0c4401c0c041d80041d401081009400e0a00710b061440d800000f20917a4102101004125480440d404250a0706003002c42c900031400c0c554101c801007688074105001c0c8001001081c040c141e40403038101d421141e1101381e0b18011504058558100311500c1016401d0f80c9200303801035120b0340c03002e50222203c6c1000760070036559400041540d00522030101104000240074070400c80303004550014026103004210601e00c500301c4980c0340 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 734704874 1250 734703624 734703631
    0xa0905030414030a05010e060108120a0f080c0904090506060f0901050907050a440f01171203160f1d0103051504150501110a0f1709120102121e 63
    0x191a1005242c0401c1e541400700c00001c90380a0700800011045101940d210350782441030100c0d90159171216441103104034126400d42010b50303134050000000c1d00c001e444c411005040c8090590041c0040c480e203880e94450114100d0142c001001149400001c00c0441458102030030300400402c00104859162040920f410060310304145880d034404140c01c5036214071003004107462500094035203d0840d00072a101c1e0001305004000f141034250454141ca2004c0144c1c0d031000402203175801002503a01e00244050016000426030348512040c5803422000d4000350b800c40142d40d2454420031086030840c481070310100700c50818102d40f50841440f68050081d00ec8110305150f01e4100059581c01c610306450344402c1c00400400ca840745000781c41c400400503018050125010207540c01d80d051000803003058095000e031104d8000b104507566613030101509241003202c00810b00c07402e03040340c0e900c0c2c0e09c1000c0d4000c41d000058079004200c0c412009a500900154140124000242907070700080c01711710391 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 734706124 1250 734704874 734704889
    0x3020f121b03161d06092e0f0902030604140403020a12030f050717010602010b0a030602210705130e06100323010b0c01060902032e050405040b0105090a09050304 71
    0x2a07001035008070b41000c04105443c03d00c0b45420700003184c90010404000030640350342c01c0c0c09840d6138580c1c0c14001111002d485001c40743c4407070700f26903540d45c800140240c1c0f052001815000c01c3c0340d40e4070900d02e0240b180d812920103141c000c010045035003004e1050f485610140c412030182410240c038060348504e46060041c0103040501c1007082910300076000342912044c0858104024506144010140c4044e24140d102040005000265052050140350b21175a001024040b019141d540c0c2c180c002e5100310301c0034074010449210b98a03443c13a49007000744602015100c1c02e41d902e0420746002074176565030b04200b4260f80b43c6004d2104503116490303044040c0b0034a040004a40002143c401032803002c900c4104e290341e02110003c9801801e00018040b00f641c40b0009006003034440765000c06a00044402040a030900c0301c1010003034481c90484499440800c032401016900e880220301601c074112000e64083ca6820010000c504080d0314003540f01410f00000c20030105c10366101c40c2c49100354403070045c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 734707374 1250 734706124 734706163
    0x41e050f090c041a040521120d09050d0207080f0610061407020a0321021b100908010504061d0d08010302061e07060902030f1615030e030703030603020f12 68
    0x45001c6003200803180036101c0c040764030701e000c0700101380000309612074041c2d10700030411003101017052050a0801158050824050311226010308007100142e0041c02d0f9003c010307a100c07508100824018021000b545040c1d50261074020b060242c180d2070100340381d103001120351022040107000c8031805040e4096880510301000303640d40300c0281c1d0019000b4043d01950003102c404001080040b4030810f0010400c080244440031020002c0698440c2d1554010b01c040c5154603a416680d86405001c481f601c81c1c01d07003001d03000103842d004050300b115800c41e0115180d690b00c0c805c401c026242c0100c0c05000104820080014464050380240480d0041c44020300400700420522388500d03403001c03440c50141e4190400da85030a03076420100081d06406605902a015155880d0100d40000c5111610b8034521100c010427a8a8220b092000b8100c031342410342010390741c641c01781c400903003840100306850103540e01048075400c50040040340c4000360280e9100b210030881c4049080380c0404c0300f40003050740c2e140c00b4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 734708624 1250 734707374 734707381
    0x6010609060f0e0d0b191503080f070813060c0b0a0c0f030b0402043f122316030e01080105100c0c0302060c07030501060509060d02040504020d0803010902041e050f09 73
    0x10310459041c00d00919140c1c851082000d1000a00d100c1031803000f203046d0900c01d070040d10001458841d43d902000e40310300420010080304101040040011510400c0c40900d08202c60880c40c403201c8041d0051301c0010079140000003071003514110a60810070405040100c0e400f14040a41090f0354500e03034006041d140c208408199607954160760013031000030b00c0200715804840c0b4601c2518483e0140d4146140140d4001100c03c0907041c50207000c0380c0c44401b642c0d803401c0001c1c0a40b031540c010703180c1c3e0501103422001424680c0d110005070150149a03072003090320300300601e4040e180d014207400890400c000100100007590300d0200b846078082c03482c10840c0c402505410305001c11005c0b40c001a41091001038080480400001c0c1e900c21607005000802c0500c0d02c0340304001d00c0c40d60649410741c2c072003016103214015180540c02076402a2008110314a0200c01383d440c0b902e6600242d00900a05501080401900c900d401142241e01d0422103900102d90900c0000b0701d01110201302c042c0140c5c401c1002 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 734709874 1250 734708624 734708629
    0x4150201020a090e09121b16060f0c0501021c0f050a09030912083a2a02010f050a051008060f01260a060f0f05041104050912070b040506010609060f0e 66
    0xc2c41c01407110002001e699804801c0f020f007141d0700a101c0c1466a105200107d8242c00c0319880350403d427092a60b038041c1700342c8403050840b801c5403069400d5603155400c201c4651003800d2a80e06403441640e100380802c01110b088102c10440d80f004000c010660304203260031001a6211204009541030383c4030b680c005501d00c0c200080f09001b0845010780350740e480304130440b4841c030b4001202c2043c1e5062012404000304503c5140a8880c054406d540b03041100313400b90007940c4100c1034140462200d100006c0c60320482a0564141c07441a02e604a00f560740c0d10a0100a480308040800070346012001070041d81004c544d03014055005100e451a40b0480c00110320140031110081d000b092100700454804103024101440100951107500d6982494811040581350103070280b540302d40e41000703844180c0100d40040c00040d01005002011303c2c001c0c0421484001440e8000d82000d500420302c02c1190300e402c1c54001e10340501a0040810301948440402c06654044000c86a03100c0d20304d0100503800d01d080c007 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 734711124 1250 734709874 734709883
    0x5030705070f0b0f0c0c33070e030d05040302011e140706061e061205040c050604080606030c040509030a0e130903121d0c01080c040e0c04150201020a090e09 69
    0x10040800200c000c0300b00034001c3c1d103200c1e14050100c603c1800c9031600c03035040709403d81c800c070f40070304180742c012100f00c1002124507098544041e03456000c10740c01c1c690300d0780d5111b0041c0d000c80d04000404ca9a40b11850141001c001c540801030303040c2030192425003580c0019015600c031000507012164100c041d43d0849210705003c0684000c9441504c0c0c0710511880d000c000b400a601a0a081c0b10040c0d6a004116420402c024111040b507102c40480c41000e031044405072000a0065032031400318180040d09031a04070090004080c0d01010b812542025010981030500e12254244120300b00000c0c00001c850200454441072654100141c4840014000c104e50302142e070008041c0901e00b0078058103054026900140c4520040b0040202c600c014615800001104070700c04420b9000b98411032255002c0d845543d003100c456408103040a0b612508006101c83c02c451015060202180800481100c05980c10038100c03940029420507482480041207607801c0d01c0303030543d820f610101042c402c201c14407 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 734712230 1106 734711124 734711137
    0x5041101030207170f040302011407020a051c02061216020a051c021e0102120c030f041112010501061d03010621020102160801060e010b030702070605030705 69
    0x40110001e41281100f00c8001001c0710a9039140100034015110311700165500903600c1c3e086200041508008141304101c141c418090040141ea45a2407013003a61003d070b8540450036414000c9031000070b480000a03400c200b0004042101e04c802e001550701c2a03820340c040302c140010102040b80c1e1030000e641c01070030ba90000c01c0e01040f02c2c4d003401800121070081c2c0c8112110460078028402d02d03a511240c8042950313500045003804010b541508907400f00c00740c402103056140900c4421030719507009100074448009041c0c8401e03245ea400d00c0310383c02c4902280c0200100d40c2c4900014000c08101001103080c203400908401d1075250500400c819980100d505124140070040c80d20f02e10000110101d05500800034141e14502400c1c0f2403000400f855400030800b1841e04a000e080d241041e000800344060030003c00141d07a400240400455010b40750181e9030b691041402c84180c007a18 = true := by decide +kernel

theorem cover : BRFrame.Cov 734532374 734712230 := by
  have h0 := BRFrame.cov_init 734532374
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734532374 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 734532374 ≤ n) (h2 : n < 734712230) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
