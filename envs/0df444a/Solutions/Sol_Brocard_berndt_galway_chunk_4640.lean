-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4640
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:16:05.133325+00:00
-- url     : https://prove2.me/submissions/4e525f56-25d4-4d93-ac21-888d79e1fcab

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 834352517 ≤ n < 834532374 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 834353767 1250 834352517 834352543
    0x16060c02030d030e030a0311040b0c0706080916120602120f092509021e04090f0c0f02060609130c0801060303030e070b0d1e1a04060605180f030c03 65
    0x1205440050040c1403502d41c1c003007408828589051580060382d4400015a0f284d18083e260100b10180c0800c0044c0c224092a4426400f02c0c5000c90044a000e0000c2800004d0341c48583c0e07440340f41d940e655255a40c890708442121220a60044144038060302d000103030314128022040540303421203a044100841c0401c0b500410103041410a100d0140010701c01710ba141e58409201d40c00c48510340740c07004003c0c0c0d07051117079040f4694002601c117150500b0f0201c01112a0f080d6160341c0e1159a60020040901700c88080c020741580303840c445036140350056400c505038500aa00428443e03451100f030000e0500060726000342500141e9804000541111a8601401c1c40c980041805895440c02806842a03144108041d400410080c86082607020a840d91940b141001103020008001180d5569003c1c840d81b4100d0b600748030040b14031a2119441d0140818161406c05c4480d0341c50740c044556000e240c0e5580c00080380c08004221600c0c09504540da4004005d083da031007203066a00092400000d00d0000c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 834355017 1250 834353767 834353777
    0x3030a0f0c05040501020c0904062003040203010b0a0312200a1a01050901030f2006030114090c0a1d031c0903030305070c0c061808190b0a1512051606 66
    0x590011200c50080c10260301a80c288241442c0c2094000b030346803203641d500c0501418503200014103210740354100348040c02c0303500e607080307000d003402d6450031a00d6104a03000c5c0e00a608001207407030b0a091001100003140d130454882441c81c400564110750841300600780b601d0500040c048980e4110781400a008028844d4000c106158050032003108045016803100380f20301846001000403400094545204503884403820040e41c102444441d028070350510100c1e0002c00210010410b618001c0017528480001c5401da103043d0344460386100c00380702d006400c0c0c0c006661101541031009805003a08040030004003038a20b111550000d4103001c040d000032103000522400420400e15070148210364210b40b8501e000282211140c90303410402c8080e00c6950b0410080d1202c100807000a2441c404c081c25058098640781c0310a40040380030f012010a0035242e0300c5d540000f01d02c904125102d0b40d0710401e0710642101e4158607150001c003041d03601060030307200d81c0500c1000c462040c040070903000c060b18a07500c038 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 834356267 1250 834355017 834355031
    0x120b01110106060e040b0d0804031e0f080405180105010f0c02130f140106020102040e0f180a080c1605150f0f07061b030506010905100c021509040e120901120e03030a 73
    0x100400d171340d441c1b240369010f2080c01d079040000ca61080229001c1d40c0e000810115110070520a1070395400c5042006401d4241401d440010000e1110007441281d0040325480e5200c490240907000c5580b0a105180c00324074164030210b040c60103800c41d005402d0004001500c40e801080081003654002c00e42c9000d4030b0781d5542001c50889044074440c2c007400c0c070303407008600f4036052004406501c0005005510158118800031720b4488013100d0700801c061780b107420f49140c1d214a01d000407280e0001280c440103405444103203c00210006000012100b005040c800301d1601c40d40448403d034412485080842000c00c01c84068001c0d400c010083d1622502c800100d0052070011585008a000e101004240c10b01081c0110f0f070781e001e0280403c2e41e03030031900e00c40840c44001c400e8414640e23a1000a401c05c0311200c121024004200240201d0170b8207a90074080d03004508420740c0c079141c02491503000e011040c070130000554400c85030901c004000d0000000c864205043c000d1458000715000c4070300c0c2e5140c0b15 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 834357517 1250 834356267 834356269
    0x320040b1b2b17090307120203030127020906071121030706050925090f0b0117070201020415050c15060102030a0f0e0a12022803060911090f01030c0e07120b01110106060e 75
    0xd047c04072500c8502c040c1d030465042500120a400595051a6034040d211003002209900c9030704580192900400d41c5694080364a002504c48045c800d60718811503d581000000941950035803954006403070285240c030040d42d94202c000c2802900a00c0c05100d000f41030404103045800100c2ca840d01c0c0c0398180c1c000703441c10108005440010682c0c0c048142401c2c0c0e082c0490342c010740d031000003184644145c0c2180d03840b41c10480c024003c9034401c134400b444c0440e86000803504900207110506941d4190b0b2616000c0720000c0070f000005842d124010790040140da100d80348034425061a610003807a0540f081c0b8402c2d400940c10b824141c00888880c60001080707411490030000360f40705580c0480804034075295405240741c070005a1b120152669491700c0e500700400c940103000b0000528014202076403810203c000c2603901c0003d000440f40b0a0070094085815a503001d030144c4910007a030b43d81000402104000006400703a0000e080c10f101c001a503154280070203004200c060311459036900c90740c6080c88 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 834358767 1250 834357517 834357533
    0x20d031707021b0607020102010b0a170609060912160f0c0602010b01030903091716030f0b180c10020c0d060b2403070320040b1b2b17090307 62
    0x40d14030015503000c1444803d840440700c0144810040445103c0d031115203900050380540345d82500590f00110f44100407501e0b03010881007089000d00501115090780e00ca45200340d40d0305094032510030350780c8000300c405e81c202c034036030000d101803581189402002c0240d540c0d003a2a051413402c0440d401c5d20300000c02d0041c650309204034501d21809103824070100701946c8024203141c0c924061a440c51351499181c1071000d4080041107001c11300080f561076107950b28148500411504038040702d480340400086400f01c400c0850b1100c50020303000240004d00c01e050200010480d14441032010b6003c2c005800e402680e845c0200b44000e80510404a0711860900401c00341d205000c8000d80d02c82102c0b080c84004001c00c40a60b9440b603054200062504c0142e1441c0c01900790786c1d4017100c1c11520000c0c004c15000562005004602c1209882a810074002d40489e0f40f900e16107186c0d00707000480d020b8180c2904a8502202a1502460070310b8280c92841c0c0c0d28040c0e20441c219a00c4149a01c0040c911080100326 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 834360017 1250 834358767 834358771
    0x6211203070e0d02090f09215205010905060916080a14071806210b04060f0e07060905090901050f0112020f040603050a15020a020c0409060207020d0317 67
    0x8441d04150f8000d03a0380011703041d13071000e08203c107141c0814000a183c48400c0102c101391040c0d101703100009100c40904004150b00c0fa15030000b0000c541c46040c0e503000180101c80402507040f81c048041c0840420300701000e40d01c503130383c4081030320401c1150b400414070078800c51030f01034042d20203850140b07410401d251400032a0080c14910201c10300c0200441c0034007080b4144102c0e40a00da503010420b071014105d1400d659500b048000380d411760b10340201114182e020b60100c94501f00102c040c0002842c02500380e230f49800c00500303480805400500050380f50303070059980300e42d102030000d00301c3d034400181880d2004c5a00b000c0302040b500c4205016074a0085119544006e9410080c8a5440c20040c01600c0501c1807083c0c0718a0810600d07520115900d0f2071080c160ba0501500810526580303082c00340c2d59825041d070942c0c1d0b0f400c0c181c00746d0341a0620b0380202d03060580c05400401442c0541424440141022a015606076034248100d400580d42c1c420700503e10781c000c1e03482810303c0200c0180c1144130100 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 834361267 1250 834360017 834360019
    0x706020d14040c05060a0e09090a020910030512041a030a0609020c01020d0e12070b0c04034103090d1106030f06010807030c0f05030c0d050f160c0b06211203070e 71
    0x1c180001b000c9998032180312040d004040e031388244503480b141c01d09807805159640081d44214980100213820406d00e003034008583c0140100e52014810710880b84262246003d00c115200c880610000403010b03400c02147c00410362240050300d540c0d0744a00c1c504980003158240707505c0e50002003200125030039004070891500341d04054500c41e8040c200c0307020317203201d1010700800d042400400940c0c03600c983e0b4191002580c0216103030b13000c0d0b000c04007041c00c046002c10001d890680301540861151a819040c0141845440300651629608104206c1030a000c0802100c8803c11740f203007451644c4500001d18080c2c900e070540450795062850001d1b01d2200000c00c000201841c1c52281400c0d903500ca540144007105a081181d0b0340c0d1500303420070640b8420700c01806080b6050009020481c2c405146051141070f01c0d00c1c80000c105c0703000104440b42c3c0305000019200003c80b50200d680d61a100520941c10b288407204118000b519150b10303400d181c60741d40080981440442008007664000080d0032403120 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 834362517 1250 834361267 834361279
    0x302031204030e0f0103141b270103061e170f030706020a03050c0f030a020703030b120a020109360902090108030307090929010e121f05010e0c0706020d14040c05 71
    0xc10f04003001f2444000400b00d200318038901c14843d59580480003114090003161203540b45580c9190140540303a592200c26900003490b2000004003441d0964140401314210b5280900c006e18055050301c8480c1d0042e206402d0b4001e003204041c400c141080103001e964800d04015031182c018090190850f88010300c0841041c00c2004140c91510b40101142e6001a010200607216080d908041780101810482503400c96030a21101c00354550000360170324558400d980d114001621660b01d00024461049448510f8542d512540c1c00c0305603100310443c160b04001400200c82040340c00048040d402030740103120b00d8000100748800a50311411038409091a00c80070302440017850382c0d0a40d9012840e552240e2040403120f201c4a40c5e2142144d10030040004040310f9044d40c0a04440b03403a048070864544035030114441410120741c1500170141210b444101c00070b403aa5440000402d681e000c881c0c1192a02c0d800c000119010400740304030440c804500c1032602d003e00c0c00f45889448001c081d000355104031 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 834363767 1250 834362517 834362531
    0x1b0c0a03021003090302151806090d090303201509060109020a080a0c090e010b090910030c060c080d0f02040519230d17030402030607170609040302031204030e0f0103 73
    0xa21281800ca142039a1031800040c0b4804d41d00301241000c002103250b20031244c40c14184240500c0d10503448604c45c0d9500c1c00c1c3c4072a9100c1d0340c0605e90724001544030201041007494100003007805510745461114100f40341e0101110211103182c00c00051003410540b00c4600414404099000c0007401d015001241e400c524100e17412801401d003980c0101800394140e01c9061501320700e40b04070004c800800765a100740308156123460441407542c1050610b0750241082000140c001b2003118001400c80b6007109114010504020007100c1800c0d08103410342d001142042240041d41c2a8032442c41c0f03841c200800140c803035003054100415548200d2000d0b008a441c0c08041c000f00481000242c00e0891100c284003c0700902d80204004514003100030384880465488007e90101c0c4071700440c0b14034802c07402d030341d01c0d070f9128481914024800c1010315480c2002400082150074610b4209400c58001e0048905003003e0003000700b0251821103080307001419401e041d0580b401e00f084e404030100b0302400c0c288100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 834365017 1250 834363767 834363769
    0x23041217040320031b010203070f0c0f020f01211e021c1a04051003030305311a181b01021b06191d01050702030a23031b0c0a0302 57
    0x500214001e00c020400c0320f0b62078003040101002103480b0000546200c00c0010702c100507a034000d401c22141c0201103a0501c100300819489017800c20f0156512282107100d0101c90707000c0c4003042c0340326042603050003100700c501001c0718080c0d0011030f040c0710740ca031020450107447c1e44019640d01d80340411185d003030b0040c02210882456041603103a000005040010660110314418044a651a0303015030000d2401c400c0c44030b1100ba40002000707590007a00d00340241d8440b00e121502c40381c0310903203100030304c0b0140e42e0382c52260071b0ba0300b4592082809188240320070742403102200d40a00301913400d2171425507803503a43c405001d01400094072036440c1311800f402c002d11070b000107916800c086400c0214160250b00840aa64840c8141c40404250784440c14120141100140c00e4400000c56038046507002c01c249951036100d802110309950b030140c003500d450351a03581c45d43e4900041c104821204003102c0e0300b0f6240d2840402c041d0401c1455650040c02c0346401108050038200d0000c049802044000814409 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 834366267 1250 834365017 834365027
    0x151706011b110607030e10050702090c160803071110050907030209040f0602042727020f040c120f0c02120a0e0a0609031202010c12230412170403 64
    0x1029040c074030360707900c10745003850411810040315080551042000c03911905250307000b401000c0450003a180900071044046081c1d41600030a04000d5005000b40000340488200c240603006442c5082804400d42a2503036542a5a80089400342d0008100441204903a541040010039050301d81e24204040d041c880000f507180c86031400043d0103903181202003401c02c90481c0300c000584c0d40155045444c4c1e52210f1045e40e2203111000800d1810303003229070079500d11185d44152040720380260300101180800500d44000f0707016048099910102d44d54902000351694007800031010030a64807610b40341c00380c5240c041200c10141c2e0320801e5a15000403406030316000988009804401402070780c4403d0413171070440341022008550354105000c1000000c01c86d400c1160341003560300c40d10580100b00454003080b0308a6481c0d1031400c00081c140d803a0b40401c044c05030b001c400f5443d48040c658400e00035907400001e0f401401c0c0d80480d5403008090500d81c1c107542c001444119021040d1090b2070710304190301c0080c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 834367517 1250 834366267 834366287
    0xc0503060118031e05030906120709061d0907110a12110c06040e040f0c0e010501030f0e07060513031703090606010206070507020613120506070206060402040302031005090a080415170601 82
    0x80318100944004c06010b001c1041d1155550014917050750340007499940c505500082e40c1d2003000c10550710b00404c20a0103140b18243c282c003000102c030790b1001174038100808144044c0c03520003840208079428a007003009111000f01280500c69110660900c07180082c141c50041c071071440160021043c85800340c0c1c80c3c40442d8111444d010030025245c44905089290402072280240390504030000091200b1071584a01c0c12201d09072400c106040303d194242055a40c15010781e441a007011100340955400384024011500e200c01035017090756100c0d551201c241000c140c25aa0b001808130802264100401145501800a02c044c0c000ca00384075402502c0307401351910080c821a400b20f102082003140201550050144004c094001034080c200b0a480b1203090710700e80e0060240c8000281c3c030741464000c8030120703a4042e0091594210800701140245409010304425008107041503002c922074101500c0505120110b078406920790b81c41c0079055072011554503000300307040e000300000caa0f048810302d0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 834368767 1250 834367517 834367553
    0x1b0f0f090402040e03070b01052d13061502060907060f050409090f0807030c060b040522050c0d030203040806010807061d0f03060a2f0406050f040302040c050306011803 74
    0xa4103684440c8006800f4007401d00080c001d074400441c0080c140312000c0e4505d030480701300356100000c0101a0405a905603014007181041d00348030401402241080700a044402d50f1080002030f0007900d0b04d0b070b04408150000c030b141e0016401842408540b0005001031801441c0f94203082055968003180034002c0e02992048548041c1d40e40b0505080c0310301c00701051941540409441c0e0f0324000ca1901610034502c140059078228904100c2c0f0b081401c00b8400e050142084065600d0b1071750300340c08408551010314108540034020f40602d13070540e4507190050000c640c82a0041c58545081020040c80c092059200050a521407542040030f00c1d040f400b142c0b00240740c41e0081101c0c107c01808900015101d9560540500c1140d08012088159912102e00034402078041104043c612110080c0603400c001c4802101000300001c100b01d60046005056000b4034038013090030965a90001011102d40d03241e0b00012900c0041000784a40c1c1c000031500c0e0303910b18043c8071005107041d910703140c10700414480c1503 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 834370017 1250 834368767 834368779
    0x80108071a0a05130e15040902030601180b040c052101050904141603210306031109091c0c1202010c0e040b0d060e010b180f060d0f050105091b0f0f 65
    0x211989481401107581c0011004e40150101d030b0b0742d0b6043c50400348219101c0c4601192514130801c0744c40d160082030012600140107240517424088900400c070b56211250160030b40e11801c0c0e6079140c88038010348a041145444040e03c035040d032250401800001039580c0101410200144000c0c1c1d1081c1d40d840d08180c00c42081e00018050001b0b00e80751950a01031641610b911990005c10411144500f045111080540d002d144c2800030054040c0c4016020080092941c20320146c0c45040c20120250300c015104120781c1d000c100f81c583c00c59030030320046208000854103a9644140b081890603082d00100510007005146040e10004000ea1100401c0074031a0f515030f80700a030036541e0f186030004130301c1d08003030200000c1101c445914001e140310307100704d0f00848941d0302d00c0c0030b00300d050711643d4412200481003040c565911410402003603044401100c0b40300280b011100810301c00d12641d840780b542c15004084087c80d01901030b8142180404880c8200900100c20419417034244082d01c3d201000d1300c1c6 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 834371267 1250 834370017 834370027
    0x60403080c0c060f01050103060603020703021005100b040b0711100e010c0302010b040e030909060402030118020307021222050901080304170a210f05030c070209060d0606120201080108071a 83
    0x1e0790403078802c0d551605054441d020511022001c4204254100c500c02d0b00c0803c000f40c2c0d50041501603004002008d005600850fa003143c01d507810b0b4002a03404990469100c01054941c40004060b17001034000c2020450003088290070401e243c10f49003200601150824a070141d0904010b040700d070b800394070720b0400079103881020806000b50018011590001d10502c90511850919a40c0ba000121114450103070240031a08600345842200e040c1c501e100541070010b19030401c0e40c0040c0d440070f001e0b081113102c1c0780f02e80b80500f0100c0c400b4101642440342a1000425582c0751045d200346e82d43c011a10603440c5600402c40c101c000001c035800c6900c644070607400308500d624898100140d0800151041840551145000d11420403140d00c91b5501c0c0ca80600542294108441d24081225100d400c020200207110251401128940d4011002405a1000d0f1f0103a5a401c007642d82035840744040d1420000780c03804568002c01041e014003800c3c4002c11140b03203012890154901e58020f005c51442002807 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 834372517 1250 834371267 834371281
    0x150b06040620010e0f12030f04021207030506190b15030a0b040905150115050c0703020d051908040801110702101808010203010f060305150a092409090308090f06040308 74
    0x2800d80c0310908104000c111109507135a00701c1d2180d5140f003c080c90345c040c020242e562456080141d03030240c990056540e045555603401e00803281091082c80f0090310030413200000103042003180c544140d840100352900e03002d1101060f8180c4492a02092003011145548001c4024510680e50710042082c000700b001e042c0b00012800900d104800540940a1407040700b0001d45460312050480310310002c4100801085901201c090040000da0f070345c580c202e010200050314090705070740c60f1103000c4c00c26107403000c0c204101d5079240342800074110f40b00e08001c241000010003c5c4100c245541100400c20700c0c1060944c000b0b003c50032010001c1d030500c9517041d00800010b105030051070190a10000855495071103500d04808128144a1100043d0600300040c54844036640480d00e681d0703028003943d45541c01c20100310094840c1d031300d01c000c0700d0954140b2280e0b4032080c0030303841d00101642040003801840300d08000304407600c0105050865400040c451a0000300062069807007601880d1a09142c2c42d010 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 834373767 1250 834372517 834372557
    0x40e070507031704241d0d0807020f060601050a1b060e10111c02071b050405010f230103020d0c0905030118081b0a0c06081f0b04050906061213150b060406 68
    0x5107a6040140000207401d1b070380ca00260301440003c10303480724160351303130740c0d0780d049a03100c880000346400c50b00300e1000700d4120750080b80a01310030741131402d11281c40d1001c10808240d0702d12946064804949072200804401011f12001c440721480040a00824075490242e038518422224070500b468011000902d0380c7c00c2c10760550354031a9003c50b15281c1145407441d0300c2d00782d21060144602c25441c0400004884013000511030850b980c580706035030703844080d5103014800704802100c181815000c00c603843c07403c86644540480d201c0c0544035400d2150421041c1421180303030308490940a200030307051902086402d005c3d22102c2a04901401314110803510003400c200603400010b000c14088600412400d8000c1c012a00c58201c20120011181100140c4403075020780d44501c40031808104418812810051916540104007810051a1100d001d5a4401e020411641c441100c60071311004070401c442e00f030160b2079854000030305001c8010780c600080d43c1c07446244600c1e0140880c0c2107507400801511 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 834375017 1250 834373767 834373781
    0x1062001060b0301120b010b0717030603010b03070603021b060103080702060d11030a0603050d080402090601030e16080f0f0a03051602040f09030801050411040f0e0c040e07050703170424 82
    0x2c0d0703202c079241c0d42c1d1920514203480302990101c80184100c0d00104182c80302005591049402525126500c01d20f0700d82174610b80e0026215039019521000d4480f0b80d07407020800d60005200c165030041e607443e40011302c141420300f54803014400f500500c0040003c9050752007560016601112034a0b540c0c2c601002d000000c119401d080d1592010204c20000e249400342c1c03004046034080c50079642e075000d07814004c0b2054242120000e6000c190031000c910702e5440717039010302c1034401118122483c0e850300000f58100c5580c2940282d0085e40002c1e0b40003901e600034008030815102c105c0081c8901207469901520b50f02845103c10f00300380184480100f5035480f50401c00b031a0240000030007822a041c10b00078240381d400d00070240903c3c2800041380709011035000f01c40441d0304046860980b1030030720303900d0f00391100d01500f4a15140c000b0f0001051510780040d802d4066001500ca59542da90b4615001d083c100e07c60380034070300c102e00880070880440c20500c3e914442e601c0c11807054004480c543c05040082000c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 834376267 1250 834375017 834375029
    0x110309160b0d23101802070b0a0e030c010e0f010c080f040b060609130603030914090c07022b15020a0f030c1b05151b0d0b0103020927010e0106200106 66
    0x4048284081c80803941600d405172290880301d101010b0144100205911034054024140c0b001180002d03910600d940c410743c4510708110070740f440c0901d146030035429a0107a001c000f0550300481001c1d10a03107401d1007514219909814a1001460107101c07a20651100500c081c1c2905210720014009541d00b41c11200c21840c01454044051060715000c0d006000c0340c003046010522550010a08000403907645020f500002c2512440b652010101c00c201c1d000940100d80250808002840e11018200d481181c548201c0004581486070300f4140c8a041000b90400c200030b1040054032403255202c45007480c0c1600c80d08002c1038070a01154100d41503007610001040030300c030f0602c42000b0401c1c04250f58182e0081c24003401381135200c40441609002442c078583c1c164807410400303460504540d8100d503025407814100181040380c1c41e804510b0b0389001842d110f5000e40500401a00c80d0041c60149001d0030003010518841d40c1008400740030700c1d660144020f128401e50315000c07400002500050080c002d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 834377517 1250 834376267 834376331
    0xc0f0c0309150507030e190b07020f0405010b07120c020a1e0305070602010c2003090d0602070605040b0a1401051e120d02070503210406051c110309160b0d 68
    0x9180c60014020b804c1100e0032000520910822402e40c5003a04440c1407560340001a0490750b850f110105640364000030003241c00025100c864582da84c0d907407060310b000382041001c0030f40d00c0c08945000e802c000c2010015000740140300440f00c02580b154030b102c60a07039214901c8086d41c0c0140000c2d2103081040350348001c2c0a0712500e00d0103e80303158190014681141d4644500303012040120948105080401c00c100882d4014040d4410310724100c91503c5030103000e9540103141c001e0703a49450003a19412079055507511820410f0101120f01b51081001090300104d142600d0750501c000104004c500103600d007401001d40e05200903954a51801070500c10140c81180c1e10000304080180d1100001e2045034800c0c0661504c4608500021a07800400702d0300041d070506c1e00d824001c00f40c44070340000040c01903024510451fa80c071000544540e944201d45690784584030301c0e080f428280341c48155084401301e401100300421000f001135060703914030220300c10003080316101011700a40c42082c5200710300c90381d8 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 834378767 1250 834377517 834377549
    0x20f0d110a06021507030b2b150b0307300620180907120c0e0f06090904140c15090108250c02030c03030a08060906040c0f0c0309 57
    0x280100203440003940a480c0941031650b10441aa2a480e5101040c0400f186203000641c441d8800d81c0642c0f2840d00c010700300b903040010b9406200310b10590741030388400141044941d40910003e0a8042c94010083d1000e00040842d400802c1c6c444000c1d10030090900600c003040c80c0d45000b204690798490403041e400b003040000505040c00540100108a0220044040d451070341110300001c5405070b00186240d03880002200042c045100d4000304a641040040a4840d500c010b060047e401240c8542c2d0b0741409107144130b070070020340104c0340702d83c54401e8078104804041c41c3c403050500780d803180e04800d40c8145501005031190401c900c0d2001d203580031048010034400460244003510903042d081c0c1c2c52a0484d03403801030441c0c0140c0550490003207070345106658441544640705058141e8070290070303106d44d14140c0340424034503000520030001044440c4100b00f01820150302d15641f06104440601c120781c0d0210380030303004144e8103c403038081002150071081814002c5400b0801415840a02d400703038 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 834380017 1250 834378767 834378773
    0x7051615020c030d05010503010b0d0f02060d0903030b0f0f0a0915080a05030a031b08040f05010e070f0501110a11130209150a02060f0f07030c09121406010603060f12020f0d 76
    0x2948619400a812482d11002147c1410144284e2141800150080c3d80030f02c060f4a4203601d442032108100e0784030302c00304040702d11400c80d80504405a8461785000c10413007007400800601c0240d8094640c001c000c1d030a04002d0941d074001a1608844040200050201c0c50000300329150070bd42d04620803911610800008000700000142415081030740c04022004142038074241c081744008081c00001d075007a0200b40810008814419818030803400000e41c000c44140003400c00f1100c3d070100d201301915250030491541c0140c10070303070820b6100000d4510b061040d03490304141068080858003d100c10003012028031403590484240b03c50040c000032450581c14003d00300360340704000501c0180140c2c1c3c041858a820100141d0203520000804c0310a035507004412801803440819400820004a00c0010004e02c41400c0000031805550702a450340c8001070f030b89180c4081070b0f10610415140c1b4100300840c0710249240401e440903520200d2500b1601c0c000510308103603c02c01c0c1a40181c20030000020 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 834381267 1250 834380017 834380023
    0x20412020a060914041a09150f0306041505060325030606050612010b030915090c0a0f0806061c0206030703090b010512060c0c0a0f050f060c0307051615020c 69
    0x20140c400c8070380200d51621a0710403107464160b071140c18910207103182102d40710300d840e8000b030109052240301413550b480b446000a03007030082aa020041c44600d1042c411141c1401e000c1c001d01048182d006000c60706241d82c44242506014100b0303640c0b03c1d070315400310b460343d80c0620070103070340c2c1c00158921100d28044401ca0b03e070110312440110b800c1860100001050f0520400307503445906400c206040e40c1e0718152441445900040c441400c2e40906500301e00b2031102d41d0300303c502034600b82e00105010010b02c02801b40b00401030b0032031580c0e40c03c044000c10188200040c0164010710079121a642508081d070702294024180328002d50050b00030041016280c1d00d9444800c905010300c01100142e41d0700c1091028029005c286440e01c0e0304040001041c00c086400148004001841100c40c486c0007512582d80040450808a481e504410020000e6000c108072064008500349034252a5060203000580a0310460079a8000c141b0b0529000c02804080c2c1060303100c00c1c0320040c0c150350b10320811841d561 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 834382517 1250 834381267 834381299
    0x5100305010e01060c0f031d120f060f01080604170f190f08090c041a06120907050a12030f020c0301050a060f2c0c0d1b021c050301060f020a060204 65
    0x704010316400000b0307030b6601c9840d100e81455006038641140041548040740e4000000c440d07450400030a82c0c210700e6279150112241912442e000151040560070740356a42446400350800100d048100d0050100000108000d60070a900200310902002ca0b01d9004d0540d0083c1f00094a040d01c000c50211000031a45001585000b83c40e035030f9a040c08116101501c41485c2a25001c2e55070f4486401c0203101d06207540201110003c0c10240910040d80b03400081c0541c0c0000104514402d44406000c10b400c020010300002c0c150446130004010305140048441d120000d20103010801a1960000510300074000741c502200301400901081c50b141e00d014000e00194030520000c2d00204200194092010703200742a05a6668900f10003c0c1080c0240c4248500240c440c2041d19010004051011a2842103107680511420041d5055588190103410500350226075080c01e04105243d5503115800422a41580d1003414815407541d00500704070b00e000039080000345184c0c4000343c00b142c50038049410721 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 834383767 1250 834382517 834382529
    0x3040605010e07031b05070311030a020109150902090411040b1806030f03130b1b0a0f0204050702030c120d0603020d060906150303020c0d2904030305130f06090203070510030501 78
    0x10010f602c5840080b0f00300c1d55080a11800414001d0044507118803600042c0391650207403500d44036a0903400000741c211b61180c851440543e540e0f0000404001290411540e11504075004226400d8590045092620001d0000340b40354107042c03550206540d03a50000010703200207070a1180d200036410b00c2c01084a8203a600138440d00c18100341e5650f172140081100e00d40c030141e140000d02d0b00d185c440f0814903900070f40040114200f00c2c3c1000d00c3c1b5501c041085040e114000d04c05d40400366040c5c010f10041310b1014140d08210b4004116544c1820b10000d9868482c1b07080034680766607040343c00040001410359400082d4007441d21060790050110940021140500038002041a104620141d440701600d600c001000350304504083c1740c0c586480c405907513806000301040c11041074074002e94081c0200003d0007400301e001d91000e0006055040c42202e52191170494110b410303103115190407407000c0300544000c015980f84ca1076041103480174000c2d84010580035054241c450400071020b00a000b090040c6 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 834385017 1250 834383767 834383789
    0x80c160c1703070c031205040b0f070326071805100206060f01020607080c03040515160f0f0c02040203060604150203030711071206180203031308061812030901090501020304060501 79
    0x31070007490010084810182d8003c050720401c03851540d5440710001510003000500c0400e210000b43d000c80c1000038103455501e50703012580c9907418500908001c85103900c80c80180303680030284264448450700142c0022250403e2802d00600c03000b480f003142095082107421488000d4080304031038002440710f016003001c81e1206050584c0100480e42d411007180d5110006150340c0116000c0c9480c000210b411034002c60507907006c0324007000100c04044040d248101a05049148040080d9200350404a03a40c03991900c0390024003902001000d0660145000e407045038000b0104899030f0b01c2c034003150007d05105014401000b50322001075140e800446440c0d0100b242c1c90191580e4403404500803064510a000c100300d4030025132900002081d440b050a000080d0714140c007405a503042000d071180b66030a81e14802c42a0030802c11030704000001c0c103015100c00003496004d06c03007440468845e07401c44480807443d403203075103121103d800740214040280031944008140400d00c000c0d0b80045069401610003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 834386267 1250 834385017 834385049
    0xa090c15180503030906030f0c0d1a01110f0304090c1106010914010f050625150e011d100b060f04090903082409060105040b03100906210201080c160c 66
    0x80c11384038403c803006560700100800000d0303e00c0080e07001298220751003143c0c260030188000089402c40d50b000c601421641e0307103440c480d4960342c2c0c42441c0300a00c0700064007401d042d41c6840e2503d903480c0a40e0084c0101070b42c55403680c0401ca8460480080326480003403c50f070280d6520303041c00c0014100403900400d00703c0b0800010411545035031078081101d102074940c51402c0b05901c940d00541d0314000654421a01100400c0c0100315402102c8170380c006034410015804900f444114216100e244084061900c41140940346000c0407e034410340c0d20134aa408110040346500040c0544078800c80c2d040302810101303000c20101c0d88d50b03119001091203a00d41403407039140c4a03806001500f03801c01d80c440081d4950668071445c00d165100c1c40c3c10401c1810420b0070142c41d030007001040e0300100d0715003005207100e980803c04c80034140500c200810b0030b001d02450308203407079070b40002442418030003905000c1400c0200e03800ca00c10000715400001c644a0306841445d1920302603141d051944551504c0303d80700d0403 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 834387517 1250 834386267 834386269
    0x20c01060b04060e010302090f060c0d0207060201090b2d0a09030801120f2310020c120a0203040e09031b0c150f0a0e0409060921030606080a090c151805 67
    0x2102c003a83d4950b1900855118401c00440195015440d6150005000d2803407258640321207018042245580c8090400126041d00003841c20303005604c880116810700c2a00070106002c1c0e203c094220314000c40b42c0700c200b505002800601c01c00d12186c1c1321300c4460351b420020b050500d680031050042c0320741c1c1e400103281d036106c8030b4070b409540802c2c0c05802488090100b10001d00102c1c0c45020b03c08032260081c55000030010000e04220100c031030034481680000d182c840d5000180200c45910300042080d80c2003201441c0001e50340e010b28011140d0a95003500807645142082003503460364000e030078441a0064502500ca41ca46c40d00100490150303a01d000c28820718100381040e40c00c2108c940240c142000a4a007084610b54808102e094209a82c0c10b04000030070018042e0651440c01500009410b80c1004290344100302ca52a00b8400c2510f49401030120b00d90003100d991300040f0303c1c5d07004a52680a41000030380302c0c025034081c0040360034041caa060041d0b0411980c98202c0d4900011510042c0d5841c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 834388767 1250 834387517 834387539
    0x303010603140114121005070522060c020909010915062909150409050412120b03030d240e0106020d02010204030b07030507094a04260d020c0106 64
    0xc0a44032000395604c4040005041c24009007002c1d100d1682111700f090900d074185070448405a84450025800182140c0c1c0007548052443c2c10100941100111a01d0301100408031922400000d11030b800c0e84002c108001e000f500104400307900183c000e40e001c0104554200201a0f1380310b01c1c5040725032aa004641d0105440c007800d00c10070600c0c0e802c0d161501c094100142032403c20200c9022050500020521525600ca200d100c4c611407140e0003d070039440c202c080e21224120340e5448019080034000c4042d40c402006454400c1d81e9040040f810f82d24110700000c07604c102100c0c1206121992a0014460801c150701070b04840158094607250a039042c4202d00380e100d03034007020b402880030304040380b085440f0f9446280d201610345003009000d51180c0089036000300004d08a02c0503000d900d135401e02e002c0d200a50341c030191140390061450010320f8ac0003103a0703914001d00c058007620902e5000c400303220031008c03107130314a04001e0117a560314004452004003d400509000d51503601e0100040341c45e42e081 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 834390017 1250 834388767 834388769
    0xb0310050c190e0a030215040b0f0a0e190302040b01050714010501030605011d04080903030405120f0705040e0613030e0a080601080f0607090b0a0903060c0806181603050c0c0f03030106031401 84
    0x313040d00d41d9041c02c43e002e00c00025946200080c0d00b400c10000055400c2c1c5450203804000fa40040b05503580c05d483d107006002c40400a00544141e00001446110800200c51442125410358002c528284a0001a11103014201003e40071541e102c24032011183c0660003503060f04c1c801c8000300030992b294401200b0041c0400c1810b02c0e8022404003207030101d4040d030054007110000408a904e0b047c1c6139004a8848008290204080d5000ca201020040f005219a00107028150350400041040e4201d0541d0b440001d820389080c85000c24044080c10b10904415100c00381c00703400c0c480382d20381d9071022a981e00f9013481001607500500490b60090f903070115034940640100d507030f00c00142d070401d141c005081d40080610018440515030000000301c00f40074100400155498003202c03071a20800303002c02046103200c460442e002d84020000e21049040107010140300618000030690f030ba500701c50100b403084c4403141c7c800d8884d050781c9051481c00080118142c0ba42e569003801011700d501b10510010b00c003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 834391267 1250 834390017 834390019
    0x11526040b0f15090a0902030a0c0e0c072a050405270a030203040510170c030a0b010207050109090c0908060a020705100c093804060f020f0c040b0310050c190e 70
    0x701540760000b071500c001516041903201720001007050030f5500107450f11000f242e044441210303252042150400c0d400d149640b144c0c1c40c008581c9083e8103540d8980d480e50800d0031140000c40308213100074505d10106240405860050010445410000c15015a54400d82c400c0c600d00c030300c50b80341244121400700b007260082e075050f001141040e0402c010841441c2d81485107800704181181c0300e04001c00c0c02d0741024040e81802910b69a241002600041640c06e01d000d09030565002003800c002c40e9a0117290300048858000c4000b8505d441003100302e400c28405da119488a10519003030010401c800d0b4001c10080d8441d004641e950100640440291128800104040365499070308100d4441c0c01a40c8400c8141d02280310f0070900203c0a10300003029008a401c50540da010a080c444640c000e9915074101d61103000402d10b805023055011740e54084100c811303002e180c17030318000e6149403420400140c01480705242801185040100111241c205613007009007005110f45041c0d8103070251001c210a648 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 834392517 1250 834391267 834391291
    0x121101050c0d0c02011a091e0403050711120706080703020d0e0f010b09011208090f0303070308060a0801090507090b03030c0613150203010e150303090a030c030c1508011526040b0f 79
    0x869941001303441c2034020610100a000204e500d003032360b035218280600c180e00c80c5d00c480c0c1d00c40f00d8a041208002c00314041280c0110003d90031001405400542035088500b9454400c102d03a03101038089019000751a04008128205800c1c0c010a031008180010802d8084008000c0f0600728020440810383c01e10910181480c80003596022907802c1008109000014103004240148100801d1035030b0b12070345003940000c80b94011301c0388034035200310240300821200000b0321041030702c2e880d40d070380303510644c071503066450790b2030803180e04548062056410000742c10050700c40314030340782500324045560000b04844050340d60480305030058041c400e4905075100d140c006c10301c9668050521010502c8a4105541403000381700b280710b5580d170b4180701c6001e144190b05800c400c1d03156103054034103e07805800054070a055965106500b41d400648a030445000294905013084520403c1d40c5444410a4091100403034000c050420750005040c0c50240c1d204240560569884214a0700841015075448403140 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 834393767 1250 834392517 834392561
    0x5010509010219080c1c09020108151c050a0813080f0d0503070c03030e16090525080a060305010501060e3a08040b0a1e020c030604121101050c0d0c0201 67
    0x244140c15130360340205100c0415203007001050302040c05d41c010045481586445901e03480455a22803441ea4205d030007801c800003100c0b03400340050b500c84281081040d006402105540500004000743c1c0742c040c3d000b040042e902c1ca0300342d110b6940c002c4680600300f05445070030f08080c60031000141c44d225200042c0e46403415074541c40d504407605020000203504040d10303071401e001c0c01c043c00d009614810000b81c40181d02d461401410038250340c4010680314a1041c03402404100d440541c12a2001030b00628062481b0303922040c119000741181d81000d031040d0300e0a000030440343d4120102082c041d000300d81056a2039000041e00a002c08074601d1080c81c40c80c0101503104491071080800f40c55803040012500f4144c540701400a02c1d000350320322034009031508820014412060340088175040c03030b1348054400c901051000c00c2d980c0c0d40c0580700074034112880c0e6080070701c0c52103141184410310780c0e02c00034402c90512130710304141d5404c0700d18000007191410000d4074011740148242c03200000940a180000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 834395017 1250 834393767 834393817
    0x20c0303221518051b0109090605030601050103090f0c120b1312050c100e15010f03031706040e011802011e0207030f140313031a0601051b1204080307050105090102 72
    0x54905010000c2205041c10703d0040003e0b03040c400c208905420405003050145083c0004181d0f042c20352241440354a84907041c00591404101141541c0081c02c0100d03c0c6559450428410120703814043d007241c0080c5030101d08005850f07242c2c4500b50265020310001e80740c41141050b18100748c01c004150b40242016000000e016802400800311040c05989580c0444048032013a0f400c030b49184001d40c2c00c110340032842c51041c0c1c14a9170144c014028000e2141d4207554024151204c03083d01d600880051000150b05c607500c0e500700340500c40c200300013404000c0c0f104800c92440c91007954107c1c041a01c2440e40030702c20a40704c040703040c14101c1d0340c010001790380b841e19103203070950844074141e8022b12180b40c1c0031080d500410040c50300d1115507021039419851030070005420880d503d2000280700340b0805122050307a200e0240c0b0300b0400d010031200580840b602c5074501d81a14640d15008400020600061001001c80903080e60f5000b440240442e5179840f080078200d01c588480381c200c02100764000f100f0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 834396267 1250 834395017 834395021
    0xb04030f17041b15050405030d02010b010504141c11031b0d020913050712060f11040902130302030f0c0103240b0a0203090307180f0c12020f0d020c03032215 69
    0x401100c9500c81e040c8030380c880c0403158969030000c14610210310001403c0007e41002c004c841844c680901c020003405403c0c200003001881203209500e54001404010201070f8ac2c1c10900c0342260401c6483c0346614500d900d0b041c203020b2a0f9080d418400d000b0110a5038000c401000540319264000b40310b144000215400c01030b91070700c080e02e80401d20418500c19000240304108690241880d00c500c00d255890303a140100543d9052a003505046040030f107044a540072100980342a101385440158030b502c01261203024900031a40065070503c652200c04440d51004681880410030aa8041c032440c80700c80e8503140340c11500c5004004c60108040c00700120006c403c0949556205841500d140902c4000040d1410303800760030140ca81c0d0a88a0100c0032200c0c40d11500b403414036408d03818001280600406886c0b50000c1c400c0d8403510f03400040301040304944600300e5058980240b002c41d1500b000564956a03508100c03440691442d152660541c2c48810048030000243d00c1030680700c140a8031040440 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 834397517 1250 834396267 834396293
    0x20a0e031908031824101d2202150409060b0c10230106120f0c08060411160c0305010e070806060402130b0d0c0906032c0a0b040b04030f1704 62
    0x4221702580c041ca91490034030181010018983e541c0c11641814001e0780070f00304100580c003400e001003400c1445501d061400550584c09140f04000031103040020180c0c40350b5034402d41009521400078000502800c16000c090003c0ea00a101c00b00100381d2503454100d145c0c480c1107403d284035404202c6414007040241c004911004508003c9545c002920103d41c8205500b82c0200c404140c03801d40c22424003100d41f140140410300140140321513100104054038151000e481c1500440c0c0790034152501724098411100c000d0440000119212900d0420003940740040c0402c4515500700b0310001d4800d0300c0000d8100664203000080c0c0324a07100c45040000961159200c2c00541910b98000112036482c1409010040c00406011030403c1c61400d0041070b41003150801000d0507e000520840807014020034a401d40064505400016650159034648282c4620003082140500704002c1040003208005004a10903120481500082e04054580100c00040c2c004080000000240840c00e00101b8032 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 834398767 1250 834397517 834397561
    0x1006090f0b1309020612090c03010c0504140f220203010302100c03080a0f0908030c1c15170f030c1615050316111b1507081219020a0e03190803 63
    0x1070b141840e0b81e0038490301e81804548429003500801c08008c03846c00d081c0100616074001e494000d180c24200600c0510000300741c209d00d4041c3d400303002040840e032500c1c04c10b1040400c541b0b02d40c1c0301004c5d100b2840d0010354000d02040340a640f0901d090383d18a4004c1e1150042c29134984c507030f44038696a0130b030080300802f000f103090a034280d00c8070481c0d808036a040d00194000c41c0c41d4501165078000c041c1441d80c0c003e6003c550240280d103006440d03491141026004030613180c40c0200002e41d011421145441d080f0502040041800300180119035080005428000d041d90b10080094042d0b44503031740c5407840d0042c0c140c040481c404000046021809d07004029142c0203e0034460740c81011540400d2900319000c2664010b114042983e04c050315116100c410100d0040000c1450b00c0080d549294145c02049002d40714001080041003155420501c600c82c002c000400454896003004001401e00400300e800b28000e0090659640c1e09414650300c109040b0381011106103551110391003445501600c221003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 834400017 1250 834398767 834398779
    0x15350a021c0507080f0f060105180312040612020a0516140d0914030f0c100212030c2502010e190f0e0915220309081006090f0b130902 59
    0x11400d240400070034003126140001440b854000000303444190094080c4895848540800c03850b584c4030400359030b114030280382c01b90721420380c0c180d102c0551001c8007400350302d80110111250f410039050050007c5820959440b1000c1d0b01c0401820102d12405800900043c820440300c040da118a4101c1008540f042900c40b02c5204d00310102400c0c05420714111002510448080100800c03810303500d58004000c1f0301034196540c040030a5903880d1015403446016000f186802d004450080c4400f604203040c030b1105c5070780d07440d01c00324072041036102c00100d50700b10f1110010702100c5211780c0040c10107182d042e154401120391180420294034a02550008000d00c2d040001c078620300400105002001030015a00690414002050400c1c481400105010b013035501040b80000da0180703000900c0d4183c0e100803220a590b81030483d81651a6000032607a4880c03901700c00c80f0342d00d1b603500c079004582800100f04039a031082e031000c90980c1d28112110781e00141810f400402c03240380e5407120074418401484 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 834401267 1250 834400017 834400027
    0x30818100c12050d05180c03370f030f0f030c08040b15040e0120130312021e0a110105030c07031d040c0807020606060f0d1d010615350a02 61
    0x1404c199842240c0130380768100c10340d924407000d0f00c0030003890320240c0048001d452810303c842600401d60080b69031325400ca00401122404034072000000400083e00f2041070186081c0509020b0032204c4440e5690340010140c1c540d00308601e1282c030030301260110540d82c1820b50340b500e03103540051030b10180540350240c0300c20400c14450395030f80c031400b440c1c08274000020070700c181c841c5180e41e490312a203882c468030310308100941c0c15105504000139095961101c1600030f500c440d500e0480c58041c01d102941d0160b0601000010305c4c980c000b1b0304242c1241316191302d601921104004441501040e204002c0d60f19044c441c00e00000c3c02614819a545000412450900c0d0100005019110600d60703000200d0542e205210001f503040c4400c0e940b028081e14901d01d4110380c1c000d02521031058640c0f4080e0b99540b4064bc00038212203805141003051548020b10400ba241d007401d09030300313400ca5003400125511551890356000c074101c02641c584045412043e02e00b10400041310742c844000e05400300c00b0341c2001 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 834402517 1250 834401267 834401287
    0x30806040b2e020f011107030c0615120203011b0f0f14040617070810050108040305120405062409010909080403080c0606040c0e03061f030606030818100c1205 70
    0x20a000c0b06024201c04900024020001a0038540c0a4001100b142d040c8004403440c07016074011215150b52600e0150070115039420248010240d4484251189820070000100e5000d42095012442d000324000c228000050701104a1079114418074030100320781813141804a40140c1301e00c0c010031202d04041c2d40580d0344900c000080e0f4410b07081440410780042100c0c10400c0d80170a041d0f40103142d0304102001d400c002465aa00304514803440e41006021030000b420940310b002900d00d41003610b80e1040d040d06140c900035854140807650300341580c21070509003a0114010102c120141e6014011804030303400c2c61440700140c030324000192841e0320108000000251180c00070065502070f80068a001d08241040205441d041c2d03403200100b0848124880b0150360114141d80c0100e0b02e8489821054040c03690740f1032048140e400508582d1520301f000050000c84ea004054543ca08840b0002000e40b01081080030359030085c28a0001c1e042001000014010041013958546641806801c00350480 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 834403767 1250 834402517 834402559
    0x40b030a020913030807082a091306170c0604091a0306040f060c0f1d041503030201052e0603020f070804120201090503031e0313210e030307030806040b 67
    0x80c5000040f1000c1070318010a261740841d900b0341201280c644854141800c030b01442901c41c0c200c40c0002003000702c0b488210f1110b2404100d5029030409084c201044100a450000405051103081241c2e411aa40303220010804221140004e8000f0041c500301828941440010b1040012194107944c030141802c03019030341000b4484c4110311500e94060006510716000c010355600f44c1d010070074001210011420a5000301c45c00d11a41c20032a14001c94000c5840014041c2241c0d038003c080c01d04903a4008424540d041d040b09106007015951040358020700e42440310510481e040c00c040d041c2501e401800914480e400914101c40e2000e601d40c10110f0944402107158050ba014225030f0100607829411540c004075908000c01c004c502660030405000c01c64800001c03001c4040c500c0d107000200141c0081c0c54454001c24084c0c00c4441c1e0070382e9106543e005412150b68468880202c0c00038024440300c2e01c0e000048a9502d0f03815500c0300c09585580c010301018180301c2c03803110f500102100750381030484200 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 834405017 1250 834403767 834403771
    0xf090f0414091c0c06050604110a0216050f0604050d080403062a0e010e04090309231912060b040f050924010e060d170d02091c05060105040b030a0209 66
    0x5402100d498144104030a03d44510540c2c480c04a40f200c1c601080c0e542d401852801016402c00c001185175079030000003030020640b041035003501080214a43c00219030000e420282e0440708040062180e440307100300b000158000f4141c640c050780821042c021824500c407562112489456524102900da548100548419140070700c941c01185010040c3c0c0060310740c02c01d02c0d40c01a42023046241038140002085010002000390195880d20540401c1600c6400e04400420740387c8010703105000d0b2046444001490780044a200e14a1181401c0a02c0082500d039001c86402c802084c1c0c10b284607a6882010b460b40802c083d500c0769503028010035504181c010070b40f0912280020740240420840800089051112081e600c1410b4074014842100c05051747d9030049021145c1d45456411361900078a070002e0407602528240c0d020850030555485038010b8000448100c540c580b0b0000c004022234030164400e40c002d02540d01200c010049414154030100c0c4500e8081c081d40c882a1041c1c020482001c82 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 834406267 1250 834405017 834405041
    0xc070305030a1e09150203070605040506040204140c0403032307030e030d051201090203060d1b080d0c08091207090908030a0b0d0c0e09010f0e0f12030108030f090f04 73
    0x1d51910b100360f000b5100504080d40256040d2104603840000f03241420a000b0100840701c480203424111b4000c0069032449540401c0a0203507142520386280c840c041030300c040b80a03e0070042064540c83c80031022510480070035200c1400c00c0d2558a044922100150b64004084c2e856041e254840e45000b0040070f03140d000380c80340c618503400c0d0020700d45081e100342c125070308101d070a02c400f000c1c05c003000c102103044407c0f102c000741c2c4940315240051048085210010040e900c00d05440c0d44a14200c03801004a55810042d20001c030058281500e011540c014001d2144100708071030a00c9180c20b5201c203114011503070848402d17130b44502440003260000300d026980002301208110552a050142070880d481c1030340e001d42c400146680e01507000c4000c1c010207090100c04800541603c20942c46111840e58140d0248800680c40501d5911402d441010405501800b00001c3c01c0c2c813000c904890407100150011407070201340381d0324100240c01c80d0200a82c040c0e03010700056110703500d6004a03200030314 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 834407517 1250 834406267 834406273
    0x141006350a140114030a02010327150f021312030e06220b0c060c07030e0a03120f020d02120f0c0708010506011e081504020706090b1027110c070305 65
    0x1c40110b0074488110160302c141d2500780c5942036840e00c1d45010517400c018550a00700401c9c641c4080c0d040300c140500032030001c00c0c004007240e2071006016084a0401c1901c04691b01040320038801c484181c241d1003000c040d800540300000c42000210001942120464000d02e817800f44484400300041880c0d006094140140040ca44040f4502e01c800790040001e0440601b81441c00c140c282d10340b9103030034004044444012003c1030540a040c040c843c105006c90b00100844000c68980c80d1107011300b40d00074080310009842c01d000c1c1c1841400020741c42803a8140390020f020b48464985204800d03400189540a051020301641507901e804010043c0a019013200100346450448001454003107811662403080d00c103240194507070b0b40c008000316000100102440d07200c0301041c0100d00a48100741c2d008151038138181050080c000c0c1e4100d42c5005510040c0c0701030402c0d50311030741680c1181259103c42e40580744042035086800c110340c805200c04509203030150800c800c0881042c180402c1c0d500a40e01d03a0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 834408767 1250 834407517 834407531
    0x5150c03071403060d23031617090901090203060d02030307051c14040612020c0616030608010915091b140118061b05010e0d03141006350a 61
    0x2030740100382c010002c101102e185046180600c00a04004100000179018206042803029205511080703290040a40c2049a5490100c010b5014081200110664104245016100941151a080f00c00038072000780100f00c1c69003000c40110080d44003400b596400802080e80b14010f072800c2c0064a0300710b005101400c800e03030915000b608a00e5085004208000742d4009060807001c440c1300f52000c1e2816480d10050031501d240880c8020300c500c0741c05020f9442040c080000e00544040c0b480b4100800350740602155550b50941400d850500300300415045001c480e5500851069004c40c3c4018024403141c4800c9501d5409031202c1402c5400c101c54504002e0074041c0c003540c1201c203c00310300064540e24100603280c9200206105440031800c806140701100b0360701031000035048000380110440030740b00e4184040324098000e0039099480d40200120400042c03081040c0d03002d41c03045490303603100c44131400114541c2c044400001b030354002028031001076000706000b0f9243e8030b500c92100e0300340005040e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 834410017 1250 834408767 834408781
    0x1020c04141005060f0a030903090f03063e1c06180c0c0b060108040510050703090201030e160512030408060c0304050c030a0201020c040c110604030c0b071b0f05150c03 74
    0x50026508000c1c004c1504002448190950008441080c4d805290014101e0702c103241c11201205035600c159052106024040280711503030b400050f4495100e805000300f448180038054901210f01c0b078250038404001c44444c50fa200481c010104c0814140300c0d10485c0500848601c00c40b20150807150159800d00100e501208a51151004030195170038001c03000e4005507915101e1a10040c50320781081112404282009010081c449003850311030024091803400e48030007401004088800d90002e401d04014880f524008201603200b200d982c6141c000705402c00d4207016404484003104041d030b200c100300005001c0c034103001071402941d84544899584c2403038107140746802c004420300d510079046440039500607a00020110302620301520081070992181c0b40940303c45551405e051501c1c01403208210806502c40420084988110700c5d0800d2034032201c1040b81c09154148101415a4030001b210000c60035903424016914440c1d401c484040c107000203e03414148040d42c220581d014003000748140 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 834411267 1250 834410017 834410041
    0x40803070c0b12040618051e100203010f0b0f0d09060603060506190603050a2309012307140f1803120f0d150f2306030402011d01020c0414 61
    0x1004000300e190306008920380c0c03c1d80e54000290008044a544030710115106640f02503560703d00b82c000099482c12908581500041c03400c1c0a45840140a8595000c10344800b82c400e9034140c3d0901c80c20109a0307810301c03035545102d51084640e4807600f01c0611101601c001c060059865117449280080f41031403a603e00303c800d60303202070107a500c200d040300c90b002640048000010200c0e41d01e07244c00b00741e607218031030640700401c036145014203107883c4c02c900302d5664001c0b00c1009014050002c001c00039110950b0122003414040c2e020f074200410351b0713408910020b1040841e04c1400e4660b00303e142c81d251043d40241e131240e00c19008202280c00c0c50000c10031038034060101505000c2c1c142c511a107400c20038004401c040c85150403095100f5550095100c211105104140152203070600d40c4030742d540c5071100c81e011005000c50300c51020a50840600040c10312100b502c1c021581030f1501c4486024503e82111210321702c010990440c820100c800035180d486001e0100c02d100701c2e074660dc0d4941003c2041c501 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 834412517 1250 834411267 834411269
    0x6110d030204051804141b09070504030b0403121d0a030f0503151e15031006031a12010e0706090513050f0c0a02073c06201002040803070c 61
    0x4141071051200708056115100d0140e80442c2d284c01c011083d40c0c90749841104810300203c004c8640c07142a2400008138420386035079542d034a04907802400ca40c0c80d503e007110705101e00c1c0070060903000580b001c1800a40202000103904990031408160000000c1603000380231402003031a1030a510410780c600600d600032903004007030651450182e140d842c000028015402d143d07480b0310b001c2c00d00078100b02c2103c4038482d505d0003070300d10080066817008145220390246400a03100074000c084020000606a0700030310449405d0151314a000c9800d0b2034420800034042da032a071b4044095501d4607031503491084284684005400c40e43c0b18040054103003418001483d030320f00040c00704035281c40203001c43d040c64201c41c0d07580184003c440f6aa2600320303100880c03c2468940c4070085100c400701170300c0911101c02d5030361042050181044c00440e584040c511480350f03814401e160205180300e4400000710020540651040661005c0792003141d1929540d4040341c0c0113611418454002041c0d450400030090b001c4c03c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 834413767 1250 834412517 834412543
    0x241b0908060105121515132901021006150207091a0d0218040309051c2003070f15110a08040501030c09030b0a0603030f0f0203071101050f03010611 65
    0x840d0914500d0303a920348041c021540b0071140400705004000042110b074255482d80c1050000c0c90502e2840c07880c1e85005001114440d40041c41d129148201900ca46903c21034080c10440444d8401051102c005008140c02c0381103008072172005410580d00d028282c01040d60300403807102c100502c18001e05101d455003005c0140c40c1480341100040b480c40006440f03a4404a4141a240da484d200140d071010b0b9040d0860072000c0c46d442044181600031241104030b0f5801c0c0c40683c0004010f0314004a414000c03c0c0003481d0300d00c162030f031048640f65440c200401c05405000c0758001d41d02d844100da01c2346902e610102c19000b00004164003154484480ea8200090710000c000401403540c0e260f501c1d00a902401d03040555541e099081e09210b10b40000c000c5070040d0700d006d02403c18900d4140903012030300066010911038002400a68400c050341904008507a0280d8140601c5c3e80d0784500e140ea10700134580c10058244943d170741113190070008600900082d211071000d03040d01e01c80c10b420400088400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 834415017 1250 834413767 834413777
    0xc1514010911070c03080f12010f031b0501021f020c01090501020c0c0f09070309050c0d0609030e0f01050d0e010b0306130605090a020d03111213050a05090103050c060304241b 77
    0x3c4000030b800d0144c60810740e5880641c1c80d480710183c051440050044800041c2403c00501c00010700980304450342d41641d005940301282c800c410708610b940e02d15948030b12401a44404004125401c0e1040019096400c526000d0f280c020581c8003e400e4030148007050781c00d80d5000442000c1800b00300030640c0401410784050915211080c00185040e000034007440915841d90084010000140b000400c0e10000a2a07880028094140380c0e0003400c141c9405c401140741d4441c8451540791802c00a03c0801050355024a0065115058030180c00000c04080309076403601881100c982c1c044c42030610444001b0113860300c80c5080e090400c183c0383c014003a0140f86c0c100c40c91800c09601c0e107102e807111082c1c00d401c010304d0260464800e5440c001d0540940c80180d5804a240552403944a44000880d03000b192120a0b081e01e80c03080000103042071000a007641e2100c00e40300c1043c244023010319030190048541840e210f8080c087c07410490310900b13501c1101d42c0e03070320b9083e0200282031044010f41051458030b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 834416267 1250 834415017 834415027
    0x81b011d06030711010603060c0903060c110601090209010315090506090c0307080f040302150703020c070801060b07170d05010b090a090203060109290408030a0906110303070c1514010911 82
    0x491020b02c0b020700f415003000740d440d6050048a0094020b0300045030b026004200304954141d00801c0342049000403207030103081200001d001c5225840b0b07280040340c2c00d4050107240e4a00040d0310004d503c1808035a0501d43c840c40d005216034011303d007107002480e8100000c2513614000f010000303081401004804a08410b10034400c11384d034440c040c60b13071140c5410101540343d2203d050a900e03107101d4200341c3c601c01d045203040103a003950580142c00900700485c01c80718200d440f020241d00f60b4000b405042c1c0e2036001484020f0204000c1004502c00c4941d62001a1a2450a2210000340c8100340c00c0451200000a200050350404482502c000c0c214904218214108100020191185413140e58004914040603406245141c8110501c0074074811183c4d56541e610400c5036120b400c625984008191034040c0058024040c2e100900c401903110003940c51940c070f4200980d002082044103440384411540380d030111846921802e4088911208400c2640d8906070a01084c0c600d6108121200e40f01482 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 834417517 1250 834416267 834416269
    0x2070311040504080d0216050118050c1302130902121014090a18050703020906060c0d050c07030f0302060f061c030806060f04060f0210021c0c09081b011d 68
    0xd031262603410846000c1415191810300312101d01400c0601c1003524400100020780403d0025010135080c481da000740310015100340303a10007810440e1006802034110000d046820700c0c041044080d000740c07150740117040c030800483c0300500d201142c10041000d50b0006400686059420b995980b004e072007961100704900300311a4184140d460701c40301c0d005030744480101c2c00000b40e9030000700007a801200102401489820700c00d5585011348000e0b4001c0038284003113030003030802c041141c08c0c42c0c4101004080030004143c0490340c3c2e40c42040400b2a0b40030340741d404000500c4040c6401e41c145c0c0603500900c043d080c18200b00344800006030801e4440d501101541000040d9402c60b12082c68041c00c05000b25644e120210f071003807048600d880e41c155000100403070390741d0b0020351117030b07810806908454841c032001d40d05000300e02c59200705010000740b40003444803e14081d009100107940a142c060400c0d1350720f03d040c1e0710b05480c10b400d000c0d2040b2016800403195902c050b2004000d82c255149080440c1c89030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 834418767 1250 834417517 834417533
    0x8070516180209011101051317070320070e100806060d030f03090221011b08060f040506010203120108101a0a030803040c0b04030b071101020306150a0908010f0e0d020703 75
    0x2000800d01c0d1500400c100000d60b00501c40107202c00e9a00d0000d108602d000140b85d4040101e0070130840f03811403050500001e031501c85080d1a40140c0c0368680032116603005100c903600c90024000310103c2d00c45d42c0c0d4081103510460159600a01800c0b480c01b1a06081164243c20074400809103806662103c04c0303400484d03030000c0784591800c850306000074410f945001003408545205084044c8081c005d00600789180e0560080326428982c5052501d8032000c50400c880c0403805442d040e9104501000c24419890103603c0b42c0d03048a01401120b2800000b10005219a00241d00141c22a0083d0058410364540c6001d0340e6401946403001010841000700000c40010031804054100c40b13011000034100044001c001c00600121b0768071903182c0b07a89107801c252403031044405200140c060101a01a00014002d5030302441c4d006090001c0d40d80c4100386d503001500400510420400001c030005600400ae201e1804c000220390341c0461a40b8112000d00d181c0301212412034210f5000b02c01c00c0010031514 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 834420017 1250 834418767 834418799
    0x60f09023f0706081e0c090406032003071d220f08040810090b1602010b10020c030c0d05031206041104060f09080f030906130e0408070516 61
    0x5415620003000e441c101c020040712104500008000740080010044900001c29004030384003995502e80d0b83d9903921042e19034004290170700c46600c42000120b0410b1340b89002511100c00b01820020351141d81c3d03100e9000f41a8000c8046240650f001540c14941c02c0a00104c0c0c091b140c1c0780051060340790881f003419289c1000034103803071800d28050000310485094030354810742c403a003002d12001d0f03811150400d0004c580c8680b1528109108000503000924880d0082c048440c2c0c0204154000d940c0c0d00500031210104100e45000b155a0360707000e042560f65140c006484003000d41d00900c007006000c010305160580125001c0e10817008640c000e000290008100d07240e41401c2c6003040456148e600218010b040040c8a000100c5408200800d00aa01c50401034a604182d510700c1e0020b640c0f580e60584503901d19200a42c141c00403c4001c8190500328010b081100012207510b0100d5910944070200010a4a00302c0300e81c04c001400d542480703802c0050242070010f61502c104a149010f082841030004 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 834421267 1250 834420017 834420049
    0xc02011a0906030a0506040c08190f06021c021b0c180402120a08210615040b070c0f0905060112020a021b0d05010515181918081204060f0902 62
    0x74003400a08107031018000c8010840d030180c2250050b041516068030742084a00400050388100f100103c5400208082c07245101d03004080f5040d0b0007140c1c4c441101940c85002c2000c03e950304080303041d2841e2804d20003007078072000200b050071014080e01820740c00e15800d800b2181c03258003000010125280800c103040c1e0040c0d070480c1c008810f55400100f16080c50320402015000c11004146107032180764401c0552003210040e401c1b240f141c0d5811080041104560f11480e0901b00e09020611901000d20000e05125000313012400c221942c40840c40d01202d510340210503520348a1041c01860b58004c800880110b030310000c01c1d410400b003144002c6d51391aa0f000c0c9040c3e00b10000300b1800994a03194500d60234940c10800070300031440d0034884910713050310182c2000c1c090040000282c0720385d54500e040c3d80c064100c020320303081c40c07a8651000001829a606c004d4524004500c04440000d080c00c000708103442d60030701000c4040c03505040620844030341803031901d007032400e1050b00030060b40c0300c46541d00e0500f0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 834422517 1250 834421267 834421279
    0xe060f0f07020f06040b0609010803160311012702010e011407030c0f060e01140106020f0c3007031a040b040b0711070f03050105090705010518010e21010c02011a 71
    0x140c0c15404034a010f03002c1c012007015016690074401804655040c00784102001d031054420760741d0300e11505680340300342c04585031708141100d40c2100280c8100340c0b10b59942c140c20004942440301400e084d520424240801403408500c51000c400c6503040001e50040b0354090034003205d29075000c4210f01540c4106e0320000d0811000b401d0682c1041410b004080100c0c2c3c10030010441c40c0e08030300070316000745102c401005010146800002d0360620014414403465207003409005800307400c000b84610985018505803480f500d107800590469000e0b84042018009900100704951031070801c3c510031052421609071042c240b1040001217940b400341079411507840400040540d03104007084446d5030005001000303a018410f000101c92000401c00026240208001c000e56241c49101c590b82d26030720f108031400b0850500c5690740e40502422155815281814245a003000400c001048002da008000b12660650388040303802d544240f00310794082c215030008001174010b03140c0c00743c8500d4040c4151403080c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 834423767 1250 834422517 834422521
    0x605070507121a0c09010f11030c0a05151308040501050a110321060904050613170301060504230f1903150c020d020120030411030607030c030e060f0f 66
    0x48100036060003440352401ca5a2150307101d14108184038503c071680046051414080743d18003078900103c2c0d0320b800058450040200140310706541c001c0ca0b207041040540010b116010f9104c030140b0a2040041c0700b00017a00b6070b1603100384024072406000d015400c0c50320110710b050700020031082c100c0d0182c0e002401c0640c6c41c5c40e44908d0482c0c0000110900c0300d414040441d40c103a10a4294a0030004544100c903c0d088965411052051941d0126000b81042c0c1c00710300071440e60b030200c201c03807c9290f005002507170b80c540b9100100d42843e071013a40301e40e0000d1000101040703641c0300e01c90280b9480c0c064401180707008031250009400754005005e101d2044015000d02d249200440d0b400400540d4020041c1812007000018032008200300c00d0039801600a89284c0c2c00c50901c103220f607614200395030349200a0840d43e56200802074200074402c4404126000144000c0c4e6070401c00144200e882d550080380b2280600401004d5030384262810146c4d074072080a01044401030750800c2d0f4804110381507203100d0303 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 834425017 1250 834423767 834423773
    0x109030b27010c030b060306060f030711151602030316030e150f042a0e07030b0d0c0504060b090d0624030c080c01050304050c040c09050307060504090c090609060507 73
    0x105200031444500e0407614680e1880d128040d0400c9044142a842c1003003804007030010711095200844040d07038050001c000754984044c030f0030081d640145103483d215001d00c01d4041001d241ca0001285220014442820004034001d032034020880c421983c0b010f141141841d103121944040d264151406154840002d10b60002003000142803103640c81241c0d080c181000d40c1841d22004064a0640d030400e0b000440b2601400321034801d2210380310406a00c1106440d140d6000700050000d058082019150154500e1980c0c4003c03520070040d0191400d904130074a044100300c00c8960301d82c8012010602482100c401e070f0340300c01c1d00300d64560704040080744017031501c1d041d9645400c108206205400d82c483c0c000c41800350954011080d610410304440f1500305070801580c003800100c50042447c0d0000740c030060a41840d400040790040300e41000300c40d440e03c40c0c0c0003a04014a64104100255020404001c03c142030b0080b02e5003c0310508205c0c2c1950705101c0c0050010241d07008400c240301c00083c40c2410 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 834426267 1250 834425017 834425041
    0x12140304141e210c0d0504050a06030b0303040e0a0207020a0b0a08090705010219060e06090313081b0402071b06020d090e01080616092309100e0114010302040b070515070801050109030b 81
    0x81e40000c00e403a076000840301702510542081c0207650051040a00c0480d000d40603201c1d00c580358100070011814a440c001c9030704002280141741c49051602400280d006813201c01070880034180044240d034485900f200e00418001c40105181001c0e0710074503013000982d07004206403030481408221030001390420704080001d0424184814502d100d010204401d10b1004009000307500b404e10b400d80405952410309541d00e41400d54403445d05034190748c2c4101c45142ca80d0003000b10343c0c0300e4070022007041840c4c00000700d40d00e56a8440009a00030729000c0000039403141300e8201804507490f00990a50412088907501c1c0f4008150300c22072440c10300411030050280306041d00910b06d220701c052030740b40c4514407204800f0408042c0da01413503000c0d01180f400038141c0440d4040c1c800700302d1680282c1e868003404241c160242620f9506255007007202090048501c8003c0c2442809a00184400d41c40490005522480180300c5800c0010010050201d43e902c45100422240c0002009400d900c9034500800c03 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 834427517 1250 834426267 834426277
    0x30207440a0c050316030f02120c06011403151017030c06150105040e070c0308070e030c0f0a0902070602040e010611100c0e1f080a06050d12140304141e21 68
    0xd44c40c801e41714041d0415038001048800c59490f41d0a440003801020820f082074042c21100b00200d81120380140303d03031100350120f0361101200404641c0d0825200d51032522040b001c0da02300746580c0501c40701340540c01080f0191024148101c000310b00c1c08182c010100c1e140c2602a01810790100480805d180c0750303100c0c50544001d0401130805800c103041c109070252500141c200210003148000d0300003030100d4042e92108c898464054050020410100100110182c501064991002c000381011852410ba8405401600c0c0f04000050390386003810601c031013184c41640140e0410440c5103040d00b2150380425a11280f120111700071039a440c80c0c1200b03545ca81d090035106600010201540d50a800200d1f8194200c1d81003511801d000740c56441c5102d0030f0710b02c0b80c0103051700319502203010380028580a103003401da25210b25051844564814100d0429401a10280c90f98800d0003081001200b05105540d20175288040740603610b2880f240c0c1640360356031f8140d203a001001405001c00d01e110310b030003218 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 834428767 1250 834427517 834427537
    0x12040b031f150c1b120308040c0b0408101409031b0a080f0a030c091505030c0c0102070f0309060206010f050f150a030606030e0c1f030207440a0c0503 66
    0x50707540c00c034400c01048483c1d5400d003510110b000074249482e19043d10401030a03140d02d5226603c080d2001d403007d40c0c3d0307440c018004035035040180c0d27000600b960303c100250003d444081e024100f034009007484841507a010701e201380300141d013603001d001380d03081c0000c11280340c1040444001424015805602e007040c040030070140c00b01c0c1002444800c10b45252000b4a2054402e480030001c07011508021503000c0028094447c0395001601c0c0d80d02d045000e81c02540d80600703206101d501d005032a10f2450300760313008404212202200010142e00705900b00c290000601254401040d440d80342000440020510b4403030103010341c04540002107039469002c0b4140c200c1041c030102503521144824024020301140c4075480000780b0b8800648d402c440d0102c1c1e4141860001032900300502214240b0740070000202c80b07410f0506508100e600002114610210f034413944406584011164600a0001d40c29400f050b54020380c5803841010090f500c000309840c2c1180782752030502c10210701c500d04070707166101d034100030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 834430017 1250 834428767 834428789
    0x111040306022515020706060515040314030903061801091a01170a0b060909070e1f09020309070b0d1e1505010c0f020f0d121112040b031f 61
    0x10041c0881a0002d10f4188841412041e803c4408100820340041c076040041c00301c85501c45081d40074265401030b2030130b42c0c002e03440050840d694100003085c04103aa05081c0d8482340c082010024000150800107840120001031807504103008002508d54a0040c90f0b600b1109807100754105a0100350302c0914040d5000014450740a4140d1200c00d8082d024484c0c18a200c00205c81101d8202010071040c0455a015400d00259102c1100b08500014002c212a080b4400c41500281d40ca0b1740d000d400b401205140034011380020124001000c011898201201080c010006e011550a000400c90103d5500050071034446000000203000786c082c6100c0700d10017121481074010302d050350343d1084c11302145041003860700c19600d4006503909240d5200150112240f0400705015003441c10001d007040000410111403152140c0e190a5a204407019000000350b410350407201410341000340b00c1980704003815003800d19242ca00d00e505588401030440050486441c80103042d9450255444007a080380142 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 834431267 1250 834430017 834430019
    0xc03100501050a031b080117010908070206030c091c03080a090302150a02090d11090106022406030a150c08060102061902090613081c170402040218040609151e0512011104 75
    0x8002c00e603110238080da00030701c0d500e1210b4440da00014403035200a5a400041c182c14410716400f08005500010b11030b200c400001c024040b416940c02d040c8200040500410200103030b004d060080c00c004009110707810b610300d4551000046a0000f0f001c0c1d64040d581441c00c14640e079988038070070280c0280c00300381d41c1000c010344a000810081c900710f20120041039550f014260ba07100012a5580240c5446407640e44007081501034210b002110746500540c09400c41e6202c8221341d440701d540e110082e5001c410655185015807009074050351180d000300e800d1004007131a042c0b03442e21813000003442c0d0f110030340141c0c006001e1007240c9680302038811040c54950700c2d00d0125607401c0442c0c1c642c000e40600080c4e4103c200d0070300c000ca500039281c43c0c80040c109205020f0380c4ea16a82404000d52001c6405000141c590350340303490640d1140031f504081e010015001c03484a40e4030120240c0c1d404581c0113280340702000251080c40f010761080e00d2003240c4048941c8090b00c080030510900520144c40c0800078001e00042c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 834432517 1250 834431267 834431321
    0x81b04033f0c061a090c18100923063412020601080a172d0d060b031510090902130f120302060f0c130806010e0c03100501050a03 57
    0x701d00c0440b035010343c6061010940302882c59850003102c41c00998401060310201c2c41c00c00101d03000d810000d1a0301c19502100191100080c40c1074003081404001070040301c824080d0303403130349020069040c030340d001094422180a00050310070300a180c1a22641d41704c10948603035210911400345035401d80d00004a90302c0c01035060942d000c1c001445e500d00075210b06400082c91040000340c050071507800c50011441031880100116055012404480d07000200c0410b2404840040708420895803201904603035510019440000340d50fa1340c1d000301103504040c01085040c1a1201c0d40c0e480c21141118040900388111605482240d03040c1c0140303017014408140d01c040e000c104018481031325985400311010669405255a140c01c1201008005801800105020345146090240c024000c2c0302421700780349480b070195054030415808041198800c10040200c1c180301d030401d5400640f001110361071032030040ca2802848549104890405c100081c0c80500d07030f0b110380e102c100390041110b021140108241 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 834433767 1250 834432517 834432527
    0xd060e1905010b041d0723040c0201090c120f0f020a030f05030c01110f19050d0c0c06050606030c0f03061813022d04022107081b04033f 60
    0x1010542c00f8a10f401003099079038100c04201401c00d02c03205d000305107281c00d186002490303a2080300e0044001c08040c109201035a12402030240c00b05032540005801e1a5500f01440040d00981c414504181554001400b0600501da008645a00404c244006a2503440800c44009850344050003010500c00c01004009011004143d0b080e0f803200240f012005201a1803c1441404092003900c00d04000100080c06440c420882c00802030422074184401008034109072480c00d4801c0000604100c815010451284a410b03040781068907114210b1a14030316402c1903100e8a6003090306620b0110025080c0c2e59102d1900c0421070340d420015181d4104244080eaa030f03130907407000303d00c0b82c2020f408843c0c01405040e00e0003454417070f090181240c3d20b504802d0000950283d13a41d600d2125062909030b02802440d60070300c0c0104501d581724001032600c03882e14604034038070000f40410520108800c00c0890400d10a403010b84c8000d200b100c0000440103021500c46005012103826605d030380340c0540320707240c201e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 834435017 1250 834433767 834433781
    0x5040b120111130801021204031b020303040f0f09090512130f030809040f090305040501110a080703020c12010b06040501030b12010903030b3606060706020c0304150305060d060e190501 81
    0xf15100c40b481c107455008441c01e030f01400242034800b03c01c030400600841c0c032490421a44540303071620800840003e030042400c50b030040d04440810266020100714031044a400e507030040c40c2c01042000008035690b0344903203405d00e0902c010344101003c1500781d004070051207044020030b17125040c001501c1d078070f150090350764003d100c5903441145403080e1100c1002040c09540380081d8543d48443c54541040c0054850103590701034034110348150040b2400040d9180001d0140c02e0281e0010480d01010508120300481c54042c0c0035210317410807011481d5038554000751801c0d1642401e000c22140a81c0003c41c111000c0e0f6404401107600303110a40085c982c2540c404968a4002d841603c030101120354200c4201d5801548551041074480d044000403400e0807200c0d0300a030740140804d00e804029121001a030300254030007201c0790000141002003060101c015100c44200307060034489460403e0005038400f003014030291540c0e071204101040c900090142490341c00500200f15a80f1146041050080c003074 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 834436267 1250 834435017 834435037
    0x2010609060b09010c02040509030705010908090a0518040b070c05030d0e0717190821010f05090c160312230f06130207060f0c110d081005040b120111 66
    0x2a12801040785506801103440c003040613125109650211b50070f10006000c020142c50441c0418031032080061000c0c015111800d002e40240c6031602e2803201008221905540400e100c1c80b90310a14440199544018640c01500081c0e0010160340719a000e48041d00c41c032a0040c101d0200186403038128805074006288003688808489616480706000e4401c0d00b0003850b00340c1c0780d50000d86c800480d80d0100c0f00905d8004e118074106401e08800d0b00c03c4180d101000101da02e40d0400e004010f000171100448401c00800084a1942850034008440c810714840d4103c440c10302d030383d4154070409050041c1c2c824400348003945010408800d02c0a4540d0243c610041c030ba0121540c0c210104220400c0c00d080300b4082c0000801c800d000589400c803190083d8032905045607100d407104850105000b442c41941c41090180d120032601d601e1300303200c443c101040302d0500014407aa400510240420003d0780c40c1c140d444c10760b400240f40c100b11002944910242c05ca6440c55130a00868a0356015034030017604200b00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 834437517 1250 834436267 834436271
    0x140303040b0f150409020d170301060305070c0b011707081e0f010204030305121803040e0702011d060601110109050616110c06030c030c09040f1d010b03060a0903140a02010609 77
    0x81e4000e003400d40720b00664401420a425000c1d002d01c519056002c01d005910017000c503080c81e641940e54001d00f14250701c00740c040140c00700040000703d80502401d0381c45a11490300140e0034007991b56002c0e800300107029034410006a40301da003001c204100b0088001d0a40e1000319003900503c00b4601c0c44001d50020b40401038000c403032028410040c1402510182e03549502c5407030400046440201c6441001415182500310384510a54091810f20040c80503014894200505142054001c0d080d500c415100107102828000c0312107580b180400e92503002042441c0402d1003140b006030ba6405080410400340850184600340110f160341d8a80450400c00243c5030f0080180030011519200d4401142ca6900300e10304000184071080c0c10001154003000901d000390030200c209010508903060f110264000d00d0f03545a00000c0580306010881017920b01c03500a1200622090211340c481c0c01c083c049500c41911003800d0406c1500800d0b100020000c80142282c840c500c04400074040c00e254031030340b020300d4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 834438767 1250 834437517 834437521
    0x105040c06021902130b014a0d0201050c0f0f0601031202061605160f05070302040506120717010212070203040501120c020a1502130f030507080c0d0308060409140303040b 75
    0xc030380040c3c482c07001034004203406010300012007403030b0151006806d02030400407a070081003085000203030301201d0411300b40340c03581103010220310020080f200c02000c030b40342c6071056901c02c105507a1354407040146035083ca4090344840040400b285070907000050719010b4024050280c41d51031000034100d0481c3d006a4004480741d03a000030aa0311060280c8588018422020340348840c64001d400070309043c0d84a005a1032844101d464140000f14001400c0380c25400041c8c04205525144c003400d81c1141d4210780041c51110841981603a9422512501d103260f2004002a00e11100030b5042d550441e0710140b0801070f6140902009440340d0050180c035002c100000589000000301d07104103401058560018842c204107a04ea450012804510400b00150200a03503884030f1600c840c504014001006903140550951600340d0402ca2280c00c5100d40c0d0741315a46003019035886500866180b80c250400c04015100c850101380588202e00c3c01800d02c00c140d047d07003c1d00b00000402903110b68001e000b045844c1d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 834440017 1250 834438767 834438793
    0x1b031a070e030601090915140702010608030a0e0409020f041803030e010212010620010e010905070902120403050c0f0a03080405011407050f210c090307060203041d07020c030105040c0602 82
    0x106030124010b401d50b11140040c03006101682c050062140111741c18003119a0802c4507800355200d442c85010740200c0007081c080301c40c0d0240148005400c2c000003441c10103440b200020071000e80020316511894a0f020450159214112803900d0040068014084003820701003a034401d010386013040700021324102e2281d206031018803d90b00940203004a00c0101c0e441c10310100c506003a0401c0d005c00c00c802070146146000002d100325090504020700200305081e50303091443c18102c00c4c0d0b2200280d0f0b0700401000f0450400032182c16031203985420f0158440b401311819500c1c01c059440000010b2180c8a121410f05402004203441103104100902a002c451035240d5444103080c0c0302040411000d0026140a040050280110f410002c010000380010a510395502c00c000743c0f6490145000000c611000303040034050304014000782d00007545000d00e0024000c021202d00c00c000e60302968100041000310384280001c40341644002d00a02040c145420045006012882840c0262155180030b00c00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 834441267 1250 834440017 834440027
    0x16050f1615050f070807120510210809040507090b0301081e010b0a0608060d05060f09010e0d301a030c01140d022a071404050c161b031a07 61
    0x46076203030b00503081c8152a00c0b101945d0620303000d004a4203201c5041c002007244100d51148910038949a082e0044080c036014000c90030a018032031b40c80c1c400d06000188404039072440d084586141c0250740010f081d83d07404400f01d0310310307000d60449030031250000700010780c1c58400205007901000d940345551040030000400c80c2298110050300340c00c140114000c014942c0039a001e40da100c076003d0060384003400e15540755801c1c403804861030740c2100b24010500548032002d00c2401200c0700100000d10201c001280044d10a0fa188e96480c10228041400c07181e000714020040300d4109544142030058218545858105809401c10180640315070640f00c52150320070706001d5250750100188500e48003006030502d001e94010607400e882e1030b041488005800441c0c00703442c0c20b03041c850b00180150f01d0030400d28090391214400c402d4031480c1030400b480603d0500c3c0040318686c881c805120400081c0924040c000a00382d8050381d44684e8820000209200042090f0010301002c680c44610a40c1c0d405000c0d64 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 834442517 1250 834441267 834441271
    0x151305060103050a0c0c02090c04150206011a0901090b030c130909051203010b04120204090c0303171617091c0905040506040504080f0705071503020c06100b0316050f161505 76
    0x20306d48101c0001600701b07503103401c0d041440082c0c07041c0307403036201c3c0c0700d040b000d005291601c0f0040c0c1c01140104208017012070000044943e602903545850019030008004c001d4a00442c0c1045800001049848607103104a4185d852100a1141019035440b038000061014804c20780c0c03180190800040440c1000040328107880c103600500d4207150a051b6098082c0840850880e0065943c44800c80441c0100c14420b0085100ea920840c0125105501c45e00da0080500004080c040c5040c440c03c2e250707040b014000390045003500c8105c0ca40d450038074031440c0060740e1380c142900707840c11944103800b075506c02582d2069400540d4203018030784401040c401181c2c811100544022801d109000c0c1050702c0c40010051507004508845416480310f00030141c40300c0303a41005001c40d0b80001d0100c18240305200213507011078402030713018001e8a040085803c5110080140004031402c84598a81034000c20580340c107001c501d000e06840307141d048a11030303066480c07200540e1007881d00c008110a4010f1402201c0c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 834443767 1250 834442517 834442541
    0x70e060f030f1c0e0d0f0314040b07030311190207090e030c030a0f0207091505130e0c01050d0e060406060614040f1503020909040c050a081b09151305060103050a 71
    0x40382c054480104507040f4940c1103200340c00c202c03900300490310550b1030140110041380211014502c1c3e403514600502040103070a00340c0e000c248140000c100d103420000a40e000c7c0c9405040c040707641d100703403980c0075454440e035103500c9441030307258510384a4a80d002840000743d818813182000b480c006050f80340d03035078011511100455031080082c414070920616000601e070705503004449a05841e1a0542d081d140c4203040001c030441e007141d0402c02071070003030080002000440380801014100c0d801030380e00c601d840300d60141842000203000c2031491490303103c00c0340c41007400c05440b03c41c24146403c002030104e45c410500080d0b40b00481c40c50300c4801c1c0c5d08860468a40c543c070601030601d064008420120143c20043c2072660034402c150f060786412040030310684c40f61010489040c03d043c104064640f00c1d0f00410451341c000348154103213041c81e60f010f4140310b0f412242c056040e80c038085010050340081c00f20a41160505c140e90018040ba0740006028081c240c80c24003155a07501140c20071541c449000c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 834445017 1250 834443767 834443773
    0x609010b0d1202070b161101030506060d1505100203180108010509040609080f0703030c0909020301050604050607170703051207080f010e0a060f060c15020306061911070e060f030f 79
    0x90000034150303806000070070700c00d0050340c0d40e00e071741c8070002c0380190021a002d540c601c0280000c00c0030082c001821404200090804025a080a001186a50040f0300c2144015a80d540090f00c0d4046002e0382c072402020010702058a80705c120340000d441e80c2104882d60348266009812200b55030055017018181c41000d004401c4660b26900c5900c003030005c074582620824000c00510103a00360300c0c00140342050013602e002c200c08003c848003c2c460300844d8004032a0074414001840181d030348400b01d40455204503410340d10759800d42405d036903d2580c0c83e00803008200008040c401c26070400d02924008514205a01c890f5943d2841070f64502002c542e00310490300d00c000184826148480c60320341006112400282c01901e841c0211110101d41d009500403810421428003003204510407401c00003017041c400e505509085011944600400d0140c041c1d0900a07580300a041c0d100303526164629000000326058140d8602680030341074000d9a0950040041031003090040c01d00144030580800e400c001 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 834446267 1250 834445017 834445039
    0x90c120a0506130f060504121715010c060e10140708040302060a0906150314010f06120206070201180e0609090d0f03231501030c0c1113140f04050609010b 68
    0x1440f156080044821074500b03240d0161100415100c4c462144100e1095200b2300c254440858068000b0041e440ea550b0700a42800820859116101d450400401e0a08112030b42e0303401c902d044005003841c80541c00151152202452003242035400921103000c8000b43c0120a40740c0e0a4101c0d4011802c440c0903025a11020200320300e401c05602c180c01c0c0e0f0b802030400040d807920321a044003400c4280d600c151007a00d00c0d110f8400002c4428402c4035031001d90100100072440c07400440081121030144064840c110100c0d0000969000cad0000d0803010400010001025840d00948540c1a5050312814028540203000403035000c0005420002850300d52070f400345208810900710b005d84030270f40c402c20000b241c983d90030030700f00c59000800307005000c54440448112014400102260020343e84c2c4070402440c40900d4003c85c40240314050340340b2040d1034440d4168145001a000790481d5039482c85030a800c10704000380c011825440c207018510890a4405640f103800341103098803104a800d60340030b50200c070 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 834447517 1250 834446267 834446281
    0x5010f020a120503151011060a142e180f020901052a030a050c120301050a0608060a0b0f0c01061a090f03010b040c020a03020c0103020f04090b0414090c120a0506 71
    0x1011390380c44000c085070744410b64030301c4000c074084003041040200440e100f00041d0400d1241402001d1b8003102542082240f640003507021070411101400c841d0040c544112803d45001c0f010002060b501c0d641c07000c600c0803e5540c20015003001c5911201d0780308034039100c05505052094003c4908240e4141d4410382040758003d0b031038518510383c0b007401b504000d0085550b0f07402c1c03905002400f038516140c2c845503120000d51720240c2c2810402d5050103281601000148502d50312a00d01c0425201145040041035a8000110700c68514640040c00b603c1c1005c0b40b6500300740c40c08802040020392510080c4155940e4948000305100c441141d42001c141c03d1200303e0030340c203141d2001d110340c0300c00500104003122014041812110b1042081005800c035a2180040c142c0402446404640078a011490120501c1501c1124040d9000320b2410316100d0305003071483e41d51500b00d1201111207154821150510354002582c0e10200030129004031720180800d1441c060100760001070b00e03001805090240d81701d503 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 834448767 1250 834447517 834447527
    0x23090a0c0806091b0a180f0f090605010b190810120819090602070501030207020109170a050715020601050d021207151112180a0932040302071e0e0f0105010f020a12 72
    0x8080c6d10a01583e03004030841200450062800f131ba01b003158000385030704003405c0000549005070490600c28404000c0f91440d03010400020340780011520f055400390f1500d036144c24031000c180d40b1001e014100840c2e84e000f4400d8442c0146030304c040050b10808000d841500c141e45400044c4100d00258018450411881d402a0018880d051051400415503511100242d040c850710802101c41640802e50400400004010101c043c04200d01c0c0c560030400301030002035440005000d41380c01894503201c00011074480410320140d041800060301c00c120344801f0b00b050a00080c03054600001c411110000c0010404242c00c9050780482400d03520303111140310b480720717050b84d402d0350141c20006010000944803224851031148001d9080c0041d00007122140752056004000490083e910100041c800000d400140700011100c40c2c2c001c1c105010024a03010078092150f0f0b208802e03036014a4100108004690303400c42c10390304243c0f50480450031100c0308a98407404407500514003500e402c04054003602070 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 834450017 1250 834448767 834448799
    0x9100303030c0e0d06140915160c0515060103060b21100512010504060b0109150e030c06041202271f1a03040204050a23090a0c0806091b0a 61
    0xd8200421025610070105003416418a01901d170659210803a01d08901c624806a40000c6480700400f1446003840b0210075290014100b041c41c0c140215007110018085c80d227510103a90890252080e140403002146102e00c000c45109002900d0200041000700300601511450404071402d0800d003e1200c4122008030005000c120f0500d10f0848002403654884ca205121442d00b140041160304140c540f60050b42c2582600c24103000e01c01d541070014401c075182e03014190706c80f858050702c00c00300c3c60b0109041881110b413840d001400007402140d252455001c11508502c26a0f4000030700f104402d0b0117000090740c04005504012010200780b4000c12540d440740d40d18a00c2c000000305a5071078a080b1043c0701945200b002512010080209600e070510a03030354448000c2c6c01c148500240c075130340e00300e680000c0d140b14900707041104041103d2203401c0021141250b0b020a5540d810307626900c01a07170316002111031321281d00c1100100c50072003000030000d04078008017400c04a80c041c04c0c02032040301040c034 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 834451267 1250 834450017 834450041
    0x3031615060806040c150f12090f0b1611190314160c05011209170d0b120604120207031a060420130f0503070608091005150a050910030303 61
    0x21990007180007401402804e000e01e200359894842d8514150064034845865600c210900c191400d0070348240e500314846022214040100140e201c80b1440c5c0314000004160000d003455200d08200300d82444d18008105410240b41c45100180034070000c0d07a40c2c3c52140c407042c46d45001c0a400840e0002e400344034842d403401c849115071810302070a03510702003403440400d41c141c40705851074004201958000c0f090345184a882c0e0401d00142582c1c3d242d18040411402c580401100c0002c1c1c410b0609850b54004c3c608004010075211140300c10041c016900c40080d80c06a401c0000c11076840141400010130904482e4860121b01b02c124000010742c0c0000001170420350082c2d2914004110b00710400c480d504c005144138240d0791140ba00c42100d505484054100452207000305106110303a503000a151021185580340007092a07a07600012800c150101f40414000d43c01c03d824400342c20800d0460f40003035403040c0c03502845260349000300700300740b0416150b4103810801c0706410310101c0c0c841d402c00d4181c121 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 834452517 1250 834451267 834451271
    0xd0c05060c0f0109051b01230c07170a0b01050d0b0402151204030804110409051903030e0706020312130b04021e0a030b0603010606080105100c17032403031615 70
    0x4600700480742503413a041c0007258590001c1603c10740c0000007006c030303e00d8548203107409900a840c420200641c0b0300140b0140030f5110000ca0500e490100420051010b01450b5181180c0e4848500e0307555916044001b00b20b8100d00558008180ea040c161008818203401c40c2182c1080d0301d0350b030244038000c5454a14400c801d07104228200344480120140e600451095844819a10f071078188120700c100681140740c8143d041114460100d034000503403070240120105001c400d040b49107070540091003155413900030390041c10000640c070f50700070000d4030f2404902a4603100a544040d00c01c0049820000d00410a9600b000440c025085c200c0407040406290f0010003884020a400542c4100250380119402c0801c203040050500702170144400a0030700b0b00f0070050303550600d000079807040c40c0304c80d1100030000e007034584505001d803407550900440b4044642e181d40707040802014031a4241020504041402a404d541d02d40c100001181c149150480300c00340c4c8540c990340c0b80903100640080100100e9 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 834453767 1250 834452517 834452533
    0x81906090501090c17010b060903101d070609080606011407030309030c0213020a1202030112120521060f0f030d110a0203010e010509150f04060e1c0207140d0c05060c 73
    0x1404c122031000a4410804500c00c281c1d00031001e42e09442210250901400b402d200030030881e01c4c0001c86020460301e40e10302043d40c1d8144401480240b4030320521010030300c1000c800140c4540c018000100340e901a50650b41287d94140055489000003d40d00300001d0007041000040f9100741d000d0800710f0300c02c0c036212034640401c0e00007a00381407110b40c1602155030700044001003e130704020181f01016a0000540c290740c03600100139508140300d9005000c0d41c80c00249034904a2245c03084a454149040b01c040203044900c0309560f14150880d5543d0040d0041007505000d0710740103061200d03030038005006008ac0c00c420030045410f144001003a40d00c1d0b11a900e60400166001c0c010103001e03500c03074000000e8511740b44a182e8908401700b0305240d582003041c000d01030000d40380406d007980720b40c0007540821080900c091880c50300340440303014094210000c9648140030303070228911044420070054895191040410450701a03000a0010884518140100054100f20029100c0b51740300c802914548 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 834455017 1250 834453767 834453773
    0x21080c0304122f1b0a050d030c1b1814010603020a1b1a060603040308070e1219030f0504121506030209070302130f0308090409170d09060608190609050109 68
    0x1000d10100c43e01d018801030051808810308114602c00748031100810700b03109400703001085428a40b400341d1401a02144c245400f0715005041c142d001caa0b0000f250540c0c003280082c500070700017540c0500b4914124803d100c8200001c0750198904802c440c8500000c10b910300803003a0003c1d484800c421047c8480b00706e070444054045000c2c103554500800e00e0740c6d00640104c0c4030740307030200c80280705034030035074051050002203540700700b5041c1c0c842c4d45428000305070300d042c00c0000e030908142e03132440042c2c1c82400c05030520440080041c40440e8801e480c0c86018042c010740c1a0b070305001c3c41c00784d1448010544109800b00d52103540e28120520b041000280c450b0b1030350003290303030148200c801a001c20380001d068441d0300d020106450041075046901c045030750030b41c3d45040441c80341031101c901c910f85822005046c0a084914401c139803096043c20303644c4201d01145100601500e000035900380749001000034955101007154200c0403100d60390040210b0290365554010880c8240075640b41d9070700c000d60000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 834456267 1250 834455017 834455057
    0xf1a09062b0803101a0729041110030204080c0613030c0b190504030c170f370b0c0a0e041104050301180305030c090f060721080c030412 60
    0x560244403001d40d24601080c421941c2d00c002e45c840c01001d20064138004001c1d0760101981e51059100c00c40c2484032401d0303112419084d040200c0100c1074200b0b50b043c08200700c0d03103118003460030070300340c4191240303608641c0103508901481c4203080300c6420910148600786044070040c02c11103801d054040d01c0903140d8548a060007120b07001401030b40c07000906a00c0c0b105450700e1000000565240035031038107046945e007075118415071182410b10f108200e104489082c1c103000010400180d4030031a04c00340c600c120a030080743c210340030022040d9280358480302c0004210303007104080c60300000f010760180c4540e00c0031540c0d50b00103254241080700140726a4800e95075030151600003e04030400700c0e100c5050208250031511055031012240010b0420000042e810a050700d50040144805944440c0d052000c60301c1021200d20386644210000b46480400049107030101203424a0000610000b06401e0103485c2d039201039400c100c50003c1440020005001508400321000482c9424045903980d9041d56070 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 834457517 1250 834456267 834456349
    0x3090206091012021206120a0515040501090f060b12070803071103070806091e1605100e0405010e0411010807120906060512060f06060a1704060b060408010f1a0906 72
    0x140c045d9010701032009506d044150704200100c0300000d0100c1500a51701d2540c2c0e4a0410841e1000342e0700e58002406220713003036000010b00364200500e0303c0d16400b00d2170601c009114007880740d442042c0340e0010f1080644d0004401060340e403441c1c015890314000383c50789c0041c03800c061078060340761243d44000320b001801072000754014000d8400a040110300f1000c00c040100903201d90203042c0c1e00503144283c0d10700c040715020084850030f84a00403140d182c8901241e11380c02158805400501304000060034292039205076100c1c5001e000c41401c2d918a076001180c81401c180c0e5110001000c0305000041103c0990203240a10310548001070b0565803030700402d0007000c100500c4c1c00590044400c05c00d0000d15021070701c0e480b4404548051800d2003680700034040d100090b034603001360340c11500042c0800034942c2c001681848003c3c181900e941c0d940d49901e000e07122401c01070610500701007201c6103003000b058100c02c131070600400c0d5001c2c40e81d45005201240100d40c09071030305040c2c20005416182e0000780688 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 834458767 1250 834457517 834457537
    0xa0204030813091b0818010f06061206050604050a0e100e070513140a0905190501230f010507060f0914010906050c0c03030103170c120a0f0309020609101202 69
    0xc2d1050b8607240d035400840e0007070074190188101c0c00c0c03031010303116138020241135100011409100141c0180611640107180055150202c41d290840c00708003540c0010b60302c1e8102c0242541403240b6600c4009010050045200d4140c002c40400c80c01d02100c503041460542c4868051031800700b00d540d60301545400c0c02c059558402043c00000d4030b0302926440500f242c007404029014405010342d140104001c480b85106104c501a554000303e4030b00b213007140b5050403000c01880180180d50311241e4440ca8100c40c0050000b445a114a11a030305080c45d811a07240042d05840d0309007000030584075203028001d4581259107480d5101c0c03412000421138204d96028401c070f080001001700309850044116a80035003c00351940b020b200c0c90306a003e0010489041d60362002c0c0c140035845215881000c54003446014441d94020404581c62401026014200c120555680e240c01046910801e4084030b000280c00703508110200140441400c221040f00d0b4150706520b4000000310407900740d44101c1e0041c40c044c0c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 834460017 1250 834458767 834458797
    0x110111041716050402070302010b1002061e0906040f0213060303091806050d0813150503071d0a0312140c0c010806031203010e04021201090b010e0a0c05040308030a02040308 76
    0x51004400103079680510801000050082d00041400c103070401c01603109284c403036a0002105402c00d07100b90010004580090b004144550300b01c8000380d144c03001118401a81d120000f005000507804070f02e1640a0060341700540650b8850317455000c440380c1c45410a0307030881d905101000b5040303424492940294000e030390b034010441c101040700d00c49942e2207501c01c05490400c0414050f5507140c002c0d07105600e6102410703903580d080c4030082c6035000b00e81d41e02009114a5900203440201c0e005002948140203643c3ca040308011180311200043d604513031915040340c0e4000050000a0b100c2841c0d41004505040254228401074010f0503d079000c41d03018142074010500b00041546c004800e01d810100440142186d200044805006800f0511400c0408501c07400428150348a810b03e10182e441407000901c455610346c200903082020038030401085414040006140310014410001802800e540d000c0c5011301d56111150581c2001d410106915400c000000000c1c0459008290b40e00c0d401c508 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 834461267 1250 834460017 834460019
    0xf0e01181d09120f0306090603010605060304031701091a13020408030c0c0306150904060f02120a0509071e0303270312030f050c0723030c0f120406080f0711011104 72
    0x2c03441c1411a68003040303101c040f06002040268000c1c2084d41d9001c007040ea103400d215999400000e0141c2b030f840e84000d4000b40c0000620007450780c4446090030740440c0081010031a640e4028a0080b0780041d404425008035811495003a0719001004a158400c0d107480503080ca52a400c050f42968441d101291050340300300d20241c1c1c6403d050102a60051100e400000841c0401e03000c90711507800200300504c0156078807150230035840c0302d505541c8d2800c2030500000d00c07441c1a08001c00100425204003000d441106000280010035545012103420300f90394252005140d50b500b03035162400002c0a8285044513288807803c0805404040010760203014101e81200e10a00058215400d880800c10780600341810080900164406c4810407584802ca841c0b4035a00c0c00041b40c0f8190903020041914000014070b5100c0d4040001c8040d2030350002c009031008a00c06d0720070b1580a20591280c0070105000c000045c4460100d00030f46503100e5642d0520344502034661076040d00f103d0301e603070407d0b81c12030300418 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 834462517 1250 834461267 834461281
    0x409060e1e10050c0a0f0203040b04060e032a0d110d240605030a0f02010302090a0f0f05040e10230108060711030c10020307090b040b0406030c0f0e01181d 68
    0x4040314103a81008200f603042c40315071002e8501c500c0d0800014060031420b58607055100f0070855006000456070341d034840740c0b5603400502c08042082000e21a03c264a004d40c0207100059038594915040d40000100a10301024000d1540408000351b42031b41d0f4408042526458815007804400e214ac0d00e0004855035846e45e041100c410044a40032007490014140196200000c8007110b841d0084184001f00c0f0162004a010b4400e0724441034010b601a8000181611aa5002d9081e210408503025800e600e580600c41100d640c0c00200d24160b01400c0e5a1520010960002d00030346802c1a80c003a102c1c44100044a241c1400c3c0d02801d1160301200410180c7c2d5404a501c5c2030313800010300a549021a0002035a650303048102030360041543c0003020a9005004403491001000820440b50300c0b00d03500c1c0b9401580350001c1c441c00004c0303810900f44c03e42480c80b90601c1440712509444000698600e82c00446001d8403014100740007200415000c1440d0007581e141f02550401110142c0d6149403841c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 834463767 1250 834462517 834462523
    0x60b1801110a112106090f0615061c0c03060305011a011d1507080405011e120b0619030906051b0a03090f0c08010912030e030a080627010e090c010e0409060e1e 70
    0x40389201f040c1c8c1050040c465000711741041d14400c648100c901c1502d64480754401070042c0c43e1003800e80e05491812000d481041c0c1c250300044103c2e030003a4001c00440282c00f0008021070321030380c110303070009000350281110b284404400042e101005401d000503150504400100756114000c251b4164134081010442c031360b404600000003541c0e107026842002c5100b0004ad1170340d20200c2401d6401c83c0c840b082e6241c0741c1c840d02c0c15100c0f0100c0400040340d00c01d0742014061f0080030125000d660071030410740001c508d141c0351100320b20f020f100000114030384134110f0000c50003401310314000c0710114009110403000c105040f81e030780301174920500005519012460900009005640781800b41424400400040040441600d003800f6140c1840c1a41c0d9440d540000e0b0b0902c10011644d0968040d40d518a001003112150716040e542d8800001c119515804020b035540d240c0c1e007201a000440105402d040b9040c0f0760407283c45144100f0010414501030101d0700d08082080440502000300d018010440400030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 834465017 1250 834463767 834463783
    0x10e130311160b0d0c0207060c03050d110307090911030c07020108070302071b0608090f0319051b071a090603070c11120606150712080903040801060b1801110a11210609 74
    0x150000301f003020f01d043e001034081c4c0ca003d0405002c0c041d0100d6014000c06d00c640005841c9000e0119032552840c0081003d0001d40f04c0f0f0080d407034150300e41680c806000c051402124000d41e154007034141098150340c01100c48103001000d078010150240940c00000e00000da040702181d119070b0386207610606100303004014140c02014000700d940700c00301740c0d4246400401240c0030002c0d16041d0400000700110b058956104e00f45a9684107941c6040140103104081200415201302680d203000040c26004100900c0c010448400e900000810104500d1406100c5445d10381d41b14200500b550801c183c0080c1b040040103541d428550420404c0008070301e06028142012194802840e09042c01d0341c440507400c0206030070748010321007400049118441d00304143c80080c0700920090106544034140c1758595005540c0c100c0c0000b000c411001100d600441036241c000541000500a0401d1502c42c00880640c919481c2d41046040c130054034001203400890700d03462900401800d407070074102511031402240c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 834466267 1250 834465017 834465041
    0x21090714030c130b0a12050106051504180c030905030a080115090b03041415150a060908030d05071809091b03080a12140f060108010e130311160b0d 65
    0x7031490820070f540f41c0c5500c200b440181d40f800070b030452008000c60022801d03a00f161050286001d100c1c020440c05420500517624281c40203020b28404084015841c055400344c1d1111800c1c01c0606604244141d0104000c94010300d8003040d90841ea44885003075501001d10040003070110001813165440680c09440c004c511380c40c01c00d042a2400700401003c1c0009080107043c1140041500600501001410b01c80c02210315005001c2c101511a00000040000b0450044451800000d2814002d000300e104564440c0050352034154920b0900d002408000c20320024400c80b403001c183d110540c1c0321903402500c403e040c002030030340850500d280c2145198900b8428110103100c280001a68801902d40d034440f1420102006000362000a000d0720500d1000d58802070741004201c0030b80b061055203400b40a082c0c03034500150740c071000c0356010b64000720303464682c0ca000030400304002403003000c40c1843d0085c3c04090781c0314590040d0944282c003005510040001e000400d61036500c40b40740c0310300605e801c1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 834467517 1250 834466267 834466273
    0x6010206060d08031b190801050306040c0312120509010212090d0e15040305100b10021b1504090f1e0e1216020d030305150a14062109071403 62
    0x54030390001440c2008003440180701e58000700201e0090101e408106003406a0b560840703840c3d18100e01e405081c090011041b4001586c1440002810f0501044090003181c01c0008842c0700e83c01d603201c101174883c2c2c58001004006040088504100c110300c11103005003e050b0016954692400d07080020759000341070380d0007980000e001d440c0c040c0e0701304886c0d0404c01e409940f62115401401c03883e200310700442e8409041400303031455210f220300865000d070a101504960810152980d82e034201c0e0303207803000c6c142103030180141d520040c480e01c0d211a01d265100081100b0f03038501911601d120040c2c44009503100d401940310114082c040354024410a403150380d0310010001e101006100c107a0342d110881c504505480d0029100004e501c0481407044025000350101d03004448038174005005000480d5002c03070071076080ea450442894031004410444500500120448009404102c415070098202c901d82d07a801d44469142042051205446004400d0241010728540703003c01001c5081501401e100b90 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 834468767 1250 834467517 834467521
    0xe0c09101e0801150e100e031009060516170a0e0309040e0601031101020d050d090606030204020316080c04030c05060306011e090e1620190c0f0b070f060209180c070b06010206 77
    0x1440d02d106c055140c401d503191a021289498001ca8100130007400c00c0704003213041103200300c20b1003007e4204900420040100400c000c108210883c0d00780420781c0c009a40c5045180070418005458005032407401d000003e582c40c062000001400301c600c00c035540d4160341c100c2001003092142c21503c2840f101003c2c0040c2c02c035020b40c0b0f00b0040080c46a8144e040f0500c0c3d40340d02d10380a00905a002d4006594081c00841d924100100900249801d009040b00000d800000050100c28800d0641d802c80b507204503003407485400d01c001c003c03041d08020b04246c100300350340300b1401483c00c40401130400c1c00c800e42c9480b07070710b0382c01e050703a41c0302602c001002100d1140090850041d00f82d4402440020040c16070b500084da4001070081a044c18103040c1c640340c043da40100d204050041ca405c0c1c0d0b1003220209038041c07000940d01e0034113854900623008054296070b2000080008907640d03070000d291303c00004242d94005070b50030342200300c00501a00e01019500e0040303020002c100f030302c21907171750001c900b400102924 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 834470017 1250 834468767 834468769
    0x1104120f0b13030504031205070803010e100918031d0a120b070c1122020406020d02010e01060b03071b080403080306040b030105090715050d0e03070203070e0c09101e0801150e 77
    0x541724510004000c040c4d0b403503040d42040c0c03150042c0d6000c01d512405140d62960740340304154074140140c54662002000740d100103012150361055003080e000703503802c02d04e104226850644a00c2d204080720300c1e5818024a24003110303a901c1101001808da40310020007100c80c50700340b040303000038028881402d2002c0301a010b80421124101030b602c00e2021181c0c040c02c0c20345413103e840f10386111440340700d00b41d0020801050f0141c001c5420a8001061f50007000503541e1002c40d1420303200c052143e0b03902010108041094940701e001620b208020525507500e000400c0d41d24188291f000e9401650180300120611a1600d400c6c0144986954200d0082c0300c107007003001650761103000e68402c0681e0902410421400da07030081040d03441104070400d0401501c1e035000030140c1c803640f000074124800e010b444000b00e202c075440c9903840c0c080c401d807003e91070504100b9014001a100700040e440144660884081407000002000c40c0041020342c2c0c585405500d000c0c0c1c40341400b202d000028040c003144003031104407 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 834471267 1250 834470017 834470027
    0xc03080f09100c0509031c0e0618010f0504080a0c051203071a0604090203190501050c0430022106010503070b0f03130212030304050c010305191104120f0b1303 70
    0xa0002d0040c400a9072501543c030542d800c1c4a803105064040c01503020007507005010b00c41c008015540c03500d03280d101e0f0b480b81c01044032610640e440380d08181380040c1501c08951180760440055011070400300e207815151281e85141c01c80d100011200346c4e01c01003051000c0c0c182004c1c01058480c881c00154103042d955a1504c461035450300c041420f402d81c00f40007501c0c1c0c0e136031604000e032020340140994400d001ea44041a21031070314a0426a84c0d5820030021443c4040796900720303030889284000c0707840c0146104049002c0d05184c010904000522115102c0240c0c2e100010600c69504400350940c08184209800d0306000059000341d100ba0890300c03041001100c044202d692040f807440e0344a44d265120142043d02d46040000603402492940d04050410400030055015900603005c0314446402500114242c500071107926400341c0341a0840c3c410080709030044419000a440014105900d8100031014040d91101c1626030b442c10042440a1000c40c0c061150800e1405818403008900340d00d000c1c1c0707 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 834472517 1250 834471267 834471283
    0x1603080901030c032c010c08160c0c09020f09131506210e060405060105041e050a0f1109040b0406030b01050d080d0906020703020d020718020a0c050d0c03080f09 71
    0xc1450380700e08602c03400c18401d51100890031240c06200c1143c00c1741d10301000d102c1c05190140a4590f180c9040c0740700c99800341c000c50f0b200f1301e2002030b00c0310840a83c4000f1140c843c0d43c2201100c2c0c0140040000c2481071041c0042c0040c0100342030855125039188041202d0741c0d00018100c01210311700306000f032011146201c1801a1022402c000c0a00c0086406182c41e26040902c0c903003844d850010208010103000c02e00a0103607026808850345641c0343d408100131036032040c1c4a0340f0604920f80101c0c14819003908038540c40240100c000501050b00154001620403903140c82d400c0c4d0000045c0061246081d01c6050040035054504000c400e040d9640d40c14540c4060141e684200151682a420080001c040750500c0000a00600a291061511601039000180300b1030140c06010a0480854400104c0d001120114109400c03440c00d02135010b002944546107410801200c650240701040b020400b03042c0d030b108282d4079581c10740c4403800c0051038101c020b00592020219041440388a4800080381c1d4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 834473767 1250 834472517 834472519
    0x8010e0a0e030f1614120901080c120c0415030605060a0e19090203040c06080f0609071803081b03030709140109050d0609020913021c0f020a150216030809 68
    0x100c001e5503950092550041203d0240d42c14000620140081030880070601c4003841100c2903880b40604c2001641c803002040c18107007403640c0502c500d125562140c8040c40d00f0210500806207007035000c0121200c4084100c078008491000001c0030400c1000718801d25140070800d00e800c004440c00c12000a40603c929a04402084000e08041401e0740c2e81c0e09890025450410305200744d540c0d1580c019002c0d4100305c40c20703507185149510018015009164403803158a4030140c0030010381d81c610810000b41c034003801c52020000f040c2e004031440c0b180f40c403205001d140941100c940340c002c40061008660101043da00013500240300303000080b6001176400c4103550821003100d14500d103010048800000343c1d40100e0b0701c1402518820305003c01d9510446d80325009441d07620b215601c2c084941c11110110b50004d400050540d011341080c1c401141c1a00d00900c248100d41050701c894000460805441e00100d010000c0c4c04011146603804106d00710100380c516015130350b50741c07542d1240035550007403203855 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 834475017 1250 834473767 834473771
    0x30f06010b03041407080a021008041e150906090c080f1903031503030e01090b18150c0d0203040f0807030f060f060506040b0d0f1a220501091b08010e0a 67
    0x301e07040000c01c144c4080e4032101401201c50b4581e0f40c00e503080c1d481c400c50400b81d0003401010050200b052049102c544034036080600d001c0384a080c3c2d85c01070001c0c0108001524120039100b10080f0188450080500c0d44e4000ca102007070142550800b9800e90845512000080e4007505002c1080350011074000540d0901081002802d0418102980030381600070424460031000c0602004064005400c0c440c880e600782e039460340c0302e61200301f01c4142d441003481d04c01e400a0b54800c18038441c50003c0c9007507000c0b8494002c441c1449a5070b03601510b011902211007006d0b80001c90103210500e0301204107001043e00100420b000b5180d6114180c0030038201c0d0300a400c183d22074000c80780d030352003d070070100040c94042c0c5000c0d074031952518544555000740030960845420071188500f0a03d02d8043c1c0c4000c442c01021200c00b60f01004104076482d082c0900004d10070980c440701118292962107940e001304080301020400011448c440c8170443d600d820220140901071005114a841418420b40d000d4001440 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 834476267 1250 834475017 834475021
    0xc0c0213060905130312060807090c0309060603110306090706120504020d020a0306020d060602012703260f01150c03080603120c070509061f050706021b0703050c030f06010b03 77
    0x900094601504000b1449042000344044014401241c1c003415000343d0b62840d00c02c2100801c0382c190b504502c80c0d82d0143d88804418426003015a100840da5021410009850300b001d540d8170080c0c03203240d482550101c4440b40a0222800c0520400c3d6200e244136025007481400e01c54050148640e0204080d5119540c01c0080d0441d03c2d00c400c0c490f100368004005400d62a80d0349400d80196010121000b200350070441c0000310140140940002000c01425a004c040556078060340b4031404201c1c2a410000007020700e083d04c2c603585250420180c14201080001d2a0030840601c103194103030702120f20f50a4942d409900c00d6400384000180541c5458080501c3d124440042d2504420300000300c100800086c500400300b4000626100725801a500002d4555419007000b21200d50098000c49110344c1050003990300d44500001c20364540309903001410036004003140c0e0141c10b082c5c1c17810602039102c0e0301c0c20700603c80108468880110110010080c40120310105521184107100d048844800440 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 834477517 1250 834476267 834476299
    0x41104080601140a081009060b030c060706021e130608060d081206060c01020c0703020a140a031212021804140c04060e0f1f0809060c0301120c0510020307150c0c02 72
    0xd500384c020240d001c200d82e1030041c1daa0042c00148064481100c40303034604000c6044606000c00c0007000d85600070220b0342042c615480c4c0324007130360100c3e18100c0405146001c040b03054902c500038040c2207161940fa21205420610081c1c55894040c080d03500c514202114140000c0810080b00c54541c004941c01060780c031500085803032030062401030740e9254004074031400c41541c00988d139000ca9008407070b0700c00c60355a210a01051205501a25a0040f542c500f05001003800c43e16084092080e030b24240e032982445d443d0240c2203806c000d400c00719142d841c3e221011107280074000c003840d45282e00702c1c950850400e5100301c80103110f184654400d20400980c28030282da40d0120301d070302e00c0201816401c4114050b044a01e00718640951000c080340b1640003142d6100400500c0a10500d0000001861030342443c10000a1141e07100040350aa22446400f003810340f5110000c400c0382d0249c2d001992209c2440ca80070300c0c050282d01d00b02d444949084404521141c0c800907400240b601920810b02c6a01c10803 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 834478767 1250 834477517 834477529
    0x50d080a020f100207150b01020d2019050d1409040b0a09050c0310060f020c010e061b0d020714100f0507060203011d0606070218090307150203040204110408060114 72
    0x40c44505041c0254034000780783c4203031900141035152203004410100c0104510110072155002c00c12801a80704008170b40385240200c166140000d06000d0340c2c1c6c0c0800ca43c01146180c03110021001d807800074500e00440030048200401d03124002e050810101d81003c05840300f00780d00030110342521403a11030139011044c1d01d5115a4802418440c4020702c46854900c54091440d48142c40882c0200184040041c06910603807241140c14260750103441c2c42d030508001115a1222900c10690060040043c03800c90015011101040003000700a04984d22040c00c0103824803507258008424100104c1e03e0000c0c1d85d849a011404945060905001c4840041e4080b201340c0504038005128134400400801c4e080c00e0580a41c04892321040503011a036245010b01240d03010b408030080d0805174401c4e25142c6031002005140d0b2048551048030b00301807490703c8000b04608101800d0f13100d542d0002c10b000550415010b40310600001d0700910380350034074205409548060520883d003100440c03801c2c15000c0e076548 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 834480017 1250 834478767 834478783
    0x12051b130b03161806080402040510170606031c1e0201060f0609080c060415030504140102070b013609020315010e100e06030c0d020f1206040b01060207050d080a02 72
    0x2164403640320700e080f0701c00d40035001040c0e2401001c110101d841e849540303125100c840c140d40c2e242e034500185444035800d11000c0c281c00b80c42d07000c400001d1840490300e80c01d1800d111b9000d075040001000281803d505050500d680c4102040c9610344c515960440f140e040f200d100c0c0c01d43c1c03a030003145043d40800c0c82c040340181000d4205110304607079620300081e2641e0250540040c0c0d5840f0040d2a801e0242d0010415903118a02c0341c6284445007645d9540c1480c002e50046a001d030003400c0350540c0310b41c1c42030403508aa124403002c41e8107900140c01800380c0c4a240d00c3c2112440000a5280c48091b085114070507400d0480c6c00020b1240c0d26900c020b811920107210400000103151790a04039941c40c1c0442c04407090b0101c500d103200c3c070359007000003550300030048800740201c0001d4080e000d110070500a000541d10380c2e040c203a810500801d40c41e0b519440d242001ca80d041104809001c00e400c1c1490654904201a0b001100310f60011400344004d550750000ba0802d80e9002c3d04440ea0b603000c0c030405904000b0fa07 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 834481267 1250 834480017 834480029
    0xb011413051804050601050306010311010c111504030b0c210c07060c1e020d0522121406090c0a12061e0506040f05010f0e04021f02030a12051b13 64
    0x5014240050b044142c0b0a40380124429416586641e0321402030550f00e0500340710184c008070f01e41d00c0c41da00950080010075419401180e2117080d85049401040040a64140110700010300140070800e11011a15081e0000000030006140025480d00b5800e9030003050340c12201c2c40140ea0104006084100845400c140d20000900080d0000b500141c03010907261089800085006070a00d501440441c0b0380c4400340361620f605040021807441d04c41ca00e49154011041345107160804200d130010003c0c2c0c1a0000c0c802d01c05689a0b241d00c503880340c00d201d005050050300b03601914000342141d030356680100554110300255185440103040c8800540002cac46120004114480c0c28030402034603411040c4120790940b018004c00502c0030b04030048035424070807000c00d429410001d12035405113442084d00140028036203805c08482d00c1014072011203c0445901507031000a4527180f1036000300300d02803086c0300d5020802281c54202c0b5403482c3c1c0b1a02d42071044203060700140740c010070700b441001000a485 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 834482517 1250 834481267 834481279
    0x111507060c0f0806010203090904110a0320030c150d0f1806090209060d03050306040c110d0306050406120201170901240e25050702010509060307030b04050a0b01141305 74
    0x88840c014024031203800c0e200c2c0001d140800000c4c1c0c00d50000040310000070006c0c26850342c90f81d5030348a0f403852a0340400b010b84d000e4144580040420301c101e800145d072031030b03084d400e00d40c00d8010001c00d440d0a076849203941c012000340003040c4043e8020000d456600c402c8220100e000c0701040c01175801401d0458098542407000e25288082c010547d0046070701602c05e50f1080907644906007000043c4900c1c090007000164201300294090415800683d054121810f02e4090140d00c170500301d041c4030b484000080001d584200401c03485ca054040c0100074140a10b540020058a0b0002804140d121b581b2007150240c00d40030642e041025070005601c2c6090043d01503000c1102c22011340f12292034840e04141a400c040864001200300800004280c60540c0070000c0008140080c1d510b50440002039040c85005d02802c100c41d119a4003d51081925a0f0b001540c0c004081c20081101c4c0050120070440b0315180102c0800c1e44c12411030001c81550070f01c040d8580180c9440c0345a14103064000e203030848 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 834483767 1250 834482517 834482531
    0x705040504140711030903330c12010b040b0d05070e0a08070614030105310213090f050405030f0d02091e1206090604080a0e09011806090911150706 65
    0x1000006558000c0c0a680e80d04c030700d01c00e0b0040030b8075542c1c0240002e581d4160080341046500420314101d5003034101f1030710f840c0b1440030041145501c032141e04030f85048070880006a80c0700101104100d06002d840355054181c141b0f820f150ba00243c901802e10150009a039590201e23050b140180c0c3c000130807200007405600303241e446000c8161200789504c110300100301d10226a4103050514800c1e00c0c1610009801009031413a00c1140300940030b22428400d4001e07561840203a0203180350300003020b1480b004142038071518907203c01e210448a40b89022034000e480c0a050000080b4040101d42d403140e0160381a64590840d441c481000344a41c09050340c2c42024a00c1e6811031794000740f281220080d08a030904010241480010340382d4004441101a03030300000002000503d20402905c4007442c42c0c41c01d660200012004114001005c2e0000c02d0b0b00d80d440d0701d03241c01c800c0103800703800c01a0103000c0c407d01c07203949290b46440c030300110b002c0528441c1160300d034120000281c007001d403032140c0e4028000784045 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 834485017 1250 834483767 834483791
    0x140904060602030c120316051b030705010c080604020c0705060901090513050f090d0504030303110919080706050c030301150c15020403020a0909051914070f090510030206070b0705040504 82
    0xa513026813540841c60040340b100303c00180c8034005691043ca071481c00c1101c4400d001504aa05e5404500c44074240340044202c1c00940400704058860a8441d45c000902c140320080d0141080c4002810640300c2c3d8010400c0c0b010842000c1010340c210f42007964140c0c1c4806d01c50300142d8100b030254001f549c121340b450b4800b5840d000e281e048140203c0b001c02c2c00700c1c07142e12200003c0352142000c200e12008141d04000800c0024881d0380502000440003c9007800c2c0341510f00003500c07141c816035081958100090040c0807452083c8005001854281860761800000307a001c0d5489001c1445081645114071034505c840e03074052b02010a00e640d101c2d0554004170a20b4808100a4010b400b09a000e06902d05021416070780c548910f14229030400300502c0c91140c07601d10030400c08a000401c41e00d4205c4020145a110b40402059011303200e0740090507013072810414a00100c03070000348055503500000354104056210b40c41103032a030542002e5500960ba48800c0d054456102c3c42c0d20040e00700b840c203d004501 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 834486267 1250 834485017 834485023
    0x5040222050a0302030303070c060209060307030c08150a030201081b04060f0e040c05030f0a1d010e0f0105040c030b0a060e070f0210090305270d1a091507140904060602 74
    0x5000010405900340a0710307142806412540c5000094240d4020000301c2e641500400220390311900c941d001524040c1c0d084c020544640007521840f0200c0d0303c1d41c03403480c40350360041e4086511a204980003410f400304040013409508551102030b060199542c04101020f012440010b01c0c0c603520016182d580765500401842c2458035040900065004114620203240c079000e40e240d00b442d240e5880b400c541341c00c4000b8503003500141c1a0224941d0f11054020241d80c55050982d0400c0c00000008407414000111401c0c409207040d107442d9640b40c402080002054500c2100640e60443d407400c4550b030302c4c181c030303003001b00410342201c0041224007041010a5078086051803440049509a58101541c410320b0b00c01d0364044500240801c00030300001880344004880c807100c01c0880281142c0c08541840490540c4d034001c0c030306a6100070200c0703441c803c0c0c810003042c0036004014840100782150102038529550580509100200007207080c10712031524002080d01e041c000c0c000c1c001c1000399911480603503 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 834487517 1250 834486267 834486307
    0x10e2d04020a08090618030a0e0d050f010f0e0606060304080702010215040f02151e090a0302090c09040606050408060a050a09080c0a0303061520070e150117060f0118050402 76
    0x551071017280e00240306400307215607074080148420025030800850410550b01d80d0b4644903011b401120f4018000702058082021040142041000042c0c65001c202860b0540c1c0300040502c20720303880746040c0800ca0700d55100301c1e94016041030708035807603006030b100403410400c42c06400c00d01d03800a0400e100034007610910200c440c0b0300c00c03141080b650341e10380004c443c14021b401029188100800f00b140064204200401f01c0d090020000748030280ca903070002d00611420f88040d0044440410142150700703241c45960064225418030b1401d0501d0701e0562030380d451004090b14200394658010441c4541c0540000b00c0541d84020030340d40f2800820076150340c070300307a1400540010742854800189225088125001e5801c240e031020405194600502980150003235007001a2050010000320858000744060084507076045d80c2415244240004207a49108503d103a81c01c0f00705014081c980d501d442086209410a080c1012807079411402c0454540c00760780f0440c0c1260000802009001508642d41c0d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 834488767 1250 834487517 834487531
    0x206030c280806010905090f04170d02030a0e070b160c050d080c01150f06180806040302030a03051005130905070b13030203160812030c070516080c010e2d04020a08 72
    0x8060f55070b50401191606a5072003035035000583d400c00710b655038080c98901036001d409200300801c216211000b218440e171040c1e84451a044e40072040c00780010580c080c8030403036058030004201040c14480da98115104044006c04450341c26003285081002d92200300004080c002c1a009004060b400e04403003591189680200ca54680b00c40c0c985400304452840307040d9a0f401219102c0e140c1421800e4500d0019081d0303544160038000b00000e1200b8080080740d120382d00c254081c40d11030580d0030000d4103072080035150159400b540e5605001c0c1c0c0c1c40f20444031104030b481104c08900c41342682002801c1902981115406250029550480311030155109017203034030980880c0c1c0500e030554220b001c01403040c0100c15054100100001c2034018100c0590f4002c51505100d52801041e03503a06840e001d001ca40c40c03c085001840c00b000b03854400d0101419180c020300380b0000e6410180700140e40c8015220100d455403441415111200340d12020440c004100034004654400d16410f0142000320115610 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 834490017 1250 834488767 834488777
    0x20f0409050603010e0714060c0105010602070e0106020304150f11060a020912011806020c1221090c0d0305030a090f05100c0c030504050f01110d031406040c020a0206030c28 76
    0x200c2c0b01c609051040464501049004c3e080c500d090206131000031a003080d0b43e03a8440c03014002111060400e100d1b440c002c0205800924665180203414529000142c0c40a02035400912082120702111000c41700407100901d041c0c100714800a80642e400d4002c040341c800710340b040c5400c010b001e400716401441c07060f0b41114044009122004c1090a0b68440701d43c01ea56902000f801000203285900640184c3d03c0340400d48002940e00040c456864200d20303400d0000038140d0400710510034409582940051000003d815031211840c0828844541184010200300002000400d0a0307100d902c055402c90b404800740302c000c0e41500b001e5a40c1c80031000342c1e0103206d01e0001621001c0e8010513001016035816210705080501c0d100c1040366091501c1d0b4040d0604c119a40048403203002030000c40d201d2512920000f40c031030981a8001c854001c02000305002c0c0c0d00d000500f518041e0002844510541e048561941e207907034540e0004401e010311940c1a200c0750310b03500500500e5007070925103a5038882a17510 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 834491267 1250 834490017 834490021
    0xa0e160210110906070602040b0a030207020a05102102040506072613030f030c06090609140c03031c0603060914010b0a0b0f0d091b080c030105220f06020f040905 71
    0x751422540c1c1d148042840c1001008019814204a8050074419028000040c00c0c642d40d5540c0140e9035002440d03038000690700150940c11480c0203100c0c0d0010740419034400311409440032000c2e00840e01020721140c2111041c45640f00b189035501201d01403c000307089503440b029181b410102c20420400040c041a00d0031003940d00c0d0266040507221004003071485a031420b4656154103840320500c0c076050f0204858a06c071203001c68000c2c00f0b24101e04c0d11418001078070400a09180d4020110030220141d5904940880e1882c0d0b98000244c0e2079010301264468202d90507000944010715003644010541070601ea400e00520a05030351285085065000070302c01d010703914080198002c1740707002c1c20200d000d0034401000200712100141000e0080c5010000d201d98450301e4005801040800b500908000c01200303225412061002d5180100240c00a00003824615502e0405074144907a05004040d110281802d0001e40325060f20b1082d00310b04210750f11100020201810381c4030f4001c9401c41818500 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 834492517 1250 834491267 834491293
    0x906060618150207051509060a0e030115150f03090f03050a080a09020109090b04180b01081513060902011b06062301020c041509021204050c101d0a0e1602 68
    0x49141c030400b4550107080440e05160030055070340442083c181110a05011015054494034024842c5040a03102c7e81406812170041600b50f03001c8000000c1d0390000c54508000705200c010b00301070f59140c182050185a051804220010a00442c0c060503452446070503100340f5400400410350504240c0e1510703002d540b94900c010507103124480090001d4480841049541c4480c1c5c0014080c0100910210760800544444480b80420440644030008039900412a002c0b0400c048070031015082601802c03490540441403c4841d40d01001d03202c240c56034024801c581c8100080281c0044011a0404003000e5017810070041c189801050291100c45052079a0841d01230650808400140e008020385103901c41800b024103104011021002110b40d000f203084010340c0042c102000440030b20004078a8241041ca2410200500c15402020401407800001c2e07480b13040c40c185415410211528043d041c004910308020350f90159111030f164000b07024081a00c400c000c981c03402c15600301c03008062504 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 834493767 1250 834492517 834492539
    0xd0605061c110c0a08032a030601050a11030d0c0f02011a1009081002040303020d0801030f1101022404020906010504151407060614090709060203041406090603090607032a030905010906060618 84
    0x1074040b44071f12810b1001541c1c42d0f20030802080783e0310803480c01c00341000328802204d14642144200b0703400940c036008502c1c00d5603480000f006000802c1e20081c464511406c0d82c103111141340b10350040c0201200040860300034090b0890b400281503060407903000080c2c01695000030340040c0000c03401400395a1461300d00c3c1d44500201070699401c020f410007840c071035589000ca0b00100c240d00300d0560242a001807100fa02d42c00071014103c0020510802c0d520300b41c4100038250800908442c14001c0038070060103403003030901d500c9002d00c03080d061030440c982d40342c101c00146004100008112500700000810203100c031034800400d502c0140c5100d07415484022040d900c085590258400503401030000300918040e185409e2412003015102038540421000891b1243e03004071502802c4e80d00c003909015055505100300004c81c1d850100c486a902035000032040903814045200c0700b0036440350f51140c1440000c0d8801c0080d6a031100c020001b41d680c400c00030b0301002403c0c000c2c5a5100d1804c3c00000c10702014 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 834495017 1250 834493767 834493831
    0x608030909150a17030a021e0c13181a060d030e0d0c030c0303021c0906080105010503040213050f070f08090c09100810020d0605061c110c0a0803 64
    0x18400007140d600c01c2501484078800124282e44a68610000285801c800e0548621001e90070302039030743c445d22628064a480340036542c111080545c524484803107200030078010b03401541142c070703990b5400040059501500181d0094008034002c002c0d41e030200705d09409102602c5a800070f4810702070340c0380401c00101048840c006400b0480f84a40301e001c1c0c0c500b450850b24180e2140c80c28217a0703581c484d00c6414108050b90130490242c0d0000c110031030400305952482103442c030186000b520080c14400000c04101043c030989040c0031b004004070b400c6680d1104000c14002c010142080780346440c04804a9004050f215034000c1605040c6142805220300b00d128490071581000309541d0f880d8500340001c1c000e000307006205070041c07000003184090042c00005541c446419015072101242c41401d070840d21958402c61050100304020b00c400f101c60281c0810312030840100040d00040b07141c20340301c54410710001010901951400408215100003c1c501580256840c52018240004181449948 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 834496267 1250 834495017 834495019
    0x1e0506090a05040c0215130b010b0a090e0c2107031d0604201002060906060603072007080a0308220c12150903022b0c0f0618140106080309 61
    0x40101c050005050507009021407465900c112840c1d94884540e50703800b260191084580900030a0784442072000300e41125000d40480486640b5100f00c12801406200061103260402490301d40044c40544010b000d840d100600e104004082c051a4a411144c055040303030b003c00481d20b00000340d41200640c182c640030800d00b1000030902c1c1e4823a51510b03100d00300b240032500006005800034005071b49030980758003001800c0c0e4006110328205131040a007030540007405107014081c28401c00044951103010001501d02c0d207004181c512a1b010055400c0802c640c01800d60781c490103c450b0201a4030880300d0f4811144010003e84030340c0d40845244002502c4035002d0424030010805100da00c4001c0c0c0c40c02030481c031918900b5a1014a0f90000c1c00381e0325110030a03405030300218a50714055540085481210020301034030350012840c4c2801500c00c00e80780c803000d0690340104a6031800c2015550021280c0c00c0c079840b820000b400350749440c010180c40600d4080181d400d106000403481400000d40d52a000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 834497517 1250 834496267 834496279
    0x605070f020c13110f0c0304091407050d09330e0f0c1c150f05090c0109061b060510080d050412020108130629220c020f03041e050609 59
    0x8540f03400d55025051850842c01d41c03001c108042c0081403004001401c103042410095a1240c0c030b2310b0908002c86031214941004241d444003000345456010b800c0f5000078011606c0024014020304101d0450200210031219040380b6003100a81a03080c0c08086001440c090307000c0c445400803118450720380485240701c02469000242240e1185000100000c0b018502014075218012548800038022303294400d044c46c1ca60307a082800f5003070354540246680302c0c60900041c1481c6c410040000c080002d03501c500c0c0300700540c0c1a81c0c5022581059401c4a109402103070600c07150500c0c40800b45012024070a00c000c61181c0300b07a00700ca040c0940180d404941c050b03110041101d01c160019140e07128000d000b10700350100c001801000540314498440d00e000c80c03000e0f426603148044404c4031140d0740c10038201c2c800c203c80360b4103d8a02c40d02284240205078650700104000d50010b000360b150002e403080c0c0900a000120780841e00600c0340020b0062104a485030070451644c0780d080c020303140b09190005400071 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 834498767 1250 834497517 834497539
    0x30c070b070e3f2103040215091e030a05010603110924100e120610141e030705030d020d030f290f1e04060902210a0b0604030605070f020c 61
    0x65103603c9030102c2100740c000395207071030702202d00703a0300511403020001010400110500042d410f00d050340a820400d92003c2d41c0c036123040000041c0031060700a28107040119103540114070343d00c0c2480707800c000e694494024007000e80c5034a4112160580c00384114083d0140e0000500c10203a03505489482000301c0c020b500a085102044c05050880f41d940c500510500040140e200d0303c070005101c102c1c4100d8805064182090f1002441380c800613480422030440c0000d11244a940c1d03640019015210384440e944541c00d01c201081c18041c0700c1d40203d9240c01195000c511036a00031640c1c2c070048410b0740c0c04010040c502c3e008001190010110380100c13201034415a1000d1381441039104090318014481034000f40c0031000a030070030040c07144c16200c0200d000101d03602400c2c20b025440c0601a802425030420380c10304600c9a03108201404040b00d0064640822079502d510381c403030004502c0c0070304480d640d9501d0741400005003400759800400074030380c40c0300446061300c0861071703500026005200100f22 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 834500017 1250 834498767 834498859
    0xb040c05250c150e01031509050a0b0415080c0901030c0605130915030302190b040305160206030f1509010302010f050c0f0703110a0803030714030c070b070e 69
    0xe0010004040c00d6503811032040442ca0701c100c40300003005409000e40b0b6042441600130442d11095515906260134600643c142082c44504441900c2058000045e40c0c0e0340c3c005910003401140341d80c0c0f40c2003490001c1c41441c034104403c020045c0c851100489208880400c10700406203c00d11020702014514141484218851070040103c1e50740385c07800780c0185403184607400444c2e044120901042c0314561003001010340611085210200b10034a20994106a480d20260300c58001e10060801400080c0d44520281091b9040080c5030041c000503240c0c50814980e901c0024280c0e0311484507480e040c2607489524141d9180d45c10f995041c0e680b203031402e03011207050340c560f0054854500c0c0e502a810413210610b00030850040114020482117800030030b8134041c04001d003059001040c0c3c6400810401400b15000166010550038820b64540d980d618040507084034082c0c1c141c0200b089643d02c081c0048141d0015408003986011285442c06100b0729500340041d824602101d4900b04d0002410226 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 834501267 1250 834500017 834500047
    0x603021522051f1206060806101103030606070f0f0302060f0609061302030c07050f0601030b07180302010e0a0b030a1b05270a0302090906010f0501110a0b0702210d0b040c05 76
    0x14000f002d00b000c449850300d90110b201a01d030143c01480024526000300711240c9800c000210540c019428440413031491202d9040e10703484014074850084200013400004c00503034000e0401c119810541100c1030f14a07525000392589400c0d80c940740078807140c1021480354070b40000114000c0d0b2000302491318080c104440000039400051445c07800780000c0c040c2001003802484075421201c0d018003e0245d42d03040d03290102d41c0200280c081010405190b0244401b4030681418105407502400d020415180e52400140c4808980d00030a0402501100f404400182604405080585000e0f4981010b400743c504441901515143c10301c100840c803c0041410080c02d0001e1043d1000f411103082944c0783c1c0c0204210315410f440b2811035503c0748004100213a03410f204107010348401d2030030841c6512000a0150303a201d5044001d40071000356070100d4031a40c02004164001030301103404111030440104000300b80d030080d0030b40601e40341c181068050725203428441e8540f42c00c003540340c041c2004407100d49004 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 834502517 1250 834501267 834501319
    0x82802032205040606030209040e0a03080c0c1e0a050d0e0109140406080706051207020d171503100b090a0203010321020c130501060201140903041701060302152205 72
    0x100311080c40c4082010344440c000c69011700460b440242e0ba81c41840140b004984604100030210303084040d81500083c0c2c80300e00c00b03410015503074449071038204001c021801c2688008050480240154500d0959900802c40b8001e04e4082c100740ea0100200071400e480c0c1e20300c3e0400460018003d000240140d04402c0c10001062101800000e2001e031103034000380c58118507810080c085103010816401480300076075810341c4001d451014114801180c000500158203035031202c60b020800200044564080340701082c008403000302269842e00c800c020345401001c2011400340680c0038900080c960414138000c80e0704980e4840c0d507002900024080c03040401000344030070011801049c030768110700d0b9210503103510060b20140000175607501d0082d0284c02c50714815a0300320702000342d40c1007061400000c0241d03811600b400400004207900180e2250041059070002580a4208018032101c002007501420054811121801a5030b030300003d613605510507071180179403003102c02e0340d81540e80090700400c1c4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 834503767 1250 834502517 834502567
    0x20f100f0612030e1201150e070302070506010e011502030f2b09030509040b040504050a0303240305010f110319020a140c010e21041a040b0708280203 66
    0x840503110300711182c1002e1910429000162078002c3d03446135290500d03014401c01a020002c212181140c131060160b542540714810216140c2000110414081d80480341001d40c810169181c5603151410a07410410a02400c1038600e807032550a080640000100c8809a036075407030050412448003c01441c036925405d08240c000e80058103400800114000c0d2050742c4d04c00e445050321044aa800e010851310190b2109104600f000c043c880400ca0201c1c41000142d098a400300700702c1c4880c080031050f00c801c16040c0341a40d01c1d81d0400014800107501c07050880102d19018000300544110711641400255544041c240b043c0561800b80c0c036051f4010034441a181c104120040ba101d415031020b034005204000a0765126210000341d22018400c40c801544e00f01e41e44c0c0b424090306e80400c5000d0189011300702071013000041d24951441080180c80040c104103000550b80c02080ca4008907a811032092030b906550b004010140350500c042d20440c4c00c040030341c011070a218040742c049101340c450b1031070701d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 834505017 1250 834503767 834503771
    0x92d0e0402040e030f0d0c0804020f13020903101b0305160f021002070807170307270509040503070c060806010507030e0f1c050709180213020d09030905030d020f100f 73
    0x800b10f00000d1016203c104225401d01d03403100c03400c40f17900058072166031454040005010401c00103a641d8103030392000c07020a5072000320030600206141d00901c154036259505201e150303032840d54141c054014240456008051114101451800350160b4000342c4005c1a446070122004601c90320514004e5004510707881203414a402d00c9204000320381c0104800e0f2061000004d150050140d035051204c01001c1645071a441d41c0b506404c010070000100492101080311604400e0030406450850f0b805030030020401c49031070419141c5030759a9440399004841e8504c00300d00c0050224018281c4500c6404182c50f5580781156542d8125001252190441d60091000702c002a043d1100c05142c081c25291300c0700d9103c14441707424600e240c060a0340c4014000c5003440c0058218000c520780348c00c80140c2c1640d450421541122030034010380204e15458981c2d42c508800c0d0344c28986e00082810031214290140d5408804100c0b08a03145e07115040c0200155020f8009242e1941a40d4042c51030002c0307034000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 834506267 1250 834505017 834505031
    0xf0403090504060b040e09281b120b0a0e03090405040501180b07111b1002070b0304050606101e0e060c06010f05210d080402040b10092d0e040204 64
    0x42c12101143c00203201c101001c9030603c45074400b0041260080348000040078162200d20f05610b40c0d450344024222420002402c0b90100080800c0b1141122030001014421342d46442e003030446045c0081c0103951104600300400c030910746500c80c5d0078910007010051840d00f03ca000c00d00015107405801118650342c0c942039844500c1c01103652042180c481c60518145003001100200390900425924040d6001501a440d2207142200e09030380400090b203076480801005d407416400c200a40d03002c05500000003041008004000c250300348074920450b43c80180580243c400ca42e420841003260201c9500c5d0a960b035000360150385043d440712360080c2854030705180714000c42d04100c000c1e8884200355081c808103021601e0a01c03401600c20a401e03071801c2014482240482d510200e9a0a84c13042c008040d001c1019529a9041221010070142040180d5855400020000c003002d02c154040c0400303020034503088e0810146802c22003016075400300c0300c00d03082401081180d140504126802036035441 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 834507517 1250 834506267 834506269
    0x160810270f030906020114130c0509090a0501060f0e1b04051c06050f0f01030303180c0e0f01090e0309062104140c01230304260d0e070e0f04030905 65
    0x1550300d191050341140314211061501074940c1181d60000e070156410079503010920441c0c1040f20303520a01c513808404000700c0f6810500d052007165004075810131160400c000301c124001a40200d010300c100001c0143c0f0381d580f011084881c00a0156000300d0241030007003101a03c51102c0c00b220b41132010344c2c0f50b16182c0d44000080d21483c8a031107055a03103003202003400900040d8402e00b90f0144071142c3d505058030b03058404000000d414003009080c107640b51140910800f080e407101000d9075001420980b01511150001494001141e03a908015281c200115442c030b480d000300c41048120070001d50410848104100c020341000d4030764000c0c010480c42c20966600c00740c00441c0264043d80585054203100006c0b50700305007031000064180404c400c82d880788401c0c21101203040240c1d400c21542c883c0c42c0c0b4541000a10b00703080211190040c4000b102c04d4824010008010764504a64100080b50070000c01d00d4449046200c1d0042801070035000424100f040419541d20511034035180c0350043c6c07108 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 834508767 1250 834507517 834507581
    0xf02070b13081504030509010c050f1e0c153c0903102c0c0d080306010201061d0c030c0f04181820040e0717160810 51
    0x2400520103544510707010803140c107090080c0103081043c1200044145090744002d000c3d0303c00d001d01c503810070031042030500911109001da20342000842c0d054074460b0701031042d801071801c82c0401c05089402610701203440c0d40340c00d03022018000320340c6100e9804d00190701d44103902c0c080700e080702100c006e1020080c00803540c2602842140c000b0600c00c082c1d02c132180c4000389072910010484000041e85840941604c5140900302040b01d0740381108403042800000c0b0303103142041d035602c121640140c1c4440000c3c0401950f40c014600c103020a9000708200d95031540c01500450b121041e020300d100507030001c1407250301000015503101c0240b001c0d0510703200c28070664031403907800359000d048004100d01284941c00742c18003a0384400c0c4007200d1100c101c69075603250407969001c8170680000d0710422049011154881d60070074041004c06000b9a40d80d255908003044c5401241c41c1c542d004c034015a002003403001080500417050340d800800800c2c91501e800201c100070218140b450a604661503048041c446660b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 834510017 1250 834508767 834508777
    0x60d150f050a0204091107080301050d020409061a150a0909050919050a05011a060a0804060f0c02011505030a120809033108061b1b07030323040b04060f02070b 70
    0x1003005a1340c52a00f500c04044800138008004139071030030061540880d020030256410746008032610f0011500510024009100042c001031020b81080302820405041e4242c21866542c1036841560010008001e00e01c503200e64071803880414000c060500000c05030340c0c4003940c0f00b0840c104a0b2100100d00c951042c21054807070b0205c0c0c1c540c1c0314030706140800c0b900b805202d00d04110804184140c45110300042c40901404001e90204118040040c0612895801c1811041304203481040103581c0c1c080024043c00f8030b01d0807500c45490a4000140c2800d001441e00c88003a040701850348040b0110404841c02c03c401740c0070321510305c800e00034080e5100605000400c402f4585014030380c2e81c08005003103252802e865001c100d0b40e4010340f04003c0b158040c03203840600c40040300801c07641d90622a441050702104030803ca200751248400200030160000807101c095801c14000500302c40111800480602c994002c201c00041c0500041005c00e014000484119265005403080107480c0c0821004603001 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 834511267 1250 834510017 834510031
    0xa02090c03090f010b10030c030f021b0c0d11010c0809030102030a0c030c091a130f08060f13020a0527070f03240324090f0b0105010206060d150f05 65
    0xd01002040420480340602624002171104105180000c0c0c4001e92001e076210615807203260100140313129a00921007146070b03001c03c42d124401c07519440181511a04290701d62700c5402100712542c03600000040c0c07081d902403008408036209500441da0520440000c43c0d00030014408422240e40a001451161120301c2000840f118a10f5004094480ba03081c07000920900d101d0912400040c0ca00d046030803000d0036562039070f0b50307030180c42841110581d81c05444028a403082c0400c0010002c2a610700403041d0150120740c42c0c40d1003c0064500c088440025401860000104080e08010101e441241c042084482c481488004101e407451012201e00c0c000030103d2442c0024190076115481c4403030140481000340c000144000c246128103404013030040c6241d10201a0388a05000400d15650000d202c107000707440291808212a1941c40022524201020004151540700052043c45610020f03c8032540c4032480d280c620b1030b0101001d215900e15245d8403211501603a034000c850140705 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 834512517 1250 834511267 834511291
    0x5060405011406010c020904030509060c120309070b0c1504031b0609030807090b040b0706091a01031e021f0519050405091006020a12020c15030a1b020307140a0209 72
    0x159850b03100c0d0440e40003c216605101031041c14102507200e1081c01a4020343c507080c00c6955010000020365680950701050649100e9074168500c29000311020314042c9080350110340343d5640340d04424401c1e000d428040c0031254841240aa586c08a46100301e070401c0c002e0501345000601d0f41d040d00f0380c499001c802510007548841c2a8410958003d8403103611441030300d071007001141007000c895501e2280f0720034072814010102e82c51003806955408442e41c0e80d40b10f9007c4450202046681804080911003a01d031a0018003401003001203011580143c00d500800c0102c0000003201d0b804081c43e03a200014003000b40a20100c040b10380d88100d52502e40300d598940c00d071154500400c00c40d92500050800000c1181c000e000c03c1440d400040c0c141880343c0c01541c0e5490440c1d0100c040b440c11404d010303201c1d484008502c0d5010411a0800154003c030f0310b0100c140950904000c20b0502880c004600000582c001c00803080402c62080f00001c074121048182d8452182540001d00c00c0003059401104100c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 834513767 1250 834512517 834512531
    0x21b150f1305010e0d030809030903031329040e0a0e0f0a02190e0402101806050a0e0a0e1b040306020c061012030207030b0a1508011e1401030f020d0506040501 70
    0x41c422140c50001040c0910b421846a860308010a840b1307101a00000d0074030000e4004101012418410b442c0349510140869448186c01401550380f9081482150080740c02502c0c0080141000d8816030500f01d10904490700d000e20700600d0107503481005100048441c0d03606000e0400d8981030020a405c1401030b0018004800c179401008001c0c14903582e03061643d031500204210254100c080c8a074001e8045541c0c205081407514180e40e00403031603039005456200c124001c1f902582080c040e01079140140d880d0001c002d0401c00303101c0c0e41b4100f0300a0388080c0c4400c00010701c10000001107100c1c10303c81420308030f003402d0703a943d02e41060740c1201d585a01c0319081042084400d901030442000107101c01c00c021500c0001648020391035a2980c00060600000b4170b00007884144550811030100809450a1038107070b0750b440c0d140e4002c01400c03600120002c00d9000300c503181c80041c05981315030b0208910281040e440c654034010b140200c090201d0300500c0c201a2400884d03801e1010078800d9000e50004100c4c9 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 834515017 1250 834513767 834513787
    0x150b04051509030d030c110102130e0c13050909010603020301051501030506220504021c050a0213021e0a02010902131a0d150f0b0d0807050606060703021b150f 70
    0x101e825540d200301c1245040c030010384165000110880050341a00f000101c0d49842034003159201d160b0309400f48198000241c05800c0714000c0080011508000440000394990360b000d0101446000b510f002d00e00800b4400b4442d40c40c1c6030745010341202c03c1c80000181c83c1d50fa54082070075034408440820001d03550007020302540d42c050241e2a481a02221400301d60f411444514407400c84038000003003082c3e0350720b0005045441d45814000210800c0b20244010411441d025680340d110030000c0340118001b4918030200482d0b070081c0c0e5081582039175000440078078840381c50131036080301a45008645d220076a03117000d6183c000d010103482842c0c640104000c2444244020340c40c08980c0040d000700d5055201001050752129428aa2046c0040c041200a0407110100151192080702a489090500c040080001c0700000744030003889103080d40d5071642c5e80010401030740103180c0050096044158210705002107042080f228290080c00f00c00010190030703203c040c5820031182c0c0c1851500018101d844 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 834516267 1250 834515017 834515029
    0xe0a170303010f050f03061f0308032404050106020703021c0803070216120f2604080c0108010819082503052107052b0c0801050a0e04021e04150b0405 66
    0x5000f017034034007060010000c40800e40e034140080c080514a02c001c4040c00b1300c41c201c03004030b0008503006984140c0381e04003051810302e940845607544070044042c0094407103500b001c0c06068121041500500401403447d024003841c080700e15000100c0c00c41d84190b075000502c141000d0760054205600403d2004401000c03601d83e10102d81019007682340382003800000403070303e4030303043d41ea56800b40300038981e01c40b0080460140500c0c125848a1900d0202d00440d00c01000141504102801d9a50300001e0741e0340d22102d51070703856100c8c48106d0f18403408031a01c0458880c0008014a41d4400e40074022880b900d41c1d040083c03001840b00310300180c00080e2500c0d910200485410541581018200c810f042500c0e02620030700c150300c007482c0c461003115072880c03012211041e84603841911290600001c081118018100c0c0300900505214200d0000086806500000c85502c00ca5016042290000d500c1a2200c80c40070100c1210350702c191510184902e070307460701d0009002880442c050f10b464508000410034 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 834517517 1250 834516267 834516269
    0xf1b0f0906050711040b1908100605121509160326121906030215040302120a150b1c140d03091e0c0b03130b1b09010e0a170303010f 58
    0x1040000d200311000b02c1e014209600307000c4e500f20780004044007208040380080781750f404444080700003c00005000c600220303401044901e020000c0204c01e449004002c600e02c11090320140366800296801c0318030922400558110403400200d40c01e01c0c0c11503c0c6010124085e420445454100c0c106c3c0060005a08148071031540c0417884580c10720030900d152016100004029144015a981c400070308a800c640c0100080c54000e0321120854102a80a2595a000d880308a00076000914920071901c00407440d083c985500c40704c1042c024824a8a07100580114502070307070310850400d00070071a098498040360010f48214aa00c007040e80b21207046040c0301540c1111421316051085c00700000300c3e03201044000c0b241e81c82204201c82500e0510001d001c1803a004102e15400000500580c0c104620030052414483e4804005681d00e49071140c088002c40e44616000140178045403000d580118007000905101810440c9602e80d40c1c481c0d0710a140341c044942146810000042c0621340a60a61034 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 834518767 1250 834517517 834517529
    0x702010201110c0a030c02060f0c010218041413082505010e010507120510210b060a36110408010e06061f0e10030c030b180105040f1b0f09 61
    0xb50410614110007901c0340b503c200c1c001d04101889820b02c0c115540c1d102941c040e040034a0f074168a85000c496000e000f0345c011400d100c03c00d83d030810000f181d443d040c01071903511049051011801e0b102c0060080701c415800408a941000520852a8500108290104110340d4440b50f03130702000c05041c45030844620400a44035641007c3c10840e5443e04210b050004690036031000500c2e036240080075501c03030f17a10b40011650a04a640c140b100000c0011050354890280918000fa034951030200b06c484540392081980ea441081c003d01c805d100c100518403886801c10880c40e84002c20240d0400807075814411544443c40c010800b8400000c00b482400781105450b8002c00003420500001134028030380d880c048060000341c2080c0b01c400d6104101150780c2c2107018042074102c04c040710f005005004090000000646402a04d00052410501803034064018041b80550342c0d080034140310103800c0c00d1160b114460340350000c01c100c801c14a41040203d240307e0b07a4289803148421801007441801da4829 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 834520017 1250 834518767 834518801
    0x607110108061f18030c0807051f0e040f2d0609020c0a06020c1516031413030e0a0b0c03130515041e081615020f030301090207031803080702010201 65
    0x1250107250084071146607039480d083c4002c4c0905640f03241c01d080707210350b0001440d440790f00301c00094100c00080d11701c0c00d0303880441d01042d840d90840b030142010b0700c00708942400124184526102400d040e07002104070a000b00c0c0214854a44a0104014442038416091120001c10303038441c0700845481058058055910158070b0403282101656507660401d8000e003046a0004503204092410041c1e1000e414540c400c01500d490712001900380894850300803004207041405a0801c1d080d064440c1c0e1103034000a810501007a000d0700c08031004000202c03450f0f00507030654008503d40c40110081d0002c210180000d540d2011000f080090382451607007c14003444100b002102503500c880150341c155604060342c40410018000c44680d601c2c0281d000382e4180c060039040343d2406104d0902c0f81d050303500f00c03c00001560800101266202c07e00301c01c04215402c01e200620178507041d40c0041070300c5406071929400c0700c10b180280301748000c1140d008580c8502c0004001045580a01400005600b12010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 834521267 1250 834520017 834520039
    0x131205040b0a080907080d210b0d0b160825020115030c090b0607150b010c020603070c06150609170a080a05070b0f040c06051b01060f292502060711010806 68
    0x1c0940180844880004100840008c1440641d44c3c0d502034515004010501071100e42942400303000f50780d0503190308040015a10a054001d40103548460003a030400e19006001c0c2e010b0b15a2b40c0441c03041901400865481e000580301d100b84d614240c501450289034039040303461170030310f000302181c0d840c1c070841d4002c01060000b400400d10f00f0006402c989038480021605d00700d4000106c880f81038a00c4000d40c4407001206020131aa8400e1000b01482d110f0f01c401c100c0b00910000c03003086040309204030400541030701418031511460341030004142045004464a80501d5620f91455070000f41000c40002e1380400e4410900c00007411154108600f51903181183c103041c1c6404007030141a0141105000d000203602c1610300c0300303c540c1c0c4d079a444108000c0200740d07110061346540403213030710808030030380d100300c0c90002142d070806088600001140500b03864100c076281d04600003904003211480414824440c400940c880740010301c1418802d240b507501007078040c00003400d4010050700040c041c1140c102c1d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 834522517 1250 834521267 834521293
    0x100306031b091a012c0409080912150703020d0603080c060403120203070203160203100608030a0f030b0d020103050402030307050f100e010912080a020f0d02070501050f131205040b0a08090708 84
    0x1202034844100c0010400c001c0740c880d202c1c2044803408154080d04980780c51610004d2103108000f61109c0c0ca0100e445202000020910680d9020100041d502c40c01422010a400c18000ea00824262001407008140c1e0307a560381b50811309402c03807100c081c42d41c0c210300c04200c2010761100740d09070402d850090031400d40c00c0c0340800030344d64020040c0c81d4850490458401083d55010040d900321000c0c40760040c01810746a9040e04d80740c0c0c1080c005480804e4414030240034550080c0516100d04c44090040d650f070b0545600114040c080c00b800981c2c00d40001c00040c0081a014044040552200c0bc0203141542d41d0004842c2100c95104a00d805079140a2803040085e41030400001c0c11900e92420a607540c5401d41500028841c83e5055a1342c5100042c103c2c85901c1c00e5000f408220b80105d0003000030b552815111400c070700c801c44050aa034040c0d050040f0026008800e00c030016040c40c500942000d403030b40c3d07241c91554007801d03080c004543d10404001c0c5024082241d10003a2080c03c0c09030800315a100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 834523767 1250 834522517 834522527
    0x1403010302090a0b190e09010c080c0f160305070201020d0e01080f060325140402160f241b110d05090d0206030112031b030e100306031b091a01 63
    0x80002445069042d002ca281003090342c010004204000300103010010320a401c20220a02503ca030412060410001600c141010300c907038030080d150341d183c01106a0710010140d055a02c103480588888005101841c002c6035242c1000a83c1d5100c0d8841907590907040c0000780c034003450901d10404210714226401c03500e0b640484001c2d000f500300340c0c0c0070601d078881d80002402e26007000e00405541c0e0000e04d000a503d150358820900316217186007942c19600c202400d102c16071040b101c1c0c9517801c002000d500c0c000605c0d80100c02d003049008558086182c0d0b5007000140303840715202510b00020791901e9096142d40360741c1c00c1c0100d180c1e501d410b045900501c001c814503100c128a290100900001050042c003640329441070301603e95006142da50b496071203402d42d41031000701110988c00100300b14040c40c105146251311151690300341d11503000705035640f0b003003299000403428680304240d01c40030000005880050040c0071034211510600b101c60402001d00b084580552900702d440d820b9401008950b6080 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 834525017 1250 834523767 834523769
    0x10608010513030e01030902101808010207030f11010906020711010f02061510021c0f0908070e060d2102061f0f050d141504060b04020703090b03061207081507140301 73
    0x1410003140e01d131400070050300140302d580c00103504047ea000f40c68840a501c2180d1040b20a51f41d240d0285032038803080340a00b00d0154010040114042e0564110024022a925065070300c500d00046200303011952204180c2c4c11116049074010000d603038407015581c102e80b120701d20030305910090034035281c88200c3c150710100089180340920078050b9005c0a80d4800e2001d42c2d841a446158000b0380d44064400600740b0f4070310854000002c128010220740d291000c01e0320000c445203c403c1146585a52080000450740120100c50515107102701700c209170842607290110b0102030b0050100d030324186400c922011000b01c80d90860b5110201d00380105450000c803481660700a9038003a004440c64542807501019605074001c161081140e90100c00200203001440b592041c1e82c20310035046458140001d03401007581c0240480c00c40c410034401441076001840d030102c3c00400ea600c00c0c41c0303101c048a0078005680c01c8280f00d42c1021181c0188000e8558405170824103600e4892040010401c5950f240c0c001 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 834526267 1250 834525017 834525023
    0xc0c0210050c0a050604020307050a0602030d110408010e0708010605012105060f0915010909021206010c1731080303070f05071a09010c020f0309060d0908130305010608010513 77
    0x110540d40140a2203081a40c1100d1000b00889202d00c0060406a64038002154124031034851168045840d0400000050894550341c00031800c05200e8981c101c043c20340c2c1a020800c0c030307500707210014580c034007400b800030144a007038060000d89042404460a46803250400c2d07040c0014602032003100c200ca0701e02218060040900003c035601c480002525180001c6800c80d4440c80340401d0245a0315810183d40c412442600c910410036a85c1a800050b40103030f0081d40240d035070040c0050059401615954081c912801900c1d541055001c4c100102e60001700d44149400f011246003561070643c2850000c0c45441c82500c40805072900c074040d50f0300e11004002c00c007008030103000500000e0054003034904c0715610440c0825551151000d614840c1000c40710100303103601b416045c130031203400410546615207500c0c01540c50114204240416544103190510405507110322a10109045a01074400603502c44400c0090610b942040c500351800c6401100e043d0b4901818400524a0b995103520000d078 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 834527517 1250 834526267 834526279
    0x6020304150c0f1a0114030a031d0f0909010f0501140904030f03020c01020f0c0c01030c020d0c080f030c033c0406090609080c1e03122a07060e010c0c02 67
    0x700b10f1425101110944100a00d16421500281c030319201d240c400905a030001100750600103481e80805075075010b0350030064003203100800c115040000890240c015210080e0030002c40d20a49400720f0403505044a6080d641e0b50746074131f420b00000c0305004903030040110444184103045807a0000305640c9001c3d200606000341c1c1c03141216024069016030340303900314000c000c5440301c402070024039080d444014041c469014520803204c8540c000d106450a00c00c180e030040c0042d4540700c9040e039521380010401e40e0329000a00c04200d10082e1200214440d2800307003035451b12030401d010598001c400304000225182e50340d8800101e61040382200000f0721200c88001d103203d842e1414890024085403d000d01202c0c100b4000109100d500c1e401400000c2804044503c1c1020b02c2002003405d4080301e6526009070030401410f4800d00d5007518560700141c000c01c580e0000030142e40c48100d00f40007148820002e00011440741c0510109110b00842042e9410092200b43c10000006080307000d81c10009200e85 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 834528767 1250 834527517 834527537
    0xb1005090405102007150518120d110c0715020307050c0603280903120605060412020f030f150f070804021212040e060a291806190305010602030415 65
    0x4ca900794541404810101c4e01d565100241001e0718908003080309145000d00b4207020034000340e6020781c542d02c200d0011014001c03103411141001c0e03480d41304105d20004181c84020311120520000028640206920002d0400030325181e101c80c4242000707070824003550014400313040450800f040c1141b122408640305d580d40c2d40c3c1c00040c6a8400603010540306070600a40d42080c1c0c581c1e20f03070310507824140640c48031a4000c260329408010364081d40562608400140020008001042d00c111082440107012020040a80000c41c2c0382840030b0715050001d501c04441071f10b41c8003a40400640229248040c650700b490922070103000407201820080c0940b01598000100103814032013840205030b130340300d03080d03079291348048110014400f40d4030144500030484c2c0c0051403100c02c1400c0031030000d042070303c84035402e2141c410041e150030040380401104002420140d02d69107440c0100328900b00c40c0b034403c1d440848560018122501600a20150343c0100320034410b200398030860400030740301407610350418 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 834530017 1250 834528767 834528791
    0x5031314120c0d080105040e07140f120a15090b0712060317040305070b04030b0c0706020405090c07120309030816090b0301080a051c0c1101020c09040b100509040510 73
    0x202020a1204035501404076465401c0b200c0440c03c46518415942c80c030400740d8840c1e081000721001c40302d0402d0b25900030031041180541c400040e00004d00e000700301d282003404100c046500e48546000300245a0410b4040900f00720480107259817003422204200403890840e95115000e031800f4000006202030b12021a000300441d0704100041c5500406480403109403541c0d0f0300c1550049d002c00c45107405001e5022441200b62410b03501140d401c460090300e16268890818059072000100b600c03210707000c001c085507984984c00b0135405a10109903441e03444d54241824002030f80c060030090100741c106100754020179400340c101d5400600c0c500103000c6105043e03005882d05080c0e03070310000c500307000407000150418012031800c841d40e001d482540c20942c01d0b80d212281641000310700c0b40100b5403041a080104110b0f8800a80740c02042c01207901b040b01e030400107008258216011540e01d0308680070818a00c0e0003441c004001c0c0706c250b4035001c075410300d03540e01510b80c1081240d118102c0d030344108407564 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 834531267 1250 834530017 834530023
    0x2604080c030d1b021509100b03150c03061f09090f06170303090d05040f0306021b0a1b05010207060206180a14010f0c0801210c0f0f0e0705031314 64
    0x407a880700303008003c1110030032680c00c03ca0f100e03080740300702500910a503101c00f0b800402d005ca00c10b12041c4050240c94919a21580052511001c545d40522400b194140036200740194603000b07011801d00d0340e44a150001c2044140c030610010034158500b40b04042c1401a000100c140540702c40c4200031840c5003070300d030820b0010441584074502d02c1c52004468648280080000d60007074540c08181c40c032080d00c50809030344900c02c0d8070038259041d25401c0c0820100d6000c0d40980358a4000c0800c2c921100386402c262441c041a5900980c0e42800200b40815001d101015450041c0001e00140500525200c800307034640348014500c00f51181c16095100132400309000d1030380c00c240c2c4490400340e03001d00320881034000c00c1c3e45a04154041c2c41e200149030340500031040c26041f103450344001c0110049194600d5000c100100d81194441d1400c00c02045070031003031800030043c08010311600c90043c60000f595842e801d0280c540410b1160410601403540c40014011000343d8000b22400502251120540d00e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 834532374 1107 834531267 834531277
    0xe281d09150703060b03090102090102010e010c140c0a021f09140901053c03070b040b0702060310050d0b010e0907080615131b2604080c03 61
    0x1005000c007200019400039040c600410155680c0f440d48120b60000d1761074031000d03500411844000c5d6824030503001a00500c20080c0040303102046c000d40f80241400000c6c4a6060014038803a021404000601d0099405410384004600c95040015403a01030b003175040004180708000682c5e03003129071820805000c02043cdc04050303445c1404000e008c141c40b01500c0b02c1301d0b418042004005114011401c0540090a404405064200201400d0622903003020080c4201400140104045034055407043c40d03041d01e00e240d9075100c60001c0030388030700307281d00695200410b1020381381000701b4214000d048071380040301c0c9000368846120742e81d11388109005000a96202d0000900ca50419059100c81c004001d0514052040d810100d1000c0d07491680b514004500301c0d140302c01c0180c1e408091291080480d00999110440301070060b8080c0c80064405080040081441c12070b104003841120 = true := by decide +kernel

theorem cover : BRFrame.Cov 834352517 834532374 := by
  have h0 := BRFrame.cov_init 834352517
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834352517 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 834352517 ≤ n) (h2 : n < 834532374) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
