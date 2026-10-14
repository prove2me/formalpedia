-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2601
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:11:44.335991+00:00
-- url     : https://prove2.me/submissions/ade3e292-8a1a-4f2c-9312-b8aecef172e1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 467625899 ≤ n < 467805755 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 467627149 1250 467625899 467625923
    0x4030f0321020909060618031203070906080108060711161d01050d02030a021908030d05091e10020f071e0204110a0c02190308120a0c11030328060909 66
    0x702000c01c83c040c14840c0c6820012203c0010143c1c40e090006110020720503900004405400c80441d1600c40146002c01c038844c4000240300c400c94012484070010540703841c0041080d0f0400701c2007500c8003005800b00060200c8000c3c40750b505413051000302c0960703a1898840c0c403c1666440368a982d0000800d4040310800010004207549c03c0c200c00c80050a40c0242c01840ca600d40341c0d0910480440d000444d074184890010701144d43c0101303100400700071091110114090038500406420f181400c02c00d034802d0300c2746003c15400e4044c0400c0c1c1c00f550355400e903401138581d0300c2c00003041b00070b10802c88010000c84400307000c602640e02d0b900e0029202030090720300b0445584d4406951751948542d00c4410302051450340d00760010714100d441000c0e030080181c40010030369034035039600d24103030040302c174003184c0f003036000200f1204516511401c09400746903c0c01013040314041840c2501e0340f01c068011a100c00e590a2422601810f04802c010320765800c5074104450f569a425030310040004103412524404501c03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 467628399 1250 467627149 467627207
    0x180c090a050d120809030d06090b130c14030712020a020307030e1c0602090f040e03030106170105010903060b0f21211b01090c0609080c01110715030204030f03 70
    0x2210505143d1000c1d04041000701c0c0f00c4103844050b0010290380081c8003c11074049607607510b001e924003e01e80a80040f40b102c8a0504004c410003401510407510751518a03080f800d00d0707201c8102140c101101508030ba80f525807100803901031040da07481e00119400015482d800070f074000014061f090180d40da403040080480f0820801034000c03440f0f0302e02c102010007800089101c43d4000d0401a900074560112083d458020130107032035800e101d12a840d003002c4010402d2035081558810100104039404401d58104400602080e4130380c040035250943c0c03508852029243d00995000c070718401020002d07400250501c11184107030004103001c00d40101112203003035020001e441c40c00e8000d10007015081200e10100c2070b42d44807160b50845250364035011958045110720004a014140941d501d40d20316003440c042034078046007038400c2d5042040940258681c0c3ea13010413117000f524140c4510b850103495908080340a4080c6800c040d040d4080c0011207010550810504c980f000c01d5101c002480b8441d503 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 467629649 1250 467628399 467628409
    0xf030b0412020105090d12020d2421062c0102030114030307020f04090507030c080c1011101a0a080105101d040303050a020d0f0c02010e190b06180c090a05 68
    0xd50742140d61ba0b1007800d4501904d402515000c0c2d030400803160041c20004040043e2003620041e0200003034020140310000c416441b200070610180084940e9101b110500c8503200c0108002c052001d01110350743d141600c0c403038445c801c0906216441d140d12107860343e9070300800e600035070081c854090210001c200d0b03103003241404001c0e9000241c000b400c402e803041d21070702448090b20366410120340500620801000183c510710464003d8040c100003000d0521404040c0030b010001e95148800380012455107448103000080c80304066403032107801180240c0e000c400801d060016941d071070360102c5680300c00b044034001580100d205614600d000d00ca000e644606020499100341c0031900c1c43c00314400002e02003400ba80105402a0314060010718103141e0404042c111b6882d00341d8400721030b80300c03840c0400c00b540c2401641034110902018110030281603628a0380e03050803420003071260120400150a658601020700d8040b0000c00518a80d89017003c4a641e01791301c03c943d0240300700ca0300d0001090078140 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 467630899 1250 467629649 467629651
    0x60212060f030c01090e07020f1608010f090f02130209030a0b2202150306190306020904050a06050d060f0b032e090317100305010e24070806060703090f030b0412020105 74
    0x40e150352032000c6c02c0ca0301c0e00500e14001003100b01940326516408184074000c0200d600c100c009515180061400d000c3c0007801c3d62040040c041c45241032004000c042146e284030881800e40c11120410380e2092503203003201070702a20748200d030706000380340b07915050081c0c110503644030f8107000c0b603800c40740a01e00000d10060b02460707502035040042c05d02404002030b0180c000715008080105142030100094100e0100e0010742c1c1c1086400a4010603440101e04203805880d030050446602400403c0c00c18021513000750240101400c0c450300c805402d13412081c640e0014a64003405004c0c0c60070418044001260b00310384100000d071002024542222020041c413400030340940c950340b401c0040b00d42403900c011200002d00600b021541340b120000002c1c0091140804046515001d00b0100022000c2140924103401400380710b80c011a08004000d6071220710290300a004850b030a86840c81c80c242151854401e400c410501c00960300080140205048042e1069121b0f00d00070040000c420022400d80790 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 467632149 1250 467630899 467630923
    0xf0302030c1c0b07090503070605070b06010f120c18080d09140f2110060510050403080d0203100e1e330312040f05040e15010b0d09060212060f03 64
    0x20001411000280c04101d0058029501e0705d0450691500da80009007058401d078055000b0403000180f02c0c042100182c0044e62011b42401e10b00c1140c1845000070305188038908500d5107095454103030b41c0b059405040200301c14045502001c1010b1349902d003036a6100960030006c80401c1c03000100055000180d03900b8110114060801d1800040240c1407009411507540703030707155850001002c0e1006d2242007007480801200260041403c40c5410180400d50303404001500c100501040144040b648407800c5a010441210005a49030f84407040314410b4010354100055044641090040607402d902d01035114501e800100c46c141c5c0c640d15400ca4120305c41e901064003a21015910480f80c40c003041140d4902e00c000b405895602c0541c4a08802592080d0404403901d000310030180400d051500c61060214145001040107507108100d407003661105106000c0d8005000034450002c0c121908030440e45544820150748580020402c01c0d02c542044451a000f41252280401c43d86000154004841 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 467633399 1250 467632149 467632189
    0x30c2101020310050a08070333090f060c0e031c0306030c06020304060e01091d07030f0c031d0109170702030a02120d1206230a0e071205090102090f130e070f0302030c 73
    0x40d6011035424403440900e5109055010308410100032709401e0256410300d0703106000c2510304501c5171030701e0300c100c80704002101c08100a81e00682500d490009990b9100c440030001c0011030030010310120301803d410f4100406042100c0e000207552500000035000b41c07041912510100c03203c507001100d4040c000d100711045445d010300c840712420244046075400100c28500402c007a10303805080030650f0040002003000a44d505400d044614110b041140208070590080c09180c0703182d1200e03000c5900040209103080000900d1008540e410828110140d5015028181504051400d0351301e0703901c4183d0030780105181d40300c0c0003c09000c40c81068240c030310031303a8251401004003240001c842e48142000fa0810307012840805c011150f5503d05100d01e045580f0481c0d84101c0e810102e040c4d540181c10000c0503801800010304030345d07888a61044844054495000c030109022a46000d4040f04014001c0d90260140c0406c1260042d40ea10b400d4900a038200e40c0c004101c001030180d0701c1240034004c0205 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 467634649 1250 467633399 467633423
    0x1509050d150f1d07230906010f1b080903100c05180109050a030507050102190201080c030603010f0e01240f1406120a0c0f0806030c2101020310050a080703 68
    0x158072680007a400322072004002408201000400380075036445000741c2c41c00d0340080800c200742c00c50342025952403142101c00c0081a4010300220b04000806842d1a05012920b030300c0644143c422490300c3c1d200c00c02050909548030035810032087d03d500408441d4003902944c00004000549801201850760150341c50078948248140003081c1d2603101b6040a04001554000041c0c5648540401002c0d46c0150050803085151100291034810070102a441c1d40d60103040f4040541c3e044000564001c440c1c10b0040ea980c2c6d241c44c0020b004000442e040d48002c0c2c94420f013040074850540c0010b401c104880790040f0090160300803020704034498403d15040d1341c42003100344022034101c10000c0300c42d0000342c002070a000555000032520b0200b141c03c00004c555035544582e603ea03109052002078940ea040c8640123040950119440f02e4a42359154081e80c00c808a0030031410700040d5040d000a00310b4003c549a003001102504600c02c148178041c8984220b039030200d9102d402055070012264401000441 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 467635899 1250 467634649 467634683
    0x140d050f010b0909160e030a060b03070e25030b041d120c0709110f040b090103060b040b19020c0a0e16080f04030c0503120106170a0501080307060b0d020a1509050d 72
    0x20502d40462401c00040d4091b020694a0420034151464414000458410080d009041c50070200754440c400715449401031001e0740141c0090000c0121600c10303401c0b02c00740c1040060380a080c081c80c001c1d40040ca48840c90b50500c1d0504034102d40540d080064514102c0030104001036400749180410700c41d00285400c0002c0d4450790701480f480140c0c1005241450307056081d811f4580c00c9688444600200000d80d17407102e6902d03125940141c1580b60107142000d0a0480d4248a03008048a000e00d08120081c10603100707000300801c9180b108000c4c8100d00907903ea0070b6680c0707a0308003514500c04c0c95a1400740740d0251406002128841c40413003000301201c0d900c50714129418000304800751024002000101245002c00c03008a028202c95202c240c00683c1100c0f10900c401030080c2560541071410300103012010020040780d0404e0b070080800310300c0740000c100203511301c01010402540400380d10700012344100e100100c0c5035041c407039485515449a54100b0b01803102c0d8030190040c40000e43d01c2030b1200d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 467637149 1250 467635899 467635921
    0x306040b030f10180b010b0a080109090b0610030b032a040506010804020607080f0307030204060f020f1b030114041a0a110901080c12090106080f031c050601140d050f010b0909 77
    0x540c04e290850701005009039446500c0559001e030850b112802001501117901078201144500520f40071008001000b20b035100d0070090400900b4091050034400c2c816450580700350807a04144000805403000fa0b100203200c83c1c40c05070a240000d510040303100fa5170b40c203460140300300c500c41e92043c0c60300805a5125420400340b030348100d004070b64401040c0540f01d48079218001442c0300d91144d841c016034032428a0400f50801190b0210f40e0115486401c58000d54440441c0300001d00072000000c4d4080748036000003d01600d1416072400104005004010038458143c503800d00c05a0351200340340d145d803106400d09040d00c0d090b01b1922518241040240025481001402d038007000c0c02440500707000550015102d4540180d6035480e460307440d114140300c0d80314203010288a00215038000d40c40e008010f81c003440014000e00e0321a8405684000050b4564011000181e001c04050150faa646e840c0e00128030081c441590b50303400c40d603006e800102e14106034200302c0b003070703140c1c01000c000d00f95490525440c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 467638399 1250 467637149 467637161
    0x50108101808250317010801020a12021e0c010b12070815190c12230402040b030a080429040308030414070807091a010212040e041109010306020306040b030f10 70
    0x2403070404900d070303007100c42010611910b00f119100c1d507107054030328500b4101040b61050607004100540d1040107004100360300003042c03031b55115034400003603100c010b0490b90b0b812480f91805e40c1c04682c0d00000d00c0d005080c8040d4400c25620714100c8401c23013804801c04046a882066000790141c60b800f4078030250428171620009580200c801c01940c203440c8175482d0f0002a20b01340113009010809464083d82100158080c40c0c03401d1242d441c804076002d080391050a24510301030806030196540b80e03e019140d40341072000c07071911500a90360750381c3c07030342d0b44c40e0004e0514110342d90f2209190207003819010200740850884045035001140300b801e54039180c40da82c450100c00090139170700340b042c40000944aa0188100001004e00141c00101101603603c000584400c50035594119003200d40040c041d51024001c0e641910346030182e0440b5980e880c030b0400e0040c00b0301052690f00c5100d0398000001c00020707030004e51050a0a803001e00195000e441890341c0c550102c1c800c00641c3e0042501c240302100154414 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 467639649 1250 467638399 467638417
    0x1020d0e040615030902040c030b0a03021c080f0705150c0f2a010209040501050a0305070303051c0207060b040f0903090b070309030f0807020102070e16270603050108101808 76
    0x200a965550a124110a50f603000b0b4080380c0c50300e205900703501c4c1c98400e10240b203810f0300f018400304a042000800744500d502000348111481240d4a035084014030302880a61b9001c40304907602d000625452907190007000c0c045800b44110f04140b00100e100007151802022449030403810300040c0e04e0304d541183c110380e01c00741201804582009910b50784500e4a084080440001aa1042d040c824031040e910143c2109008400310101000003a030b00150100c210380d058540b4686989103508040790f2050403030a0f1266140c00032403204284035066200340c000400840b400c11807410400c00304025122045405008103060440c10003e50300031030001c00701144a49065040345e500c075030341d1070350f000c5501e10705035030709007012031200b00b1942c0400101d00680100b80d0921007516024081815989144002d60300304062604a2110580c51481070100795240c0550382a005848010040040c5424807030340c50340d40700d000840f00b14440386118800040f00840b040d2100c4440d030352544080ca6001c07400da = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 467640899 1250 467639649 467639651
    0x1e0306120607030618090503030604050408070f120f0f0c0201051b011107060506010804080d0c031d15060402040b04031b0e180d140307080411040e1c0e01020d0e04 72
    0x303280e2902041c000c09114034116140021040d0402c07490001031000c004060b0000f500c1c24882030040b410000a40394480021200407840380d9071850b00003801d01807c02e004207101c92104500c820003080702e41d100e000c00010707a684000e4242d1017408640302c4010020001c042854400402e026510460090043c030a0040076150302d1341180d80d10600b11040d8180078440000081504001c2068500070550040000d1070100c040b41400e40301e444d000d1003820a00d200f110341d284920001e003402a00108095022170b9805940e195118031150f4440805548030050b04c080c40000800500e490f10a84090f0340c41550298182421035a5140e500380f603404505401c604581d800042079802d80c00380d1441244011000c80002007090502d600d44040e50b03c01030180407011110311a1810b00e801500e1f4401d0322860803005a803502d0412100c00203003030800641150400040c0c03010348000003000d50b050390f212034000070300403c0340c00c2c1202d0044441040c42e006800000d90403413802d1080c5032a201408000384 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 467642149 1250 467640899 467640919
    0x8010f0614122404170403021819060b070201020115181e0203040302031b0705090f060a0305030a0507020a15080412030e100f0c0809030901051e0408211e0306 70
    0xc08521032122000400b0f00000d02d6030402c81048090b0882001030713281030403654109411030340001c0046000018122186881800044c80c8900000140600241010042150607119052884194001c1038244d02641c00c0056000c2d019562840b100b0850303480b0241417080c00990400307803016240034081f010301c004510f0320510405640e48011406071788207030000c55841114640010700b01696203641003d42c2c124501c10401c0e0b4441d1030f00c3c6540300710030340015041a99240009818400c0c95003001c0c08512000ca0880c7c00c0d00c0e0000028030f1118000c9503c5103210f691001010382d8034404405000010b075801e004070740041c600c1c500322408809241804a0001403070344d4498030b82111100c0e00203107203403543d840c0c41c001c08135403040507511661850700603503e160007180d951381c0f4482c8011680c100000011030000707080f034140c28031021603410040740d03540326507408500703076035510032061307038980854881c0344041042291040b100c10318800100700080c400f1201c00d502c0300c4d8000400d50340c0c000351440 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 467643399 1250 467642149 467642173
    0x627180e0607050a020f03030603071401020319031a06091309050a05030f0301030b25180504090506090106080303041101200a1a1501140702042408010f061412 70
    0x404224800c0100f035440a8680c1600700700240b810000c0403101c460341d0820000c0c450503440124100041d00c800316009071400d10b100700101d140d440388030300e004802610310300c022040070780c10f0300a940700719218034007000d02c1420340302001010b10070b01000940c0b246050800000b03010036074028110807400390341035400341216034840600b560703c014032200c90a00c00000500c100228008819040340c58a800002514103640225018040141c03052081c801144180000708200d006140702070308015200707201d50421032030429a204000e0b144c4040c0c40d4200071011840360000400e03a40b00d960070440c40950301c403108005443d9104c41618800c86000740034041004160100001c0d86084c0c070030340d00004810300d03840302c40100c0ca0000c1c0070180c200d04c03409402040b40e80e02101c0c07000305881c03c14096a84242500c0020001c01d410703040790501d1558008940011003501c010301c4100c03844140240180410b40d580c1e0000c031003040c000c680d0208805814980103052641699202d4080c207030840703107600a00c0e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 467644649 1250 467643399 467643403
    0x150804140a021e13060602061b1c02040512031c020a03091a0609061c081b1204030b06011407060b1203042606100509040f0f0b010627180e 61
    0x740c180e075000500003540c0d000581c100031131001c210b03c1d61004100012820104025180d440c058205420600001c202c0c11800c00c080d82110100700c440014084040d0700f0300b1030140a0f400c24403132203120f07131b03c145140076004001004a842c0b092250a0781080c820b06500030038002d40041100c0e600301503461510800003800c141c55500d000c2120315000440b1f160010402c50148030041905014044429140c0410018040c1c01128140d00c42160fa03254640c03099021100c80c00c1c603000890901c1200f103059183c0118400900a5901800740025a590389000548058141174480c4500403800c100c1240400c155034031046001000400b0028018451a411403464005c1d07003150b40a0710f8140c0780719942da02514141070000352104080c4c030252400b0440c00340b1a0009105060140c600c01c8005020400310250003814540c1c05120107d41c1e910f03a04102241080901440d004504c1062130748188024945101c0150300c540c1380880240b40c1031410381d002005a1120144001c1d46038807034402a505d007 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 467645899 1250 467644649 467644669
    0x4051c020d110f010f0806040b0f0d030807021002030603030403020603040609060e0c030706030b0603040201031d0604030e0109050418060c0905030a050303151f0f1101020c0601050a150804140a02 86
    0x281080d0000c0c0b0030010412012940b000e00e6035040c40160801c08544942090034a03a20520840b00080d08001c0c00012444c9408201e1441e540802c4c5e4400038002c25070043d05090007904a0b500f02c400f03001c91080310308100e00c000d80d0342a030305500900c01000140360440c004c550003441594045201205aa1204152601c28034011280e8224507104c04640c10104801e02c000c204c00e10302480101051300c0070404510005c0c00284c1019202d14000403c82c481d000403035450816082103403c0c9251030b0500420040e5200001c1c3d000403681c4800243d2440c0030b015816151250403044034000300d50355107203002444816045400d2003070306200015241e80521480c1c2405001c1e501440d9030386040400c00344206041041e05204104507140100c8540d0b0306481c80040348940d007001d0708182d000280540d091441100c00307001c0c0707600009a504401402049060490324207807400c21400f51203101c585580c10b51000700f4400205034100040c01705003082d12039011003900000b92040241140c000c1011425 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 467647149 1250 467645899 467645903
    0x715032408060901090f0b06010201060e0c0a030506060301060503181f140f0912340201020606120d050318010213210209010e04300206090c010504051c020d 69
    0x31400c504000ea01c1082c0010b503842030b10003008000d0b07800302d581c580c0d21107002c5010160144c21030f130300080d0702c0e079000f5032003107015040504060400b882e10f0703e0300e9010303a84804075110020382070a002c640b1a04088066034161891500e0350780c2140e951041c0c030104150300345d0003502244100d01e00020b0300c402440245450410344c510124620051010000110038040d12211320685180700b042100780001c50b1322080070700c40c00c61481c0e039100c903070510b01c201e8810040035a42070100c034000b8003030b00da408402030504c6c40e100ba026a5540c0da590780c2080700c0418504000800340e0460014210184e1040b8006c5600850004030107400707064920090f42280c120000c20380b604454200c1c00d20841e80d1040204000c1614145410400c83d11940481c840d40c0040c4610281a02e03444080f4040040c0e01080b50504811110740340906190840747c4940c43d82c041f00c240e13016000c0c8901066080b18007050254281106840e00c030b2910340f8002c01d1000e40b00e801000c507040102d18922240c01a580c0c9628992454 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 467648399 1250 467647149 467647211
    0x9070b0309030c060c03040f24050f15090c0405190305060c03091c051606021605061b03150105090d08120421020703030e1318050c030d02071503 64
    0x10740421402880c04c00301034030554507a44240b003080006042000490f403015480032010b10701041c01c0714184945a2400c046030086803c013002c12079178003001140c02e40305513980fa007002140341c40f00d414003580c94419100012406001c10007070019040447c410015084885401200c45980351101400c05005079070203003075040b0002c00d2000c100c8080003400c018075041da003001d01c1091340c01c2c005813281c4a40700d8440c0c00014883d0304801401050750580c3d2540c250780c090480f61010320722b03240361643c0040301c540784115201141607c050f6543d0707059920401d070301c04000c0c0c100c00c503000c01903816070031800000d03511058540503800020003200140040061640d14800b8070304261614441c00034940c0601441c01d200150b0f1046195800180300c8100e0740c050a200008599800220b03c180302e1400c101c1c1242400c042041c000c407480d1038031309900d45008000b6a07004000990030540c450303501000050041c1d005190074020145211554402e20090b4100080c10650404524400000b4891006184 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 467649649 1250 467648399 467648407
    0xb090a050109050303040302061609271503020103051b03011211131a0103231b04030c0e010b040f090b010306031a0f010906050d110315010e0a0f0c1709070b030903 72
    0x19010051140c00c010001d400d078112441908002f0800029446220603038507402c1d4280c2c40304040260f04141e0041888400d102058440daa0111601480d1004a00003481c0c0000a092074070780c111100903a040001c0007500e507134a402000d452002c1c1c503042c151018404041a00b15943da500e02c0d00400950080020402c00c2c081051400040c00c08407003d07040c1810040400d51487c541003442c8140c00c1001440324864454002941d0705803900e0b5131840b0700386800100841070016482c00d65040304c90400311055141c6c0c0b6217520300b0041c000d510482008502e007940502031500c50b90000c0d6000350061400050b21550380d01c0303188048a9000041c103410405100340030a01403c103d02c01c1c050000c1c0202480080c0c0703080080340081c1c0c2d4104015080c904c00d01803104035aa010b20500212081d11004400340c3e586a42c9400c107160000c0e15400501c51400701e064806408600402501f2072440d05d6241c03240040304c681d030302082d00061000426025103c00070800f03070454009140a040310704011611 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 467650899 1250 467649649 467649653
    0x11413051c0b010602030313120905040c09080f01090b190e0106120311161412150610110d0507050307050703140c150910020304082401060507030c0b090a05010905030304 75
    0x1002c403040c0c000c0401c40d0004c10800010143d40c40304205010303440130024074030007403201049401c1c80c0b40f90481640541007009400c01994469106e0003a60850303411785020706081c0b142035080319507104004003018960000200810110b202000100514180c0030031070140401c0ea9030308440450300240c2500404401d904d0601d98451f04614a81030b000c0c00401c0700ae27001d46500004200980b03c0c0303991044d8840c05002d403e86408010102c0030700100200d441c0d541485440c404141003c46415001d480030b120402a924801d0401d245584407901c05055040c0d0701000890342c1d0782c08000c0c103460a00c810415800001c508106500003140a411603503180c6070122005400d140c80d02e54624420300850385821800e8580c5d0007101c80f440811107c1d041011010503007a8150b0203282d0100020380103241c1482094100c455500001c1c1c01600c00b106c96607a200d00c5e00f941e480c058104040c001804900c0c5190003d400e0b0108075403c1084641183e0452000e41c1c1c400d130949081c40811280340d0808028001 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 467652149 1250 467650899 467650913
    0x4050a0809010c29070512040605282708030c03060d120c060e0102090105191e020d02070603021c090312150f0611030706051005060c0105160905011413051c 69
    0x2801c10a141b90a52070f0441215418945480240020b401c9644e14008500b03280c00007824510907076040b842800604080c400c50700c00504040d428150030340303202e51a41c0c07801800141a8100c59078070184080c1191904042d40969800003054280c010b614290745102266403201d0055000d482582e0300c0285e00100c0c51700000350f444a1040c0e141d268010300003595980e80040c140c40c480c0c1441d007003a01f9030002d807501c22030b81242804908200403507074003500520b847e0b000c40e03140d10303021407a000c80d100b1a681d040200c0880c800c6100442002c5090480244400c0441d0450041c05010340b0700343c82168400d4041c40c0c1241e41c0445c0308920541c80d00b0301001000b606e005450300a01d0301e4100808004402e0303488c0c9403a0311030044020419a030761400140c00b10300c2000180301809020704071a0319400da03c80c6050003045c080c0c2e001c1000c000d2070142ca118032841107040800792801039445410620f541d8540071810303046500d13902070004e412080801c007034079802801d81000c410142452032881c0341d818000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 467653399 1250 467652149 467652151
    0x6040b1e040f030f020f09190509030301030314071b14210307021c120c0317070e0118091521080304080f0d3204050a0809010c29 57
    0x5200c02005010800c807400d03903910020110303a0040e000e50400200c40c80081da4121400100e9540541e6000a1041c2c2c0d510301c01d03150580344e004c1350040101da00c806002541d0b0340824400107002a4251070242c6d03641310000003802105100703070b45c0c01c0b05403c00b840c68461902201d41100802400015a05ca1149469811400400112042c401c00400c40e61241c070303281d02c5507a001a0140d0071100740c801502c00c2e0368688508007500981d64a071801d0403480c1c001c1c40603020030b04c2a4002032040041544200340c00001900a003c1600d81d40304031380c051001991805280e040900c1102c0c881c510000e50105540184250541c4075203403017100c5414102d842e9a01c9850694402201002e02e0f0048000341020303045039000380c0c00116858035000c940018031050b201e90b0103048445400c00c1e01c600da40b009154070801c81e130200c2005010483c003000d030f0708000341c22044030b02a0455011900c0c04022030b05400003071940502c185011105a0b1954440c0000003003684000081e28110100006035040302810301 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 467654649 1250 467653399 467653447
    0x30c04091115040e07230c01020307030b030f0606040c09030609050c030f0303010e070c0c03150608010c21050a1d0d020709051303080901020904090c030209090309030a03110c06040b 80
    0x194200760030b140310425441d40043c010350600c4001800c42c0d4000031800e5000d0b046c07200b1503440581d40c18410300140e001c5c3d001600d6080c0480d007000c112075130515000c2548070b821403c0000074100b660310402040054841214500144581040c01102041e641d00032800740c503010300002c11030300d000708050501e49038046a5141c000d400920044c49440507805440d50000500d182410f0004058106017081c004103a00040151103246226814903c07140c000d1030807510640c000b0080710003022005d586000c0202c0c54840300d00c091441c4c46060b041070350b00c0603400c00014900051803012285a0075280751102c070101c0c1c000c4e030201e06241091a4100a0b10000d070064920512003805c16400da1001c0c000c02031402028001600d0015040790000d41c140c3d60a03d07001001804030008074245000703200311038002a809001c500001540d4001c0010440d05080300103402014103c91503101103c20300101c00310002140640480300000f07507160f0b80900090940c40f00d100c0d80d941190445810f0103000540c0d1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 467655899 1250 467654649 467654689
    0x1a0103050d05070c0b0d15050a050f19080102070b090d0f0c03052d0a0e0d0b01180b040c050a02160302091b0403021009030c0b030f0411030c040911 65
    0x60002800c081015820000309050468441c000c515008013001c10315088246060008256101009001c0d085501615007595840b1304040c0c0300c02c1800344600803402a07a40148107030b160b0070041d051090350101c403610302c0d0103071507035480c3c44800241c2a0780c0001010348120380302da010300c0400d100c04d008611a486160900180b84529860050141c08184c540a41800004168164440c9007030100a4641030b0310850031f9440304564800042c80d800000001c0b0004042452f40702550500d10680c1d2200c0d17030050242c039502d0b0319280b1007031440f07605034001083c2c80e42c43d06c0c0c03108815110750140400410440d110f1039210201010000d140800160b008a810140c0450070000741c1c440c401c00c0e0340c004000050590300c0981d00c1c1c0e10f0062502c19980300039000808105103d112981c000084001d4034410300c41d0342d451640da40501070190009135180c07144015080c000c00e00050052126161120010302550383c102503600008040f59284102a80d01040f50302c0e8010452402c00c058291265508003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 467657149 1250 467655899 467655901
    0x30e120a05070e040624081b0a12050f070b0d0e01050402090c032d0108070509012321150718140d020d05101a06030601230c0304031a 59
    0x1140780c0c0d50480c5124885606441602003000e0124640201e04861000c070160840760841c02d662a000500341d03c1024214003400705a0901424003051020390210000d0102005038100448101e02d0380307120780102ca80b80720340c034510b00001000b0701c250f80046c80307801241c94490b403120f05110241c030481040043c0c0381e4074090403c4010f07603450008541004e071a030056500c943e20307140f0b0750003400d0366100e458003441144180301e20340f01ca50a0906060350350403026103904070f03075a00c140409140c00380121035010b0403001a5880c0780d0b800f1804c01c1c1d41882c1c000c3c00c1410014500300040760342d0746003518010a81d0032580340c3c4401c00d58a095169040f80c0d5501c3e040140002104007142d10321820b00800340c1c590b0080013150746c6580c0f00f48058810a800a10305440310036580303003482d62050500c2190000508103030040c040400c20200b04011102d002e81510b1940d40c0d288011245035400e149210b50003a90300d0100300040e030112020b0014202000000c1da961400c504101b1020000134051101c4018800 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 467658399 1250 467657149 467657153
    0xf0b04080106050f060a080c040902040329010302030303040f030905040e0a030306050a05010923030619110316180306020d0b130203060a030807060b09161211041a0c0102030103030e120a 82
    0x201181d40098080c41d01d041c0c036444100c8d8170791441c416540840c070300305e0000c24080280410303000032949021b8041e03144580c1c00d000c3c03140c07803900280900c0040d48c940c00038030008010030680f48584407024442e00e04400c24035103440c0003404131043c03291a0714140e07201e00c84010405415229800181000316075001b4242d107032000007000c00c4450b0007640e1000c0784514401d40240b8180c00445003000d401001d54007145800b40c1c523480f504c19001e84131507005084c08600300001d0202801c407801801030b60940358944015072403c0c0e84016100c16516a0700741d9030800000891030074230140a0000280d02c0114280c181c4204000002da0401c1103812410f10400500000360707110840e20301200c0c0c1c000801d50f250811410101d000740543c002e4560440c1001041103800300c240d00d514000c01e20745494031490b90481c01c118204865240745507010000b0208014019500d001c0c61142c60b000d4401003051504000c02e15503400c1e030300281e100b1004180720000744107007071506103480e25075030003404010896002c0d26 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 467659649 1250 467658399 467658409
    0xd0c091a100302091c142e0209120a030908070509270a082b02072f130c03060503160b07030c02031903030b0409111302040f0b04080106050f 62
    0x24000207150f03001030110703500d0302c9102d18220f44205400c43c0c0e0040c00b580e424008080b07860709010384940e0046a0001607543c41001e00c01c00d0024a06030030504513507041021100962005e13520541c40030f149002d92a81800030021590311074420350314490414238202020340303001c2d059000140301d1420801003082207140780c50800400d202e00b905101b0014038003400d0030300f840c0341c070034000e0000240040d850f440015100441600034103d200c450b0784900004d11440100e0140715002403007031003240c2040c031804c2264400440840072482411a42000b00c1001550b10030078034010045481e141c0400400c0c00e43c06108000041c00190701520034000c2c0c2c406c0200d40380c0c0035402411050380c804600081458800c1c1755040d001c0d1f9001d002c941c0b000003000018800b0a0000c04120700007400d0654040e440d04140c0100108180c1c0001d1107001c0d000c02000700650310040d079140c5040c4d2607013484005024084150800010300c00892000e0740e442c101800103082d80ea040d0025400b030462080c40d0f08654440b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 467660899 1250 467659649 467659669
    0x3180b0c030714031005010905090c0d050403090b12040c0501020303090d11010b120a020a270b0f19060f03020a0e04050619060302040e090a0c031509020d0c091a 71
    0x241030022580d03540e6881c0c05640081e140180400c800c800402005000c043e0705100340166882621030322005540c0300100000e10b001281c041609442c00e000595a104190b0000b0342c00a109040007100c9075202e02d01104590000000b10310346103299814042889100d440d80c9000c0c06080c40a0740c03451801e01ca060f0b0b0303200100070081d020000c482000f2800320100b0360081200c2c0c540181410100103450400a81d10301d08041d090b4071581c0204c1d000240020300d49500c403c42084060a1408414140748a100038540d4506058014401034400006581d5602c00ca6461a082483d00903400f0b04040000704030540c031030b61840078503104012580c402078000e4840d04419200b254082081d903220b20120720700307144144031032031800c02359280404d210703400d038029105079000040c0524003039542449907071b50b60840903009000d07443d820b04144085250f0345600200c6500300e510101e121000395010600704180341c4400d807400c6e4003551061000c0125401100f41e020b000031000c0551155032000038001c50a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 467662149 1250 467660899 467660911
    0x131134050d12090203060c0a0807210b0a12050640030c0b0a1b140702011407150209040b03241305013201060c1e0b04050d03180b 57
    0x100c006403032005010160403108009a0245c00d07039046060a511030080c41d00702203520404581610002104944140204201c6415815042600c403403040c000e00000c04650380487c0d00070480c11408542e01e42c020944600b82e0707209000810046c640341d00c41d00340841049010f51703000458804902988051b8000008141d00004211808111146400c1e00c0000900c00f0003020010954200b119880c01d45d80883c070b0824000034484003c0014440c100e9141040e02050400484280005000355118a200946000324803d607203160402c039442d41c200c42c005140403401d071250005000140d60815000c1c20f5206c080540061084181d0030082403c05c031701d8070700800050251706000600e40340c6220107009050350000c008016220000c2c0d1003c062500d064262980350b0a108000034210410354a00c0b4100e8801c0c0c0c0e202074091165680d4481d440301e6540c207500d4040281042000850000e0300c03854069885207000b004014041c0c140541550030208006044844803140c6801084030022001d82c402c0c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 467663399 1250 467662149 467662157
    0x70206030a060e190e1906150f0e01050f040911040903210b09130b0c030714041e0803090102030405190e07020303040317070e131134050d 61
    0x6910102540c008000340c1e44075850142c0020188140c40005400501202d14050300c2805144124175400342e80d0215000d0000c02e5580304d260080c0400c40560211060055075000c0d0600e032603943e00c03030200b040c0c2c84d504400000e4000e00010041d619003020b1038a4140700c11784052180410680303900680040001140d4010703a212440c201c20188140c0f0120000804050703110300c00c1540c603000700c00400c1c030480a9400780b0b004802181c4d192400962081c9400d610044c8041c281e070f40c0f0541c81c0340c6a00003030401c50510200303891245020300c0031009880900703d9030200000c010050310368442451081e60203c0360380d03001084001d4a69074080125400e41e102640c1c0c40c0c01004a45042c00a20a10380c4c2c01300840465110034031071412750110041d03014600a07a01c40301d24640d42d075800201000156041e2000c1100c184008485080c2615100e94103000e4400c0095036600782c3c040c004850348020760704451390540032448405010072620a0442504001103280340c0e40c01035481030f40e690b0200000c1000c1c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 467664649 1250 467663399 467663401
    0x110d0902180a0603020109170706140c010606030e010c0906050d2307030b011701050a050d03030e0d080a20030f0c07150f061d0a021b010908070b061507020603 70
    0x95100d80224150703180660011072003914000c8a980010301da81d010880c0000d41540d80015000b100120f100c18803e0305c003014140d024035103030080c2c44100c2c0501c103999200348240f10100701401d00780305010060080d40c0300814041c00ea08c0341c2600b101c00e16510b890034030400020a01009511800381c503e0301380c0c10600001c4203080a009020100b194a613148580c042160401c9807503030341074000d260100d4080e01c581b11441c0050401e0100c00302d003406215040421180104182c0c80e100c2207903403241e4000d041c000b4025500e0030b03c15041c10078141200b00800c054000744500000d451140d00c4084250b68040c8848109504107412203100203088943c104540402080019100c071085820490b40065045041d000309100f0202a0400c048041c109a141040000e0340e8402407101c048005401d43c03d00400b641c40c5103c42c0002e401c1181d241541140c85078100401d5a0244144c00300540602c030b5a5444030114500841c0800340200460701500c0c040650204000c203001c16207104950454a00d502e0f = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 467665899 1250 467664649 467664653
    0x20a0b010b030a06081207030e06040311130906020c06060906010c110405040c080718110f07020103090521070b07030606050307030c0201410105030a020607141e060109110d09 77
    0x2500c5a03410103045d9006041c50140c00304400401000e04034443c1c0c65428440e48040100f001a001d50f21010341003082020581c3e48906d082603114511620002000520303441391748401040380c010401d220110f5100c1c0e803e021103440c1540d001c2c0e40c0300718240b81c001003004d450b40c1c070122014094070740c00d40540d40b074401060400c24000d0040e40a4082e80007128401907442d09841c2400c0464180038842600c1d0003240160078003000c040f111010241158140ba004a55004400601c001042580e0500605220300b00c1301c2190b4440035060701190011030b4440716075060244072a00d0242411040c90725226040010b1a0040292617001051303080004020081344001c0e0b0140840c1d450440c0d44036082e44000703026054081c00e1178030b601c404042100034449441c0d80c0b072074812021702034594541c0c0700c00003010041c980040145001ca105149032615240105007081c54680c0468929583d184034a201c081000802c100f560f005141400d07051150f0a004540c0c10303082c3c496412500d03040c50711844e01c101 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 467667149 1250 467665899 467665901
    0x10e040c0c0b091c2c01080c031b0d02040612090f0b10090623040524040e010609021c0c23220807140604051207080f03070c0501020a0b010b030a 64
    0x52100c1c042c0c48524040b01131160001d08541042c841120a80d80311400202d130300c82140e22110700100c040c1c5034024162140c1c450803007075800082c280031030001d201d4200d4800340910f0016040100c141100941c0310707800d02d05c010385003a2508000d0503001d03142c13911000204005010640315913070080c244d11015240c46080410000080d0011070001c2e081540000b40010384045030002400d4100e035031148030400504002c01d1354402d0342d1528449601c13900606540c065402c1480030041d00500000d0301d201d181c2d800c40d09440d400d600041800340e011569601c0c0c1c0646001d0440c05410901d402c00c01000000c1c0f0162a1143c102c00004094800600140090080e00122030341c03a501208101d005060040c504001f40b9001d0099940a00031480002501d40b52850792150200009040034103041c20a010b010480c10101003841162041220001d8454001c3c003c4003262482200034555070344403404c18458060300340d400503046501c040d030030740c01080202c4140c42c1501c0c001610310340d498680c607041b80 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 467668399 1250 467667149 467667163
    0x17100501050c030c010c02161e142115090f0607030b0622090e070b0d02070309051309200904030f11030d020c060105090123010507061802010e040c0c0b09 68
    0x110198030741b500c1040b8084d0005603128888204026043c012034883c0c1d08002c0e50310344422200310403019044113008450480a000004a0700907140440c24030749030882000341c55551014a40342d030400700382082c2c041c00c011411070b441041c82d0020048550340c0c034420780c0d403200000c00da00205a0b50fa00004036541e80c4074215860707008410210490081e0f00d2107003002c84005442195900d42c500b01100d6025003010403603904803040c00c1d0342c2c1c40c01e200f000c400c0c49000c3d6101e080100e013041140000401c0135a14124480c903518415800001c90448514140501c45c02c80110701c4c826201071810a00f13079980312403805030b200764103203404421390021403820784031b00303241d08090000c902004c940e070202c0e141182d003d41454210380c2c0454070b4903661801440550542070141100070701e144101e03d0481e0760443d0020403170b1641850901d16203456602c94108803242c01414016005511071010300b550780c4079a4111044404032420130401c10701c0c200162003851040c00090810718414001149170806201d04 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 467669649 1250 467668399 467668417
    0x7051e0304060203090d08090a080f070b0c0a0905031501050d150507021f0c0c0807080903031c0b0906090a0902030a1401060f0807151218030f17100501050c03 70
    0x41900c0e400c0c1441c1180194204484020a51240e10200341c00144074000c090300811034031002d031030360a170030303480310901540024810b0140c0e080c10042d10000541d41000a48101c64107039070541c440e484c090005112081c10380c0014031950020b90031ba0300103400001ca10b41100d40403201004007810a1400b2007018040c40392480125150208009000b600881d02002070361301e85040e040180400282c14007203a02c080d62541c0000c210049040004001500030010140038444803402c103040c450029107954020907038400040031501030801c00c4807050140c03039110348044803c02c00034601203022400d082d0004109441041c0c88420600c1551421302c40c3c030540c583c00a8103440401d8011b2221030181285110340001d030181c490000491001c089001e5060352450070300540c200281c10000c0b80c140721442c16400500d981d6015503440d808070348132039909036882600c800102c2c3c25820340103801580705a40144540c2c40c86410040121241041d00b001c1d00d8090034850340b110b0070a140303980b66000e0b495003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 467670899 1250 467669649 467669707
    0x20f01140703060e0108100507120501080c0111010b030a060b060f03041a01120b06042705070326091309020d060501080606010e010f11100c0315060302120705 70
    0x14101691810180d80e2182410352002d01581d07030341d00c01030303a40043c09103c1c106c01c90308250000040600517405c0543c100702203140490017901c41040d08811039a0a0b813010704198031040110445503001340024001001c030380300800c5004500350100e52203074210780c0300403c0c4560720b6954210076034074001504c0c80795091114580c0c8900d80340c40c000390f2003108019152440c0d2000d070000240049840100c0302c046520a1080c0c50325180d40f01030201401031084110b9800c0e02090007054468603005009100c4c50090700200301140c07943c28159020a040903095241008003c00c03241108003000440d480303020b00340d0303c5400140d0110607580040159020003075000c6010700c840f1003404600e4018a041c1e41c04036098410a48440005581c000c5000d02081e0108850341c100000440c014210702c801092500c040d5084800341c0f41d0584110380c001000480440e5542c01049a5850590750060140246007000c519088110004c1008540028260000c0000c0006c07e4030070001d43e120440b10139464800 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 467672149 1250 467670899 467670911
    0x4081b031c02011b0819022b02040504110a0305090f1e010605030703030207080c031515010306030618061d070b130b0414040c0c150905031c0c02070803070c0510020f01 74
    0x54000c5c00c6036019540b00010070740f00b8140046000341c0f4400c58034140000b0320441450b00c4405d4a4403002c1031000c030081d1800d6400c0c000000c19442e51b0046619880310f40b1813250342c411554501504403030014103880e49a0f40a1006107a4844001031000e50813400d000749100103003106044140900102e800094040c0100d0400200305074000441809480410090f1000c100002c400c4c1075076800300c100d05203103004106010880307403108441c00307024100061501241d415101c1d00c07070308250b541401d01540c00c000c03010303107485c14040640700300346409011401800c03480c04840b003801d40d5244140030312036140701c1c0010148130300340343e1181c40c0c00148101e48000da1a40d80da199400b40680c5501c21170f5004a0500824080440c4980030041c2c04640c86900540c80d01303030f84d405807002071900303500c00c60b141d101c104100e55005c0d0b001303c4000283c1c66613140100d803c0349045802400c1c00030355448454150301c140403903000100040a00b00507508151a0407803070185c6084201e107000704070b808090907940380c51 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 467673399 1250 467672149 467672201
    0x30c0d0c08070f0e1608040f051006060519090b0702091e04060519050613020a0504031707030306051e0103050c0f070c051212071b0f090204081b031c0201 68
    0xc110700f08580c0b00104600d0182d441411810200504c1c0200d540010070050001f4000b0322100002180c01b4003503000c48040c0d64110040300c0032511280c111101003540411240d002d4442c21016901544191610543c620324009009066015004c8000c0c401c0602c034000417990043d25002d071200d0144503000b9181d904060400c9002031009031440310202c0703400004a4070642c0140500c50040d40301030300044911b02e820042e4802900195140400c00604000010110302038070302c0840780c0c00304109002d549001500d400703011209146d2059000e08005240f0b039209000c0c1c4581070703070318000a00707000c6540d581e8910803102e035214500c10f0708a8031101060381c50500484074180803e5680644058070306044106449a9a54005544581107101000042c002540c1500001c500340341d1030b28015101c503180c00000101807859040040d4180d8003007400c00840d0403c100b441d00c0d202540504035501880d11010a0702d4a03400900505400c2c04869006040c078800d600102d0345541c100300f0881424441e07 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 467674649 1250 467673399 467673419
    0x30c0901060c02040f0624090504060602100501050907051917070e01030e06060604060e030a020a0803070b0a11040e060102100e0d020705101b0606030c0b121005030c0d0c0807 77
    0x2011080c0c4c021403800c0d81341c2200c0d14142c8a84015500308a00074001407108a050042560350507110324200102ca5100256030b0701c46009200c0a4802500a070038038050341e0f815a802c0b01c038168480c40c03040794140103101c60707103410108a980001c01a0156a102407403a00251840c01d2242103420004a07041d080040782c0da4170078401e4034105000d030703030900c10100c0640340030365035000a5800b00d902030810081040343c240900f08003403089101806444c094481500001c2030882c0603840108147c200048020411040c01038199000d100c4220400c02030210904003c070a002c0c1d40949401e1202220200d0b0190b802007180c620340106130b0360140303d07c911a804c51070310340e0769500c998409881004404034052030610300480c1c8050103640ca5240e812000d01450a00e408a0a0b0036207030340341e0328800403000c26503142c07c14000e00507560707045d5a2007100d45e00f41c60310404004c100701c40070058000e044c0840c0d038000c18444c0700c49104480d46613081460303041042c2e0100e01c56120240900c42c905c0001910800 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 467675899 1250 467674649 467674667
    0x1003110a09030b1e0a0e0f030a181e090209033a0e0319140d022811060f0d02040311030d110a020d031205070c020406062309030c090106 60
    0x1185041e0072041c0c6038009182201c19135130703480102e4030400c0c0d030005680c00e889501210905625034100d61030f510113080024195030000980200090080c0003840036000030310b079100000c1c03960300c0c502d0000c0d1454550703500308032006009501c989500000c00030800d03541001152031a07014103404a41245001064440c0c0c1c039400e92468030346101c500c41800071b50b0300071001007020a902034080e003c5030700c00f0801c89403c10000c440c00c41d0369584100c44012080d008018049030142c16400418404504c1521007004024104488280010b5607001c03c0c0000e82c52005010315a4080d00c03900c0d01c81b100e00d108150a030082c5241c0308402440403d000060010f400c29140329a0302c01e900b0b071002d504441b141180c900d10b0340301c2c11001c06c0e808004408012309141400401c5a0f000380380014000000100380c005440081e10303c200040c3c520201041580f62900c240320040c03003a810443c1c181c01411501c100200385c1d24805888100e40401c05042d5074400f44405081d042d80140180b540b980c5900024100e2a0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 467677149 1250 467675899 467675903
    0x7080a11160c0b04030201090e040c030f05030904110408031207030b03150f1b030f04020d140c010e0102011b1404030203012909070507021e120a020112050601050301051003110a0903 80
    0x9030584009071054050f0229415290180d42d1003072041e04000c812051418050811600f00064420000c08100c8020164141030b108001456580700e940e410001651040d034403003600250104020012654000b00f218000c070ba050041051940d9a90402da00800401540300e4042c0103038a001a080308010b01d00b98402c81c4421180341d60781d2500300c01d40c0200c07101e000d20000710b96020400306070003100000e81903170720a10040c03503038080d14099a25100300344001c0e00103c050740c0c0701558002456030002811503040070f081c030080100080c00000e0341c0c00c035100ca00582c01448565034000961186142c1190043c54010f0000d00007440c3c140c0d0240c1f80740411021820314040c0c2d03100d200c0c8843c03400503207245c00b40d8065981e403420700c00c0ca030b001c1007440506800c80c8500d1480c50481407103191265124081044402005400f0070919800058000b0203c644030a002500d000d08101080ea00141582c2c1510001c0c0c0302c10b809519503130070650050402c0107508004010110f40c0e210b0391540450a882134034 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 467678399 1250 467677149 467677163
    0xf0420040611030313020108040813030b011701050c030105190b120612010603030801091a03010e06150306010e18160806061c170c010906110c07050a08030307080a1116 74
    0x4030b0026401500ca0105864030304010008100c1440036620501804c2c3c3c000c3c0c010520a4600701000244001000c66507000300c1da141000d400411008802ca8100f064130010a40248013914003040240d200b4401402401d2282c2c0b0641c00c1c0200e101e40c2101302002409203208007a5540301b40000510a90804443c01c0d4810701c06141c0d00d00070408180200c00c00c8a605032034986680e424054900f002c0d04103407080111070f21004104036003d83e024050301440801c042c0c0500583d040200c02062000c40500c00039010350b10402c0104481c0d0460088250301403000d0303000702c412a0f0340406080c107140014845182c03000c1401d802154407c804105240610380c2100e0580d500d40b12252088070701000200c0250081c03840701e00e80074032103940c0d5004001120314080005031405045d500c0d01c2c204c41001401c5814808041307a20054802c0c200600000b800046030703c100b00300d2404000d19600c0c44010310281c1048056030206d0100441c0703400c01d68000480200251b258a007413541d240e1072140e00c20043d0740724 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 467679649 1250 467678399 467678417
    0x120105120706020d121113090501050a030206191e020601060801060908060a0b03070503030c01020d0f02190c020a030b070804020a170a03270b0414060405010e0f04200406 75
    0xc00000c024080702c107241c014050b2221040c2094070aa0408040100c0c40d644441100250103035803c014030a501c441e0b000f01d1140c60400c0d903c3d00131120160460f80c024241d4041c1800944d070b41f64269801c03901c0e802401e81c1c1150a01c101251040c9840018900590107400c3c03030415075401141300c5043e0780d004d6541190503030742c1d00f01c1100c041c01c1910810304241c019001059130440c868200c0000c01101604517821a0780e0b0f100440d01d9a07000c5008910076075404902280110325600078200681d401780c4040d4100b2038880d0401e21004600c0322440d00340110000c04400b1502c80c00460340003590403000250852600600141480508036402c80c07068000c1240421140d08800000300d80c44d010788008e000451461f98140c6203c40140c1c072441c081070040c000c514800d00540c401002070600e80f101a91640e28000e040c2c1c050204942c0304510a1000340701c20302c042d076401500007102c507004232420301c1d140c545030000c20024062500c00000715006445038038200ca588000402c06c40c0c025940d04014 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 467680899 1250 467679649 467679679
    0x40b1b0c1804060b030a0c0f331809020d020d0e06010305120705120d1b03050402010212090616050c01021b13050414010c0f03050c18060d020f120105 66
    0x80c40030a107841554010003280c0801c40b0341e4001140604080d04507105603c294a925040c41c801e035101d9490b90f0030303550043c4420000c81218207850a42410030440c5000d20642e000344030014400074804225054180c51f2004003171411001c01001139010840d07941365400c0c1054082e40c80307401800d8055007040d8019060307240005031790341240c0c0c010028088144014421030502d922941c015501c030305c00c0007004485110508000c0002004440b40002d001c1501c5c0c42d01414059400b5001060601e01410480940d0b00482e02000500101e07400303913a540d0f801400074070300f40180c4e050030a14004160015040000004480005c030500741c003121030b401105c07034050310a1140801510380000c11002004030780611a001380d44c20a1142071104104900400d42c03034212904035106100183c0070031a08444942c03d4401c6541000081030218508000d040845000c0340381c52006501801c000146052480c01c00d40c140c41808485502842d900c0318810b0100494000038010031748100c250b02e40d1508 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 467682149 1250 467680899 467680909
    0x8010918020d03050c120c0a050c0a150f031b0f0306050409112b030e01081015180906060c06050f060102280215070c0801060506040515040b1b0c 64
    0x41400c1c0c0c000d10503989110181c0e400c03a429040107003a59645c0c89130f038003840080034110000e000d0038906000101125056400d00501c0c01074504036480c01041e41500600288145059810f00045241424080104940c130700310000c10822442e40346180f0b4200c005140319501c194910403401040e5401e005903030f200c600b040102c4502040c000c1642c5601d035501a110f0408803c805040403440d2081030201e822080b020324104100300c1c00314009210a0018401d960b00b2081c20350304200b003080c0500f000c40c01c060400340381700e00040518082c0015580310100301c0641280340806002040818070466135949005061000300c103204403041d0313060400050f039146052001c070f4460f50b0160300510a05d413103030424072642c2d04192940c494460000880c00096101d040c4200300321856607061544d5200941014403e07101c0e150800e03403007641854003c110303130341d1044155010b44070300b19402849500c4510b80c010711031013568046200e442e404201c075070440c0c40144204071420f14000564a1441106e41040 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 467683399 1250 467682149 467682191
    0x120a020c210a060906090f12030e0102090f0d02031e030408011406030a021528030b0d05030a1d0405010b0a080a060f1a093006160503100306020406080109 68
    0x488182d000c01c121401184441d04180d00c418014400001c00071004e0701c5103801418540d000fa144005822079403030b281c50380b40c4140d41500c03103000d00071030600c00c0410000b10360f400d007561068441c0910410080079540c1c10301c2001c030030308044280c9542105220301005e49a801910480300a540780c166102c08044020701c803103201e000000d01034003840c1015403c1009110380d4514400941c08140700841000c1c00003d141103032407110641400b0b41c0070420f80020240c0d1620700d08240594130000e0500300140002040d614500803e0621a99400c200c02040c04a081c8d0403400940c0035051000008900314100001e05264074103580d0f4a40540c1c030041c400c0103a03020f074841c05403500c492010800071800390792610b400703040008070614640070891000030501d52212902e6101d025400040b2038150044007410920080c00e10f02420440c9403620390540b075264103851000c18072100000080c04501781e8048040650ba00403070840d12641c03100001803103000c0c24050b4900c4d41c0d01d01541d8468804d4807000b18 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 467684649 1250 467683399 467683459
    0x1020c01021b12070b0c0102090901091404020603060111070e060414010803180a080d08010806070f0e100c02060307030219050403050c0f04020d1103040c0b120a0509120a020c 77
    0x40088a00c02d00140f00000303910f0085140b60380540301020944c41841e4004145a03036205002503160f2803480d003040380c0f036201a400034104a02c0e06030621800d83c12043e801c0d50103a0111407860310f070754403840183d441c007521004403016401600008240300ea2039005041c0034280c01e0b41c04020001f0b1280e0015810803003800b5501c642d50090210071003c10441c41c0c1111034420150980001940d00c0c1030107480c0002d1020008082074403900140310b5801c040280d140d00005500e004d812000070f009000d4120301c080011103001d010710a4481100902841c0c00111956001e080e490b80c1e45448032004009401464103842d556040c40950b0701561f100f10f0075602600e4018000e851401080b00c100022903000c002c0107500b098003406040134020192180301103101e41c501c0c030a583c81c5803501d4403040d42c1e4000d4009401810060181c4c1aa01000c00030706030780308520080015603a180c2c404841d140c1000005620240740340040c9800445601158240d0258800c1d00d25949809400030000c81c420004205 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 467685899 1250 467684649 467684683
    0xc050c060c0702012c030c040b010e0d0218010305060403020c0d0320250602010f050c04030b0711030a030b120d05031b130303020309100302120613020d14010501020c0102 75
    0x1150848101d6070042000e0791050402040d613a1600c0280714140403407041c0507001d150320310500345c0c0c5400c0600100341101c10840b0200f18074440580068840504100d43e21b0003604031411420864031001040328809034055a188140d44e980c0c070740700b5564101120100c0041c000c0384d224007918100181040100c0754192201100303050702e9403051100380c1d00f00031084014400c8141407000e8181c1d5043c1120b0207003030300348003901290400034041e00707403020850581c070030030301c0c240c00c00859060090607641625440305031100a41c031303109002c850208200c40e00142c5404001034800c00290598400300803114142e03031200c58101c035120116180c000e4030022001140c5c0805c0090150741e51803401003000101001d405040c0054a0811006001690801c4015a0000503464298902201c01c10040042d52805601d04052071554080d0007002501c454002d4105d110506230b01c500a4044d80e00c0280031050810132011840c03554141c0920a00c00c443c054010708554494552022619000304030300f03581 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 467687149 1250 467685899 467685901
    0xa1209090b2110060f09270305090a0f090b041b021b0a080f0f01061a16031713030311071a220302070609060e0102060a09060b1804060c050c06 63
    0x14028a500c0e5040c0015546002d42502c800283c0042e1003444050300f6400d900e4100181001e00000441d40c103202e054401c480d03030000c103404a107483c143e2143c000b0ba00d03180c6942c9a24506020458103003a07a040030b400c8003014030700401d50144a0b4044900b8036401c035418883c54840520350210000c0c02c4031940c0040c2c00600d41901c10400c1018020510040949850f0300e140d07850078098205001744032003410642182d00e002007042d609000f8440074180000e581c01c4c2201c5442038000480c07051b200c618840406020142c828140142c0801c045103044d4461960303e4039011080c2c003c010303210401140428a050000e030707a260820015036603035a500040c0e1051040c41e00c03105155021000b0400c1001085000d46120a1064039030340905603803203030700203002842c103002000d04009500d801400c01c0010407522410107030390003d1001c0e0040c549000c0081d4101d10381c100040607158001e40c440d040f00380003150405840741001054403460280d041040860440c1008540c0781c0b10382d03a00c00b070b00742c2d00000c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 467688399 1250 467687149 467687179
    0xc0f02030313020a1d2a12100902031617150d0f050d021c0507020a060503070e04061e1403060402060d0b04050f0403080a052401110a1209090b 63
    0x1040d103103803e000078419a07480342c4d6505149040d88a0b0314030310945400782401c0c054905500c00030440c104460030440c03000001c22100b595024040c002021140705040c0010409058002e00080080c0200700c10540d5245400345600c807096003d4030030800000c0400c205504201c2035100d9040c00750744041408a1001e541c2d03400c11000800b10f11040e01d05804818076480018000c002020f015201038003e0320f8400540810754140309030b210300000521404020210060b52090340740400e5585908006849481380d24007200c4845a9810f00d5421a1400380c0200b845019211000c60142e0035540302c3d6812500c035a15010040300040860b80c160f4007010100c2c0c01450084050b00c0141e400710b1000403100f50080024003a40e07410f845210301d0011880a01c0305041e4032104d4540e00c003c20317503024005d904241c0281c0d0000f17070205410704c502c040c0a80b403c1c1020b0b0b00c030b0300040c040501e441d0100e401609507810080040c036061000c5001058050800080c840128010700c0d5210f48018121400c3c844e440e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 467689649 1250 467688399 467688421
    0xe070c060213332309100c020907020d08040204050a0b15180303040803090d1505040f110d0317070e0306091006120b0a022b0506030f07083a020c01030c0f020303 71
    0x404d0156142c900034400d40d260b42d191402036616030011942c81c10010b03034150062190f043d2014000c1801c540140102c030100c0c603008a8940e4005038103807000102c1d50386504600c00101540501254054000042003034012004d0000d04807101d040d03180f020000f5580b004041e0349100740d01c075606054000384028040b520380843c4040400e4025090380c0c5a0139181c2e030002c0b0413101c08403001c41c0c444011a80b0002402542e8880c0d41c0000c1d0203880960001106446c09401d01c0907002e1804100d40c28880065a854400c0c80d20f1500038030050f00300c03001030074002c8103141c0b038458424055920078039100340021a07440c6a035114180f10b81040905550303456070680d01c8003941c007134690a408840e03c0d11a181904034041d0384114064103001c800a05400d082003054107108980c0c507103140c554001c0c5400d004e480008210541c028001602c8041130309605404203800310500a0702c0765280c0d061480ca1031166802003902541400241c0c0c0400041c941040d00f601d01c03c00f82c143c50301c0140d20900003d0507103041 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 467690899 1250 467689649 467689697
    0x807030210030b060a051306033e0c100e0705010c0620070f0c05010e15090415080d0807030603030509040f0b0301051e09070e070c06021333 62
    0x401e14000ca03c2040070004510641e22a40840000801c00070f44240d14840c45070203c0c01911031803600744000c01e45107100d50311008240c42c00546002e100741c400c4011000d04403415a2902d4400405030700c0d01e402000d0162104200d100c4004054105000210340d00c0f004103800083d03e205031292802120182c80c0d4000400c0112810f19040000f8070304e403946008810b01401034a07220b68044104511b0900d4000392002c8264051410702102060803100d5940d0720643c00720003041401c0d00c50b01d03042004000350141c0800d440d8032180c0504284046282d00012851a12040345501c50400a86a03100110308503032584c407002c0d000410512a03403400340f0385500000c1e1b51040300d12021984889a20000b401c5070416248840820104d4000c80090740880b8245c5500034142c40140141c6450b108486222180050441c810481d002281c20200300b40f80d41039868401408000c00c010b95151501d00040d0746d24034103010b480a1003d0320210400a80c620110017019240e541c550054100303940c41170300c0206c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 467692149 1250 467690899 467690929
    0x3060106140a1b0c03030e0306220807020603010306060e0c16030813060c02030301050a0501111527030d0f020a140901030f0e03030610050406021506040914010b0306090708070302 79
    0x42000c0c0d5001c04030003103040f140c1030a01035480d0b403a41900d189000703000c07500300074a00c5000f0342100082200003105141c66442c0d81c1c100c1c0301c2039111141b132031415071460305c22100025846480480040180702032980800c080d00c0c00100043c003661201303030f04c6a110340034050b030346455400400003c4c3d000901c46c0c404241c001703020010400e00d00e81d0702d42d581425111604103540042e40040010481454990060030050000382404641029200302c200d454a58409552031007171038840c00f10380d2901416941c180c0114040c044d042000c005440b44503104d0303028451420640d820a05d15003000082c0340300702c0c1c1c2074800702c0d01d459500c1d40380302034580126000320380e0f25410b16950790155030b03d03d10740e401243c050a8403038010716640c0c60310a080010209240c11500c080040600040c00a0303600001c4002481c04014562486995900c0005015001500d0002e0041204020340c480360101500000301282046003585c41c2c0c2c1d542d9441150b95822288680d80040c0e001c0340c0b0810144c2001030303458003520 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 467693399 1250 467692149 467692157
    0x5090708010b04230303070f021f050d111b1b040e03090d061e0b0910031707020609041103070831061503080703140f1b071a0705010b03060106140a 65
    0x140311480001d00351f0304610800c0e60355402100d251000c5281c69911140402200c102d0418190380c1020020902e000f86600700003800d41d5050009400c06d0200180c500d00c00c49110940501c21007040c102e40c54032401c0241720007407240c001d2030000600d070902031020880c1d41c1400031030525058004014042030b4000c03050742e8081e603c50319069105d50002803000d10307078141500842c0c2902c0b05401e0200b0504018454022034026403000d04c001001c000190791940b02111415444104c507000040881c403442c010310380e00a00d090310032615130244d00003452141c000c0e611000d1903640c0e01c0043c20000c984801c03040640c2101c01138401e1051804180b1908407502540380059a0b40094141070601980750300155209200460078004041e4030400c190740031404000f549040c6402c8003040442d83c082d18002c1303502a400003c0781e0180031420010a0010300c803003040110040c5d030048503001254841101035600354206800542d042c1400181103040f14207640d80c3e44001070005146540340d400584a604c108 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 467694649 1250 467693399 467693459
    0x130b130204020f130b0703020309190504151401020111030714070b040302150a060e04030507060e2d010207020a0b09030703050706080703062c0907050409080405090708010b04 77
    0xd41c545202070580700d03900a094956a0807000640320b19080700340c0c0b000d105e0035004c0007424006030340803090300c01510040e209118070007076a0302114001040b5030800b54110f442c01d04620b070701d008100441c07012107490103111403005003560012400d07203c4400c5402508001003003c240114803031420f0380120340c400a0441e0601003180da86d00d12001d401d0320103034016440f051130880c02d5425207600607049951b25a0400c042e61405d0307d20102c010300244044e06204001c10080c0501c901c90700021a12246581900d102540010f0384964003a903542e45104d80e4601c200780b840f00314030148200c0c9ca0703054000b085078848626000d014092036009541c030740c1e054012012b0000010f80308200e02030180c03640742c942804524000e40700a0448d200e030360041940790704915080c581c5100d020f0130074220b5400307007441c808581d50f02d03a03400b41f40066951000b80c100f0301e8803c216080c098100064003e03910111280b00e02900d1784201210b181e5028056415452002c201c20081040c200340811202000440c0d02080c0e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 467695899 1250 467694649 467694653
    0x628020a06090606090b190302060a0c0506131202120315040b0d0507030615060c03030e160b03010305063d05131509230402030a0203070b04150503130b13 68
    0x2550b4150004494054840e007003030004648601810240c3e2905545c4c0b180351208411440aa41d43d05100103809840c0025103001002c1c412401520b8003500b0408440c0c0c3c6081c00d245445c3da400c00300c8010b481040e030441488130750b18804152a05003920880449095841d1805410700344582195142e40c4140e417400300400d143c80310014031111602490242101c1e078030b035060440c1900c24446a454483d03218590034041150000c160080564040c0b400054158140d4607643c60300c1c0411408100582c0d0744000055041c60460086050b2485071041d207480f61a0f00088680500c0010f0401e8040b4111404030b02c0c4444980311420b004e189807440319924582d40b0000300d601010b500024400440d00c43d02c552031050141082c6074001c6c0010001080225600f00c070100c0d442c0d152841e082c0000105101180640d43d04125180400d40c000713064035105d507030341c04003500184e0051081f451143c0d0b00d070003a030a1050149099a20454541c01c0c18840d080081c0d44a0008420007009410140606404980 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 467697149 1250 467695899 467695901
    0x40b030a060e100b0102030421030e12010c110105100e070201060308030f090d080702060c07080f0406030b1201053d090e010b0d1104021c0e060f060628020a06 70
    0x608000c004060f081090081e04031105659840d41824150342c0200010015041e0441c904c50b071a800b42d116040c8036100d42e1808460700703002058a00e6003c40600d01030404401d06512911010041d03440b07412259040305885803e0702c03022201007240c00c0400c8420003060740701842c20f81d80310019100001c1c100762030303a48600301c90f0400e555061070042200200130401c1740400c0004040b082d0381c1480e400501d0300c803000035540c1e28024460b582d420404a900da0400030f140c020354001d41040e00c4126111900e0b03042c02801441200c12980c42544020803980500c60180305032030041c0407d07039144040810700100030b600f0001c2d582401656070903d030b4092492a0742031005070083c2070804000b04092460200c40c40c01d640320001c1d001c2c805c0301c14030105000110404d46101e42c10505540150712401c0701e20003419041070040c00803a66505100010701001030119155104414048112071a511060103001e56030282492210142c107074500c4000d002e491420405a44005510407510388120b2680c81034 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 467698399 1250 467697149 467697161
    0xb06041e0207051f020310051c02040608060a05010b07030e0d1104051503100b030c0d08040806040305030915130320030f040e060105030402010c1704030c0b0d06060f020a02040b030a06 81
    0x5191a000000c0c0740c0d07480d003403195a40f1140082c2803000d60035810f00071f0304101510700500c6184d20580388607120007030f0039540031101c001e59074000303004210840d83c8643c3c65495101c00c80b01c140180e46054000304c2c1459081017900c00f51a09030b55011220030710742080c009990f000c0801520500309481600e980c075a5030f40590b500c0307142e080c801c402e00f81090000703140c6440241c0d042460804d00b001b904141903100002d200b90007600071034040c011481d2905180c1c246204907000746a40b400341c50200300605803c2001180600c5c0c9940c2280c055500000e140d1258110994841c843e034001d5042c80700c0072a100c0c0304079100700403820034070f110f0761914207100a00e164065544000c41903000728041218861450003e940840c080c284103103540340030380c0001c1000d803901000a100550441c1c510000c030030b050043d203015580c080c2d8031414040d1030b10b00445164000c0c1d100e0354803541c2409004a0141e200c2c202c456007665080c2c00902c40581c00781e0802004d040389181c026050311541d01181c1c0407950780d000329 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 467699649 1250 467698399 467698403
    0x13110d03020a0203100605010c03080640090f1b0e1e0a050f0402220c11010b01030c090510020a0f03030e0d0807050d02090f0a060513050405040b06041e0207 69
    0x51040b040b251061500313009502140103469498440304000990300450151510344d03040c5085503041eaa01d000141045414002007424610000c28078101280102081024904900c111000310001d146905041d5039006800078540380c050020400000c07940b115000107601000070701010320b034640c405039070019000c43c0c0b0341c1d005120310f2890041d0410044805508140003100500c910b00c1c0408003040641070107080240034100c0c00c024035044040031485a44400c8010fa4103000f0300041060040c0603034500e10009034503500c0d103403041803150f01070b10940d82e2503034180d121098141d00d0300040000c3c100440902c0310650150319071400001d8407400345689550301c0b0792400200c0340c1e1200f10007450415040300050a0024420030310102c141c00c00706440c003100d0202030140ea185840c0780454111410300f12956000056500c0c0451066000000b43c10551004d100903c0c007541d590040100f038481c151001f824810900002c1036a6080640082c2071043c049059001482441003014049902c04601 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 467700899 1250 467699649 467699653
    0xf020c220b040e06150a080111031e190c140d06080c01020f2802100206040b0703090f0206030c0405180a0b120d0806120709240e13110d0302 62
    0x64803014286032103200700488055804101c40f105414116a44001c00f51103c507030000640c00900e400d030385080e459000750000c44024051410090580100d5801c01c0e507494034050f0321181d0410300700c208402c109200d4003409104401d404520441c0d03c00501c104088642044501103001c1c03010700b8020020000c44040510004800385041070050512180688141c110740144641c005207840c000361480b040c090422682500d03080000b0710315a10714070000000d4000601c51105080d5507004551a841a40100340850056465090403801c0702e9540600138003000a07542c0030405424044041c580c407810f062802d61816480740c0c009455034480c80840d03070514031400c0c00c20a850000380107044c44031a0623140c2d03001e0000310311016a19016401020345c204102000091034a0f038031214040640c100c151300344d0b0740040c1c40e582c1000103803035401c00140e548544102414251407a0044142c00c80300c00c1c4030307010815201c90790343c44102c0d6000e8006039150305100700000744960310507130030780d98091003500 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 467702149 1250 467700899 467700949
    0x218180f0601051503040803011a09090103050f1c02070e10080601080d020708030a0507062307050703020c06030c2a010c0f02010f09050d0f1202040e0f0c03040804060f020c 76
    0x70030441d03c0341e07130070424160380c0b60217000303020024120100b42ca05403034141c5212040700030800082c04640c042c003421141e03c000d0305000007043c014089908031101509006a4500c004a94015080c1d10202e40810006910208041201071140d885403a00040c11101041c00282d031260f07a02e25180c421b8000030b8040e000390051440d1207130100124401031402001079420f01c01c1c12240a011400390311000741c80a900c42181d8602169002003680c14409442105c8802e8200a072000340b8075040285c0887c0903128650f060000303880c0c00d0054070701c551100a00245006400103030750000e140e0343c0d2161240b0751007a901c1d2900122080c090704540b2040c139601ca42c118aa0110000c0c2500c00c0250010611490700a246001c5003001c103201108450500740300c01d8445c184c1208507100d000c0c07120500d080c248081008580c103464051800d000d10f28216062059403607600f0f41540751303c001da40041000e0810401000228040c01c89000100401e005641d01c50103880b000c24410303041c02e05a0a282080c4070 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 467703399 1250 467702149 467702159
    0x607090b090f040c022d0d030e15070819050c1801020703140105070f03094205010303030c05030705041a16030e0103051302150f0408070305030c0c0103090218180f0601 74
    0x46c45800180f8900c0c0d004d0035180107140d00241c4500700c02024204042d15252104203c85040004580c90540404203003414901084020454030f002c2c2c40f050b03d0503e03882004c1400861794012507006a640503501458488031107407500240e40038205c400c2c15406202c1c40000400c203254400d0042650480000c6028501100c0040410b19040d0070076040c0b52510401d540441c03401610b4000c00419064940d5103c1042c004010306880c20660170840c00054107500850074466800c00340c1202c0c8a0385040c010f242d880c96007960302e400101d41c0704001134002e2104005c2500190900505a1418a6000e103021202d06140015640d03032001540458420038948001c1c2d61f1610807554084060545005034180320742c001454040d20641d0252101c0300030640c030883c1c40c5400215001040780e0012208495580c0c03070110784a410929081d00c1a01400ca070034071055000740100e403110342e03008041d0107510651820110600700003070301c0c15682c00d81507419401481010004a0724220441000f80180d40c540 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 467704649 1250 467703399 467703433
    0x6090d02030f010915050403211e0f050627070c0605092a1509060c160e060f090403030507030e0d1107051917010e06270607090b090f040c02 62
    0x4440c001d02a17a01d400100400f280c0d101c400c000100c3e041001506074561010003110191205034490010078620b01820803c01c3c1e0380b540b0201d0f6a6034500b5040c40f0341c5e41c0320002c20040c1c040c0c1c1d50881c10002e9400c00c0702941c2044410f052a485580b41c181648100166100c0208031881110f52070744907030248118040c0100d041e40601d00c800790000c401683d60500ca400728030103100e0907001150700c100c00306403043c03103a403108180d9019a0404045442032070100c1900305010741c0c184281001c40d00d210f40407605505143c48590100d003009841c40b000354840e56030407001018010004c0c0101551103400a0a0040910051910b54403545d501d841664040c842d0a0a02100358402c511030400b542031361100728036481d0814100c0c0c0700c1c40040008034921400050160400703801c65041030107517000b00200c5010b0b00c6a034410004001604d00c0f00700c1c0d840d5001e2503a4040a5401d84049401c107041007082d2844407004000d010300190902140e070091401040964140e14100005130704041c0c5401707140414 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 467705899 1250 467704649 467704673
    0x5060306060406031106090409021816030c05042705041b0b030f1f091b03060506120610030e0102040e1b041a0706060b19030c0905090606090d02030f0109 68
    0x104030303010440c1d0f07880e60340e840300801d000300e004900402d40803d0750126583c0b550b0140508030b40190000c5049440c50304020070444007141c0c4080000070380700341002d550388644200c0c11038600d50f803170b414903150030003007004035207011400ca001c582101c03d5041220f000d20750280c81c3c0513510510384608041c2e034020943c4401019a00030b4114400700380704014048030f01d8000160006a14021000300d80480c1d020007100c050182c11100b03405050860b084481052000c43c01ea00441654080010740e07100e07020480c2921800c0305a540c0d069603039000c80e200c0d1401188000741800503007400038410140c403c60b5400e98129910800c1062500300410000014070b02d0301c3c2c0d140f5811251101d1500c3d0500c03013074a000390280c0e84241560341c40464200100409680058080d008040240303407154071044c00707010f000340007101410010741400c0314035903c14001e40200c0196034005041080325542c007814094076401201c0000c0d4440c80c020410710140c0c03014401c100ca1000034070f001041d2040142000b180c0c1c103035 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 467707149 1250 467705899 467705911
    0x6030a030c120e060a0e1c0203100b041e02040503120f030c0708090d110a151d0f0d030504060e090f0403030513020a120303060f06050406050f071505060306 69
    0x18006000010758050140d46101d9400038020301c1001d42503004075010008050202e40010b00043e0f000361040d0000350740c08629400f15088441000d034441c43c00b0990244020094059001a04c804600c0300c0d03d4100c80c0c1040300281c80010596024005440079861254110300801e40c006418010341c1400d0001000b20003100450b107203404102c200400c0c0b01c2c0720041c45441b15510100b8108100941d0f482101d416010040c0300002c035061605080c103284c8550001907210f00c02035100002c5d000500c4251051420454032003058075a507aa0100c4c900400d92035689611a00f000c00c0359a89550301801202418020343e01c0b243c0300c80c20060007400d010b441c15555445441da98007004422a50041da0a03400703a4189804034035500ea000800036218100540298000c040c0c00c00401d401d2201401055140d00968050204941e04d50542008220a005080003d8010801840142d00500c024040c180c0b40c120f0340d03460032280d9240c15517418030700311a1003012520b80051045c1454200b004c3d41d0041 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 467708399 1250 467707149 467707153
    0xc021f0e030303070e0105030406230610180501110c040609050919050304060309081b01200412080c10290603070206040b09070e0a0506030d1107050402030406020f07030f03050603 79
    0x105140c3d0303025243d50210841710303040040000014041110036042014440d200b00c500c141d18448035426009259001c0714500d0040c9060514850094462485c800f0b099000d40740c511892810710380111841c0604252000c290709c6040b100c42010f031564414200181a240c01c001002d003000c0c2c203450b04210550340980007200101d01094081240807003140d044a041d03090004486020780790048050049105001000d0403034807000b4006501034102e428104045880c04820106140c2c80391030f6802036004510868408112960005000c0b200400710152010101c5040d03122118810003038841c507601c0f17a03410480010214121807000d1b2005403200703400302c484600b03501d0020b50003555440002d2019100e201d00e000801c00032030040c80b489001c0d100f0f1007a407200c03915000c151580075100030781e015070017407040c2c9050070003080c0720301a5078102e02d242c0c3d0080c0c500c5510748010880a50000391084e00c81a9007084581c000b10759550080610303174801d4030386d4840c0c00b51414018044400c0204024025 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 467709649 1250 467708399 467708401
    0x6030307021503090d180e190207030206040201180e0408030c0702090901090b0109020a0203091012111b0303060a061101060e190609060f180f021b01060510120c0c021f0e030303 78
    0x52400c800121080c4c403c00347c0c2508159031526131030031024107081d81180300c2c07507c0001d402e0306156001c115079110314000e8a5907401c4044829070880c842c1014460003069419100c045030010301078000544d0044154880c56081c00c246800007401508180d410803500d0f1342da4420030301001041c0d900c143c018070001d2811070070000d4a1401035228442c2044040c4100f003901d280564042c0101301c941d00500b4074481c2004400316251140001e42c5c404a0b9517907610b641ca0481202500000084034419000a0300e4148034910381a0300b5500d84140715104e100c1c80d500d0321000310302c0c100c420302810b100380c0c400303c6610b014400880c030f10301c2164487d40104075011b003000780c1031040c0c5100b82c0b4410215a001f98254824198030070441008010392a05c48500c6400010040140070b1921241e4128010417402007211a03600c50400c1841910b01e141140030807916184080582174551000410240b1801c1c8040c0c00406030b400601e4024004050420840000c443c02c2d1030b09a000b0b81224181e80194003c43c51 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 467710899 1250 467709649 467709677
    0x1c06091b09140609161404060f03110f12040804090507050405041407020628050c0301052701120f060e01020307030f061202060309151009050a200306030307021503090d 74
    0x3003e1008001c40c1807071012001c85c90702c1324818205098000d65103441c07a03894030388a110080000d280c0f2005000084c0c2070825031000b5a4a80301218040f1103903d585e1454014005140110b13410000c1003a00e002d24140000104c40c030351400303550f01c2010b8030b0369401d80c0d035070612007000b04849481d003144075900c5c284020010300c1c0380c00003085c64004865171072401403816441821400da007181c02c1420005401d002c144003420980b41c0c041d5069580485081a20710300e035204810610360311040400c1d6284d0b01b44010000d58003000c401e8800b20f805020200323a203140030740340e840603a425115545841ea50000030050703070701d40c544100f0b01d02840d01030041c40224a800074401e402003020a001c0e100c0d04000011992096007004820301d101c01030781203220701d464005440381c1031140c01d01c1140091f40c00c00e0000b90a2034014400c1410000340f01d840701001c1001e8500241040e0002022030b50544000c010480c00350761150126515030300c801c402c29690b8504880c001e401d01c07521301035460a0200300d102c8018 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 467712149 1250 467710899 467710909
    0x209030c0402250b0603120705100c030e161e051e06130e100e0106020a0609060e1515060903150601020703080a050c0f0c1c06091b091406 61
    0x61841412100036032203a9112000e283c040300030a01c0e0700c00c062600c100040410011807540b5106070341c120182d0320918a5218000c149100b0110020165000308018112550560b40241e14226040c078000404040c00b5149a2510404401d001402c902c9900100604040c02516070600180700d83c101594a29040109451201030203200e815020040740d90941070f20f465098462001446500c2c80d4000e035a060f01d481010002d455000910400d4800440e03c078614500c002d048030300710360042c00000c1458650200404407528200c071100d4070f81044c0c50311600200448018400d0307442000c2c07a6400c142d0000b42240e480040d80d41d01a54040c010041c1d15980030a03030651000420050311540d40d5078600407400d0101541005001c2c03038012801410407640100504407003100d20080741c2c02450401c01340381d80c44000704000d5074010a218840040c1032400d004d4007012522422003c201841a5680ca50014411498600f200b00000b00104525099401148400c130014508070845040c9540426 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 467713399 1250 467712149 467712163
    0x30f0c040612020319020a0c1b0518060d0b070306050a05030106030b0f0a0905030a030e010b010905090601030f0b030303090f151b03130204140a110c03220f140a0603020903 76
    0x10302c590100009000b0058604c4c03548650440c0c0c0307011569142c0034400a02103410707000c4140c5140784002d24a030914901d00c4040300070b45500030006600d9514003461420304c041c00130720302900061807400e0400050001e841541c02044143c401252840c280b4090048052442c0d1000b031280c1e0604400300041040613044a41140c04481407100956822103030402078200800002e0407444001b407038031407581c0d05134099400320000600078840c040b1a90011650b410b014040c490340b2600c814045141c543c041da000100f0405a49004a0848010700c00a411500101c8030101d05400c484070744000300c00180144514000c18040541792400c1c139545040041440078400d501620000020074003019520a406040541c001d00c00c2c840d10062900b00000d01405450000103c2d003800d4503840c0c0c00406009880c00600008015820144421880f100050fa01480d00105182d4990041010034650300200050240d1a002ca04200104030031301019100c02d5000f10101841804030001aa9000c660301e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 467714649 1250 467713399 467713427
    0x1e0b0d05060604030807320714041503260c100f060803030a090c061b060b010c170703022a100e12010e06090a120c03020a12020102030f0c0406 63
    0x946590749000700e0000d1080d0380000e800b109001c50b09208000b010100d090b010024031055a2500b01c1240310301c601c000103d14100d255422514040c801d0403407400001200d210010404920a080002054205440ca07017040e640d008940d0066040c0e200b90300c213170030b2a1065845003e403501c01c41c001101c1d21410110043c6050513103070003180300280c0d07003500840068107507130003540d5417410110070300801080c411000715010032110500183c01d038060703804100c4020304402103c01000865a0713690003005040c07060350500400900c0d440214480d40040c02450f0148860a40d0307076649410f000c1c1c42c08000c042441040e504141c1c1080ca411940c03108001501010340390300c1d00d07200a564040c0c4001d030018012540010107142402303010001500900c41c41d001c4d01060b0b0f002920340e210305548030007500e10094180e01352941d402140603c920742e094a0f0303501905c1507900d040c08550303407220038802000c481c50050303401200344542200f034283c1e50b076040415410018a014a811005464246400c1c01 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 467715899 1250 467714649 467714651
    0x308011503020d0c0c050f0c030c0603190e0a0510330506180406050406030c030f0614100e06030d1e0e130e0d050702130c020f010501030c1e0b0d 64
    0x303a40c0c00ca000b90191400c0e0b1440007428403280a00c00300040400b1000ea0090b00e0740d20580003c0c440804020590702a541005409042200200024450140d01c0135202c01c00c400e02c001020720250a0f507100d803065840081000c2c003a03809660604615141c0d1007600440e0143c50315161641c14507490065840d5a00840801100405c2040d2091120f400a41c0490340004001848401005044040e1150500100c0d01007241c681c03150103000c11145a4000201050080758092000c50310701820b45141d41d100350f401154943c00c401c07101e040600f050701c01e020070301c121340c60a0000040180c50b01e0350101040d401080403c3c14204000c0800504014488944941c0007500251912a180c810302d00c100142084083d86150308121b4028008d505220741c240c02000d14001d1718510a4088425058004000418001848108030002c03d400c0960300198030800d10780703180014003801010300070b601800c0382c41345003850204600808103441a0b485d510010a0740140069440e55081d10071070407130000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 467717149 1250 467715899 467715929
    0xe1f050702120f06091f050606040501051e120105040b01020a0f110301060b1216080c1207051b060402040f0207230a0c2d030201171f080a0b0c07030801 67
    0x1081d041c00031920950a80d0701500d010030aa9440000b11078448031100400f40c8644590406c002040741c0c401e07240c0a50261040104001d550301c43d002600a40220403138416242c0084030411442d82d100d4030004041d034182d007004008a103090312404281490a0003d801000a81c2c3d4038100980540c1c54020140e1440300b10250007902d013544840c002d02403411582daa2400c41c4c1400ca12026030460310700b219140ca00c194921117902c1440c0050041a5500d51181800e15000a41d500104010643c0d4200034040c00111000480c0c64415004140007401803c01810540140800c2c6d4411103943c0081a00402c209000071340480d82001c42180c14900003211410703440106400d02c414200003500b00100e1030310100f078505802c02e0000d05900c40c066000b8030a9000c2011201c460014400070b03002c1424890b100c01c3c02508404a664060204200745051000000e601000f80055420003103e650001c0849820008003440c4240c020480542c0c05080294941c0e00070854001401042060142c4103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 467718399 1250 467717149 467717179
    0x4050c0f030d18090c0e24120406150312140a120b0303090603180d0903080f1b070902070b010b12060d151a0102100c0e0105180d030e1f050702 63
    0x68144000b92803492014028217201c0c1c0c0000300050726145089206410890032515003251901507841200c101c2d00e40381d4200204502c0b201400c11000f0030581e60603844032013601200148031240f002641c803a64003210300c0c4d18001c800801a03001d0303609160b0800001c0007a603a2058002185884d2240b803d000496003008443c00319045003d1105169040203020013401004800b00401f808422260700480b60075032400700341118000010310020f410884108044080647c1c03810041c01c9507074803001e0030f1110050303814810385840070f40d91007000c143c1e5003c40c2c0d031030030481c03044a294014180400024106803250358014401040585464440d1202c180568200310240c18003d14525250200b000810341c5200c0303003641c0b41c000840c0c0314018012001110100e5101b4468000051100d41c0c8030058620322000554030742e44160f031703041307190951139030094995030b203500900b9285031181e660404139200740b40c140100c100c84128202d40d10140410090203640d0f2100603100c12640448681c00442c69030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 467719649 1250 467718399 467718437
    0xd02030c090c0c1c0e0f0d0b0708013303330603060510020a060507020f2508071809020607080a0804120207261e010504050c0f030d 58
    0xe46a5180c100394044100091455a04040c110030200102a01c00700071801941035102d03130200c41c040000c62800075040646080c1a000b5040485002c2d0100040e4451503c8100d1500821070f0b0547c00508000014402d888800d200c441c3c14030808030340307420038102c006036000140c2c1c14009043d042695500d00041c012000c84001800a0368841425507822408203070080c03035007046e00554010a003801070010310303400c203d0741400d8107006583c00350211354119500c0c0c2001c0e060260210381184201c04443c5810f5a080c400009420403100c0c2003008828419104a0345650f41e5000050b242c2140c0d904000c10450f41615001c2e4078040031000540300d8084c030005005011ba104050f140c4207002c20340e85140c0c2e030000c4a840c00b441c01409003440f41741c1504070499842c8142e01854091300b040c0c45031024140440c56201a503591414181d0b14031400d03c540c0484002602d000b0100715a45510512090003014010ba2896107020795031402412100c00c0403c0ea02c1c0a050142000c001074070301181c8900b440 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 467720899 1250 467719649 467719663
    0x150c05040b0705030d18210207090c030b040e0a020625140c21070e0a0207060c170f04030509010810090203010920040303080f13120f02061b03060d0203 67
    0x5010303035168440c082c03420065a40d4110050f804072003490a420a00040d4888101007a8503074804548407c01d030120841d01800f48a02c0000e6003940304060340032485417618000e030000c4c3c1c2840c0c4d40008031581d08000300001d584117610706583d80d4100800c0b2401584801c402c59400c0052811941c0c045106e083d040301322110200307405005400d4004c18000a40d01c08180400502422a251a40c8a880001c0101d89100c1e15601640302c0c0e10410080154100100500c0ea000803c20700050610800340c0350300098410510b0007000103a052500400500c82144201d070300845214907629040c9019030b0040d0140c0314001c4064103100e40c0744005102020685050409007684000075910ba5075101c2242d80984000c4020380300036091012015186c504100545084903050343d607501607521665078520340c840014004070340c1c0f08400e03810341e00464000b83c1c01040b445c2a50742e50500141c04c0388070007418100040d2a803440c010301141c022501415507426290081000c940c0c41a20500c83d01c0041c2c60101c13 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 467722149 1250 467720899 467720909
    0x18040f08070305032710150902040801060e0106020c1809031c0f0e0c2404030507270203040309030b0a020c0609070305120a0903111507050a0201120603150c0504 71
    0x30004161041540c060302a40c0513240924214000d14420168152014455507810682d94011058185c1c003004a40010f1104450144036245158407521101d090f40c0c0603400c00e4641344c0d140c0748100f110581140d40c0340e00416440c405091806a00c00009030b480200000044040d103400c400300e0310310041442151034040350040c0ca8141242d99002850150407011400401a40b0b40301000481d51004295030614100040c01641030280505820404254270101b00b0174401c010320006c000201c0400000c400341468009040c803140d0f596150b048009041c01d400d40d1303000e005000303010010350842e107114240c075480120305049580b90003c1c2002402104030038a02881a4018040c040101280410a40303003e10142c0f82c0400c1c10441010551143c80a140700260312020100041403d44a104058a10003002c0c0c201000482498247c1600003660903109508900940d1303003150780000003000c0c611452101070000c2072541e218070070306000140c0d155045644494445190921031000c41e00a82 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 467723399 1250 467722149 467722163
    0xd09060b06070c05030118050304151407080c0606011d0f010509060a09140907140d060f0e06180603030d09020a0302040e03070c080c13020901030e011d0709050618040f 74
    0x2c0344604001d03482ea8511300c5030350b02035440d00030b116544e40b0b40c498408001070303006070042d450305e0324154003516020ba920024008100700d40034401c0c920407100d0000c00e00107004052664540c0c5a0a04e924204200940f1041c18083c0c3e5510707564a40810307906d4443d10b00d000312690011646400010b036968450110307042d070700c0070700001d00d4480150405000c40a950542c00441c08404a039004d000fa180300c1950900301060250b039681442d9220301000b40b040496011011440d40c0e070380d180c1c2c0c004058003070700120300e01c0c2000001c000440c1003803602e8020340003103510315998904012021030740324491856503081d80c079100d0b1401401d42d00c1c1c0c520224015603010300208130219140303885a8880d0070511040b0740c5100c07070b59000a2081030004480c02041e400502c154030001241c0a9a0000d5100b109080c0c145038807a03080c002c10140c00c2c17003400040114107200c60000c4007603400c2103041c00c1c0541c02c006542403400701402140c2d107942039071520442d09a03105500a8440d0301f819884804000b030700030424 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 467724649 1250 467723399 467723407
    0xf01080a1409150901090b04170706060306020c06060103111e07200907020309011409130e1b03010207050309010e030708030406052106030a020402131802220b0d09060b06 75
    0x90000140c42200e031843c408501d0719902d910300d1107030980728540c4000e042d9244102c00b080c0402c0c03400ba00e4820700c603c0204000e10f011550760b81c000030f07621581c1c010b8030702590110354034454150a011155215000346030400080d50700c401c41c4050350050025034481c03101c0c0f02c41d410780840381100448032007540100f05007a0700040040203000b09407409020074080c40c151004100308600010549800000507122108421081c115400c900d80003a540340f0380c803240884041c001082a031040850024400e00580004884101440040c2030070f40c00300d41c00f0780e204010081c0881e10100980390842400d2034252240c020010000e0b1902000d0780180040b80000a40060070350b4100c0300074488000d4006640d0035412101003050401c1104940141d0180c1010b41d0346001031030079600521420540d626030b049000e4076000244030480e0001c108a2940d13900050080008088081c901c1ca800000c04101c0c0c08242810100c80c41401603a0b0b4141c0010744848a000803c0050f4111a5040380c0140c485500c07 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 467725899 1250 467724649 467724661
    0x3030c030408120708030609060d060c020105060f01090f050409020f100201090c051507060b040213030c180203091b03151311060412140127061503020f01080a14 71
    0xaa900c9807041003003a20901050050800043d0b041c0e402d2a5000743e592403c0d90b07283c10074060b202d40001c101c1640100c070420210001813440c4601034101125070300000b03103841d00700140300800030300000c10303414403150042c10800050130059000584100fa103010807101c00c03a201052038107019141c150ba110180741100038001d40d0552241801501541c5100d103a160303118113200200c2d440c3c09040105440800200d03000ca100c0384c01074000601c002d000140703496404608115800203d40003120b0343d40ca148010440d5650405455082c1c800d6880704614504103d15029030703c1c49d0b01064203101d90501e0b000d0000f41e58050000d54015602040c98114502c2c5c405e000041442c104282240c08103640c1802e800981004d506070340503900301181c0714040325500d8031030b030718200c64820076015190348a116885406a03141c80500a43c00c0c048041d40c0b00829914141050350440402800d070b82658510030000350341c500c0084040008c0a084c50710040c0c0360f4400c110080c001c2a030b40708001091035014454 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 467727149 1250 467725899 467725903
    0x140904150801140a0c05090a090203060f1e01080a05060a060c0c260f060108060a02070f02060c0a350c030c0604030905040606140f13230405010e04020d12020a0203030c 74
    0x101c13840d00300408002c0d1100c1502c056a640c042d81d0901c0e03130000030110b4184080021940110b030842001000c00a40b41450000100c8800d540703007000420300070080540d040c1d5600449013a400400c0040240007900e40381000c80d207042040c2c4542d01c1000580744043d0184002582c0349405003190900c2c6142041078041d0f4084005407110a0103014070076007001a905080c0451550b0507117085902a2459460716550070700a50010107081c1e0308910f40000c410010b0391110300801200190350060260341150382416048120100740348242d1604145208041e04408029040b0701a405010203440d903044041e20344c42c501841400003d84e02c40d560602090541098064080300e00860307080c0300994403484122104055007981c48442c00c82401040a040070407000340800c000401050240c00b507403008042072034588410980d01c01c1150b00030324502400d16000f1140035044181104840c0c0c00e140d40810103442002c000036084084812040060138030a000c2d64501d0b6030010b04a03034513940400d81e42c2d0703 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 467728399 1250 467727149 467727151
    0x40908120f10080a0b06090c0d0501120b0c19080a0b0d031205090d1e0203070f0b0a150b0703080417040f090c020c010518042c060714090415080114 65
    0x71a040e5003030302c0002c0c80b0100244580701c040d4401100003954855605002c0c03003800185c0074107031b105400e00a00c1541c0d101c0c6c1c4141070090040e5239a0012642c0c0c42d0038a14048a00600380a154110410591319083c01032190742004070799600d00040265200c0400d00700a00c140608280c1c401940c580000c00d255000f401110b1a40c0e01c0041005540c40c1c100d40c0d140d41ea152000c003940858000da00c2d402140c0d2500c07017071240803402030041e28a842841d80d83d030b000c40b60310410221004804070007804080e110510a2485002e009580c4d0300c2403604128001e1154014050020304100380400041c0402c8601066032400141c0015410b88a036104c0d040021a030f4154010203008030701d810007500b2280d100182480422406031642c91910170660070300b000410100381270503085a101d0b00d141320400e0888000701f54100d00312168146415180303994034107024002d8501020051040d800b40b182c0a4944122540c214049600241d0b0804011100f8080020340c1d115500300e51818200c2103a1102806400b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 467729649 1250 467728399 467728411
    0x250605040f02010e012309060714031b010207030903110a03020411090306090a02210c090403030204030b060901062708030703020d0809060c030a02090609041a13051302040908120f 79
    0x418060007130040111a4605100402c520082030740d001d0f80c0d40059940001d10178040068001460054151200104150450070a081d903500014114210040c00140000b02d0744001d0001d514048213600c004041c0044e03800003034034240c09248580c85950313600030390000440e4094428040303817060310702c04840c541020788440d0080c02144001440351b0380220b00b0350303040caa006105007000d210040001030200085c01e040502407080c12480d072000c2c3e88154501d885140720b580c01603503c604502e040100010050841c80c00ba0421400501c13605812000211001c0504542e10190702180080901100c0c108c3d4050501ca010000d00c003001d15034081116030010429860b80380c01500c07503400325551150100c6100d140d558082c000f1400c208542e40003400c0c3e11074000d200a0030041040c0000b4121034004007039200c0a0b155080617523444c24030500081c004200c0081c00c000e17610b840b258405100c52400d5000348111368480820007088056002e807400d240d00780060080914111044100755030080d01c2d5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 467730899 1250 467729649 467729657
    0xf0d060e010c1808061f0e040b1b131a04030233030f13030905100807080105030a0f06051e0406060914070e450903070503250605040f0201 61
    0xd040c00c00f51806901204941039500103041d65691480450f00b40c1a240c10915108040b82c000010072803481081c0b1802680a03455140c102c1c18404100190792005041c3c005140105001018580000c5141d800440ba81080c480d440780d118801d5880151060741c0000754041840750400390011600d09040c01ca040106c0e0715240c640c240d88004205a0200301c4146001c0c014a10006c0d000c0d42c000d03401000618440c0c02c02000c0d541e100d100051259902c2c4070b44400098444040240c083d5010f0f4806005000c103401074805051603071668000f003480184090100741d158408134581840903035640c41151400070400e0303003501342131400c0f01c081c10591254224603414981c41c0146110040c0d0f40c503000d00e5464541650307002149042c001841640286403004554007c2c02d220348407006041e4075501400c0b03481c1207075040001170790b00c00072082c00b0f409407220394810302c440000103d00008a4031028103e1002140348500003006c407494030007525006110b24180000d002c100480c03221004000c0c1c0c801d0321 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 467732149 1250 467730899 467730917
    0xc01050301050a18020d09050d0e0a060e011d0406030302160f050f0415080d0306030302070f0639120e12071a2101050a08010c0503060f0d060e010c 65
    0x1110203000070700441d83e10007803204007000070140c0075025800b140b45003480903081400c03a80f1110b0480d29110000d40e0303560820100000450390181c040000b03103004880710101c2e941065001441440b6602e0350324148004005504280090703102814200c1c00010810b00c81c1d15100d14009480f4250350b00d4108100c418020f021611362858000c40303090714805822400e112400344100000b400b01443d141080040201010a1200d0180045504d01e8a1907c0104a45145180c000d10b440007542c05147c1d100390181e028032007694000c10768021000c3ca42d109400c4000c5a8044034280030004000c5826584091100004c2290b10102000480e0305500d81e480e10150500c10b000740c14101c149011120380054205000840d20010803810303582811024a040c00c91141c1c14511090b1b024028080031171501c001045286400c81b200000360615074001c2c010b1000750701024185001c050409803165503000200e9915848020035940071540000c0180080e109118409009000d001c41c00070000b40814 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 467733399 1250 467732149 467732173
    0x8040501090b0405090a020d0207050709022d0d1d03120103170a0906030e1f0912140904050717102306030a020f090d060509010c1b0f0212030f0c 64
    0x20f503400c0b03540c05450380c60f469859010042c02544202d00600130190300b0300c81e40c00071075070400c0070501034800d4450059540248505505103802e890b125141d00301744425120600640400555185044108000c542e01030714101c40d940082030b201c4040700e03600c00410303811000d111119106040303034003424103c0f040c00403001560601d84130b003d081074080382c10300b00c04115645c0300b9031000d089110400140c1e000c20a000c40313221410002000540750017521001c03103000740981140c0302d2207a9840b50904050440036001c0700819800b40882442c4241da440c1c00088a860065144d000b4501c807489840707245181540811000302d12500503000d160b0310342d46201c1e030f1121103101148503020004064608580d6000741060195000c2042c0d03038800082403201c0c2050b500c6034189615070a2160901042c3c074500030642500315201e0204060030402d030b02144500940015115803046504040d90703001400c01c500116130101c80c45800c13484d90340700009416890308048409400714600b400c041e00d46d59002030f = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 467734649 1250 467733399 467733419
    0x3051002071e0f1101030c02030304140304080d05070203150f1b0d091a0115090e06060d14162c040e07090c0e0301270f0b010603020702010e09040b1b0d090804050109 73
    0x7c200410050303441040854046406060202407040c4150102c0f85040e440701c85043c10284088403039800b10341c0100c0c41c1c0c0c08500d424003d11000c51000c03025180c540c40c00c103440d01140302000d003403401c07180404024802c025900d50122130040e00580c1052280c0c21042c03403c0ba81d0041302e0002860f400c04085c0000c900b0421030121290001140e9541c04290380c1041c220841c0b002000d00b21a034400c00c1008035811580150203150031759100c100401c0020b1030300000b40d40c2900340701c08000c800c000c0c0048010203030002c40380d1401e0450310f40d00c120321044401900494020a0003014000c800c0c8241d07a0f00042140080d0004150009117a40b000300b5a042c01c0141420f8802c03103a00780e500394034200f03812007441811145850b80d00307008040c8511004802c0e100c1d00c0c415a0280c00401c0000d4000441c0d00565800c06442440120183c8003010750b4a03094458a01d002d10261801c000400303001c00c1c407100c5d1100700381910000184140c0812401b1107515029007213074494032076031f03001c2031024400084000d40 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 467735899 1250 467734649 467734661
    0xa09080d02010b060316110a08071a07120207060b0d0c1a03060d020f0d080c15150a09020a26062107050d0c15030b03010b0a03051002071e0f110103 65
    0x4050651390841d100e014000d01000c500c030f03007440d040268161035901500ea04001d80941540201013036941c54280303003840c42110060030282c600c0805240c0030700c800e1a40c081e540402078081c2da08010717141d000d03501e0880060500032516075442403a0192100600aa48074042d003110210108518003c1044035403544900040710102d5101e00d5015070200582450304035640f42400c0101800080030042e038a8100e550881060300383c10f5880500d4803144048600425138000f020518080302c0e00341f020002404102050042d0b8400da5008580d50106c28002d0240980078200032215090541d44c0702041c0d02010411030306984161540d00d007501080c01003114440b0500068000341c4541c40c00c040520041c0c69000f03400b00d0b0a40003416002840c00805100111690250b03540450f00710400410903007582c0382d5000c130034414a14802c0401c005840002c2c41c880d00460001c0c09a2203066030300304900707109032500e5031002071b500d00c5d50300c0d07001c200308452800081c5105002c5107001d8103010004500b1166 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 467737149 1250 467735899 467735921
    0x406060611073b090a0204050c09100f02010b0a030803040b15060d1e02030106021c11150a06030b091011040f030f020a05030706021e0d05040b160203030a09080d0201 73
    0x8030030500c5400d852160711450f420002c0120040c0361000382c10f0b5221030034400f2542111303650021202c40c401c51900340160307500441d49078503050a003500940007c0a911a45919a0a1082000c001c8080c40d00030741004055080041483c00d01582da07007403080069204403011548400d640c00051400a462031513900781103c054000c40c01d021031800d000380100200701d81805420316460410000c0c800600066000c0c0c8260f90150090060100d070214403e06869011414094030103a0030b03582d4000041d01da4420308002449809945440d800d240080030150009010710061f0402c003c2d40020014941003030514001007003044090b05c4403e000389000306c0c061098000325060040021440758254a25090b0004014440403550760002901d8100300f0390001016070000e10a10842240e84080c1d00b51811100b0082c110300048424028034601c514011030f10318140104040c80114540205101b182d0341c041d007142da45440307010010305124114807940e8200d200d8459103503000c52040c01413140b140 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 467738399 1250 467737149 467737169
    0x1140112020607050106050a0b0414010c050d0f120203010303090f060e010c03050904020c01050a06090b06130e040c0806013320010905100b09010e070503190f0203040606061107 78
    0x8081d4200559507000c10020380e0103648600011034299224105500142440d400b00c960b6146031017611440d8820010307110381030201c49030500b404280c1c00702d50341c11084201d00e80001206c007214000d4542e880490303007500d1141c0c400300c0080101b40e04000305000f5100d5248680c010982d071500b040f9031040c60483d1160005d03901c80781580c00240160090609160014001f5041850b04c1c0c0b1032908645023200c1750170f070749600e0b03050412840040b48503413440404140d4906107040807003504009204424400e10000c40c0c0c1040014003409405020040a420440240d89195030b5406440c590100c0803020006d01c000c030303008150100303041d0196103a414005521619013803d854030003030100030040ca0411400e552501d1058001550500107150510703190113001a80e490324905008031020160405040d8104030710131301820319001800e0301c1e40040c40080781c0c10302030024900706000c2c00c0104012441580013000b070001304800c9401100944066554004040c00801c100c1541c0e0307996441200f283c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 467739649 1250 467738399 467738429
    0x908030a050d05060d080a080115140f0a030b03150402010210050103120309021c03080a0e0712060203070309120203090102011104050f010509040e030708070c080607050307080601090807060c05011401 88
    0x400b07041d802c05039010340020003d425612941d02c3c0c1d03034550f51207117609000080f8110010300441e80740d118070140c3d00c161450010000000484102814440c2c0302d003080e030410300491183d004d80c1c4681c128100380200502540c0081d20300319a0305800310301c140d6049000d4010766039034984c2100581300d1941282e801018102040080510a074020300c2040c200382e0700701d02049032071000c0040c50781d00414554800d0b03680700070b0381c9000c25105089032010305e0030b6503068110000170025566055400c41ca815009540141c2e40d4072102c409600074440050300400c0c044410300044500b5030040040d0003800000c1e00240001504915072a01d02c2c0f150380200c070391000003030b404407046500c40c2c1c004d0b0504401c05840090540c0000c1d0b00c02d8515007041310211005040050700704100200c1c06840d000800400f801800700d8202820081d14a0200401c8078042040c02000505a0f80c030408414006200b1102a1100c250300c40100070550390443c0002c1d1a95802c00449940340f10f21045030714102c0e1314100011901d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 467740899 1250 467739649 467739667
    0xf12010e190c0c0b072c0a1e05090c03010303020f0f0d180f0b130e0103050303010b0903010219030f0b19091127040b09060d0204020a090909120908030a05 68
    0xb4003140800304104680110182d0014060343d45141c040c156a4895440451070f050002d164041210130440d02441c1c1c00c800000d076600e41c84007840075244680d45090008007640460080c1e85c5803984810750050b080c0060092984540c801181601d000e43d00352850b403420001440d66030440da188811265008480c2910950311a584801070104906998928582e0356500040c5416013900160b40182d030005040c034100000c1c0314140000d04040400149942c555213820341c81e4041407040244068000419459698003075040781e82800040044485000845400500420355507041c41c0c0300510300a006110391070100e4050804032030810009068905041900c0090701290041d00c42020060143d55142ca00781c1c6050310141c244680f04204804003001004107030351441d04a68045c0c1c000c0d00511490344c607136104126039542c040c1d4000d03070382d090a8001119807a80c1035106100162808200204010108154034403101c4070b5922403040780d4440c1041d80d180d1144010b5034011074010044041 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 467742149 1250 467740899 467740901
    0x4030f0c1e05040b0f090a0516110601050402070c0b0d0c0e190504020904020c07140306070801050d030c11041a0a060807020307031803020603011e061d0d020d080f12010e19 76
    0x20110030203820341e4a981c0340a0081940f54109842c07902005444000300700c100e681200000544270b015180030358810900f10701d00c41d01d80390107005403401603400003021418044d805907000c0044c00d00d52582d030382c1d401000b05800020b1034808004c1002600751207882e41c05242c03482150701664055030319511868136003020400290b1120621603005030f0280000134a000051003c44001c0a207203d06120803014501014104030009107030780240400702c1c0c014005500e445960348895a81410900803180d454204801c1d1119120246e5a00a01348544000c58855441102c4108201601e0f4404860344503601a02c140c4021a003e000681c002c1c4080c50201e880b59403280d02c04401c8500418283d42c5076008248182e000360450300f005207520202100400007020300800401c19881e04003028005481d130340d030950b151400b915208910403400b200c15503640d400c54030682a44403101315503407041c03059154903507005413031401d16810180c000003c02c01c1400c01d01030321130030010f500280307800440c4030028 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 467743399 1250 467742149 467742161
    0x50309031b060d02180d030c060f021207110f0d02070314010b1c0f120e13060302030705120102091003150806010303120225060b1e10032004030f0c1e0504 68
    0x1112058115040c00d841e1b444070514011a14040d41d96003d0f411401e0030120140d50300708800401041c03040204104a034210680030fa0490054074000300d0500c40403842625082091800c185a4040e00d26a4100b4640000d84842164803a081078031005212100312805c0301c07a84405030781c0103142e80554603412009404400d11682c411105509408041e40f1482035100380c18401c0b01c04220720281e401e2480c07511000301d0103c180718000a01195055901098980040d4070982c0d000b694048901d0318200820b40581b105490050300800d44140840c10080140200c005215000207150b04089488480801c02078180c0b03070561500f0382541d44525100b80203500029140815040140e04550240c0c502140100f105016480c00301c0d00c1c0c1e21500070003208407030509050b0072811000c1010310640e26907003603041a108181c100003842d401d04104a443c020350314210061171040c0090040104003005002c903580c0c600071203c80074020380f140c4400348140d0042c41051000d0710903035000c00851800350080 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 467744649 1250 467743399 467743417
    0x403110603070c080f032211060a0e150d0c0207060807050715051510050a0c021309140a030f050703020a020d080904060b031812031b090d050309031b060d02 69
    0x1100f504203180c3c6501015401440d160540d10310000207020b4008100c0c414900d40141002041404803000da07100e4411301600f44000780070b18004510000c0880c05520240740403030004d420201080b0401d40a90000d81c420200d40b903501d031801c846550f04500c005622025107403943ca03616201c1d00c5103e4140c8283e00441300848121600f0760900c4500c0c40740d409130718050300740d02030390107018180c9004200c5445e40d20b10304401000024010baa040c254427181058440d5010b80c1c06500418038440300d00c000d0b204051011301b004101d00580d662040000411041441c0648d5030000745444071041101c0700d10611601500603070085d4403000c094070702030740c60982d528411080b141c40d200455011038160361455010145002d404401c1152131103114a00414030084900904a241000c2d549194180000341c0000b403041b030070341440d02a00c41c1c440200d07806003900901207051000640340107950780d030224185a00901a2105000d4552540600443c4840008140a0419000640761002900030200e0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 467745899 1250 467744649 467744657
    0x1060323030714011d1212040c080609030304050f2140090903050327010f06050f030c0604090e01020717131a04030305180a0e060114040311060307 65
    0x40d0001000c03c0f260014610101e03001040920b501142510344010405030300307880d5005000311012910900086030b84007658104000e91984072401c00d100c180c031094006003280d101d010248181640c000014610551080044900c02c0402c079103815218640c0708200301711080d0382d00c030900070300d405407000d4100001350701c0c5054105030f5076040600000004c403030080d03200944001c00b21060001c4035224405000c840300c080c009142181c3e002091444001c00b419101070078856592000c1e00101598808500c52034002d0084c02e0081c40c4020040c00c2c40c0c03040380c1c8101d1707480a0740182410085250071010781c00a04040c10140380c02c0165019144600c824822958204815400900f0b4060204941c4074504e14091300c0300c0e5070f00c0e52440510b009030044013000c4800c0e0b450b50721423a15401110192541850015290001904d0a400c3c000050501541c024480038000ca43d642e40c1d10340991081c40c099039409051713141c101300e2000a1081e8000601035070700b1400702c10700714104280195007101c0d041c80c1c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 467747149 1250 467745899 467745907
    0x102130b0a02100b040e01090c051008010506030c0708040338160f0306120605040309121e0c051c03030f0b0307050d0302120712030b1f0e010e03030a02030306040e0106032303 77
    0x2006c9421680e106d80221041c1c0590403060200d0308100c202c07600042c0da1400c1142c0700b0b5041000007503d9010080c4101e004842c00110f810402c4595010b81d00150b5000c11011300559081c1010201d00c000000d0740326004144041510481d880b080300f1500a0700807010b415810100310000315444000c040c41e0300141929504009505044001100c079054010140005c80f4241481c0090003516568840713084105d0034250f801c0030440d55199082c040308402042d68410100e80307000464980300703030311a550204500c0190030700342c10840340f07200c0c80a100c3e0303030108058010802d1001c07c8ad88802030720fa0b0580e014000600081c2405e03800402c0090180c0126460401e00010160181c0c0c000c110845280806400416900e905406242e0540d60112110b542d4078840318440d0300c41410001c07112041001344888075565900480c01030305002c002600340ca076511014000a980d81d4405d68200d40503914001c901c00c440d480c18424001901d60264051060320210010440e072014041d03900c4c140c1d804108 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 467748399 1250 467747149 467747171
    0x11010c150917070b18070303090b03040309150c17030c07080f04090c021b0a051302180604080a0b060901030807030f05120109051503010c020d050c010902030d020102130b0a02100b04 80
    0x1c1c000d4443c81d441150b2035669403030b01442c8154205042c0c1d020ba25164480601840025000a40302c01030390740c9905125140d650703e082c110740c2d00c50258040903001070300c4144c000c2034541c80120340a606d0300400c00d0004511120320600010b20013101c010507101c82c02d005490026804000516589180800b52410f240d100c0c40b0700c0d4119000c072061200941c0c86680103d028100007001d11126150464850f00d90030700c3e110104044032040c1e00c203008071a03400203450860740003070340700c8444c1342d070b80640b2071600da42e1035420140e0348600080c0103641c5801c000000600720310300b46801505a80e881032a450902c006650155080a3f1031902001881424040d2000500111091a00800041b032020669049c41924111320b01101c1520ba400307641013024012103d50000b5401240720007038900a642c440c201e80c42e035401084c5aa4000b5454010b00070341c0e850880d8150094925840b6080c1c0c00c00030701e51344504407425840b40712140300142c2c01c49a80003c80f6500d41d8020700c0200e40141c004181c00ca510 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 467749649 1250 467748399 467748443
    0x703030906051515030708060607061b050a1106040507051507060905010f0536160807050103050105060408070504050a06030506130b1f0512070803041211010c1509 72
    0x115000c3d514200c0358070503161180b42028030b030380a000202d881c461540c10000001018090000c0030741d4007640d800124041001840c2c1c0c0400c4c1c04170002c80d0741e5105072000c600018075544c0419499000541100b541918005010400c9405180d2080c02004107501c1c02d01170250001c145c0c4400b088800007032190714041803241c055505a18402d0740001015030040740510122032001d0089210500040480c0e1203090030101c14981102c560304a03400508911854980340c20341615485140b80c800d50310000e0102c50005441d41902ea00341c8041c4150380c3c0314010702809016a10480303900d5408800c003000305081030741c03020341c00c4400d00c000426074a440e621610310300700d8240d0f407040c6078583c0300b1401420b001218110541241d20030011000000550f0030345400400c01c1e008e00d611642d60780700035601030401007080380b00412003a415030392a59510b90348821100725105094030003400d50800749a1562040c3c801c02a4581d10158100e261006100c4000c001e20052108640c03071100e1a60f280708683c82 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 467750899 1250 467749649 467749651
    0x15051503033c130f030b130204060914010e0c0c0a080919080a260414031c1d0105030403050301090903030e190201030623010f050d051806090c09010902070303090605 73
    0x442c01036a071800d00c0101e22601c120750340d1066420340a450414000503000140781030700b01e14040141c80f940d44040c00010010415503001084143c0381c0f54203c8038035440120094100e6280e1200740099a442e0f000e4465548580345c6085c2880e08801e40032000144607101414000d071001d0182940c2c1080c580d9000070540d42c6400c040c01035440000040e0400c00c1c141a000a4241b0451005090b441144a522402d00071070190350b1805030802c0d10000705441c20000200b16420841040f8006000400050003c1c4002c282e03c21040704a0003000c07400754003560840b401240d040c4d480ca49568a400d8418005040107241202013589808803166020401c009485c1c8400c4810b80041000300b030752001508903900342e40300010f442c00c881c0d03031030041e00c07128222200b250000782840b80304515010001c807018440d8039140104145040d09000d0354a41401041c0c01c81c0710488121440e0f61900c001499031188010741481d4480c030080018450b461058024280304d80c070a00b004100c0b02c0752950b9520503160 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 467752149 1250 467750899 467751007
    0x409030c1b030b011d0a09080d0b06070602030f0106200303060f01020a060e01020a0e030c06030f041b03080d23010612060e0c07020f0a0b070b130602071505150303 72
    0x1003403005d170003080b640704549401c03040c940b108100b242002c1d56100402d02960100b1040d1075507840c154915622108100d580c001d0f44104215601c0c603140d103004441450270302683c0006101c40d900d02047d0700c403419000c46042c91001c0114110303038840e4208000c808020790b0740390444c0546100c036000601140108850b40c0800000541c5860b40746070b00401040900030032911a51012800320310949071001101d4101d18003060794011661942044030f0001c3c412680b0855a6044010002c20300503240301402003404162400e001c500740420361504040102d00031044802c0e003000c01000394600030300324114580e1a078140801c10b41c2d0355444c00c4286450856080c3ca4504001681e90114036201c0300703070b0907252011030f03a01441705d04140c4000d04038028502d0080c4801c40c00004120035440d192501c2085e83d42c002800e55459460b46000548881084400c2490504240c00701c2e04c1c2414148615403082d0025000b941007e5100d81c0d95400180c00c003c42c0c02c000c50052851090408141c80c500400c00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 467753399 1250 467752149 467752169
    0x9120303050103033e0a080406030c02060c070b06010e13150e011a0415020a0b0103050307200d020d1a070c051c120c170a09110409030c1b030b01 64
    0x141c910306001c0e00c0040c03c40e0f06041d1401101c110580c4c4141004100d582c040e50480c1c040d50034142440400c1e1406c01402000381001c4c1c0003150026015038035400c0101414419800d13544180c5850007440135901402c28002c0030900c910002500651244480703000c0c011005200340040491103d15404440040300c0b41c03421050000024001c0e0f00d09402103c3c018045d141c182d03034109021040b00e5090f4010341c0680c498008042c401400b405100b040140c0e0740542018058049595030b01d8059034079800123400703c0382c1c9007000d500c406100940c4801c095400c0005000c00c3d070002925800c1110b000e1081e0400c0345e4402d4941c005454420018040381c1c4070317a0b029281d4040c941038a0600d14640f040d60359102c0d010301128001c02050b10781c418070b0f54a0180071990040b5402031003210940d4000003000304041820200310400035881c0e000c0e008444540d01444000320b9181c400c009010a8a100b03920240c04600c0b550036000004070314844601e10484044001003802d5140d6940048500007a44019224 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 467754649 1250 467753399 467753401
    0x15040219030509150403180306060b03090c0a06021009030528020f010b1509010c12030b10090f03320a02100e010e01080c09151201150e0405070912030305 68
    0xc1a01031044942115040b0010410700c040d03c40d40040601000384000c003044030b04515841141500409107001d140d020f801400f0b003903221002607903541c0048501e2201403181c903010503254103010140c4000e43d440381e8041c0400c2440c01710300030040d0203810011410408100000e2101800726070a103284a2025452503450001921000385407066840901078a17034904070061105558a401c9040003404240c0048d0700c0e00100c0700107943d600f040c2400588640f00c1301152200440c0d05600040400b40d003150007004a2405582c1218054040c0c0030320000042c40b00400c0c00440e00e07207101010001c1d1407002401980c413a501031007442c0521100c40d040790764444510b040c2146408403012008003054908410340c4814900000c00c84030000c0b041a0501c6204004101c0100c145011a4408000502241800c0c00c444030100e007030ba4030020103800040310301d01c000714001041d05c0802c524140702e982e9030b1201d05401010880100b8010f40004107002c4105000100803100746414070b04c00e4040c2d100000c0d1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 467755899 1250 467754649 467754697
    0xb0f0412050a03170f04150b100207080601060f0914030102070f0b072003030610090510020606091006080408090d06110d0f051e0a0605032a0306150405150402 70
    0x400c07800042420710b84e4030340c4010054440d6150381d00541c05a00007101750030f08102800b0702c0c0c008018020003c0e0700409140b2041c80010340000700e89084a000d031040310010b070b0361000200c0d4030401000b030078400146451410091444464000c410001d4020001803400c511aa00d64500a88040c021510200030300c0030000601e0300081c035000d1040303020244081c04440202c3d081c1e124800149424403441ca0324a004507042d200f09021000781030003a140c0041c1c5400c2d484003035503480c02154142d00c1a5074200010b25203003000c00301001141c0c143d03102c40d400c03601c0b40d650700501d036003100780c02a4010b03c0e505050004105240510f071401c4641840c035aa59140491443e03003901c081d4041445d042d41040c0901c4900e40b0008100c03501003110744481c108584854142c071001c0c0c41030f503000702e40c18400c1342c60180006211801021000c2d10780d410a0032151050307810b240d19000b04803606101d01441c0319001180b41010b400041e40a1071001c0300d564075031030050001d01240c01c0021032035030a124900101007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 467757149 1250 467755899 467755907
    0x408090409030908010c0f2f0f010204030605061e0607140303101701090c12080408070602010b09090a05060406091a040c1505120417160b0f060f0102070b0f0412050a03 74
    0x100c24149450060243c10144c02c02800c140c1c0c03102414542500010429107030100b802000c90320840d80c2c40b00b81c40c13103907210881130781c08ce4115000c29a405480e2402003032444c03401d0078120032007502030a242c00902c2410000c1160a8020405c10303201d00352180705464045006000841c07240038043d4140110b28180034002310900c2950100d86400e81c0750114007008603480401c840c0c2185d0132103021182c540c4003454072105c3d60085920210240c4038550001c0350701038041d08002c8403030105560f141460b40d16800d20907510b6000c200d005e8600c0d04098003242c040742d0250840d5292a004802401c080c0d501000c14071103090703089805942265000c501401341900300d0100500200030392402c503007030400f4400406031010b0050001030580000d0450b441e50b82403c5070980741d154103180c84000501c1c03264200b041441c102103030a800d009800a0020305c1c035140c070f1a03401c80403c030180d00134070019061050f18400c0350f0104403e0311100704180000038440c207000f43c0b6030b252240300c0d20150250031040e24002d8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 467758399 1250 467757149 467757161
    0xb010f03150c080a0e01020f0301030c0512030a0e0402090402072405150a09090f08070804030b060109030b0609150a0b0d0e030a1b0206040506032a1908040809040903090801 76
    0x40d18031410b200b070810846502800c2c0380d400a810b2500040c0310300d408001180240b00384460070103282008000002800303203402685048444c203031480c0000d031440210454880c8103207044040802d0601c600160b072401c0a0380038012000016100528100300c0392103004048408120040c0044848114a49031806e1401007a0300b105c641090002c02c0c40e001000111600700c80d0144105c03142e5581803040503c103003800401012034003c0951543c0d07072001c1c105516150f0040c0002c0c1d03000701d440d0b0b021072819481000c1e10b20440760800781d03440645d2902000c10400500180004481c9201c2203ca01c413182c2d01e1a031030b9001414401111542d40340800e203000d0559140102882e025041400911661380c1c110740700d06d5040d00180490070a41d1014400a144e2b4040c40c0c00080c3c100e40080f04005290300c01100c000d40007601d46240e91911a00604445824444d441005c0a5080b025401c481014041c28403a80c000c1c0c0310351880c60520210b140400c00701c602d003000a60004510850400640c0c50a00c200 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 467759649 1250 467758399 467758433
    0x212071107061709010912081008070e060108100812070204060909020604180608060c0901031a0105161707060b150301031709010516080405010306061806050c0a0b010f03 75
    0x54071029140c00320241000202c0c1906208088240c00000c0c40c4040030342c0300e404065441407a0f0983c0d5070225100400140c1c04640040c0080c207414800704020b140068020308031801c00000070147d0303079410011285501c01800c2c030040f501c0c00000214044405001d02000c01c140502031544a032440c0c0100010f9542d641e0040200514010040c0050b0b103555040f64165035603481c26000481a1080c18001882c01da441411640100c0c01030004802c505001001d805809a034140700f071341d11070300301e840c20346c075010400c14082001002200400c03050850050b0040d4019085a1b00e0040c44104100203980706171003ca071503a07a6007824051510b40010421100c0385081031060a40d030640d82c0b00c1210f0340c0d02c144440e180302808112038555a1081c07084034164010b22810300014215450070074041c3d0407034003580e400b0a05140010034018410384480d5044440e14551801807441c050041daa03941c002c00c04e894440c01003200210110301640a56802058001c0700d1012a52560511420901441c401d07 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 467760899 1250 467759649 467759653
    0x105071d1507030207030f080a030524040e0c090a0204240c0f11060a08010602060627070309080c0c04110c0c09181501080d140703030b0d020402120711 67
    0x142000d41c495101045410040400e520303a50303030203824107074a402d685a10080043e80b0320f10080d000c0040c980b001d0182c43c4c100d40c074180215100c0340140070070154565900441c0080030b56551000e071600317800510707080901d801038440e00c0ca0311130085500c2010882c0c040f40c1041c3c00003010846188a80c1050710300a20354401081c02d0740c5602c00042c80c01c488504040d080003035060412080c040d0f101005044944002c1400c0c5d40c40c02000c2c00540920700911450002d0702035036000407180e080080d4104600107101740383d01025682c01624409802016250404055840100000051b140c50062199808400050410b14112020882602c100a40e800895041805602c080c00c1d00000d0f201076199041f141c2c051140d40741030000e41c90005c0040f19545038854500088060814a00114143c501c2c00082d02c0c0d0a0700d0b00d101c20348e1080c03100090b00c0019041001341e07501007031181d40010344550b0010600c0c400b1a126400050aa030411840c2880c2d00342c2210a02c209283c2151036800f0390ba202c000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 467762149 1250 467760899 467760947
    0x108150601020d1d0414040204050114031f0b04060f0e07140f0c0a06050a020a0311040e22050a060c0806010e0f0d051018020310050f220c030302010507 67
    0xe40340c00c0c01c0c4810741c0130300440d41c09501560f24115545403040c44090410012600b69070b00c0c0c026000e0080d10160700a92414001185260304c03208441ea0078640039000303018005000c5649200100380d01d01e91104a5640e41c40c01d480c90342c0d54052103000340750f104220342c400ca00308070044907500c1d00540724100340521960380000030380103130095604413400d80051a4882c8102040c82c2e04207416044018007103403800c01000009c4165078041d00d442c01007540c0410020068180c114458495406060780240150000034003455106030720040c2c50014502c42c00030716a00740d5840380340c4a5180d000710782544e19040000042940416980c2d409042403034601c1d0144a15804201c803002c000f506180a048174114400c00c2c07003000c0003400166408807a0030007080c40c203a255080b04810480f4200d01c2401000d034411940c03c2140141c500501070701340020f40310303101c0d20b0058200c903c11000e0b80c14403c2e03140d14010b010030f003c1000310700118007075000170a083ca807011000f08040d0080c01c0f88108004102 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 467763399 1250 467762149 467762161
    0x203100204050a050d2405150a030209181501030f030813020a030212010605060c03040905010e0907060305060d0602120108071e030803150a030321062103090914010815 74
    0x4081c0300101c410503181c5440d90f144078180107144800b46d1480382c8180d0481c1509040c21240755004030710554071020a00000b409410070008466501c0c40042d600c80501d1000c14500d807075000c6013450034581c501c03c8036040d0f200c440a8a101e5030f000d80c001c0d41d640b0303d8401c012003807540220340a0b5010f4405450004038841c0d560002d06444034071f020281c02841c0304168505240c40035804900503100080c407481e00c2d0400404007590b00d500500800008504001c00000d019522945071406400810054407915041c19021001800e00030101680107480320040008902544028401b100c1c0401898a1940c100520b0501d040c401d40d03c0151107143c03a079a040c0303450702075000a00c2503a0f80918401d5a98032807900e40f912001c0946086d1f41c1c401045000002007640140420109203119060260b22021561000b021100700c0d100d41c240c404480d10f07000b1131150003421600c00d054400e0802c1c01405499580040c11174412041c80b01e240490710740180140c0004224410b5045c0c0c580e120840507191034 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 467764649 1250 467763399 467763409
    0x4081c0605061b010b0a0f0f05040b01050d020903011b0827030f031923070527040f0509071d0c041502031606020403060e0d0503131505070804020310020405 69
    0x1402002507005240d1482d8070a2000c0d0480e0074000401045083d00c607031140c0b807031f01c0c003074056108810f09201c0441b00040d045c1054000d000c540c46050315000d0421112100d024060360050380d084d940f43d540d44000da54030214000b00320104441d0b55507403c41c145890000b80440f0b540003840c840d10103486020819050000004407260245d801d4901c58130b136201d42d10720f45d0b00d002c04000c2400c600c0d0b08280c410711045c0501c95543e084040001404c440300d880b0108150754501c5030005501010803d400300144581b0088081c0f16012009000004c04001131020641105c2068408000c650001c08041003440380601004800c4000381e02e200c4e21605016110074500d1065120710340f402c0304a409041e194500034401d459600e01c0741d28003c2444955031400200035445030000311034491500c030030b84d900e00c0000202201c600e44951140d61640d101d03580c45424408441904468010203149410500c604d00d024150180d0002c2e00c5140c0e050600d44101403c105101141014192040c84104215034079 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 467765899 1250 467764649 467764657
    0x9090606030309040b01030e1203190903020709090f0b270c0d0f080403060f021306031521050f030a0206091501050d0303020c0303090c013e011404081c060506 70
    0x11140010482801e1005802503c005440000d50340550310b0380e5021000c4400080d48240303012f103251141001c001d02000b084890308807011300160b100c0c040c1800550040d03800b4100550181c2e00c400c0354450300d540d80d5100c070030741121070b85020150301c3c50001107142001008a03402c441c250203416a05401c00101d00b0220f410b450145c503000c1400c0301d09043c00702d0354080b90050750300301d0410b000030b10480708080d0203940010103c00b801820000c0000da518884c3c41415200f056441094120074501103903803070b011030003101055800da03180765840c0005204005004445640402454486c43d907018003906240340140038400c190021540d50aa02003114407050550b00111030342555001e0701c1c1170440003405241032a9040344000418820107480c00641c4107a08a0309070b8400b501c00d601c0080d034004450202c0e104080703114500d180d240d5941c041030031500805010500024860740d0402d405250b038070041c0ca00f500d45003030005201e200ca00c030311000102a003002440901900e4900b0000c500c0f1845 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 467767149 1250 467765899 467765917
    0x20c0d08190c1a0402030c12060424022118070e07050d05010909120f14030c0d020a0c061a0904080c0709050c090307170303160309020a090902090906060303 69
    0x40e9010051a040d4003030b80030030364400d42011440c000407004850000200000303884c141d210b4810b540d410300491030302c82c002c034801c8000d00c4003401243e00c03265210f41032080c0b04840000640010300c224a0203040342d2005d0080d1100320303042010100051039103009008009030010881d4542d510380201e22480000300c031000c503040d200c441c0c40a82d50303d80c8203c2e410701460070003400b480e0400303000246c00b0055400504416000b481c1c0d4071030101030020b081d120f11000e900e215010480402400c0400542100510b80c080b500d13840c42e5142c1200e009141040303a004000050204d108030f510309050100038441d8000f11203643d2140341680d00c80a001800601d0000c100404082c5c0002c0c20b02241401800264010a11200c040c49141001e504003102e07a08490102d50081c8030320b40e0005050f07440505003c01401e02600594030316120501c950a1050b46404101c0a141d12030420300c0041e02c07841e102100500524a002900259a20402101c40c8028040c80c066910040c207011540c0e801001700e4036840 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 467768399 1250 467767149 467767177
    0xd0306171e15040c06020f01051012080f03040b0121030c0b0c16060e0c01020307020f010c0201051c091101080907060302030604092a081605010c060b060c0d020c0d08 73
    0x1c0c01403074601e00d04038000d450480045040020300041082c1226243c040d14120703001d88500840e0b42c8082ca080781c0048400f191018030300c800030041e200e03030543c1804403140078000c9940ba00d00610000d1400343d1094408584680320300004000801203c0c007405800c1d0040007007101c0341c6240e40c0700244940190540501080720071008a00c98a92450403544030000c28000c00a2061440c03c103a0024034090b5407544e910301171412032600c00c1d8400f104440800d98010640380744010814011a80319900b0031007281401010881001c24031188806c0000b1100402c40102e000c0900d441c040e800e0b02d140b07881941c10701405a05008010002190103001d032802840c0c01a140e03640c4600240c05420380d40d40241511076540c0c91001e4800403039038500b02d20700601049040907130356500d072607035548802c03001e140031111a11010311596104029102c04171340079134000305800c05030400180599000e0066141d840e4020201900303400c0d01400840070b64403040b5181c0c0001001c5451f414610b02c0740b500348a00c40 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 467769649 1250 467768399 467768443
    0x40c0203070c15110d11010b0105090a18180f0309050d1e0501110c16080721020f040501080606130c09031b08070b030103060608070b07140f06090d030617 68
    0xc0da00c03c2403104c041414507401c50301500c8240304041c28245010072001e043e075081500d4009a54055000c5034444100507125080c4a490442200c403031122001ca1228210349400b030f14403508100c40c00f000c68040c050741d008000c02c512850f001c0c100f0709190b40000e0103040810440b0010a8404401109640400740300103400e035110b14085004100b0360812840c101d00128002d1080240002d00b1203108207442c28451201d41c41e200019070302c0c41d05110b160100c512000f0290442c54130b00310f50911b5984007400080c0c5010100f03002a0944600340c00000f490f40c44003040180c2d6203000c0900c11241c1d2078801c0200000085130100420280300e034003020b0051180c005590010181700e0003520000c2c10120300351802c0945401621001d5402071000b038600504008020036450004948101265102004075240c103240e03a45401c00d609d00d60021310f80c64010903220910301007041c40b034241b0440700b420203043c201c0c1200a001e401c40b000d64101d40c0319050030b220381800c0101c00082d01d800301080c541802540f = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 467770899 1250 467769649 467769689
    0x1b0d0f0f030212041508010b0412122609010b0109030528211101110a0e060d110309100509060601031d0106031118070c1727040c0203070c 61
    0x542043c00ea80207206002c0050001902540e241c0540791a04440c1c0e604049a6a030b02c0c0c185c403940c0114001c1c81c00d1209030180c41c000056040c0b00a0700d9102440c00e14510b00e8000030084082c411a580c54030002a07611009c03c551043e0070710400c80ca6800908003103a490f41940c40d450340e1075112200e0000c804240744404402e8808505120344000d501c042049072803002070091900c00c249001d40b1501046001d540703041e001c1c0b018086e08000f40c03d407132201d0342006141c8004a4810392035104c803a4101c0b204014625004009004103103074015a0034803d075a038140307005010f14000c00c3c0a408880d040c5400284500014003240c40c1c0e4116109190208011000010800c03003002b4148202c82e50750b1800e04000f00300120082c0c0354400e01411103070011921840b4040d01c40700e90003102c400c400200c00d9034050300007170b00c03460500703a6002d804032030315081003069444500da010710412220010040302034881080e243c64000c254022039548095400c2401e0ba07903a40b0b802141a001d0b5680c4580c0003201048 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 467772149 1250 467770899 467770903
    0x201080a09081305090705270d1401060303260103060908120106080106091706040f0501020415030504061b050a030509011e02120105060a09050103020d090804081b0d0f0f0302 77
    0x110890b045a01d450f940c01106800180030703c3c8a2252900807a101c2c0c0002d00e001d0300030303029074608415668041840c0902504140000e1420500d150381c02003030340d111340300440d1035142601ca44480a0000140017401d505020705814114880d90700050300310386500440400c000e42c042c1c11a07078040004103c020700c6151000304e500503042000304440c603100c00054102d0b0b01400d41c074121080785c0c44103c2c401e80c0b100340b40754841041031215200340e4042c0000c2400601c010a04040c054050f000043c02c0070b84543d26039052468041e46040040e031108103000c24070000d4465403480c0410b10300311444403026010050218090300c10500c040c9660741c000984521000c0d00801c0d40b448005404207000c0c2842c5604200a400a0070341c00c00e0b4111076000400c00c0d003001e2041780d02340b817029121311826516000044001c2c1d40045028082140c450307400d01c0001e030483c006400542740000203480748140341d0f4040071100704900c00880c419400e4885001c00720b0301110021070319030b030007201d40b002440c0c2604090f4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 467773399 1250 467772149 467772161
    0xc0b040609020910060809010b090117070e01060f030605060304020f0d110d150f0e0304260a12080f010e0c0304030c02150a1b05060c09310605010315030201080a 71
    0x283d000580e0354104032400294400003000e036a559103c078121030315488880d60803998598402e40e0020b1024006105903945141c10148854400b02110305c125100c1040c90784a1200ba0303c040c000c540ca0390b82c0c4011454050041c60702810303007503404a082d0702e42500000c0811075038039001c1d40074030030244102e4140415030340d081c403036100054000e01c0c000312246015040c4240230072402a40a103810f4004002138854001d040b04400040c0c000c50a190904200444048907070469030012960240400702502090045521560042e5981d000400d00950040c0822800901032a460b4031504014400c5006031012180c000f201d9525003a180d0b643da140944511500a001942c0055004c080a40341701c914001080c00c09595601e0200a40b40f00c04881f100541c055001400ca410074000103582c01080380240c035040c28000c04030701c080d42d4400d803c5280c14602802580005201e4141404106c0b050700074540140801e103804c100ca69030111102e40c0d6102540402170400010034040348030548150480 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 467774649 1250 467773399 467773403
    0x94506150c010203070e0f04020702010804031103040906170f030a09060507020127080c03032506200309060c19124505030d0c05040f06030f0b04020a0c0b040609 71
    0x85613682000400a000d0001c0c101c407845c400c0320614100780940c00c05009940b880ca506864074052a269907500f510f1000c4403a40b078100d5032000303100c0010304824500400008000e0b000d03a04400510050f10541040c4045d820410240c1c81041103e100c1544116035204440b030758500503403203515610040f04e50100002074907803d00b00b00e04111401d04144401801110200c0301190184c2e00c0c8902815180d000b802880d10030040a4034141e45180408100303540755500c00ca200040940f00303005a0082400c40318844581141c021081080c0d40d5001c11240c0d410010300000b003406c000d035003440003009403144e060035401c01c15100701a20200802c0d800c11000d0015144088904001085401501c2035006035850071012258400044500c40d00d45c1c000c5070160040065840e00001c2040300c0040c01409481104124003000300054140b00d03011000064007035680c0c0401c110394116042d4083d80c2401180c107208a20410015055a401000c4005015401081c5100ca680c95061030401064074003c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 467775899 1250 467774649 467774651
    0x100312210e10050c09010e03101d160510030c0e03011a0315102102060703030501030b150604090e0a1b0509010902070c030b0a02094506150c01 63
    0x1128251400c40d400001010075614126507210600400420a03103205031141c03010390900700002c000b554800d5907290428880a000c55800c0c11036a07000e9001c44050800040003451403205602c00c00d60140801d820250348122a0041c4038180400180d2829a6440c42d40c01d159407403d06413103103401407401c6081c000c0024000c000d04e481d47c2d080f0801d082d4038011003c0c460700441d050461044145110280500700f0382803906012810300c00095030f030003010301d845504075422000e60b4005a41d007600400340c0900c42d50740440da5500d18941724410800152480c520a1060b4416030314580f942000d03a02100c0d903a145c0443e0403402c01032000e0a0150041014000c0e48243c1032500c5017a202061400c1160405e4505104980c0c2c0c82e0607a00807070040344002045c895110070200081008001d5998105090703103001480c045200b000140800300712001003c00703001050064680c01d40d0000e01d00c85540004d07441d01c02c0382c1c00d410950043d40000400c0148035490f11804c9142d440811000c1d507142f2440800 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 467777149 1250 467775899 467775947
    0x301080a021e010509130b0d0c08100e0a020f0105070b0c0d0c050306010c12090e040803040c05060319050606120a0e100b01020316050a0803040b0f100806040b150303040306021e03100312 82
    0xc9c4160320300918020b0385801e20130a1001c09a8084030301c120042c00032050041c200031f440d02d0b800c1200510b240241141009401e1000038086003002518074082c190b04244141e40e0b2144e002c0550584400840440502c44280304016890360030100701726065900107240400c48049650036600021150051601c1020802c1044100000350f401107000d10301074281c00e2206991130042100700e2008942c1c0c0c011000d40d10807100908005904025000f01005003e41d0038400d400310446518941290307403049240e1110355500780c00e6402e226144420030180300c01e022200700742d800030395a4810341c0d0030010794010749a40d84050100c28094001c006a0010b65030341c2c0c0f424103040c5250601800d440b80003512500fa0040380905400c88191411a4503c0c4050003866495498481300860024080e507050741c00d009251207969801c2c002440507500c035003030058480100400455000000818807136504504200f8400c007140014008011290b00105880c00001c01d91401c881ca401817152030f120f00c400c200 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 467778399 1250 467777149 467777153
    0xf0b04140a03031401081f0c02030d0f1406040b010905061c0207050303040515041709010e030f010f0f0b06030c071a01060c1b0303050a05090301110301080a021e010509130b0d 77
    0x1411a1511084c965a0031040766200c00600703840700c2a008201e04081c0c4501c003100404089500500042445401601d0400000114003020340d40c8900580b8032496a41110060310369182c002141c01c0f503000d8030200855a00000040c2c480a9980141c52003840c010036a844003034004030140e900703c0912030003035440b41031909d0310507070325007064808840b1802902d113200d2840c401840020701c43e0b50400c000d11461004007922500076030215450f5410040210000525520300300039907480203101200000f1000500902c03d804c40380040260b012150400c2c0c0040c1e8265111015a500691a110b4065a030281403030642440040c81601d460551541d000020312076402c5040381110341e0203000702c40382e05820f84e0a0350040031224040180820300501460303800511841c050681d008001e0000200c510702e0b64000c0e4841d4200b680308030351a900c0955840c0c11814028824109041101a5410a4940080003a115000d007138140e0340612010b41000ca0070451940280b00d04010140240248224038 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 467779649 1250 467778399 467778401
    0x18010906061d0906091f150608100605030903040603230c030403030b0d05060f10030b04051b01050a02030711010504050607060c020d0e0904080a090305030f0901030605010302070f0b04140a0303 85
    0x1501c2d00d00d0461000169092a012032040d108504500c041d003440c000984c2101450320000d520840c01517a0785001c4640c0351010340110025090684400350145040900b404001105811000c00c2140510a00400810020aa40c1030700c410b42800702d09809d000441d51000c07034028145c0d404180110044c800c203007a01400070b6002d44e0080c0d9051103c0c601c94024001c0741441140b008103aa0310000014480b100ea807580345d50001d000a2041c01c07815520740710345522501c10740d410380751030b04100b1134442404004094a03241c1c017001e082450605020308030194481c011910050819041e528126600e40e100d81c1c00c980107018000d020517103070352a9042180040116080a0015119000c25846800d024903003811140b200240030350b0303143d42c40e40d85002e003a412200c0c6003800d22402200100000c4c1b4280084c09800c0101c5601c0340e1520100d0000600361189544803a05240c0704008140104030308003203c400c415000600c00d00b041c2c41d0f1389001c4000400c001204289030184a044600b0940c0c1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 467780899 1250 467779649 467779679
    0x30106030c0e010e0612070e06070c0518280204180f050a050108030f1c0203090d02070b040303090e101a041a040f05011809090f060e01141801090606 66
    0x2155201c0c0482c2c0414001554428011001654860b0040c040b41d9881000d007001180d208145141a0303044189803004185281c001c1e920441d00d114192006000c0c1c0e045c040705581070707070a0b040c02c0800e241c1002c024010000081010302c80c010740c000813846255684c690102d400901e42032103008040c080b1032000c0c0c001001072014202d007481c1400e001c40e100440d5030054606807070f984406145090381400358601e2a0b4012110203814001c10390a5880080003440690312400442c8007400c1c01e010000350080c20440640c001d90f1150006000030300101e40d10100d80000d036403c10110304860340f1000e401d045000380c00e43c40701e59065180010b412510401601078011541048a442400d034800c2d1403200d482e000e2802050000c100f103200400c007540c03181030310500703084a245510802948401a800c26188038840580c0d904081c500ca08040082c2482881012400ca100030401780f2407504041035050070151040c2c0040600358100c030f0317501000b98080321815078006820000266511030b100c20b0300724 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 467782149 1250 467780899 467780921
    0x140109020301210809010e011b2108150909030d0603060204140d1509030c0c061707020a170a02160f080f0f0c0616020405040f0b0108070305030d0c020f0303010603 72
    0x41014a070384100080780018001c1d144d021843d113040a00213401101d81c9858410090304000e03180f0321104000307032075580719003640380500401c620304040d01c602080003040703148048007000b00d10010845500000b4005440d451821500c4441d503442d11304100f49103014a124040c2110310f046400010092154003d10484001050104804076264100700c4032141080380540841221082100e03040d5540d44000c0c2c44601c203003001c40181d60583c0754954000e03020307041300003c60403801144031a00319042c141c5d54010b032288000c00550304a6980d800350340d030a0107198120500c011900346c0c9690300910159406401e00c14458201c50b64510f005007a10a8a02c42d020b41c50142140c0040c03891000f050f10700851302444000c0c51080c0e4400144001030348044405050200e4600d08e140041c1d91b20b010381c9018038010003060000c80c841c1d04002c2041ba80c10780c041c52090f402030b641000000c80100c00c2c1d80c6040345c00400003480b2030750f4030401e03414400f4a0200c44407078003000002150f00341d016031001d40820 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 467783399 1250 467782149 467782169
    0xc021c030e01020c01120e1906050106080121030e04020f12100b0301031a06010302040b22080303090d1107030204150807090209060d0b0d150e010b030114041203140109020301 77
    0x110401c0c016a100c1204510150014407459902c0044000c20380141c3c0150310614101c944880d84101500c2200300070384012981d07944c90b80010403107164040c0009002d417402d54000c0030105000d0044142c082c1d04c0b0302008050001c24000b2550554170f550558000f040e0041100784d503010035200660b0b23840c0c0c040342c0411408000a0b000726103440010160f070b05030f0303620905560f2800c0c0400001c4140f10b40060a90341019002c00c008245481094080d03c481c60740081c208801c0c14441c0350002603010325410141c000d5000340200b2059180010781112070480d60308003070004902c9821207600300510358001940040c00c000e41074a0140d100348405048aa030300d81a1585030b502d0300034880580c801c14420560280c0240407080203001103911901203510014041a0b40c1411a079421303030060014451004c806681c0c2c4d8940342400d43c00c0c0030f0355a907804200d00030880b680074000071001601015001030407800144004240b0240654841c42000f448150381318400c0d0303511080100a94004d000c1c4040c90 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 467784649 1250 467783399 467783417
    0x903030e0c0328120806100f050d02090409021009081e0d050f07120e04060f0f0e09120301080604140a0c0e100909260301030c0909030c021c03 63
    0xd408a140300300260300401901e00d072008442c040300340f01c00d1182c090104002d4030303107200c00003908108103c0f0200ca80341c903407035018905642000780345102130403c0c5c400d121440c00c6000c4542c2c1e000b02120000380c00e68400603151003030f40c0042030091864000c000d400c00614181c040c04a900440d405048524040c00c07107038001c260940a40c0d80300c040556040d041c0c0c0c03101d010004224050780141250224a924081c00c1949a0304c2d484444c00d0602954804104e1084001070356040501a02c4040d003080c1c0c0d16a400c46151924001001607640300e42e8060f110040c0114130780d650140704170016100541100341d1296140c056581d200c0b00b00341c0342101c1c00d00b41d5161042e0a90301c0419407646c1250410960700d81d0510340190120349000003041d100034886154004518401c06100d10060140104055a411b8030b8030726030307546901201400c01d440982d05200401c0020a070841c6c1c08240ca4000b0700126000c0410b1809072401c07501e494000358401c1c0c40c2c4a61a40024194100c2e45606000c0c0e9075008a03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 467785899 1250 467784649 467784671
    0xd0b040c120b0601030902040b0d0605090f0f0c060304030207120302060a1404110d030e0d080c1b09011e0504020a12111c0e0a0f0507030b060406052d090a090303 71
    0x240801d9401800b40164400148640d17000740e002c2c10045002410101d40c040356038002034821380216008a551a40e10300034072088070702c101f10606000d0081001810680e1070314118a44e9004c2c2c84ca00c0512581c40000005c080510a00950004164041c03c505c0394420038500a5290030080361816112850b10411a881120016080e800303503030030850386080b205122017403001e0405e078010140c0500c5500c040c80c494503162410300c02e000501071041182c550820708842402c181011540e40b001001003002c0c4480b0307544201d8114110344194030120a409500030307008010716002e034407140d407003440425200c001d81d4005c2d1001c5084a280d500800207203105c0d80e0200454002c03113500600c0018020708128035008140d01c0311480704901d0044659281455940c19a00d0182c40000c49003500449410810060840025904180103c80c00d02c13445051401007007202c481c2804044c00850300904800340c00201a203048511680540307080e83c103181841404028001c0c0440440000740745c03a8203055 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 467787149 1250 467785899 467785919
    0x20a120f0606051c090821060a051807020109080d0c030f150b070203031e07030909050105030a0b04030e090405030a020c06040506071101020f01090302100b0603090d030f0b0d0b040c 80
    0x1003510034680f42d050800c59040c804140b01c0100c084603640740c40c1d0790001d54010640c098007400003803540d1200040c00c80c00001480e811048094080760003008150b4050095681d103050081e80070080301d00d4001c0d90b9075642d0b003c80c0546400d0030040c04004000445c8071808125401248010f9940d4509020040d42031024404807000c20108810400c0315400c01d12018248000801045000404036810300d1b14811580c2d8075a8415100b029580340002107801c101a00107880c08014800104200180c0d850325002c00c0c0c641d400924002d003600c92010000d000c06003d00c0303d1282c1c0c2000075100701c40354505464955500e622103001480948910800402ca40c07030000d08507403d07100042c2a41e41492601e0340d41a50034082255038034150f028503124510303504000d02c22002c2281c000d0f4002c6c21b80301c004403218011a088410414021102002000714008000509a031080c04e545000078045000c0500680204101708070186c1c031600074034803101404066031065015030700078990b00d5501a56040004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 467788399 1250 467787149 467787161
    0x70f0605090a03170f180304030605010806010e06030a08040302090a090b040516090c05180f061309050a0c02150402030f0304060519080709030305090307050d0b07090501020d0e041e020a120f 84
    0x840420101300080d218500844a00044686c41089a04042e00c030b60741e04058503400d0304040a141e114400400c4095040e0340950b401010036005855a44080d1303d40441511460202034010340d01400031a44202150344910038843d003250500d00c181c00d003858101e468140800e600a400e00c850303000030400c140944605202e40311161030361362a1194014104e40003804d1240c8155008102e05045407540d161803004114403e99454a0a281d5040c401c4103011204003078481c8a0661a000b5240c0300203400041000130303142c29102500f1695100e1000a00c0c080388078403008030600000c54001502d42c0c0110190480460040c40707a012242001d07030440d0002d00072a10a400113954210420110b4044e80003410072000150a6a01591b141d002203100d001c03003903108403040046035040010590380020700001403c1c00b44054504006003090090160442441ca10f01c260b41e660004488540340c0d001840382809103100564443d4418440a801c5444020504091034200390415001c006030303128031 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 467789649 1250 467788399 467788411
    0x80702040c09081e0106080f0f0715080403050c10060b0c0705030d02150a060504021620090114030f06090102130b030c030c03090109050f0f0d0305010e040602070f0605090a0317 78
    0x515500e1a00c0ba921564110020040c454656986d140400c52004c24008400e032040d03d100100003103120800c03900d00e040400d52060500100c0d0700c00b08150359a011030800c0d005034051420603103542c02800c4003400d009481d4200ca0880703107007080008086080802800301a2581c03002e9402c070319aa10301303040c1c541714410f110b0401a00180150303219a159008101c0d041842050300040c41d41d150030109080740d021758503150b917010310314480c2c01c03c2100401544ca42c003080c0d82d41340c021725441c60020404201040c001c107074600c9490302d00c80c0442e4508100b003002c6901a0002c0328502e007840c140d803034004c0d444020603a82c1701c420040c021071042e01540c2283d00551100115901e99690055554190b07000500000300d0b80d529891203c001c5a4100440416030700080040c0031441c40c0e8140070b034500401e00316a802490300340401000403071046114036034056000070000d6503807001498800700c59003282d01c00a010074901410320540c00c00008a007032515200e0b032100e1031688442030709601c449070100c1348 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 467790899 1250 467789649 467789653
    0x1020f07060e0123030f070c06090305090a14031c0c060614090f16081b03090706110a0c0b070204060f090207060f05061e010509180a050a020c06010909020a12080702040c0908 77
    0x1300703048101c0051501e90000444c94011a6103500d80e5503403054ad410040240c3c0021400f01d1225560b18064086100601c101402c00700e08002c1400440d4650604c0744c1403040351602c0200c0c00808600410310b80364250741c0a141004515280c4110203502d40c0100c04140c0200882c000080311208581c8069000e020223040f01c20340003076490700c1100c003404014240e00790f01603c1c070a110400514000035500502100002c1c1c4011400c000d00100305100038044481305134444a0a0b82c00315843c403078100203503030720126015074a41e80c90010034040c01c001c0c2e07c103a0811000c0500000c03010415809884d40e9841014180000101c030141c002c00e480007030711041da01c0400ca00e011001c2c840c0d42c207280c0740c109c401030406038201621200001e01c0043c2ca100d10f544031303141c500704004901510384281a44400750400c210305140c61940032640c0e680c1e05010304000e03941c0d10a016000e5595103d4001d000741f8803860300e0340c0210328624241100ea009850124013880c02d0080c550f08050240207180300703540e03000340 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 467792149 1250 467790899 467790901
    0x8030114060720030f0106060f180b0a0c030810050105091201140a0903020c0d050601170309040f0218040501140103091401050702160603061a0901020f07060e012303 73
    0x10003124280003001036141d0240080000c42e00041c0c046aa030b0070010b83d80d01c0c4206080c010042410b0030154500b04c6090a640b41079400d00c11030350482c0401d540f0903400d15015018450b11508003408c0122900a6641d0000c00300da4400d030580c1c04130303880c24414401d0740c40301c07482d885541c59580140c0395070003030b580459800d00c030742c2030345046c85102c40c05121105000420040180303004010010b2003070700d92444c2903890f001d11005040d010806a40031040035241030035180015200e0680720641809850a100014907401120007000c00540e046449c1c001d100308034407030f070082ca140025844404003c400e043e0030070f646460703441d00744211388c12100c6501e0400c3c04000d941004500910040100311140038814010b01c041b14000d2084500c1a0800e400901500030038001c180040c025a500c06800c1609001c1c00380500c1031031000491260344519905900c645070400142e00301040d42d17161900714841c0000014001e6840032080411020130b803592581402d503041808030100303c020207030032842030400c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 467793399 1250 467792149 467792159
    0x30f2c2116061e0204050a080f0307060203092803080f090d030e030708030114210709110405190f050a0509060d080f0a030207030e09040b1b0415030f0608030403080301 74
    0x1141c0881400c2c4100303000a800c0078035a541400300ca0f401211200308903400714007446142020140c01010300141c600a0013481e4601503404c2d520b200d100c000401c80c54003c80031601401082040c41c03400d01c9420107035000c2c004240c00c0c80c50b031606682c0c4241c00240c80c01c0b010482d03094180500a0240585c10050300d03030075002c048240d024125a1a11854920040100e43d010442d410061406031815201c0703040915003600800109600500c080e8201c00e500f10005202e5000014040003240e898550104884200c0d0044180c0c9015039400940c10070381c64200c00341d95420448000056a44400408103181e44802c00e12048440d18021145c2160409001c00d00310710f07000c009110590b104060003450002742c03424143e410380000340328001180e008107511013055000f03c030341c9180013016221000c10307161640f10008661400b801c107410005500380d00c04050114039049501038201c1d4030304005101d800d11002002040a40c40d0026136900d07040c1c0c0842c507003002208450461b90044051801c40c0d02f81 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 467794649 1250 467793399 467793427
    0x10302010e1012290405060132030c0306190609180e0f060106030c0507170306120f070e0a06060e011404051906080907060807030f2c21 60
    0x842c4221050160388030a00d0048075140c00b6000304a100000d0002c580c402c190a43c1c045600c9083c000d83c410750400d000c0100c580d138442540c4400d8039440344007030320b40c00c0c0ca21410710b00c00d1840b501300c5044520006c2040142c1010b0360007140100c8007a82d80020110482c002a14034403d2400340100213840400108840ca0000c90480c50b44222440b0004804880080300c602c0c3c2000c8800c411101c2d00b2500041010b0b582500c42c2c2d020000060500d87c3c540a940c2e6201280440040b401190b48440400410202d403289000700c100030312030360202c46901c0700c1e40040c2a42d0329290310450b0180c485e4000014a282610700171202100e0550321680d00e61500b00340103413442c0c0f04100300e40030310050601000650343d461004200e403089103c483c051a482c20000014900b100007401d0a0700d9a001035810004640d00c2680c565000c4901e1500150959007044120043c20651020354001c596091703070a6510201180f0a42c0144940f80480e0b4000a807055500045640c007071414400c19400d00000c800c03c030135 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 467795899 1250 467794649 467794669
    0x303050a05130f031406070315060c080714100b01021c03110d0f06090b030312160c050a080405030c0d05060705090105041d10060903050a021c051002030601090e010302010e 76
    0x3035000450b00c0a842e810021803503007140d4001c1e944103071484030740400000180110b9401c2665498280700b408000f00b41c03c2c1e0f400741c692242c0c40410642a40900a228044065400340d51340041c1829207210802c1c0c2050340d27200d4842666a006140c040901115030000404a209285100303030030108106c1c8041c03e80003000004404014454104681d1003050100e100348114004000760009005e81000302c20b030f0440d441d00c110140280d2080243c520146941820903a0182e0f819080d43c0090000c2c7d0b404650000c0003890040c000c0c46510540c004100c10b00c405841660307415001c031402000b40008010859400c4070700603003903801441c0440c000c00d00c03600080840e01c0b8103040c428030b01580c0305541d01d540901407a0642c99803507c0c00034014a10a0300e44004010586468084851070454555945506900314020f2148407969202d148482500f000d6900490300307c8260366031180d60006030000b95004540139400106040c1d00400e0309080644540e042e41c2d010782da61219504560240400071709 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 467797149 1250 467795899 467795917
    0xf02010c230f0d031503020d06060e091506150315150f040315110409090302151303020c041506030207020d1205040603050a061d04031707020328080c2203200405010303050a05 77
    0x284910020a00d8052005e109014150420050610b2251040a11400c1101074140d0f4420304551800700303f0a82c03940203881e007002c40c901140c0548194200055107000070003081000750080401d5814010039428040c00c102d038050840c00034020700d5034030b074001115214042082d40c4c1d48144000d004050180c0d01a400d407a12130300448030301e11503120055001e080200c8050302103481105038642056410310041a01d040301762010300002c1901c10704055440600c0c080c0e00101035000c41e5810a43d03035002c80030704035150030420005515000c0440100700f0740c42401900f01181c1044c1c0403c075446640e100780c4049911441c40145850101c041408114a010344298200704620002c00100c0204000d032500507490f5070000c507610186240c3c100b0044480d01e150300e6000d0812825880402c3d004080301c0d5110400c0c0b8001075451040101c02440d142100003030710751546c2d80780008020007485014107420700614103101c100c64201030003040300380c580902001740000c005201c02181e85010b400908080381c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 467798399 1250 467797149 467797151
    0x9070504120503130905071706060306010c0c09020a022d070329014a04080d02160c050f030c120102070501050a0504060c08040f02010c230f0d031503020d06 69
    0x4a01c081d002242c0e004c064101030070003955072060107203040c1c00c110341d09102d0042c508440d103980703042d400180f102d000050045050002100c4050108807410702d610001c0d00728a1390454071580c4000c0004e560b040741c0841500d40d00710700b41c0b0f4026150078442860f4180c01038a030040090354259501d2b401441010040721070384803180c0d40700060206440c1c000c1030190105501c003c601045007480f0040c04852440a82141e030084507009510118801905509044015203c0200e4946150222652142c0751301c0499161000c0b41c00b440c1c500c41058445035044c026010120603680710000c1000c2485503900f1140e160340032507030440e01824144590389801c3c170303107200060400310240c55042c01e50710102d40c3c41e400b05545000304010072042e480742c040400c80741c0c079100449141540c0d8620002c0c9101c480607051000c2c01e82c0ca8000c01601c42d400c1e0780040000207a0100d440fa200407030554850682c1503251882c05403158020b6004d1180c070401c2c0481440c041c041086078515000d004500200300c03420360f521 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 467799649 1250 467798399 467798407
    0x40b04031d13090309120b0105090601050c07060306080c0105041d04110301110d14040b0106030509160602030a03050a021e0c030c12040806060f01080f06010c02150408060609070504120503 83
    0x340d98008180e00b1024406201040700055881d0080159800e500210000c5d1084001100440d403090306d2141914400d13100c11645484401c0141c8060142051b482c2e81071080345408030313080b5807542000f03040f6090001107aa00300300c00d10054500d070080b0301490004a402042d12400c41b81c680c0100c54119000300030050310704900b80046800e5484a81900c1004140051000d400e0a5188107600890710461100c101c2da0a15649006c0642418465407042680b203c01162040c4070070f0140c80c0c1c1d1004a580c20101c016900e000281d103d40000c408040407078908800200b80900c1c50003103e18500d83c0015842040c4c1d140904040c1e190407441000d411840203015080909000300701d0b807600c0603010b0420b9501d6504d000300c400e250080c01041c03603008001500202001e0b03604040c03801e40000400140001e180d0f1901d00485800d6415180603500503a425041c0e00c40600520041050300c010f0000c0e24070542e142014055150000d40744500015402c000402000084049182070680300d041039a2030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 467800899 1250 467799649 467799707
    0xc0b1801270603021e04050102030313031b03030c08060306090d0c230c0a080712141911010f0c1707081201090204050f03061302100e0d050705030d0503040b0403 71
    0x50010341e0b000032010030b80c00036503090b402c50348000e0340f4090003c00611614160500c80002d440f4080585800990031000301320a007054081d5002d600042915100720083c282241401409400118841c0010074043c2c030106665080c0800c507140f150311718030014007600c15401412a54565244010345150b1084d150307072500303460078000100204118500602c1800e4421040110200380381c0d205c100140d100400400c0300d1403902ca1001c5015421104400c007800c2e541c241a824045901465009100800139540403c014040140c450303040c00c0e654400c4410302410306503000520810090407800304e002c110810180c803907005103103543c4941c403480e08100011844a2805400380c000018440e0085014881c909000300c803580c51000403001480d9500380098110303045482c1001c040c3c00b805640b01e11f10f060b80d0145070301d001c0c0d080c00900500d9685506090180e203503030075405854481d0040f6000111080d11a0054a000e00e070040c1170712a80e6111990184e4281509102c0c13840d100f170f0595803840d6 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 467802149 1250 467800899 467800967
    0x14060601090e1b2506060f0510141803030703080a15031e020118080609010507031e09031e0c11180f07030605060307050c0c010906140d0b0a0807030c0b1801 69
    0x2407042d05c10400480d081c1d04089040c207544c80b05401440c000c1816001101030a68403c40001d00c040345140d050780d4546406c1c0680c8410181c8540e0a80c0501c03001804808055004181701e2060450040411102812181490132080e0038032001c0d03d500486440300e03c801066880020105105040200c00003144140c7c9100c111943c1d40500c6c03032038000e60200310b16440700707010305640b00d2030300e20702040300c1c002c00380d003089503025522102c4045a81c0c40d138101c410507010308411040800c07411100c4800302e1560b400101101d504c1c03507044a000c0403201940e03c190414103900c0b0f0703180c200c086889030325550300745210340b00080c0108000304254560f41c0000b03490300c50000460089a980e070b229540c0b143c038403103414540480a880e44d07042140451003001031990040007180c10305e0b010344135a03954144d400b1010014040070117031958404240c800c0068142c1d000a00c1c10102d80c4a25108900e103907492811605074051840c4001814024130310148080d0b00c2030030841c083c00c042c03411151403c0c4252414075 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 467803399 1250 467802149 467802217
    0xb09100e1c0b18150106200111040504060b120c0705030d021803010b090f0109151502030c1c0e0607081c0c0216080a170714060601090e1b 61
    0x5580c0e0b400140911204440303d4011022900c1c810004040c0706100180b07001540d60b051080c03004204589001c0d80c2e60108107485c1c00b51072050a0003d000c0301d044c441c3c8240142d4480e00c145481580340240009045040c1c0042c0c8608040062198180ba030b070350301180340107a0000c1c0d4202c0716400100084580328038544060404010900280402454503c081c142110303603c0c48040d10503c120010403985600a10b201c50540c0c0c026103002c10f40400d0020010411a040e41100300c031149880010032030a68004080c00c50004a8000c4030384c028107000040c1044040346920500188900c0564090741c20120700a1007514898017596180a050035004401882241542d01215031100060490198100502c2d05102c2090b4900022070f4a0320710219920b0400c050000d100103401100443c02541d548141da05168010603400b8083c45c0341c1c00000d03101c5038212580d40c00300d142d040000c203003111040c600c244156025101900105000707829000d80e80c0041e41d00400460302021040c0054081d40221 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 467804649 1250 467803399 467803403
    0x803030f0c040317070c120f060e010207060e030a03060f14011803060c0309110a080a0b0709030507060c061a1e06040f030506010509070212030403080403020309040504030f090b09100e1c 82
    0x1512021203107046010880585e000104110030307091a5402300d11300c09035180320f40d54400d50000d1a504140d110601a0281000283c015460045800b006490110040400759078a940170090603450741503a5103c444079004010f21641001c8140034194000d1032980c03050126880001d0002e03580b41e5981d001e44203030130380c80b000090319120078004209a040040c01d60f800300b00c40e14a07440b42441c00d16595a6102c101c05880d00340b10700040b07503441d401040030fa0091070300305043e00c4100e9100c640c05825502d04a00c1106c006180a03400707406045006020404540000c104d0411070300c04014881005a04002d0a94800400c01002801d1800c12450700015442400a0860766261600f04032072144010f25641c2590005500a00031032040e0048a501c0380e03160408284544444c1800c078a10301a100c0320380d0700b05107400706100034103410690300c81c0d80101c1076070303072040e226103a000c81076660041e00c11142d008100510b40700c900601617080210040000307010490143c82d001040b1845640340401 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 467805755 1106 467804649 467804693
    0xc0d0e0f01030b120604050f06010609030209060108040515070201140f22050f0102030a0b100e06180f1005090109090e191b0303020c010e03070803030f0c0403 70
    0x740b0341c981c1060840c5c00e01d1400f880c001c2d542d24420406001a48116000040e505220304aa101502d502a00701d40c5a601c5030001501c40340ca018104842901410900e019903030902c58016200385c40984c00400c480e074080c1d001c4e41c00c1400c041c0a0800c0075601c1010031801081880600b50091680c0080801d40303100e504140c2d003842041141c0c4034003540004144408900341c2c2c0c00034443d11004903035142e0075003030548065403040e0003030115503000340c028030094005828500e0f480c01400b801803e140b030b40014250000f600218008961004904041006000c070b50340450f16001802d2403000420020b10b05511781951003010304801e54203104620311890800000c4c809010b4100010944524456142c0c0b4000e500d50100140482c0050a03060140010b8580021303030908403600c06001c6e41c40c544401ea83d105007800020a074010b851b500300030002c009265006401051601641 = true := by decide +kernel

theorem cover : BRFrame.Cov 467625899 467805755 := by
  have h0 := BRFrame.cov_init 467625899
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467625899 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 467625899 ≤ n) (h2 : n < 467805755) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
