-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2433
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:42:18.859982+00:00
-- url     : https://prove2.me/submissions/952863d8-bcab-4ad7-b311-885b20e27cb4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 437410071 ≤ n < 437589928 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 437411321 1250 437410071 437410073
    0xf09100209060306241206030706090b0d02030901060b210105040e0703110a030c1701060b0f1602130c051213120c0c091806053103090b030f04 63
    0x240150102090401011454801071030001001e902000e0a032a016040e88510841c0e00c503003034203052801201100c10103803200940b8403442c0c00950200e4000e4000c0c000c050000036620300940c210801e07240c06c88a403c1c200781210740108002e400091031109590340f160000559441c404004201891317081840392030010200c8075041903041c0c107a211074011440c2642d10a8202c6011901105030380d8851707070190700b03401c512002640130740841d080540450007035030000810103009641c91511030715800007840314958a441c446414082e540510000903020031005408120242d0100c1c0c045100610018885102102c00c00450f82041034441c007141000840000d0b00a21400c1903038004070003c50711012119a645820329800401488403d00c08400d072480700700407046600d00e02812103200304012000000c14109002101150180e8082c0e1030480441c840c6462510080c02c0c0204074041c0c0002d00404107142800e01e5200b040607401c010341740f400800e0b1281c84030020341c00b03440c460300d501a0500705 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 437412571 1250 437411321 437411323
    0x4030804180515100f0e0a0906080601080102031e180a11031b0a0927060606080c0c060103140f0102030f07090f0e0c0901031b030507110f06040b04050a0203060f09 72
    0x1c00b03000d80c005040d610200401c0d59413071192215842d003403403a150140321140481030717076000e0740101260f41c4800c902802145000103580504101d41c01c01c1c0456030305036031702c040c454200c0c80140d07442c00000c0341e032110041a0ac07090210094100c091150001071204a60705114180b140084040b104250b01049040140c98204035002121050344002c240216420000aa10440610514a4039621411242d075802d40d024903100b060b81040c2003450400700289041c00003880a801084040b130120400301d0181d02c5140107903030b4030300e0b005c600400c0c240e4219241e00c288445120804455881015190703200500d00303001941c01550382c600202040e08009001406400d803176000700380058600e80040014014a20203203400401072103586613191a03540040f005442d0784120600964908206680300a40c941d02c0207110b66010390300c20142c810842d4801e0f031103401c00c0404003072a5011501040105192031100798105200d6003c0721540905036000c40d091040440b40b10b20003040500411040040c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 437413821 1250 437412571 437412581
    0x31509010c09240c0506090f1c0509040e0102220509090105060618031203190e010b13240806040b060406030309212102010b060705210403080418 64
    0x76541c1401d0010500300015861100343c201c40b200b62140d00c42c81d6014040340241100a070b2140c001c070075102c961424464260341c1d900d020b541008207200d103c01c07130040302c1000844001500c0581c0d84280c6008040000c00028001c80d00da080440d56080206806180341c000c41d4540c000f080b0080d440600b440d190821104420081c1210b500c3e9040c0300812416039070380d6040700d40100e130341e8081c1d1490202e00000b1900c0c01004050081c2030b0940081806200341104c401603428072008241030050301840c010941c00c2e02c4441306907540204206100000000329074120007400514502030038541c41c3c1d003440c0780b101e200140d03120014540080741480706010469400341c0c2d204500745c0d0188001d91855800070400d00741032280750201c101d00b8102d103003031100c440d03000030340349402c66212031008122168250352030180c0e07117041001d0340c6810001324043c1418070541d002c8641003070242899098890720040b06070030100080b560382c11f0400c00480000c3d10300c0c1c05803019101244c52000d1300f41c5411366003000c4030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 437415071 1250 437413821 437413841
    0xc040c050f1b010c230424020c2706180121080f030601140c0d05031914150306040b0a200706020d050606090f0103110c0708060f01230d1103150901 65
    0x80d200b004103004412040c3da0301d81401085047c40907155040e804100d05110007000559803040d201e88002d00783c0850f42800c40540d07d004448845c42d9104e400400c0800036001d80c950001d40f0a031801002006140142c5041e4003510204c03081800580745c1d511019603000b052800300844000c024000e06591044007044941c0941918034602020503002d19620314005101e0003c01400000051201d00700740e5900e03041c8060100d080c0407140c1200c1d45078041030710071201c00020403440300d80c641692900146950241d60000d408000c20340790340d445203001e0058203910801d017a51031714280140142c2a0020300c00980905001a02c400c5004203400c142c51018200500c43c003018040380e5503070781d10707585900300720f036024200000c0303030385210800300094051107180056600440c1400500d1141c00310302c03d840340c040440310160f540e0b200d2400381e00e9482080d81001e000c0070b1105801495007468000591914060385905900c44c464000003883e0000411100c0403205c604000d12080e4402405609015 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 437416321 1250 437415071 437415137
    0xc040e010609121b0e13170a05040e0603030f03010f060305070e100c02041e051503060412080403090b031602010b090712050a0b03031b0c040c050f1b010c 68
    0x21450300070031020004070360384040c00d40750401d4141084604400e500800070003960301000030a00d0400f00114100090b981c1c11f582000e50b00c4221910110110308403940d80c0c1450322207a0600d41007001d03d000c801d0005180680500c010042e0f03078074010400001e14000c1c0300e48000102001d0905100030b05440380500b10760288402213a100802d681d0b07071039100d00408040c0c41e0040c141003050001030041c1220307550302000c6580c0440e01003074110090300a140b28204505109240024041c107255580c8012900548040a1400c001400724130a1403125086802464003601701c2e92504072400b4982c0c420f58500e582c0c076641d14011403500c0d070280a600040d5000310341c4818a49002480074000f0740c556145040e482d80d450303000a80e000210b0380a10102d013000740899407100d02c1d101c0e807034100c41014060b01c2d0003849600034844040c54a4021056528001c3c0c3d10242071845800b8603a070641c0003104d5111012440d00d0710501010300922482c208404555107840b200c001101c071301164507065115001007 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 437417571 1250 437416321 437416337
    0x140d030606020309060307080901090c0b1e041a070807060609092f010f1103031e0112021f020f1609150b0301060f02100c08160e03101802090c040e0106 67
    0x61707649050540c1c0d1300a080341000681740d40d0340c0040c24010012400e00408044d204a00411003c940d48040c1003800300380e41061624080386c0d015003816010f5407282050010360300121604004104001d002214402e03040c0302c0c1000700d10780d14030041d20043c0c0c004141951342d43c031992003841a14070b01c2441e00c0b8202c0c040c581541d0340070806104424481008181030020030101110341c60708c100b0644d8250201002500e880c1d0400c1402d4600b51070071800305010900000b00003140d03100e2184030b08014141d005001100c00c6000d9400180032102014508083d80103641750180451410300814a01581d09030520790070030706001c4104100d0313882c2a000e20590051a000740481800002124190f5083c0d00305260402d5500200f01c2c83c0070000000316400034101041614041e411271a02800384010a00703c4040a01c0701204407400d000c001e1101d50b041e406010511410101a8080b14504070a12102c04290038680c010812a20082d90015850100058100000501c018541d40034110b0381c070700054 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 437418821 1250 437417571 437417587
    0x31e1e0313090b010f0806060d02040b030108010c051201090b0a0302090406141e15061909080705042306150403050619062714041406151809010603140d0306060203 72
    0x803e84052458907000c6c00182004640b0070340c0c0e4001928001c0c0c00c41041590b03079075241c005c5d41c2c41a401c20f2061403401c0d07090810251801340a00103594140c68182494003081c5e1030f1911480180000280c82a0000b0124101201686402c2441c03441a4058540400d03000620311b54040e01100007030400c01004062405515080501e625154001c0c030303e00d241c1c030ba101000328002201d904c524141140c0030110000d450744d40c1c0d0b13080b40b0004e040f100b04405556440340d8070b0040c0800d55680380303c0744449111404000165000030248640c0001c1c016040e08100d40d0011440d18050f8030503017054415510040810501081500f4184400c030940788080c081e162901c00c401e000410b030404c4808007000940e9030308034162210361191401702c00507800d54400f402c041c2000c44610f1205400355989000380d40c0001d00d0380b60501000b503800f40000d01100c4412102c09440c01c030150024003c1a001c1d501c403e4000702080d0341420b0180c03030402075005424105600301d000340482d052a40302d84290f41050012038 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 437420071 1250 437418821 437418827
    0x40608070501030b0612070f0206060312030105130905030307090f15080103030503040f0519060c031a0f0d060203042f0303160212060f011d0105031e1e0313090b01 72
    0x601210002c0c03d0109030b0a2502c0005002c034024803c45810009240c0b04010a055200302c1d021900089030302900c1040e1994402d158a07405040c0c020b4540a40030001008642060a1071008207a004440003d0a2856607229070030b640c016070f07201c000140c481e80d040c4000c0c0440809000141496203481c0400009250013800e8500144400b030b05004c0040002400c0c0055144060070360766020060300c00130b0b0044c04c002c5c091108150010b0728450302d440072080a0500a103d110780f40482501c00340c0a4080700f804000f01006060440c80c5c00003510308a00000030385a00185d07010f03a10070041d00d40048009205000d211030180c5000038a0380c3c5a2184000d02c1d00d0100880b04080b13082516000301c51854004115805040d2030240e100348076001c03c1041202e03021015a050313a2011910741041c07107188442000314413080c05803a40c150400188400310f42001601e02c142803c80f1021703182002c000301e03200325005140941520b1035402c00103164a41e6107884a8030130251040080170030030201958002 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 437421321 1250 437420071 437420083
    0x607050c0607080415020d0f0203090a05100c062f03040b010b16080a030507020d0306050a1203031d1c031e111b0a02091e0c0f070c06031505040608 65
    0x240103641c009229401c0c4002482164040c1c40703a07242d01400c01e031401030020b690320b50100d0402c0016155007403443c03404d4804030456481102c000d02e009500b50500c0c041003142d81e0b48a12020a00c520f095a141c0005c00c1405940c40400c1c91f854000c40040c1c901002940c41d50740f210f81c0410044040041000003518114410b0566041111260701e405166030810085c500308180501012800700d0641c2606031302d5000390b0b106000c00c1d82610f02c04c541428065040e50307541d00940e07038400c8560200b0300480c10b00c2012481035900a1501013045d06154a408107181d950b80d8095829400110080c8a41e241c52001d4070f0b41d2602e28501044902c855403440060407401c8403d01d0750160b280d0010b1130000030b210f01034850408140c500c1e955168060748045641d613004400403400b440080f0001510016860b07500c030420812880071120590300c1d807020010b55405250805081c3d40c052000034081001e4401400180c03155840c00550906196015400c401440d40100c0c030540c1004400e0001400204070 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 437422571 1250 437421321 437421343
    0x602071202130501080309120607090909020303210106030c05131422060314060609040f0f170a030b031c0311042c01080606091b070c030c14060705 65
    0x80512044060701c00210094990010006800c0c00c14001040003103020000345981c58049840281c80c5500c20501500c501d0102d643d1004900302c1c010400031615541c000c2c0c0d000610050540749440401c44410702d02811251a40c101c015036080140070706500351058450203d80d90070a5400c10220b00300c0e015010080f4006c09240c03800c0f40c6090341039034503030111072890000103990b034080c001881c9c10341c3d4004114074030099540d07080300c030f80c96080d059001c40d01600400e0050080c451555070f58030787c00c24403854284211b40761a84803501c42c1c007290400788000603c071441c181103540c1e0b0000704001010390f510844100d1094000d50481d012809046511003030300c002d541000302d4490281c020a91503402664410742d43e40704070890140d54000300304140c1041c040c8292402e40c0c6a41c035090740d640d88031000c83d49072ba00080c540010440280500441c01c1c00740740c605407080c0c6861815903c4501c4014158811100c0541c10340c024400c98000400d040c48210301600c165003031280743d40b1455607818411803 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 437423821 1250 437422571 437422589
    0x609022704020609040e0d02032a07030b04080412050a1505060a091a030a080d050f0f0a0f020c1c02070501230903070f0605040509010509040f030807020c0307090510080304060207 79
    0xc4c4940a80d207458001c0f4900c00c480c0c03019551081e0074100081d44070f0384041c0e082d00f03411a80031100029007500203002001060000700810b40b140c2150383e0000c1c5000060421346c6c21441c14000081d01c0d901400c50020140d00c620301a00c030700322003490540ca99503848400b0f40318039030034002005015200e11070482d04545221001041c41c1e41c9034100c00944420000d011601801005182c5050041c0783c00180400201010104180e80e15846004051a4141d5800300e03002001c80108007140300765000100a40e40900c0014540381c0d088104c1494408840889030440348a941c0d03403543d03640c042c803082005000c00c0c01d00c0c10710034166105003d08a41c0180f40310340d8107000440c15040e6605d04001d20000b50900c400b100e4003043e26048090001c2d007080c03062a208400300b07070000c03e040c00c094100ca4040c80d030001c8050311490036658141c0d0521001006002144549142c3d1905980c0030440a0020882884000703224100004400c4c04440c5541014195500070441040755035070000d501000c41e0205c40c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 437425071 1250 437423821 437423827
    0x60b070b0411030a0506160e03062d010e09060123010c06110c0f0f0a150b131e0b0907170702070911030a0b0d12030f020c070306090227040206 63
    0x85801040b400503034040c9500b40c0310b454801d10030000001100d03801500f8070480881c2d044442d141c2220742c1d000303d09040340c041e00604040b86c0c403000c82e01e8a25050111281050f2140c0030203a00d0360a001800f640000d429001c690140324060105019260140c40c2360349420240c00c100100c03144e865040807615030704200d81d40c1188401c0c405550300c440190700501c141c4507901d194452000f6622000101e80300b4480c012040400b5a5400008a244030154402170b120818100d01c080740c8001c203180310301030b50408810080d10721010802c0c401c90855040461904a14007540518101110303001001c0c20f020b59001030500680c40d030080c00408803d0304090490030300e9134600c8812424158154440c0f0041420b2184450030010010040c61241c80103100411400f03c4c0a4100480d0511f80382014240d6198900c3d038105852098100c001c0c03c031401034026160890501441d85020b0050b072003964400d6031401c944045180c00300c1c107001c880c0000070b0040d00319070200404030021000075100a11481d400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 437426321 1250 437425071 437425073
    0x618020303040605130b04061e020c130507182903010506040b070f061406040c021507030b010e0a090504020301050c040308040e041a0901050412030c14090307030b090718060b070b04 80
    0x10502c20030161030204100c6c1c2d01d4590740c00e00a00f002845003440c408401b02900b16019840c40001c604186c1000100740183c0310415001d050300401000c0c00c82010404a18202c41041d03011504100c01464803400c3c02c0303044100c20b00308181c100d58500040c4490001040100113a5956109031001d03602c0031000700d036890103240340c141580d00780b50303070000c08081c100b4100c02140e224000d109845200d040e039082c486104004402ca80700c090500880e00030030342220202c0c0869110b17500c0343d21180018144020f040728001c00040c00b84415030701042ea500c4e1110204821800d0a0041b81d4100b00114030030360416085507200f111900440c003a06005441103c0007500340480301480708034200300e110740b202460400000503401780800311402c0c0e1302c482440b41d140010511034810068400500c4e500e42e84030f130424900312600340d8840b26610f68140320320480400407943c1d0f140c03040e001d5080c60000340b136051701d801c80440440107200000d17030340f891401e4000c12240850100301d41005601216040304c3d80d0303072 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 437427571 1250 437426321 437426347
    0x81b0301060f030c0f050105030606031305120c0307060605062b0f02160303060b0c0a0b060a0510090e250f141c0b040b1005130b160618020303040605 66
    0x8035512070001c2d42c0d8516000001e0101d041810400c0d14064048010b4141d207400055600d84019200207400200070800212108045030400b680b1a202d4011368240c040710b0f0112100e19080080b012002da00b000484908202962041d48000c00d001c0e5281c034100241e070110815004801b42d9021025101000c45814105650703004070b000101d8010215200d00c500740c10800181181c00007100403a00d000302c041680c6804005455100c00030328000e014110103030313641041080c400b608c0c2c0d54100c55600c10200305503492100c4c203040407046944d6480d40c503282ca282100344900141c0080302084d8801c905d000d0410f0540c03000c40d90360b0737000d040c07039080c62820020448120081007003150494002185502290401c3c480501040341602c0051094801076000c0108441380c0e080040c0c4c1c410f6420140c41546401000a00030b00356200c0084410b480d1b4411b486003881d4050380c15410040304030301c21002000007074429510a0300b1035010004041c04540e0100c3e6907849180100001c0c00004100c3c8044458 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 437428821 1250 437427571 437427581
    0xc080a091a10121103060f1005120a05100905070e0c12060d12030204150512070c051606020c12030309070e0a06081518120406030207030e040903090618081b0301 71
    0x60f01c4100d80201c06041c20100c540050645289110307000d4000030070040301040100d10302589450b021210118a000201328108407414203d078100d001d0a02403402049046c420080000510701e00440d0104407072404905110340c9803c81050368009400340324000031000c0503076202950116480005c3d440701c134000751100d0418400106528a6100740e212001da040d0050003c80d00e1084102e401d48460703400a550074054020302003822040800007c540c20321956003040c0250055003629603000060050840b40f0b500ca801002c0568410350b1085c42d40d003010342c41d481e11900c55102642c21403c000900e60b031600001e110712080000d510003c2103409040f64402d9008001d50011104c400030002060700403d0b00031148290a50000c2d04a82d1404070040b900302c014081c4002100d1400e420b00e0000e500070b401c041070580070066071020f00349650f266427103005441c03406500c0340062180b0f0714000410f5a5000719905913051403840d010400041d000981c038007180395000035a11056a40004240106 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 437430071 1250 437428821 437428829
    0x2030d0209040b03033601211104030503030106140c100e1903110c0d02090403080c040512030c063312120d0b010e0105030612120c010c080a091a10 65
    0x5c00300041803000429641859440b0300b010304100030b03610411a2035030300300014551255021845410000c0d800c0114094a20501119a2000505c60804403003404580d00942c200303d80c50743c0f00200511450750481640300c240e0a2115500349007a0740407107a941c581c002012243c801c0d5488861f08d07110b000d810f1101c0340f0f00781d00e83e4034880c00001d502d0500030704940302c6403841d007110f00424001c0001807d20005030500c00e42c000e0801c3d08151100c7d0350485100c1001000380c250402c0610002c50702d6039650320f03000385090201000750b4540150020007404c096000e4400c0096002d45080b10302d5030790f5a030084507401d020107402028815044004070b848103110080305c200d42d00403000c1c00380000c0304a0b00500302d00c441d50502040f082c5e90940040d5240340307840203120b02060701400028107a1608100c1c40710003070101e6055440e0701030440c20085154111aa010070340765160f400e24130307440344e01100d03095102e4800c1c1401c2c024840c0320784440000c0303a40c2e030750324000024240c80010340301480785420000134 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 437431321 1250 437430071 437430073
    0x304050a0203160603060e010312051c1a0108130c0b0a03090203010c030606080106020f06131a0a0b010e0402070c0605130f03050c1e011d04060518040c120302030d0209040b03 77
    0x1550141c03003c400d6042c081c0918804240303844004901b800d10000200e050303a9001c0110125001e01003000e0b1425003001380c10786804100b28400e081c05580764013941038884160b2043c20010482c00c000502003000041c100540241d1954565001c0b81c10b8001d0700d01111030580300c580e030710580b40804402426444601035015803e12081900450740341d40208104c455607521140d5a90300c68030200d07121840f2604005566015001083e8181014650b0580040c4942d082103240a45214480d015660454a000b010303a600c207018156075130000141022030008440462a0183d0b80c0d0f03a04161071000c0c01464100f0102144048201d1010280034000e40705808014004903504d00d88640d035200388824090080080101440c0203410304000504400c20584502d420b0386800d040d2080d4410308594041d901c15100c441c00075041d25803461004003199208003641d26860103085c4803050010651008403061180c1e00d451000c66800300a91390100344980016986401100c0000c003d82513110225601d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 437432571 1250 437431321 437431333
    0x7030605060310050f04020301051321050412030918091a060a0305100603050d0323250801150207051008091615082202041e0507050403060f05010b0f0304050a0203 72
    0x185d0652100c1d4503220b00e02c00c50080c0400eaa490880f03086100122000800546241d180c0702d5205030a5511000481070a14040c0d08007581c8107501c00112500160560100b86000b41c140030245803d11481840d031503600c404c2c081c0d5016a40d4bc0c200449003043c0080c1d000d03c41c030010580d0381d0381d40e04505c6c0c0296000402c4031250078038482d06100a003071500c000ca5841c0300359a0344001e950b00074054010032800341208100641c4080310a0b402020008200d0b862842740e400100041c00038164007201500310542d90044a981801260044102081c1d00202558003000080003503a84000724808403080d10718050301c150700c50a100e0f518101d0040c0c0c0034000704140c4a4007064a88511b494030844844981d121200c0380c4400c1c0141d800c00e6000444000c1c40075101c5000000b605180d004a001d1032810140a2500c1418a80c4001118026510507001440010b01041404658010f002c50351098060402c0b45515100d807082d80ea22a0203111110300358044001018088184011000c442c4c024068070f031 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 437433821 1250 437432571 437432581
    0xb030a0b090106091b030b0315160206010e281103040624050f120a02120705120d0815010e0a030c050406060212070f14070303030c140c0703060506031005 68
    0x3600c66003194416a40c0d840c20000003130b500940d00860382c0000d00044120410b640303420049018111413212540c15214828041e80c1041003100f00760300c40c45004607403004404850900034180041a8003810003543e182051002022813903100c2e102640c890340c122002c44400c0516440540314541d00139104160104c01c001c244111900003140a0f20320044002c1c0260504034000c90804003400303010741045200c5009112b0381480e560000405c04058105c03800d80006500150129542c1d42c0180c03020340100a0400103400c0c100b1400c40d108500c500074215102d12101e00034120a07004000580d1040c0360007070003803c3d90140c0b40b41444200b001c0c104115180e10b0b41000f10b48100d8034814180100c0c1b800d4400251760b44041000300c0000c089106142c44c10400361900d803424801c0340c2c829a440d250b5000101544401001008019072281e00c000c00c410803c5140508412880780070406000e1040000c000216004a60101a40c1d4810700008160b220600424038003002040303005181e43c03400c803c1c05 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 437435071 1250 437433821 437433833
    0x1510120e0c04060510022503050102040f05040b091e060a0306151e080703170910080f010e070e1e04020706021c2016060c0e09070f0518040b030a 64
    0x74840c0065805005465445080c02000c254060003c001a0410b464200e0f19031880e242c90071b192245890311846041d02d981b94642280d210764058075850313400c0101048641058080c04aa500003100c0c00c0c01240b500041d404400303000c040081ea1580d036210005061a50b4010a0361301071900403008029084880e0910800100d29000340304c190115016600c0341d4944200b0303001c094030700e90405000c000303166607075581508101c2c4038410701110381404510003540300c1030803092000d02190384441c01420001440300007040c3c1038100c81072038415001000840754010603070030003a01041e10340c0c003903901e000303580142c60010030f100c901d0740319000041c400c0034040709070082c00f82403940680b00028210813240000454a04004000c04038000c42c0c03110030801d03983c00142c20151b460711056014200c444d510b0714212041c184200000c1684207035031100a08155045a13484211802e000c0103420410380d01400c03c0c003440c2c02c0344d000800c03800800c000711b0321184c000107901c850140c11203840360100e16000d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 437436321 1250 437435071 437435083
    0x90604031101050108030a1809090b04060b030318010e010903060c0c0b16020c100507020306070c0b15090c070201090b0d063003120b120303060a060302031510120e 72
    0x203800048040165030240700040c42120304880707000000f1464480100d07010380d2118156103504245940300200001c0c66005405465081d605c191102425880c3c113280000c201d0303240344407a500a52092100312040890071000350061842420a03010111990004803401040c50300000c00c0b00707042c0310444403480d4000186804042c491800356a080c0e0b18103442107003076000c1c00c102c03d006a001c8041c5a0a60810601d03042d101d0300c041c50420b252104540100389415000d5800c0300004e8114020740e0f0034411510390081d041035100b80b0303159421141e60006070f00140701070004c20311044002498800c6a0168800400a24000300601c0d10740080d40140001008144070b000c00104005e131603c60000700f4400d403095605500c0d40981e100c82c1d8981c40407140d40c4628030905003042e0391000210081c0c0c4d00c114002c08c50484000c0110f0380e91408500f40b01c102481540000289070060040c010a03100440d031012030580160b441603802503054404580781d00c050b540703003148140f60a80001d0031800100302 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 437437571 1250 437436321 437436323
    0x30509040c0e0915030a08030f0105010f0203030405060109021c090f11010809030a032003091006140d060e0109150c18030f030e040e0706090801140f0a0b010215090604 74
    0x1c0259031681d11096400c0d15542520383c2c0e1007040e00001442d120049070341410404800b8003126110481665210a9548150344680d013072507028004110075a484000e40c1003e01c428409141142040c0c2c0d54156212018050615185d030007142d503a11301c01c2403110034001486000f1091100850710300780400b200c88484400e494040c403040350070300e65501490307501c2c0c041e002c2d8000640c07508044e84401c500410025070108021480d544103e885400c400c409180501500307409040d01400c5089850308541990380900d045002c101d2001c03103113540b283d2440d02d1554001001150700d940d1720951500404510500402c849102d00d0441c50000280c0c0c13110480d00101c0d06c0700305900c2c003544c90b400100c1c1030f2440000e10a000140203400001d214030318003078211502610100e8920500c680641c10301001d90007078000950401020406040700740168142101c0400c8034078003600700a00040110b0340c005150f841c80e191903407004070300f42c0d10801200d4070403804900004d90310f080405070981c03900c1c002e4030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 437438821 1250 437437571 437437579
    0x112101092a030515060409060903120f0b101b0209010e010e011406030402040b240a08011203090b0708040315090b07110304060f050c030d0606021002041505090418030509 75
    0x718403600d808800e0300440a41c0d4010005200701600c42d02c00007000d0400078005d40d0805e0700ca0302c0c0b0900080c00c030f004503c5040c0c4070340c6410001c0440c2200b010100c03544905200c100c1c905140c4804250348030700c504820300010505e09070f20894070301840189070140e0301c600203401400d001c1c0009001d00f14000035a068821120522403140d913030784010400348403100100c80e44501d04101003001860f00340d00489242c40d02401483c04044040c9a450310580819800b104100c1c00142103811207a11003012805410310300e040c0141030b101c54600410b5060a07003d403403100c400000c1c0328401d002943c01514000c5070300c0451314290706081c008120250140d0f00c0100d405440c0d420200303c5450058038054500034080c0011800e0034589241194034840751030b00841405010060321000040c24401410040c03d501e1000c60310b2031601c1e400034500700d088968101840e10600050142d200140e101001c04041486e1103601e03004d0300e10014004281341c41108919014000a000170550004064082e480040b5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 437440071 1250 437438821 437438873
    0x3020307090203010f0605160204060305010506030c09010f12080f03011e05061602060a03020d0f0c020c0909060a0b010e03010e160b0705070e1f0609150c11210109 72
    0x30420700241e000038000c1c04c074616001c480504c42c1c107101303401411688050302c0c0c4030410700d01180c002c101224406d800030f035602c0e5101d104000c1203083c104a508440201514480a190300d41584110327003101c20b024402c05c501040d403842040c4000c200950700343c2282400c55a0f03480d40e5910008001c803001d51040111102c04420000b59882e0440603140002c02040340c0e21a101416401c105040c0d002035110410b041e400e20083c401d1441c14482d496800c0b17821440010110301d03030030020303182555001c0c00345e02c12101c64081069501001ca03286400c6125050042081520000180ca00100341c2640d15003640c6405c40441215400054000102c2407450041602d182c40e181030900d24030940c20043c21590100c901002100000044151302040b09550603141041c041c00c029120640380d0721080000340320307600502c0382c0c10001026045c2c0e40e085040c150340c0c07042c05503140070740c035405030042034400c40e05840710000c443c0c145503001c0c1000c7c0024000300101c54003032602c5241e1003051012294112180 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 437441321 1250 437440071 437440079
    0x7050706030b03030715110403080c06010503060106020a06050402012607080117030f0309010222030506010b070c0e0411060406020d090f03170706090b0a090b100e010b09010504180603020307 84
    0x2030700c42c41030100e03030140156190003060b03290300a845050186088070541da0b8030000c0e9490340c1050140c00a0751107540c41c1542c42c00428811464041c041e041541f007500260010080c49800198241078180c5c880b00100b81540c1d036000581e405040641045120102d10045144030304500781c2d00c0340301d071059480b8082c40d40d0b02c600c0c0010540c54640300d101d19590040cc60f803205001c4000c040c43d80851604000348c07902465a681c0c210455515600416082009009004214050020381c2c058440e03c00054201242a00c43c01e031520707031600c107003054450b030000880c0c24044007806c0440741c1d41d405003886607581d54a080095590f044105a0f90019a444c000410b00100d0030b0580801c90b50810400b054461341c04c0c40c645020340c0003100c11a1490364920605000640700c0103810710519080900044607aa84e007030154580000a100d2100b07040070140511100c01d2074403100d815101c000345865102c11104005039802e20454024039048900e202201044d442035811003400d4a10a40660b0052541d0b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 437442571 1250 437441321 437441327
    0xc09040f0b01060f02190503040b07050c0a08160801050f0c0d020c010515042d0c180b0d0c030207050607030b0d0b0114010e011404051509220e0a021e04140c07050706 73
    0x42682c007d10745e410801040002409800280c640c15001c0c60998080c5910a400100010f0716540048d1494005000402e1103074815800c10b8000c08061000b0308c1740e0b1501c142d1030181c0c101b0050211501000109400302c480e261541602c00c0e64201000811107403c2c403620035034000c8074030020107114508210402c0d0040d03076180c03610104c800560781c81070f01d420b001c00d08080280110110001c200003080c0c880008001030315544400404110036100d86d034103002c0944100760780010100d04181401004a90000340c400a200369228146280010304800c2100c0060090780c82c051001d02180d01802c000705000d18900d800056180e0262200c04590300034a00540b00100041c1d01804c0101c8180010406400d003480301d82040c219441020f8541040100015103c40d071116200922101000da0740340700a0380b610804000031103141c01803c03c0c85043e0700080f850150000310120034842050980040d0b107464209140040030300340500f0607031034410040942071700041019a10f42c401e0000c00610300380 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 437443821 1250 437442571 437442613
    0x40605090f12070b070c02130f0513030e0906010504120b0610030509060f0603120c010b0f04020c1039020c0d0209150d05010f0623030c09040f0b01060f02 68
    0x70007007404a003003d609880c1e24070782d424010801c00034054000c1e8003100698502e003152480c001040000100c1520b091151030440303000a03d20413100310b008510303d001c02e07007020303981d0308464040b1506c07446517a8050048480b40a103522810303030441d07d8135044003008080e18049100d00410b54003800800002c0e90110f0907510280c41000140e04220301142c8580f009080f902e90008020b01181d42d034124144d0300703441603440101c402113242d55801c403600f81494a1664403d18001c122800d50500240d440c1e0182c0301c8840c40c04150b5582e585441075050301007500d4220030320200d000440703402070b100d5011380c280e0000000007903c014040c00e0300c01c1140d46040034200e410749401909003101a9101001441c1c0011400116079004245207810300000d034007409031354002e0f000480c000c280d140c41c0484020312100d100503000e110110132108403181d902d0004400c0390507901110340701c0041e203503418002900042804003404480301000007051003500644400c003546080c0c0d08440590016000f0808552 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 437445071 1250 437443821 437443843
    0x10e07030206071509050d0302030a0b010c0506010b1b03040332060115030207140106060f0201110d05040f0807030f08060d1a07030e0a0c05090f0702070303030c0e09040605090f 78
    0xb120522812020a40400d54030f00c03e545181070006440d0240e4817001c1c5445003982000c80002d8000040101100c401d0180700341003403082c01e109410000681d150b42c2c031000705014582c49a2400b0401c407404024030342498165000e0390301038a035106d44030b040038100f501c146d00d0100c4100c4c000300c1030000380c08006a40c48061006200241032aa42020314400744c60040d01d0000f0308140e001c0c030900011811844040303442441e504000180e0303520b007031406064000c044203071030b0540e4076020041030784001700c9049a1103900c1c108400500b96440d0f250000222601140207017404601280000425803c16281a01480395031512405035603840100041442c0b800c000070449007a000c0151409071295030301c0c0781c000c40c00741004244100306401051800942401c250340d030b00d24000c4100111700345500d4540d040410306c440301000e450903007401383d038800d600d1000804041c0d030f48040110581c810502070540c040d004044140b281498240f800107010152a9080719000b428200c2c0444580050007018407 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 437446321 1250 437445071 437445079
    0xe060c030903041401170a0507080a09021813120f080c0c19020f06121501021507180e09030c07060801050d0b060f0a030b10060801120f1a0108010905010e070302 71
    0x45802c0004c600010b034203009403117050014410080c82903441c80108180305901c00c2000040c940341c07181c0d0081c0008009014046014a080c3c1e034030000d40c90740c8009c1012602c50f940440c0490320b51510b0b00003d0410a100601000084204820055070000d42c2008004040d901d4000e1750700d89241c24401d038800c0d1940a00c4c030354003030100e6107c074030300055113a040113000804804501c8501d1020030341540c04a200f0040c0c1d000b000c000c001d4450096a96200110801c0c80141440c100100b1080390281d0050a05400d01002c82c00c46c101d50311803120b0590191440604a452a01344020b0103592600500c845090b14007502101040c1ca5128021007412250010600360000c0159201c5e482c00c7d007405424580c0081e045080520039480b045400d40044d445040f581c10030f46800c2004c403950311142e81050041240f207000400841d02ea00c0c00700240e40b50404205d10f1000704034034200d001144441d024204102c0f194000080d48501035001c0d0380c000340120000d000180b09002d180741c441110307000082d44 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 437447571 1250 437446321 437446327
    0xf04051f0b28110d020304080111090a03080304050a0f0b010501021009110409020d0b132003060a2a081605120c130e2d04050d03051b0d0e060c030903 66
    0x1007088180c001c10159181002e00d03c8484481da803034105407034604000c0143e0710000b002c00c0413540921403240508514100701d41840390703010009000e104644006403142601002090030700006005100c54590b0141c81c117400144903191015103100d007441201e0250081909054032010310340603090405500100ca0004c440c8c40508000003071200060507a00711942515420025074001803045c02140ca070b1000e21007040d03491400b001c2e901000482c040e40e0151046c11490746880000300c2c240c11a100c91030200e51011042c0c150046618008552340048590000c4055080e400241003400f500c80d10b9041c00d202c6213540c0c03058419124590000280e0521040005c20f5000e110014101c9001010006120f20b5907075100e105840c0300c103440200d000c402656443c4000060903000510034240040e0382c0c41140b41c03d846507a00d586d007c0d0900400d154035403000400c1246402032440d070440020f22801d8480c4003e000303c1000b07100c0d80500880c21701c601d00c08500f407120044107907807040d40404000d501d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 437448821 1250 437447571 437447617
    0x30605090402100f0905030f0f01050c160b07111617010e2808040b0a030f111e0405060403111309051e120315030c0906010c110f04051f0b 61
    0x340071341440f01e811300304052150003294540c2d0a2110400c4403841d40c0041c07041c1c642514001d03085801c094501040d6040400070380740e05110380c510b40340340340d0703005968070280d50340d10001a1401d101d04500c6140c2402030f03043d1580c1c40d0300c0c0c030700100c0705a41034048000c48d00480e00140310300702c41c144100c01001d42e02c0300c1815083d03110344083e07850010031211503441072068540c0d240c450b107810540000d682c60708041031203540d00c0d9141c4101c0003541c513059000d01c030700c2c0303c64101c4010a100301800c00c1242c0c00c0d040c101038600c40c00442110010311011304466591903490400c07421505090003014403800341c06581100d0b00300c41d401144403ca411101419044a10301c10701020310005994401342401102403000100010101a5224a010804034192482d103501054240710300031500501c500015801d10405981c840c0314110820740c17004003421018242c1c800900c9002e0080840d03540141803200b081458070003200c2040d03415980c414410990754444000c1c0c0500c0c011a504030941c0d04011420039 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 437450071 1250 437448821 437448827
    0xb03030f07020f030303090604051912050c0f1f0f1b0f0c020a033005030123031618050405030d02070f0203120c1504120e06130f0603060509040210 65
    0xd560703480181050f40500d46580864210b130003c0741c1054854110508201c1407000900a540350801200c06d402c03d543c100f66a14044220610141020000f01050018650900704400010446003108481010b0036551a200c1c03080c04800002013130740d05160f070311045402c040c000c0002411803079544080da102c0c400c00031a8940100300310f0f042003100ca513603001e000d40ca501034030002039401054003010301c60b91000791314a040710140301c645900002d29000c03071019a1000903681983c2128180440007030228110110080c254441d4a40c180510340c00503101103944099682210a140344000601c21520390000480c0c1c070444e4040d040e80c008116035080c44030700c1d600802c42248108464280743c9aa6004031b1b1510340b520801107440c840020305820619410000910704100980f07124200e0324080d80c0b8110b000800381c43c1d50781401080340c440d0903956036003410740f0002465079a00c002c04941c0c41088404014140c4112008649422004511070400000c52482184c000e02002c200005880e012 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 437451321 1250 437450071 437450077
    0x4060f0302060319020a0207030b130b0c0c030c030412060e1906021c020a110105061e09040302031c020409231b190305010f05030a0201021e03160501050403080106030b03030f 77
    0x1307408020302e8140c80c403c05042d20207424801c03d5680200145070445ca88021410b0018200303142c0b8140c101034210000d84441e40031688400701c580c00b0358840b4010010399145000d02c1c181150302d40400300380490042451740c071040b2503900682e024481d241c10b540c1e000da101c0010148540c02c400807441d081002c10040c1d0001c2c04138003505070014101002c80b24110040360040c1c2004400201c2d250b00094118009015998000008540c1c0c9003000008080070f000f074040f1a0034580c01589510f00003820f1600a1007541c44d59072588402c1d01c0da4840781c040c404029409405010720310781c500090180c00d4903040320b003c0d0700028201001060381c3c841c0322420302d54002110304081c0348070301005210702149203810080000d488588002c122541001d441c80ca021140b0703005540680e2282c440071005d030381d0009082e07a440e050050700301d003c494500a224114032400c0b002000000e1843c2c449410042c055100c2441140a950750b0411a40c030b540c01241074803c200102c0364103074024404525810300c0d100007 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 437452571 1250 437451321 437451331
    0x5040618090f0602040b09041406030a02120703020a060c1a0709050f0a090f0605091503030f03071803031d0a080d0f05040e131412041403030d0f0506010e04060f03020603 75
    0x10403016400c083e070350b03201642c0c07081d00142e1074003002040704480c909050007880c00c0380000300040010351610307001085d43d8005064002c0c0c402c0e0b91000700a2025881885001c02640e0041d0144501c075407100d8020741340070003c850032211003010302e05110000c00060100390280982d5aa1346120504c1c0ca001c100c80010316080e42940012803030310010702e49416200d24880914901c1000c5400c5240100300044268018074030081800356411003d419540841110300403540f1701c1c0503d4a0b9201c2140403505083c50941116503040c01d0403011090603040b204060301005500d8655800700449014840707141c46a00c1150055488041c04041d814021030140d5240310041c42c100f420603a40d150744110800098609081115182100707806011110403e5600720032201c000340b880604141c1140880d20030380c440c40d45c201d1420901410241c3d010b008407105000301601c20720954a100040000429066801c24007082d500f400303070685400d2a0090300121442507070941c06072480d54091003410303071000f05 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 437453821 1250 437452571 437452583
    0x506150a0501141b1606020a050d0c0c170604151803050a050c011a030f07030c0506091203072003070303051e1303150b06042103030e030c0a0c0504061809 68
    0x42492162010440341d44d0000a184000301040040c0c070390600342c60700c2d95411040440d000341c4c0c1d0407404200c00207042d00401c0001c1c80e14031081455420030709000a042e801c1620b4107850044039907040d101c0040c420f030082d0b004813180001110300c40544022504d51840b000700d80f00722401030742c000c01e02a20240c9000307410743c104140f404800320311980c00c540c03007181092510f031112000c0d1041e07810100f011303003440d01d0254010000300d411922114003500c0c403881105e03c29100050032000e00c0e00c4841401546404801c222920740380c443c54440081c00b506140300f04c004400700c1c0c488819183c0040c100302200c1c2c1544406103000b1044810f442560228246584001c10030014036580141e030075080350045001d0390742215650241c802e64010385042e001c00c02d11a020510003030141c0b80c5080c0b003c4815482606d1507841c0c0b9601e500d1b09501403d4801e5aa5420340008180303103c03084004a003132100c048c4141c0f0900072403904c840c10081111454040d1174415003000d82c0b000100c1840f17a11000040b03000305 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 437455071 1250 437453821 437453827
    0x60a0806041e11031902030601020a110307270c2604110901030b010f0503010506060f03060d170408010e0d1e02030d0921030c0e0d0206040906120506150a050114 71
    0x246820141e50003e20100b1201800000300244080d5842c1c2d0550403140d00381c020f40c514108540000c0d540e03042c0a0015044030b850062028141c0e804001d0107008140380c0d0303a045e030640046140d4100e044210742c0315152840c1490302094001e03104014050300700300100907003501840480704800c50510f006000304c0748405400700264072551003442aa008521510800c2c40c1d940c14074504100e200d0507a0f0109002e60706200500c2a10795415040d40c041d6120340c240692640d175003000182c121800b4240c0605046d80b034005980351200f403c0b0080c41030310304490003800b030f2050501c0c609655460b081c001c1030016548401c1c103004000c41420300d06840e060340c411241000d000300022403c030b0f550a030b0b08131214400000407441e03d07603580ca0f0350306000c551030034100104244030308090070345002ea91510b03100d45c152142402c2199110b2041e03601a108510013000007135140d02a160750b10410800503901c074403640c0300091980c04c0074940103c00b2003016280078030392403070080151101030356081c80e010056414 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 437456321 1250 437455071 437455121
    0x10b0a030c08040213020c120f13061106070807120608011b05040b04050f060409020a080f06010e090403030f090f15060e01080a201c03090617010e040609080d0b0f060a080604 77
    0x41006000035006010004ac1e03504c0103026140035240c015840385090114108221440000c0814695408000d0707041295066582032821038401c0e400da03100c0b840c160300e4510702085400d015400000c0800c46600740280700c52003c0c0c41666240558425194030100400050015003000361004140d11805040d040c1025200d4500c0401d0b40c110210082c0082c00d0b840c1007041111003603c445401070820300f440f01040600c200414084d0710020310140505444500502c04800d090b07005410b480d40100c0c2500b0300d5801c600d440400300c1610510200201c0c1031940200d5000005243d8604842031040208401c4a5540e10110031030b4660341841c4542c00011505815901c0384040c0f01c09658405210021000701440c010380040310f1500420708212090760224003003050460210b056581e4103a0b0b501c450390303840c0b62100c050419040000c1030a44007081c01e40c07a210254000d400c01c2003044851681c4450707004144522806982209000070310000c01040b01d0b81000d92110103078559682d406940d0080d5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 437457571 1250 437456321 437456353
    0x90e072601060e0109050f01051503070f1803050a050706090524070804090b04050c0c1b061b0d08010602010c0c080304061415011214011a0c06010b0a030c08040213020c 74
    0x4240c5c09400400d0300d0f90204403e103280c1180e9036000d41412210f2410072148400c0310368040c08003d09642c240019074401c062114002d0b2041035504014402c07003111192603160154881d451107800b2202c5100300d18001c240903009064a109682c009081d554048001ca012a802d640c407582401d03000b60001c00c110400b0504550040c40540244130011a8000020381440701b1a1401405050102014442504080c00205d041030a58400810200c40761083c08001002e91081142c11003000703c18541001e800c1d400800d00010410040d26440d0304d6aa0f6060b059081c1c0e001200c0c03640008554174514400140d654010390b4205000d0300d4001070245a0380c20b094070189050340c00703020711010020203400755030740118200303140101803409020405440c102d00580c01410f0181c261700ca405151940c0c400020b440588628182e45011034a0650307440039000d0565008030b112000203401c04652501319400361300101d00480d40a440d14907040541d01ca400c0081d0040d07035601c02d040c002c4e4135002c540099 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 437458821 1250 437457571 437457599
    0x3040f060209130614010807080c0c101802100206101a0d06030b01091a031902012109110303070c1a0d0906060f080a05060105060f0403020d0507090e07260106 70
    0x200c0000002030139400e1040d52a01c04035400e64103810407150000308560294400740c42e6405c800c2d4414016201c544903070650303041000060b0114011881d1804030a49010a8030090070324900a07070b03034401d0915003900104c2c1c80d200d045880300c8460f02c1d0f0120810460018054000c580c1d6110060f20b810224020301400544040343e0083d1011401040188500c800d58030800300e1084c80c002c002403180d900340c1c021071345460702a000c02e016400660007210559020f9080c405121030981c00c040d01c000804050a00100000813055030f0401010085913510309001046990700c603004589240d10a2030070180d5500604190102e10b22400b091044004260300380c010010054030411002c540a07017088100403111035030745d10406440d4088400800441c4000c00c0450540e0000ea800039510320b4200b103902c980c1d10569100035000002c3c503481303000740308010503240c090307845882c001d00241003810035455552941d401280c03142da111102222002040c030030910b01e01e100300000810350a9407029140e035240 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 437460071 1250 437458821 437458849
    0x406140a0501030c080106030c0b0a020a02120609060a11031803160b0f1b16240c02011401052101060b0f0a02070f15030921020a11030d0503040f060209 67
    0x41c1c032540144100000c010000700134045281c02002464a035403168240c252140c800e9070300a00c00028111045403092083c803100d16005000c1883c460090b0380c0c0f2580e11322049852600901420f0042411068980180c01d40620810402c6007035441e002001075070300d040824249120b1000300044140b400c0e550b0501c40c1c90a000d030300400c1051800001c01c51510f030005000206188002c0c4191016044035015500000c80448038450900c10a01d01b01305001c04e01c14142c950608107030248002d80c03071a50414984510701754003d22401c44420341c501242d000a00403c0c0e448000c18054000080c0044080000040240d0012511a0f13507182d5072141039004901500c1544030001d282007800e40c0401843c03004214201300020040d291043c09521403448002b06803c05441760314400a001c45d98240c0d95207410450032107410500f05400282d43e8030400a4102c6494103a4001d04007580f030b020801c1071908480741c4aa51a50b0f1ba1a581c0f002c460912010444003641c0c00d2000e044140c035200b238012210 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 437461321 1250 437460071 437460091
    0x60310050a0605030f162702070c0602102a030213030308041b0e0a09030c0203071e0518010501050a12050708060a08010b1f020c090408120108030c0a0b040614 70
    0x180f41003005050400b59412400e290641c0105040100c1d02c201980040440c0c00700b1b80c054000341000152240307030300030141101c5c0403180081b030400d042c440105c03030100c2100e0b80c1d6000c4403902c910058004003581d900e003d4010001071024070400120342160310006c0360411505d001450034810304490030304503405800960010700b18208110070030843c07804c1305025450212450a500340351412008207642d000704a4009a0f480d145001c04142c015408a181d05d41d0003010384c0c100e103454460443c1c0d1183c0700031054242c114503400001b101c4c102403082010740301450b000075005a0810005440c290b000440c2c4108120f050905482004400d2141c0c0e4028400e503680c0106906000041011031015500401d16a9244c00c10300c07011541c842d42d00441412500300c0429000040c500c040c0d0810800080290b00000354400300010055181c00a0000801245402110303907200d019040d40d0340a030113000348050b800003401e07501062181c007005a109111340c60114180040d00b203840400071041d9030910b01 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 437462571 1250 437461321 437461331
    0x3060b01031d07140a0e090d02011a09040f0201050c071202040b06091c022d10080403140306060f0408010504020f100e06070c05100f0306080703031205060310050a 72
    0x24660349030154942c0c011a41c80990058581c41800300d446640f6031258058030002102244420b89030300500000a101c0380310007001903e8503a0f0780351348600340f08040a005519100343c40000139145104514400c1c0090b0090380c42c0d83d030f141c0d04c406643c02544da040c1e0500108ec4403150403803104000e088064144600041d400104500c14803082c0c3d032040d1803261240800b40610324190716074a0350507440c203131240b8032084025528000301d202c01030f0f1400b8a070f02c03885940342900440705444000f04245582a10700c9520914100d0b011910b00f60103441c000c00296100600221100c50a0042d41d0480c2005101c285442490328034105541d2013640118000d94442040000790700e00080c00c600011010b0f120000082050200104000280c81740c4500c035100c00301e10141400307000c0b1107003006054041e0501001c034101410262101605484060010f4180b040118a00b03101003801d0080f20ba142c1c80d01401c03031030104200c1c0042c0a0080045425101e98480003004005d02d01900c2d00401d11b44000107030b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 437463821 1250 437462571 437462591
    0x30b180307032a020d020d0212032d030c0301120c0b0703091806140d03020f060c090a090b010509060708120f1008150f060109030f030f080601031b050a17010306 71
    0xc401ca07540282c3c00141c00724880740f60160f22032800c4007840550446030003d80991070b2001031680c00020f1840e68003484003041008021000114200c03000d12540081c0c0c44840c0000c00c9456188011202d50034102000c0c00100300c01300e400160209941d20580c0e8944000b52520420742d015000b05a003540041c50004007040681d06c0b04608030940c41c00e05e10148421810408607680b5601d1081086014420441d460005e061080c426042200e4480c0195101401d140f101c03c15180c0014254502c55450081c00195090346071007550b41582044e120941041151001c110f0ac94004010648401d00d003001007182501c10301d071000703201d0207006440050070300704007424081402041d0030500c500d62040104a410290b0700700720562160f0503101a44e400d943c3d8400403918080b80da8401011000c1c850060300c105070b00520f0050a0301c001307a85009442d40c0391401102610005440c0ba0007842100300c003016010310031380060200740004e01f000c0380440c43d40420200180c000f41d08c280c506a40d200300c2c9030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 437465071 1250 437463821 437463857
    0x409091a070521070e040e100b0a0f05091b22171b03011d010207030e0904150f06050a08030903060a02030705040e2d0612070609030b18030703 63
    0x1582100c0c042c645076041042c80c0d00c0b10102c1c8501d0901c080d969101640000d442244100322004450740003400a0000600507803005503144103000220b2562814550b04141c1410715400c010101d40e8191040902c443c03514080c84030170400a0035666070b074103c0d10100c400ca00d0900c0001c0c902c2085e464034500c00d003e10302202007084242a0040b207071080c005e030b40d07100fa054000181c5130344e0000c034042e00b4420543c41038002401000c41000c0c8214080d81c0c0c031144101e0110641c040e004460003500ca12510110710001c00410000413500202001008001c000c2110744070340c0f01d1401000301c1c0c407001540c541c8a10000c1e0488041780d01c188601c0d400020108405c0c242405002e400902c0410103608606090f01d02400a0207980150340d0a10f002100060800c905880c6440301c0314a102005d1041c814a895092040d100848049004c1d111401c4188444800064034400301d80035076880a203c103040d0799540e030901101801c02000c0c0810342c9440b900304007060000303200d12403090700e6058412540807070b82 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 437466321 1250 437465071 437465123
    0xe130e15010f080c0f031903020304060e040507050d02030a06080615010201060b0a02030403141006030606090c02070302060901030e0c030d020a0b25110a0f06020406091a040302010311040909 84
    0x65884a0b042803401c0040c080000345000c01d504080b01d0020000e6030503c00320346803d603000d00104a80d4410407111051507000300040080e1101c654840722468440c4003440203540d029604440060380400c00c030380c410340755030340550b40100c0401d4011904030f83e00c00806280c0b400a541038400400309201c0c1c08115a0244502c0c00106124040b10382400d11009019481c0e005920006c0c100407403100180e442e0075000d001e8042d8101c50124200f20442c2c9a0074204014490760223041062440c1800744540c0a000058440840e07a000304010701c0d00240c040110040c2c01908c0501c06c65119004280c42c250b40c0501880c40c0306404c41c0d0041101032240e04100d92240b1000e00b106040035035a4000510000c2c000c140c0e2104424141091494680c61181c41441c1c0f60710103c003d090481142c020a082210070b400078401c46410b41d59200031151100d82014001e00c4640b015520f00e4030802003000154025004940b04048004100e800c25580e82c44d08420b841148030101c81200300b5012004849034103400e0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 437467571 1250 437466321 437466329
    0xd0302060108010e0604120807020a051009030905040216060f1404150b10080703050709210309150e0d020402040506070c06080106050406081f0f090f050a1b0e130e1501 74
    0x401190815844503840787d8803900b481002c108885000450440c0204081d20256a00c0780444031501c0841840750014500b0b000d00310300246080000040510341b5009841f000300070110950b54002c0c5c079946400040c405e4400001e1300c652901400c07200a5402000e1a20450041d000e02d016031002441c40c030100d503141020300c2d11503120390200140080d40016a19030051080c2000144c644501d030003a500484150300018902424014045041110300c0da01220301e84640c55507940182c071040d40040b4410881030035800a041c06c44030401d5407038584014410f00d030002d03100528107a06e1310007041d000c0c0c1c03003c00c040d501000132050030046260300040f01c83c01840503191240c04c0a041c0340300248203c40141081c6014031421100c0d0b079184644510b080000c01c98006003800d5503075900c2e603030f102504a00c0f5410104900e01000030705a4622030080a541c9000501412510b0301150010f8603107021406016030043c151240c2c10b00b080c181c40c0308592035040e070100149044484e0050607602e14805800c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 437468821 1250 437467571 437467573
    0x5030102030112030c0305090d15060e01120204092109080c241809190e070609031205070b01091b020a02060a031a0303043002060304200d0302060108010e 68
    0x104030f1012034030a6030503a1503061078000c00800050030304880a0042c0c090b15a88030028000d61401c001c040c14150408804c000000d110407a078560003074101400034031030407040c410110240001032032719070300000fa2103214603e402c00108022a2100c0c1c0789160740703c0303000411891310b0184114002040f1010040701c00b01c0340109603a0f03001c0c20800065625a02e09035020001003004101c4d0340390642995200c48002d4035103c1c09180c4102001a00f40c1c0310110000c400d2318140c10700c20640b0000c40c80c60141d410907160201ca09107160b032140742020f4280c0102007080b50500040000403200080c40c0d000f0304d080c40b40862400b00c0c90080442c170080c20b000410a6520038440c040050704c0301070076900c0c104014100010306c0c06c44400c0c1110f01d80c411618442d454000064045031200a00030500c900b07410614a620580703c0d84900188001d65084002c0e602900500001d400500c0d80041300c105c0c00320801c040b10308500a90045401040022400c90240e04a4001404000800d204a48032244204 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 437470071 1250 437468821 437468827
    0x304080d02072904030b3d0801050103050606100504080102030a1a03010b2d0d120e06031b18040f1a0406030c05060706020c060711060124030b01020f010c0c0b0105030102 75
    0x105020a52096200086c031503a2214001129900100180004000751016410000180d10190845882c03841c864450040d00741c03001290401d01449001d041e280d12200500a0b51141002c1054036034030a8000410450204004141c2410a001460050008450200710381c0c040c103555240300ba400c4900c0f18026072405494070815601c02904070000d28444c120700300801500d00281c180c0c81c100101c01a000b403004c1e080c07001000440d81203095040815030b210701030210807404106140c4000e4840c4c0b451002c0c40c0301c002507406091401032440040880c80041000503180124083d2900c5058001c05a551000c150a40d2800708603194034002040b10b0030071000e07007190381d8129050131601441c1d0013464049011300c10460560f048070344c00f4024004403689071914a00c020b00c240384841100710b081c041e420001407019501c220f8a1200c0e000d655a12403801d010500450080005030443e60440c85400841c0040301f50130b110f9490303007034180d80d45c1c1740408030355040c4030005860603440076010343c0c410 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 437471321 1250 437470071 437470139
    0x603140f07060e0d0f03020708240705030106020a03080604140f0a050c03070203040311040b04021b010e03070209180a06152303060705031008030310030201031a030d050c0304080d0207 81
    0x10521803100e41d01200c615000342c01420104c0c6402c52642101010b8841c5240801120302ba9003508685100d86007424041c0307549020040350b080c0000c0c030880c07015034004d400c8000024000d103a15a80550040e00000d02a41100141004031005179100e855000804042c460403070460302406074051141c000d008d14504104c44020354030300ca076200c00b50090541d070700da04085955130341043c0309228000700705545800601c5500d8901a080f6a614501e940c600580e103104404041f09071548c468000300105003958450524030301d0400c0440c00c2d400c0070300481c8409400106203202d6001c5101d401503000c0042e60401d0900301611024001ca1000c0d19007602100056540015400c4d0303008003280342c150b40700d40f541c1c518440401c00d0307034020143c1d6020100801c1801c2c07501c49940c5044078001d0742c0c1444585500440c10305505034028866405030807030008842c01c4c034004c1009100c4400b13080d003202d141a42c1c542d01704d810601000001030068100b10410415000f5107040e00d8501200b0303180c48405d100310 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 437472571 1250 437471321 437471329
    0x7141504110111030d0f061d0c03040b04030509040e0d0e1801170307050f0c10050702031e0c061201060e031203060906060708070b0f090a020105070f02040603140f07060e 75
    0x40080d0700e5041003502018120508000c1c0240c0700303001c1c0c00b1041840a0140e141040c80640414020703588424542160305144070060ba0764103002c4c1090101c444d2a546558603000e003031490040c4184c007801004c0080401507103030b521601c1c1824a2010180903400c02202008101221009509209980f50542c101c145180d07094141e0445104c080820408a4030101c59400e40c0540342c40a4503a0052484d84102ca0002051340c0e890540c00711001c810b0b420380120140d659000e080d034003a4041d031140703401c10056101c1c10b011000d20401101192444030300040007130304a5114585622210041a00400080d034000a140400010840290491a516600007811400000d142c0c500c0b030900180459145d0301e07400211043d581d04204044e542c7c0c8460308064000d107405403100d4100658600000320340d00d02c0411061407a0341e050b90355a01c0c1155a07100e84200c82d61903035050340e00643c2d03180d001000582d46200f001070800004050604020008000c500b0300c003d0381d02460500030100c1c82d00825540e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 437473821 1250 437472571 437472593
    0x70305030c0d14010b07050c010f020c041505120309030f0a02100c11060c010c0810050d03052802070602060c13030f03020a1203020421020d0201080a1107141504 71
    0x20402269511500c0004880c006000c074400c0144080f540f900001c0ba10705a05030080001074041c1048070804030801004603200000c2d40c0e40f07440140c000e140b0304912442c1c1600321032828260b045c2c2583c5d41d0703521030002800754100c09404c0301903030303000044080e16818148200c0e441c6d240101c0140690007620f130007203800c4102040d100410001c1600c040010400300914003034140d44060310068607401c50110082c000e12810b040c0c01e011400c80400650001103400304001a604013078035905600201350340c10784040c1c100d590050b0504008401140c1032814aa0b0040800c82d165801449411300d000b1019083c10380c09041c0030340c0140304001c038810450f40308420f1002c50303520a840604110080c1002c07030400a01d200014031a0003200e800d800e03084d40c1034000c0c00a552481804103800018600c80c111130003003002c002500036684110180141d8007416135107078403a5212401103514000b55038010300b00d5120304070803520741c06c10410210340004200a204009410300c170802e060f606058a03115000c10f = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 437475071 1250 437473821 437473831
    0xa08011e0302101e110c101211070203010c0305060a0f0503060103020f03010905061503070816090b060403050a0c380f09091302010f0f050711060906030a0501090f0207030503 77
    0x700101070120030320b00c03440312040d04050307640c01080045040f100080c0f080c4143d02c50b01e0014400c0400c16080c41c6440660311091f00096146d08103401040b80c61500a420b40010810112100b4025000981c50038004d0401003482660b0000e02d628040f001c110710400b860708003540c4505c1422050085d602d0009540341920303012100c0b028105120400a0301401e03690800a00500035002408482841c0d20b07040d40e84280210107942003940c940154a076500e4008082e403203200030032001007104c0b5007580d00074a40e17624085d26807864540c82e921941d1070446402000c450048c0e11020030080c001c00e1651090526200b011458400d0720700c16802c0c10101d060045814407214002501c41500c40c1c80390403545114400390000c0c0701481d010020600079000e036001640400c580b0012010940c2c0b003001c0c016043c480544a00f030030902161140f0303000f08450048990401010080c1030110399038600998415142d011002c60190b04141031030007a280d50340f500104450060012100180d00b21050b02d03440 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 437476321 1250 437475071 437475079
    0x150b070303050417070510110a0903020d0503070506040b0a0b0f130c0306081b040b1801060f26070e120d080a09020607051e071203030c02100f020a08011e0302 70
    0x36803a11301349182c0400d2501c10b44610413800003120710812402040590529411903801c116808950380e4200e501c1c410480e8810000c0d407812014401450400d40307086006004804403800c0840c250340e43d0b03141001c15102904c0300c0380c0342e6040003503c10180c09030800d009415a907881340400c80102085200c001c01e544d000a09032244103018203507100381d01c01801001c80343c049824001d402c170400c10185030203100243c029802c140000340c0e0790410107000344040d950040d0707401e0b080e0f1030441c0445411400724524020400080001c0645500c0e124248111064004180311182020100076000c0c4c0380c00e00c03000307006a1202241c1206613002058a25280380e640c1000d00683c1d036110ba0000062100c43d8009501c04000b00d41c4000703118000070000362143c00c411032010020160300782d0b5995049140b141500d034244030103441c000079109400c2035120719518011103855041d14015030b0f00b6903e50400c40440a903020a10745104c40d4441641401005c1e07020404920301600c074562000b80045000207801 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 437477571 1250 437476321 437476331
    0x9011b0f050a210c09050a0b0f0f1c060810090b01090e100e0304060909060f06030902041d0c15130306090c030f03080a0c0809060609151503010603150b070303 70
    0x5043d0081d58032048a05540702c1a40e600c1c0c250f0994940100b08131a8004001815003030080b4003424a40d0034002076600500d085030414003c000b00e1003280c1d0021282c4078546030140609240c00c82c00ca070000c0d201c0c0d01d903840046600350600c0240c1c2d20f0083d20a0904203042e00308a01c900200b80c500e10118152400c4200c04145440f0040c8031919110394090769100032881d00c1103a82c5010300100180c025900c460360348001781581d454801c07041d220607000d0b440515048107401c00c00d003402035000d500c0862001d40f010a101080610b0030b40903072035000304070000303801402028225107843c41c160a858801d42d0341e101e0070035034129a044000d40c40c1d4040109a0b9540b1f41e40403050003a80c012000007143e215a40b010000315a1900800d0010305803400c0307401c2c0c0d003020f011030310780c501a4950a102d50407520050142e641c5580410090810152440c0d001c405441c07650207954440090743c03283c0c5083c3e807240590301e5141c0403004003203c071411b22074040040486014130501940c10203d03451a034241c603000c24 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 437478821 1250 437477571 437477587
    0xc03060f09020d0b0c130902090901120302060601050d1b0903021f021b01020f070f061416030c0c170c0307140a0315110403050a05070608011809171209011b0f05 71
    0x11700c074410740200342c14a80045000144120036500101200c0800342c1d035220f1070fa40c0e2207220425400c08020018050b81004000820035442503002e04420800740303601040500c0f00040c004084880484842d0002e56098418029424000056141039100880c0f580d03819050000094603178807078000803604854a460541c265078130070400301941c1d0480c002500c40c5903030349440e01000d061072031280c035020072a016100080b5900358026980c41c1d0300308141e204564102641c04a5201e90540c00c115103401d4000c1000c1090100c0b420700d02020902a170050401c10010000c052402d0307084d520410400d545503c0540789a2105601801100c0d0b008581d9101c00d1a600c80620150400310780445120b1030100c3e0000a0240001d580740c0118003810940348000e4641c0011a501a0240141030074611201c03280c00d00e0104540c01004032a00484d6407290315040e42840703900315404011f040030149400d4040c091011300038400d19011703e00080d071144050180754009052100280100d4080c09004140d40c4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 437480071 1250 437478821 437478841
    0x80907180b0a290315190b181203130509092b031b0503060105130306091407081906050411101110020304051b0a0f030c03060f09020d0b 60
    0x50034110000c000038903150f100e807036500741e1030322048142e003000c4100801c3d2009a8403980c01c40b80101841d0303070050f24040c0301100303101c1c0515001da0746d00264000c4a50020780c4402c40800750018010440c8504040424001004034010545403541e02075041004011010309010711a0310131114151640041ea0380c60f0307e442c5082c0980301142c20500030300c4094216103444042a0b1001402d410f88003040307440541c614a0b140f40190a5008010907000c20208003250b000b40c0280503c0c00361603040050850301c130307625942504c0c900101125800106603080000410900074000501103840044c41d6004150710504070741440ca0030081c2409a0300c0012805012004520f22038207900600f401001e0100725070014800c403001c0c6150000c03801540c040c441400b909000320b030300981e0054018540b00303a1040700c420070039407a09100c9a01600c0d4000001d40d048030360520200450040012003001d0b865030030f081e42550042c0300e40040389031a1001c6100107a440d14150628984c1103800d443c0070380d03940d61540f = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 437481321 1250 437480071 437480081
    0x4050421051c02130e0c13030f020907031b0509060706060906031a040f030311070501050f0f0702070e0a0e030c120414150d09061d01091209060c03030209030a02121c08090718 77
    0x981c40b508445012051102804011440b5803003510241c119a443e0002201212150405003c001c503181c428802c0661080010d0702c44424024402841c08003d40d507070000b203810540c1310f92500c5444800030403d2200c02d150716040e022104428800601c0c2c142c0e61020fa21981031f070f000301816aa07030002c040c0c800210054a4610b40d21000070400c2c1d0030b001c40c54802203070046036001032808100c00000e012034408201d0408540002c0c982c144140c4801e035008018020b00d0802d000703244010b21002c0310f0303002c0c1044445101daa903a01a51780d0b440c1090028009100304074510760040c40400030300a040c074040c1c0203d5515101c80c0400142159044c40d020b4040e251904a61805580703c042c0f01a481006500c881056841008032484100305207c0c20b841081c402c0c411540880c20102d6940c012034002d80041120300303c0101698922517240d4000f441c041d8070001120403d51003d10445892000d107035006149000c207080c0000740d132400b5100309a96207401c0c025004260225241e4114650140d081 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 437482571 1250 437481321 437481337
    0x60a090611070b04140106080a03030e160312121812030608010203180714030c060d0e070303030618050103080a1b08031303081b0904050421051c02130e0c 68
    0xd51980e0340550305100043d82401c2da002d071004402e41c41a0301c900b4005100f04400c41d16860003800c142486034405600600c0601c41c00c40d03040c01503c0f030030034152409441240245204180c1c00d5000c038800407008100c01d10103d042e1203018500300c9140d0440010350b8000c000740e940070700300800c0c04061a1046000d0705595208d910f0315070000c0305101e268003100d20206000200e81003210706050352401c64010001020201c91b8054000c072200b510b503410040000d04803103181880221f81c0c1c2104810f603500c1c25013070b03900c140c0000c0d070303103110503c0f43c00302a00c20090b9082c503070082400a94103548800043d841802074113420700c0400c007003860889500074840440103822007001e075101e140040d082120725003d0081100010494000194401900c1e0000c58000071412581360500002100b4000144005802503900c040c8100140300038070341c4400b00408660f20f940c0c9440e00d130507403044615080c00e813050599880c0d80c018418200c900c9221b004c10700481d850031090600a40744c4801400042c4200b4035 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 437483821 1250 437482571 437482601
    0x120307230c150a11070c12020a08030f0310060c12030507121e0e0303011a090f060a020f120708071119060915090803030a090813030c15020f060a0906 66
    0x1041d4103440488445861003401100b105001d1025811088003807031160342d5000300310306d0644209001c0c4401c10030010b06620b01c05042d00c0c0e081900c1315240c9245800c441050203a01c04004208640c00e94150360035401414941088580c11180b651010900f040000c0382c401019500c01c00a00304da0310601c88800401c040c280108039880c400754a0b0405174040131921011182840c0d9203980b81c1c040081104c4c103c543e00b0b2210708012044d103c40b040141e01100f24a64008104e4856900c01c2e03880f0401000c4064181d00100400380c050701a240c2420b4200000084084051050030040b0b2250800c50309542d500c06802d00100c0f100b140040e85aa02c02c0360b01c6500100080c10100d02d958100c41034505950380c00701504412a10150200c3d81040c41d030107060150341040c004aa00f0089980054038024460118a0300300700c01c000683c0b0740b4549a0344152601c0716464000c100c0d2001c1e410000c0c01c8482a0300c042c002440d203030442c8036562031000c0c14084d04640d8030b10700d55040c00903d03482030904075002c003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 437485071 1250 437483821 437483833
    0xa02090c04050d0507080d0509031c03090b150406050406060c0b04141609180c05040b0a09290405040201080711030f030f0106030510031709010e03060103030908120307230c 76
    0xc2407260b030707175038150056034128482c01034000c51190043c800c0c1ca02c001c40007030081c440d8100d000e460b1034a804422900005050f01c880300c0c04005413100d80064403652890760407410300d0b21208104401e507202e60388080d0281d40340610034030000ba030180c902032075982c02c10a41c0c520b680707070703480c04802c60041590b20000c14003940000312402411104a030080b5505840107001c402001861000c41d07041c00c4000800031001402d04000c54240307500701c100d00c1c0d04020000c0ca80140e40c3c184550690711120b005e000c0d0490494000141004c2c4a04000403119040c1d5041180703140c01e40c006410803074054032140c103200040c94603060504041007181c84c8690f8101d001500c0341800d980703000c4540020701171a40440c1c10000050600000d2800041c1101e4004c0449401032083c0e0b240e03207070326a01c81402181004130500c403031040d64030b080160a00840c826034940c90503500c0c1a0049040a000e01900d000c43c1300e0410a105015a1012031a1140182c1210743c00ca91151992011150700c0354002591341c5004072 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 437486321 1250 437485071 437485073
    0x30706060b07141b011115070e0109060201110d110c01020a0e0a060819050c0408071206050c0c07060302180301230705310b032e080a02090c04050d 65
    0x30002d42507051003041c1405014107070301c0300341d6201c1110301000700d1515503049445105610405581d0211030b07000040d5130748000b4403410940c90b6541202e940002c10003081c000071065a00148070381c014949032008000d0402150140308880c070031103050864158072061203c1100b01103c00310791382600c03150001c5695100551024001c50849290315100f01040c0000066a90040201c28454128400d50083c920007603025030008102c050094003400c14180004071346480200b100701301600c1c2c10480b20442a04615181c0305564000b00946140314080c09060780482000401400b5105542400360f210040e0800700c0610701003904283d9410340c01e00550704124a503551902e46201c45001800f4016520030500341c423180b082c051141031500d100035041032107420355032001140400e038442c90f10030103070b4903078440e00d40b900280d4211001e4201c45000070741100000c400300c40b8820741c0480010b4030300e140412082d1110340464003c0d028611070300014030020b04000c101d902800e0001c2c030300c84128000f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 437487571 1250 437486321 437486339
    0x1f0f0e061b070b0d06030606060801050105030f09010b06040e10210b061c0b090106050f010e0d08040803040609082a0405060d0c08010b0906040203060904030c030908120903010b040c2003070606 85
    0x840c1b20030b8881c907250810200c0e040d4880c1d62440c3c1660810f8448900d56151103840c00306900d00200409115540c0b002c50848a40e240c000401c02048a554200900c1c1004c0050600741021607000e1144081c07020405076840c2c03120720081c0f003903d070841030302c0c41d0076507074200480c1e502060701d20200c099080717210529041010f007620386030152a01e070000708011512602800700d0340b4540c0c007200e070100c0d1200710014151300d01000c06007405842466070f40d00341039441500d10720f940c005812010108002050501580d0401c20410400b280341008500e6089000c460603d450401201282e005070b84603000980c050f110604a040c0a96112045404040c1e80c0c01280380240031205882e4420518000844c415282c640290f81c01110000c100100544a50790251203450400804030240710b07444500080d0b0311018060030408118031000242ea0f044500209400c603100c100314244120315041c00e802d000c0c0d80c401c4843c100e44040d4046020b1a184070700c6083d155009101000346a90708010010070b100c05 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 437488821 1250 437487571 437487581
    0x71701030f03032319060302130c14041805070c05150a06050f101b1b17030c0d050d06090501081e0a0f03140403021f0f0e061b070b0d 59
    0x2001c1e0f602081612201848002076100c0d81c02e180e0700d004104408540440c0b40312250380a103501202d00040c10f03030b54a6001c039481000400304003000340da64211140246800040007080d4090b000000f07443c3c54107101900c02514580c100f4818280c0d5500f00103082c8038000c2c40e04410703944c0c00204940c0d03269040399240c1460001140da0f610454101040061142404905150072031001009030704148004403040b01c50740505201410703004588003420020172001d0409661645107078645001441c240150300014a030000001c0c13106600c10071240514203408642c00b03c0880301450101c1d80c032042059400301502554000c400c10341d15200001500310700004207110120301d800b041061004190703812684a8031040000f41c00b1311400403603074000900c100c143d05009003192952505141e01d80d00480c7c11100c04401064aa4081210b400c0b031042d00481202c01030081460f00c010220861008156035006400b011140544c00f050580740f460b80c1400b02c200134002d808605074440c400d2031a4240030304 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 437490071 1250 437488821 437488823
    0x2091c051606140403080f0424030c0806090f062107050f010507020303190302041a1b010c0c02130e030c03040311060f030c030a0908040602030d0e01060302010804020108071701030f 80
    0x700100500203070701c82c083c0c0d88458804a8042200f030400c0d02e0b644400390340d944154006141d00101700800f04070740080942c10b141900b802449504043e9440c0000340840d00e4540d940f0f0184510303103041109a80d11a508154000c4071040840c030b468840b40c0209504821005002c480c1114880701d9004160001a500301100c004840c146c100d51407210040d6040d2040701c4010307415800801050000f40940900c4000b02c299a02e0014078050b0340d4118200055112080340903606000612402d90805049a407408940300b10000c0244840441e406003120000840090040d82d030105503440b513000c0c075804103a540c00054141c2e5501d0703484941480d244e6102c1d0004903a00c0304440c0039598a400c15405603034401c2c8032005214655115801c4d202505d800c01841350300500d4039286200005a200405000140307082c3e0021600d80a0429012090364003a40344100668500b40007040540e0340501c1c0c0e2601301d502806d0801054032100c0080703507107032041280064240d4600340000200003064014806103 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 437491321 1250 437490071 437490103
    0x3060f1012241707060807020703150e0610380310050111010504110f0d1a0601091e050f0310230906060d081c090803040605090a030c0602091c05 64
    0xc0b6190700c2c1041680c0100c3c4201e0100b940114010701a850064540e135030030015600460740e02645c0d0746c3d6002034814a100760b45403829242c0b02e4174039810408025031504440001d41100e0300d24249140381c0400d048040e040c0d503501d11480341c8184208141c0c0c0140b1003020482c414150b49261000310100310b4000761184a0001d4003108802d280b00406210b054021a84005844800a507080030480c011200c40a995400302c518051000010140400c000d000074440c0e00c404c000c0e280c180000f40c1240a075900c1a012004240e140f070b4429202ea0303c0038070036200220b582245001c80040401d11f4106100028241c442c54105000c078810301c1c0c00c108050054130303a00c101915684503480541c450405441c01c0390820388007810380002407140e0b00503003211002102e040001d540c90b44020004d40e0b4120a041c0c404203000414041402000d02525910040480040950140d181e07801000040920760103800540c0c04a03d142042e510040007101d1510a4481c0091400e0681085a111700c0c40c6034021200c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 437492571 1250 437491321 437491391
    0x50304171204060c02120312070206060a080a1b05090a0605040f0207051e160b07020a0f0303050a050904090b010320030105070c020607050709020a0f020105010b03060f1012 76
    0x451440000d0358a21420301c0c400590410786021400d540488005108036806441c2580f440d13003128040014221a03401090803202d50700308424081e040c028090b00040c05076103000c601b40070000001031198625980b0030650707407000301000c41c2e0381c00321081d0b608a2a0301c803001001707000f0780c102290011400c1c0c0303030700726001c001012001c80e00c0d2040b8800c0f114003e0043d00142d0682280b2594401d590072031a4400301600c0c292038107405020f110090580020003410000704002c015410041e0342c0340054548a42400019425038a0140903030080c422800c041000000d14109582c640d034100842d9607074801203202c00c4e961a40f5001c03048100342034402c003981c143c5940304581464140185401086151946003049c109034080c002c403070f809203100b030300d95228903500040c0e040b6142c070007803095600541d140382d064404420b0090a485040c6d000e040303d56030a00a0000540d61035011410720081201c00c0300010101e84c1d0240c1d010884401c0f281070062911100d040c580c0204180400100301c0c220344450 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 437493821 1250 437492571 437492609
    0xd171603080f0c030f01032004020d1401170712030e220f09080a05160b010807050108090708101e0603110307091a0907180801140a022115090103050304 67
    0x11a004c2194100a100b6070790f00100b01045200045021248480048541200710a804241660721600d600c440055984004102102100140c23a0250103910f410051140c4031144150b0303540c071580205a00028103801d0241018090100c3d468000001b50900034081c940320b115120090307230f02803005002800c250303a0602d15400c620852038101e5100105500344141c01c00225001e070050b418804140c41c8400300da01c0441d6203005a6802020450010660740741000700040248002402c00702041d44994410300603901301081014408207060800242c3c07840040550b4101c040504811452034a80301020052007100580c0d0460460180c0c2142c1405555000180c205d5581011120004001d54038036042850203241c0a60084124a00b8070034155051110a081c0790142e030040216a5445004081402545134100d500c130000001c2107041140c1c1048031640071610320740d0950061048000105012030009c103103c081031002d0300380c030b9440d038691414607900d17407081c0500740ca03030303881206035107 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 437495071 1250 437493821 437493841
    0x906030905060703050606120c03161b150906020a2c010207030605060414071107170316080c010c03020d060503030403021309030302091c02040501140d171603080f 72
    0xc0515403000c010410703596030340c0c1c0031401403c3c0605200d40c00401045405460140d01c402e00380a01c40e069a00f81ea281040703c05101540d00050418003805500302503040e050001c00b03601000c6035006041d071182c0c1003c104041d00100005d00008251a04c0400e40c042c005070b021241d41e41c4002c2c0407040c41281608040040c1030800c45030005801030b40095001c2c0005005500015045a4040e1002c03505050304407010b2281e0204075000310008064a944140c02e00f400c015080050000a020340801504560036903101e01c07440d1a040e02e000e11401c5040304100c3c041c001c8842c4034400c01c008000302882020024040d51102100001d180d003000b8002c2420300c1e01000325403c40794006c4c03005d41104800c41c070080140004120035018076038203200e2620180c07905200c01c4200710801c0c1c07040b8841900c0344100012140180c000381c008520380c0d001d03d001c40e00d40c450b9522702e0580024044503c031009440264417807040d81c640c109000c00b409000c1c0105500300605c14050103001c8805006951181011 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 437496321 1250 437495071 437495081
    0x901150c200a350309100522030b0411120d0e09010e0c0403120c0f0609050f0706050a030906150602030c060106080412030c0c0c0b18040b03060103140f0616090603 72
    0x20180b12a5120840700c84105290b25641d960440d0500356411700c0a4900052580025040030b48003055000401c0c2c0d040d02c07090303003014981503100d90b91140400d0443d29090110200148000e00074440d50191090039030b0f0754000d5010121070101110b0311034078224002070040d400602e04900070015074002081b4100e441909600c40c84588501d141010b1a641311204004558003803c01800b115000d60404035148d101c0300c0c140710f03000f541c0115140c8a0303031515500d4420954564001c0e45c0000000744a150351181c100d5881085a1034085864070050a018004210081119001d00704070480052202d4021019000040038442503401c141c0ea602400d4419100440d8014600d180e80c488441b40b50307000e035020009080e070303d01c1c005480e01425541d0152072005504041c10083e070110311683c00622503902c88603c5d80054900b4072030244c046002c00d654032810300009003105821400245103080410110003580f2942c0c1c2201c29504101e10581e2146814004a40020300b4142c008a840c601074092 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 437497571 1250 437496321 437496359
    0x1b140a0b0a0516080d052715150105130b070c09090323090414040b06010906020307030302030c0d0c0c05010e0102090108061314040c030209070c02010c1b080f070518060901150c200a 80
    0x19000d0641c0d03162110749d09029041511810b00009010a000050381449a0307005000006c031810380c0c9440314148691044003962100100a0508500c90b000070790010701c22680c136901c41a4440500400d0315008105d0050000c4260400d103000607000c2900b0202007194010b41c061000b000c0c3d291607000044038038484c00e01880300035920410410b030009100e907009640c440d00a22400d402d0841700e8001d801500c11401031840054102c0c2d0201007449401c2c45080c0c1d100c2c140c00c00071840d10140c0000a0315990b4018601d51040154030324a080c40b0b4002e41020b400c00801030b88460042c40c041c03400c14000451800180d0241044000085c5c00c14051110580d08517016120510f03d007641c0d40e1020b501d0000140185650038840f03100241c5a4410031911a004103c0700140c01e800e8103050038081911100584503451055190901c84035454100125040d519221790143c4e44807075100081c0c41c1c020500f0320050800c0d98078042850941940000303070080324400c4500c88129a50303421100c00e00100c0b442e0b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 437498821 1250 437497571 437497603
    0xe010204050303040b131a0a0f0302180409152a03061a090a05091311030d05271e041a0306131b140a0b0a0516080d0527 53
    0x500000b98440068a2006015041d0072441521f0301c4004060315401484c401c1ca40401140c2400c07a2030b0000000444001d0301c0c40d045040540e40098012644920604240075a5640960600707000038841100461165880c081c80a110035145020110700c482c080040e001c04034142002c401c91082c001e0408503224442d40d00c0307054409554903820b0b94841c0100b6580410b00b0040010242c9814040700e1007105c1841c0d107840c80645a08000c3c100e10f00c1e590a60f03100b908100e42c0d9118982c7c0140c00c0d034141c42034400c00c1c00c800c104481d00c01380d01400c10b818042d90065000350600d00340e2101c3c94901d0140c01d4280d4080c81031600c482050301809400c07154140c1e040d0409000118a00c3e51040c0340d5059a0152403508400c1c03121903880c0c40303080741541103c1c0700743e44210080003903814603e012400802c02601842d18000800400404c24041e11071a8600ca0404511260501101c00306a41d013001c04640c007044a4248540100c0359102d210241445113240d101c80ea01032042d001c1600f140c0012850 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 437500071 1250 437498821 437498827
    0x2070602070506160c17070e04120807050c100b010f0302090109030803060f09041406090d120b010c060f050402010e15030109090f051501062c0d080408120403060e010204050303 78
    0x1100f0000c2940002a400c440b0000d03800c500000301e04c6041a44004001038603010141e0f201041080d401c0c41e00b80d0308180d2200703290300240b0001400d545200c5020786a21300c0c01d922180c861800032140c920600c039640d0307400c4c8514906030240301a55031060f282d40100343c9414001c0304100700190213034022290a2400309002120800100d8403010085074002c8006100c2202500080000350890398103403810303290078400c4c0144d1524141c0400941e5004451040100050700c01c250004101d000010410b00c101d42d25405000e403d82d020b00f07810141142e000c0b00c180f001d400c0481100000b440100c500703134001015144281e405046c2002c00c01050401c0c00721140c51a8204401c0d480a0044e10804442440d0401c0144022550512048094500e1a0b80180c529450040014112140d800300170204501c04410300c514a0a86800c580d40f618081c0c4100e1034580160410f650103000c4c59100e50000d01501d04940e844c0e4031844003c2c82960700c101401c01500c80e4922a1600300d01884c002e09030144d01c10 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 437501321 1250 437500071 437500079
    0x7080c0901030e030c0a03030207050705010e102a05010207030306090506010504090504020d06020f181c0b040311060c0a030f0b06030f13080a0c1101030b1018090501061e0207060207 80
    0x3900840340f640c1c0d801d001c4924101e101c04801c1c0c580f01d5028801d4000aa0100d2003504009051002000400003464034454080021001501ca01e103402e02c2c02e024456a195000c55100101c02450040c03003464900c514400c0450601030701035405444200d00207482e0940c08500600b082c070a5500a03d4180d46090815003840403da0060001910680e44618900b00c3c40c80060414001000102480008980c84005209441c00410b142c00000c502c039100ea041e8040704400c0d0a032041c0380042d0020480407254070360303040c203450840b12403984041d240101002c00c81680b0300d0074014844081075039001c00c0042d01c8010301e01c048954000f01d450703110303134100042805c2c03242040c20710b50411907040060780d111425503101c1c1207651100c030704e2001003985444100f040c040900c1011407440c80a0900b4460482c0400000342c07400c403603400c0c480074080c404140101821804440700302812983d40704204558407110041c1c0304560514402c00c001000d400040702a41c408250b2904544041e002814141e0070 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 437502571 1250 437501321 437501327
    0x6010311090a0b120907030816150e03030711060421021c090e0a02070b040602031902131e15200303040f06180803061003020408070b1207080c0901 65
    0x5545000d00c68800303001c2a190355407000c078640010002940b0050395503c0c00e00100c010002d0007000b0380410b4000010820200b6003101c100c4900070600072203268021540e28000300345129484030511341c0ca02d494002e6608940000c0110b0094015407100078045541035240c540c0c0e41d10031100207081c11102c9d0b480041000301c90b0032000b980c101b0750040e5a0350b00155030166100c03481c01d1450100064000200300034000349041c0c0750790481d0914130103529020403500e440c160030b90301500090200c0d50000000d810b51608204180e050f4401940075560744640f010401c810f10b62501480e071a0825007040e10800d0003003c0d125400b01c8032500d195190300d8a680c002a1203000b0300f50350482c080c10035a00141010f060900c021445140b0410001c6454540c506082046034128910807030201586580d80300031612410550781d0180d000c4680000720343e00e05c1c070210041d0066a0004210744286079000c00c98041d0b89010302041c81d5140c540f0030455a80c410100d4059105a404050344d5500300054209544 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 437503821 1250 437502571 437502581
    0x218040f1d06041a07020a02011110060b071a040507030605100306050703020d06060e06070b190c0f080c03310c150e030a020a051e030312090d0c0308060103 69
    0xa0400c0c000541d12801d201200d824091180300111190000b40c2044104030182100160780301d000400f0440c503190000029540c0c41c0b07048000303030500c150b441e10048180b004216010118500c10300611a40f96900800361a41d00b201c0030807038651140c1008043c0b014114000c152180f50000003c0500918503100d030700050070084d0a0f25420b20380704002001003035550207200d003d15070b640e8006035a0000164500112004ea4000c01d013006a45181841c0d95a6414250780358503812450700070043c0c862519403402d14004009442001e810442901c403230302d80040340d01100d5406502c400c050713030b55402c568041e0b03880101c0e644981402042d00c1d110391800003002d00e88103004007034a602030f4242103840308216800c00394020017400e042c08070809020740c0c1c40440c0c2903080340142d00810002d4001c0d40050305080076402940d00580c4804151501042403280842100e00090262592410b02940038400008115100050780c81a002d0250380f4a1086148200058042e600d90f92141c0b507050046020380 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 437505071 1250 437503821 437503841
    0x7080a0b190f020f0d0b010806010f12021c0642020114010f050123090103020a210b0109050d0b0f060a0e0f01090510082e0203190b04021804 62
    0xa40c0c0c540700b14440c42c01c14030080404c0c0703401100c082c0e00e07072005e42521000e44071395240c030324108041c180c24800321340d07007240040480c8000e03070421011403800d00c103070381d0001d0003400c810700394550030420801e104c0a020341c1316100ba02c1d01041e40d00421215034409407030120ba007a03100c0814a140040103a00c41e000c160305100711010350b2001290014140c6030040b038003002a0006400007484000401c1b59682245a03001031070300203001c1100e18818480c00c803010380103c5040c28141900022151801c034455900c905c4c1b204401c0c3d5443c0c00841d0960851030007000100b186501140401c17402043c50b02d000f207d840030559018003000b1041e901c01e003d411303071101c0c09803e064020540310800303d2034040b0414902d10400064402d004a985800d5104044d140081c100404845602c1030520104201054000d120110b0345114400b1006161034500400311412109040c944040148070010805507660b187c1250b881a042c40964003d071304000484c072541c2030007050b00ca080c1850152500305508481840 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 437506321 1250 437505071 437505121
    0xa020a0c170c0717031e0f070b091e030304170f0d140a020906030601030c030b060c0a05100b1008130605090303091e1e010f05130c150c08070c05100e0307080a0b 71
    0x1d50071461f0300490300942e000f2900700b25607030304001c0141400c00880c03c0c5a00c200300ca4000924003800c0d040d8592101a10260503414030310007044001d00030310700b10b43c40b940d5801c0c40b09590b17410f4642503000810055a4141c1440e04403004511540c803d030007034030402c540c0248031a00c1c54803214015001010f81405d014107058803441d04e1806a510306002c0e00301e00f507021014084c9540186070844c20702501d2030080007142d19000f1051920b4aa600c0100c195401c8c4c0e0820803026200c241550b07810702a0010002c050b0b40c108810002c00320340200141d0701038000032045400390402898144841041144400000d070710074102d1310354142183d0561004460000700000e43c0c030380001e500c02c040d07806c212001031810320903080040400118440040040c600c440d110414445aa40010050720200002a00040000c1218004d1203541c141d0702005020050002641c03514900010b0810255007403200c0c0700c4e01449d1800101034401007090a0714650241c1c400040755103241c0310f2220159441d00c0460342c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 437507571 1250 437506321 437506327
    0x50d0b040f0906180b01060503090a05101b02060f0a2a0203040317040b0409230103050d180e012d0b0909090d080a020a0c170c0717031e 60
    0x22a4449110310380c0900c104803030101e940802410b00b10300ba40d1040c190039064106100c4d510f004a0075400c0340505603451450b0480d41c0f5102d42c2c583c0c40c03803c4d100080181c042c0c000c00440c110103404a030310034115074409100c4944140040c401c00e03078440b03004844000741030900fa8005117a1482c180d10006814980c46590155800c4860a1280c4256244c2c1d43d1f134003580c0000380910520007403800b00d80815000d0210035192030b0502041002c2405244140103207a62581c5030030129a91024020041140382c185484a80d82e4a050040d078540403e20b1035000700d00c504007042c02a03001145803d00380d07010f1641100484e4a003d1110150308520154074032115a50f4041d60600210902c6820090034640341c0c10b9114005a41001201280680460410380c08400c84000c0c042d089403185038013201e280c00058650ba01020160303001003900d1001408040c0c0c8104a80e00c1c0a0b50300040c01c1c4c104565401c5401150310b80304d0904a4901030a000502a4420300a0191080e0079a041d4010f00440b9145075003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 437508821 1250 437507571 437507591
    0x306110f0d1a030a030e060a0c0203031303021c0f020d050111030106020105040309060903050607030f15090203090c190b0309070b0f1801091a0313050d0909051f06050d 74
    0xc1560401c902100c081511242001c03070308588100c40c4000200304a010388401380260f035019145d9220014054064800400c0c0c4c5a6058003c04c2c0c0c86200503009410340399a800b01c3d290401e10b1855070301040344540380600f44800c001e1940c1170381d0013080303500101d10400381605408002c0024850241120259200c00840c10540d1410001c0d60091080e60004901800c082c50060480c1c0c4e4590020010008000020808610300203540c580000b501c1c24000b1314880e120500304003400c0c42181c859510130001c48001920046a8021880b5508040c01d80d620280c0c0d04040013102069550244013000c6800b800703200303c0c0305480013940c00407440401c07207904541e034508185564002207131002c0f03012404035644505040a0403482c1d101c0707500b4a4400a040e00b80700c081d541541081c1200700c503072000800000d015140002070400d10390703000cc1c200c035080850706100600441c3e45000ea0444141040e0100e6980c00038071686014840180c01ea0455040c20000104d40d01e07086500002c52042e11081005 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 437510071 1250 437508821 437508847
    0xc07140f1311220b070c061805040e03040e0a050f0f0903091e19051e0a0801241d0708090109140304080c01021c050c070e09031e09030601030611 64
    0x891a0b19454003a205084450702400c00b0096101c010251001c0201d05d0006081c0070100080d150300c0d00b8142144100d0724039070307500305401d6041143c100c0c2c40d024120505400001c041d1046421803544490305c0d0f500c812001064920980329040410b0242010640d00a0031010040d44001e07114200c90400c18040006100741c0301c406c1580040c0c041001d0700300d850741003400d5018900426010f54a0441e4070300400b20302d0b0400000880e8408100004061960b03540700c451020042c03044c00c0c028001c0080300d910850a0344c4800e29410403181c09038000007510300d01e02400781c00341014203010032001c0c0c0e80d96505440d491401860480320f5580d982e00100041e242c442c0c000f06610340381c0000e40c1c41c1e40c00d10080504d010201d0801c41c1c150f6000c204850320040340011401e407100104d10300140c0300e54150a085203003d48540068008a03242410800e00210020141032605605105080d260361402c0010070584507449000da0150040340042c4046080d581000c0c0b481503000350b949241045c1401c081c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 437511321 1250 437510071 437510077
    0x120c0a1e06060b04050f060a02060c0903011d0309010f11070302011b050607020606010809010e030405120106270506041413142b0f0512090705060706020c07140f1311 73
    0x3d00703003584003c50705002d00d08000c02c8459030000c0c19a04a1300d003080c140c002945c1c8410082c80814201d800180c1e05090303071020340044e00050024924144091850012103440760468000e0134001144600c040382c055200701000141150601c0c050003955040d5001140e11450745828118017100b2400f003000003132400c02003a80b0606c0c55034090039040c00d154000424100d0060071050590303041400300352034a000802100c040394822912040304031480561203024101c1a030000d840d04003480c0c59443c0000c500920001c550344611340800c000d0351101c1c10803003100c4001c18110301071105900000c2d10102c00d081080d201c0c0380505c0281600018500d10035190403240c15400d0f02d8002041041503c0d2254010110031700d5105080c0001c540d250000b00034407500507003414002b680750340c1c6c1c049aa803200910000024210251030b042d660400c0c2d08201010350301108020075580701d486000179910120f20404403420320001c2004144417082d20070400710050307644600c03009a60300d490361901809a8401 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 437512571 1250 437511321 437511329
    0x201140a02090118050312030603011d16090c0509011112031003020a12050c01052104080403050c09060102100c0509060301091413030c06050408070c080f120c0a1e0606 74
    0x10140e0365100b660001040041031500000008940e0003090000b0b56010030341c41a07081d8402c8200f9201c0c4d5031400003a0141800e103aaa01003407400542140c06200040b805088900d030039202d039140280d403071142c0021210341204030000100c1c02d02c40304805600c070358031109043c01e0080840d0303210324164215449661069a0140040015002c04c10850812800703050060600300d42e1a4131010494880725220705007440d5240c10030000049034030105800400c0c03010030011403a0755500c02e26140c6041c0c0141c3d8000d000a40340d910400464060520f41001c0140c842c65041c0c0c0640f01c4040304101180c007601e0a44401024420305020340100c0d0b4480902450086c44d40701c8000c90740740310204e90300b00151006012290084008980040440c3d0030400c50303a001c9900410000300c43c1d440d4100301203180507481c0018403002c902da03000150001c1c00181504d285204400307036050910900900c40061003119240e082e160003003014280841c1c0144403c40506030601900c000f109120b030341d01c0d01240d5039504 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 437513821 1250 437512571 437512591
    0xc030f0f0c060e150f1e0d0e1e012d0e010e0c180c0304020f010c0b040605041b0608010b090d1b08070f0b0316140a02010506180c0a030c020114 63
    0x1079000309031324200c2c07859452000884041480c15550010340d5100748180440184208a421468840c0c0e001707507011140c0644a0120420101e10510915515140c01c0d08074035441d01c00c404200381d2554010320443d03200d0440c140001400d00320701000a030100980f007180d000000d40e511380b0001035403c02e0040d080718162810160402a03850405c200310b08813101c5c80e80325a400a082040070303d41d922400c0300d40198044610060903e030700c82c0100c80c8003140213070080c118507891003417004120f0150405030084d840b43c00100c00182071080c0e481c8a507603052190714006903981c80108281030050300140242c120180580d01d186a4686070071003601e0060010b559076048880d8100b0541c1402d116100c00b0306014865032405600e041143c0d5103600024080806102840030212005801102c0c2c0b40e400c20444821140c40d008200c1001c0d000b0301e0202d5070302c0d00078081c52a02031420890389004078482e00411420605181e40344070201d0013048035609003403c0d59030315400c0c2c80041e000260035030302c1508116 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 437515071 1250 437513821 437513837
    0x80a080306030d050c07090b061611030d02010225051e060a0c02010605180a0f0f02070309050414280603140c0a060207060c02010306050910050306090a0c030f0f0c06 73
    0x50241481c10701588408010404144100c0f10b02c0c800225501b02140c0682d007021513802034030000500d0500c11204807030082012260305d202000001c042040e00c00d4412815078184281c5400203030300380d01c242800c4d0011061400000d0a401344080580f0314074a0240d411950542000c0075079007183c000c01c1e00c142c0c2c0d81e03511190400500b1800f50052100980c443c2c8001e2003091700e42004210403144d01521480b40c01e001000091a1031210b80c84601c50404000c0140310010f80214003000960082d00150001480e88070003180c541018040d044214180124010103a40c03204a1140080b070320000303503c6002c195a00c1c600202e10a40664400b840c01405980004002030104030f15182213140c502d07020f0310303411a04000d4590045210003c484590400c10380d0702c8500d1004074020704140e04810f9005a480c0c0500104003c0302c07a13200c05645040c0c085400e55101c44024507640c5941480c010189200803606200150303444a0f84c10700540300300f0b8014034800e043ea0b181e580c180003541002000070414 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 437516321 1250 437515071 437515081
    0x501020c03070b0a1a12030d0504080a0311030f01030f230c120c030d0503090102040302041401050102121c020a0318140606060414150c0f0a020a0506041503090309080a0803 76
    0x144002a03040314410000f0030200d101030b031010b8512045c1558940c843c83c086a42c080c8070003810310441e001102c1e06031f000c1015142a24006140c1c1e00030f01d00000019150401c080e0307820030702500722401541c0310320042d11540e02e1565506900031882c0c02c2280c1e803025181501501d803024841e050070f4002c07101c0243c03500c0c0ca080014003080164004005005502a560b841c60b035440c0031504d5481200d003880c02d290b482d030310142c03041d01a01c69680002e401616100148088996840303865060320801d0342590300c0701c0504005044107008003140340520380c1c038801c0d10200d0104154010300040150781008910340c9817a03811b5410a0710401c206030740611500240468451082c0041c0740e100e81d04450603405c107424130000329012403201c0300150140c00300348040c0400300c04c0c030f00c240c1c2d100d00e03d402c045030b0005a91501c19600e4116000c412400354001c0c000214180c500481a5420b40f0201a100040980072013011006000d42c40c07800c0d0180001c03141e001c07401400a12542d20700c42c4c00307280e82c2e6a4078200713 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 437517571 1250 437516321 437516333
    0xc080a0507030c050720030703240c17040c0f09090b010e070512040218040b160f0e01080411121b0102030405130c0e130903080a0b0a181506200c131104030501020c0307 74
    0xac4c00d510700d6500e40c43d107800021b26036000034041c0350030b259107090011680e4442c40c1c29032003903555802450583c00c0d90300c00000c0582107608000c00041c828844074045903620003010114240941d034500208070140a038510a01000345855440b42c001068003d803004c0a52a16413452410b44017a01c01c405c0c0c401c1045850842204906008080d500d0450a1324542280c020000b01d220070040c0d0403c1500b0000c00d081c003802e802101d041010041803c21181c403c440308a80d42c0e000c507031840d6058a900e220071000c030340c004030684003203c0003c3c0560408881001c01c080040a031f20b00c13148280305011080d0061038131644401101d410180c00000345252941c24060700079240284800c5045060030080f0429440d1114500304441c7c01810348659101c40704240f4010b085854180c04030107080100000d51160300503440072401d0441c5a5050545040b4002d260301c424070751010325040100380440b49035031905944200c00d07071000e440400381015200e82c0d80310309aa21803201c643c40323684042407410501c54 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 437518821 1250 437517571 437517623
    0x121416061d0904021c03030902040e010b030708070602100209012d12020f040e061512040c090e0c190b040b04210308040f060f0c080a0507030c050720030703 69
    0x401160054810302d030913800200c5101116900c0e500340c07078100b20100100741c040d811042105500400601100c603c40314520700170010b14150602c03c1c82441c17000244081c000c2014070650754268046c0c0445841081c4d920080d5010307103507181c10050281041c00100c070220400d0b035100c080c16045205010440e100040543c0150006030070140e01c108100303c94000c00004580860300034200c07030300781a903400703001400e00841e810880190041c000b5045415001d2194268800c80c45001d0380014691900d07010022924080307203e180550000b148003580e450a003034082c0f41310112810001c64a521000204800e4100b0b602c4580c8034440480c05011008030001850000410b451140300000c00c543c600404080f0041c2c009052014a940b80700c040c880c554005200448801038184806888002c000f0028401203566042840c03611b808600c2052190003000c03580c900a5588070704055003600c503501e0000001c552072a03407216465012115440c00d100440007980140c0c81040158080741400074006 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 437520071 1250 437518821 437518877
    0x1906030c020f071223030301030209071e1d0301060815074d1b0306160e06071e050d02070506040308130e090d090f12141606 55
    0x50040340502e84202c500199031400c40e1440d00820f07901103003a0030300c1e0003540404424030300d9103a0003640210f60300310000700640c100e0744252201d02070b6a59101c404c0f02c1072049141110805e020556a203100b0a20600f0810300080c281d0303002500d0907510b03000007803c5402507440a21180c01c0040c6040d0380c0100780034465442203280c00c10500d0f9003c07000d80090160010020701031043e5040001c074590750024800712000c40304020f52044c000302555901651a00341d0f6101040c8200c038044541e807142400b00340e40340036045100d002e1410754405c07041503442680c1030b80c403581c110005000e0440400d104080d10b10350b4007030306121881d0594003400c08a0902580e000d1303003015540682420002034403180100c0b01141d8001200c40d4840307410140c050404546640420a40c030004000e02c29442c901090a07031056585413180b01d00161354032130004050400d44103200400c43c0b0040c80303201080d01d181c3c040e40f44510490986442c981d0442e0b10481150380380d004140014030340c840511231303015401811440e070 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 437521321 1250 437520071 437520073
    0xf0b0a0f24020709020a0806130e0c12120a0f0f05040f0509040602130b04050a08070302060d02030403020f07030b0f07030b0d02010e03010902060f0d0b090103030c020607030e1906030c02 82
    0x80360402000110500d80300300d6500e030148403481c0041d90280300b406040090320035004295507604420304002c00700c4005440c018800d0030b06c0c0e44091078491840c81f801e0410503080000c0c1ca03086d80000c08101c24800501250040350003404001507020303203000010004020a5201d0311111840420010310005440c010001401070070070082c00500c040409050884504807a1007010350380701d1928802074007810b13600e98100d8200000205210308404050b2040c0c45003035600e035020f903550b0310310a5520005444003a410400c100844244115a81c0056901c94003c2c012aa0104500310180e807030714405620a5030548030400920040c800001c21540c0c21661604d0305001026595000a08184207004000c0c140583c50450050360b85080d048511400d40081c080d50701c0780c80070410404540e001e90030341c259040c9000d0100203035140030100c40e41a01d41590f540349800041b0703824050a0703489107000341c1c140300e2241c1501c000caa8034000810788030884500070b540061315041010f000d488005100c0825 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 437522571 1250 437521321 437521349
    0x20c0c060f12010501050a0806040902060d15060305090705093603030106080c0304050d111e010605042a0c0602071709130e03090103020f0f0316080618060915040f0b0a 74
    0x207da5400710f2504d801c414119800540d1214130701c0041c8492103810400d030b422504100c11045865014141202190b20b5614240200d680c5c0308901625a102c40c00354940c041030b0000455141560031440c4c140100c8102c4d0f0310756110702e00d00324000b6102d400d1540024258030000050250355401a43e081e0003049074507516085040541d111502c2e1800980c02000b00b1881e8215001300d180c042003884101060702c228035084220068206000e4a102c0c0034580c0210705104900c3c10340d91540c48588030400e0f08107080c0b181d1030030070141101c240c4200710341541c103543c007404584d0125001035080c00c00e22040320351040c0da031701d914018000314004005100d6005e51404d000396120172408011150250b02c24a03005a941c50001401e02e1140214140320105440c08400c002003498030802843c0c0340745541e180d283c4595201c2c800c11007604082402c002080c601580400c00074103050a50980000d00312a201181c00e58440104003200c0369040c056160a40ba00141d0321a07041c650b455001800d144210b0748a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 437523821 1250 437522571 437522587
    0x40212161b060b0409080a020f160807381b0601080318120105010807030c0801020c07120201260a0c0509031203060a03171c09050a06020c0c060f1201050105 69
    0x41e0801c04414054841c0b030702d480040300c02d541c0b00e5004110741d5912030310444d21b809882200941e200c5c000306650b501440390f480b00c00200340c000c2035034108a0302204010602182810705500c400c80c241d40041c0c614034042d020040702004820303800410305900320400d81c1c842d42c00440c9200f21440c4090075034502c1c2c212000500a02c40040219400d04000780c0301c0d01c111031035100209050b8070100000340703002c2d442d000010801000219448084a02030780b030907843c00344c41d610308a00300c1c852910030a802d41d01a039010000001c110030341341560342c01414846140140e0410b0491107480505001c040340c4030072410011040e500348981c9104400e079141040c14600e401000c01c1d43c480c40307141505148000880010400e5440c0b0622134007075030744007951242c0025400c0030000b40380c103d03200c0d240e600406101c60b224920300b03070f00c1603005070787d04040100015019a00c84a001b5802406962400c2c01800e030982e06944601000300048440c181103d940d804050301d20440c000f0044c1c00c41410048100f004007 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 437525071 1250 437523821 437523857
    0x180d0302070603021c020d0605090f090604030c171c06090608030324030f060703063c05100c020f091b030703090b0403020c041b17060f04021216 64
    0x8240c2c0e403603040c016903656003d00c3c0303c0600c14885541c004101c0c000144400644110340190080341c109a90600141d120300b40b80c0140d403031045642c01c40a0348440c0005010034813404a00d10806d00444801e071040c0d0390801d035030003168030000c0f00700d030b25230128103909181c405640710710401012150380400225050a240984134407000e001110548001c080c403500842001000f5a01003000030202d0320b080c005403401c1502c0b000210b0307084000c00d2034918000355002d8410940030115a92031106000521520242e0b1030101c46882101851f1000e204040f6003078546e00254002d0400d5501e0b1045900b00600c10444102c5912800c03034007070074801090000c1c15146031801e41a510139601100e40340c0d5244001140104100900a081030100905220a154012920b1700700800180e0701880b1040b604820086090314803488000040c541e02e06440d2485191140c10344c215500400e1101c480d4005400502031f60050314501c40780c440326005001c0010020800941e0906903418200c10902c80341c0004 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 437526321 1250 437525071 437525083
    0x1080a020a17150a03031206120309032307121403120613020c0102160b07022109011b051f0606020c0f0607060509010e0c1903022101050903180d0302 66
    0x602c0c100a03a00010824542d191401c201075884060250308066a980c10300401c06440982d0340c0d4446450402c0c04500501070b906440101505070311107950442c95641e490109503102180e119003c85185a40300c0108001c1c85078000500610003e46070405c81070070003a0740b2038400900c0540c0740d40704000f6404140b00c0e20501550290701241c0080c00d402107101404042e00c20880d14644651001494032040c444070103d0400d820b0140950380469582c502081c1c1c1e441c003000060700150890340241210350065080203010b00d1030113140a0144040c2c04003880a000c01074041100c444e00809540d0210940341d060071703000100000c03c18007556203800c0000c1d4840b00300441c2c00b40034043c060111001620358008660203da40040c007000b0f0b519180e81464001c020080340c502e140c1c01a080007200c3c500e07240c41d817050200e2410705507283c844d103154200302070010001c4001000c068509003a41101d442813250500c14030040018640d90403251000294141100c113205104c1d0340c558012201003680001c0e5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 437527571 1250 437526321 437526347
    0xa030b0601051308010222060c05121e040902030a1b050405012006100f270506030a080304050a030f050a080f0c09031608010506180403030f0b1e01080a020a 69
    0x41d55582c201c10503c0340e60001904540100e60001a0a0300115154960b0110000e0212640c111043c2c80744001c0700c0c1c1c904100d038090041d601452203105403440b040c00800240f01c502c024607100e211180700001c403a811a40c080301c0d840758084108520100300e4052543c02031003e4402c00800c02d02d81001900500407401542d04000004d82c03182807032901568011510066042103440d14640705507040038411160117030704440402000d0000f820780c6500075030603100120790300c0c080110b210400c02d80010000201110f070705100e520080c00204440d140154090707802100a4a003841a80c1000b40508141c1004041048000c020032105140c0c448e41c3c09810201c045000d401a0300e40c0207080906000752a120390317050040c1110a48bc00b085186100226480c1d01c000340181d80d030f440c04001e01c080b04800005861010313140000d00081c4240d0001c48040300c801c00c00907860140c03c000c00c1908446d6404142d5180081804c51419a0080209584144c44c0d00065240031714105008015045c9205 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 437528821 1250 437527571 437527577
    0x10b0418030815010201021312150c0507021c08030106050c01060b120604050a0603050f070e010e06030309010f032003090c090709050d0804050409030503160c02031513050a14010b0a030b0601 84
    0x41d0f00209603100f90125850b0004041d0302c01c0720b5503110703c80003028401201c8101e038080c40f00d240c0303070030302010038010307190007801548501e03041c038440c0d07001d1100004100d2007803c00380e131f03980d1414000520381c1405180607101d143d80b03040d1510300b41181582190040d410081060a050040458a00f4080d8500344d00c003000b5100828151a6280201c0c00b821880e04020701c0c60161818169084000040e00411204015000440c0c2e984e21030950342281010344103207415070000c0007155403a500881080c415406540340000d03071002d000902407041038280c2410030700e1f80f100105122603441308001078104900e00f1603110302d02e804d201002400c01d0409100381d07170084410f00d8046040c440c0c4d00017958014140a070050110001c98680200581d208445031400c0314107444042c041c241c46071103614045070703001d0000d00c0070201c2c00c01c0007000030780000c14a070410741000d00ba03030000480a121222803607105140b2030324225200d0118074256000032424500407610f02c8820070100380485800c0390010301c207003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 437530071 1250 437528821 437528851
    0x50a02070e0907231309320106062a03090807060906090b13051012090807030801120803190f090f0303200f070807020a030f020f04060b0a032a02010b04180308 70
    0x45030071050038140d5514540501d140701648186030342641c0585e01f020440d1402000415110740c4250390300746149a01c50001c0c1800d480640d492010380c131461501a00074105030900e0f80c0d850a4007840d1850070f8209200103036a005003040125000000030002e0f141c4220680d06025480789001003c1855220703880c4900c0d903520000d60803500410290291000d03000040c070911600341003c4041c0d500c498000c4001802203400001c50b4240c3c0c58456200581c032504191558944031070042081c0300030510031a055584940c00d128003200ca10032a840f031485004c079468140d101e8240a011a0700280340c0341480188004050518103d0400b00c0b80508020000191034038628141169280102e42c0020340080802c8000703c1481254801d0790540f034401c0740c401d003642030390400380029140140302e00804508280714180c14240290085100d1000c90a55803541d0301074621140c203844e071601003100260b5922010710142d82068024402100b0900e80c1d401551046603030002c3c2102002440d040d4501c42071 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 437531321 1250 437530071 437530073
    0xd0f031a090a111e04030c0801110a181701050f060103020306030c011110050f0907050607020a0312020c031605040e0a020d030807050f0316200d050a02070e0907231309 74
    0x84015031340c400444103041035802e540c1400c800c4d5150f216010985280440300d800244010050180030121802442040d00b02400307044150380d0b90440310510704a42c3c18a6a003c243c10300d5140440d907244080e400040b5607418202840f00046034007401d610f0405004204010b0642c50024441b1013001003840c001d0040804109864205000c0c120000340c020b00b801c1c14040c03c2d03d00b4a01c120b0040c1102029130703091a03a00c104001d003a02c02c0e442c0094010555450400c086082c55000755050649070054070b11440c00100024101180146001c0721420008001d01c01030030303d88107010340414000c1c0104910346e01d41e000248102c03607421000302000720600c001100144588152101e400809600c03507103a00300852265501c16044005c4000100540c55a01032a900940254201c050341c3e40580081c042c1014100d0f25a0f00101c03102c0c065100d1943c1c001070380c65000903058030910744040981881c0f42004c00140c41c50244034400101c400d14071041505a6032408941000303803c1803080098002c2c51 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 437532571 1250 437531321 437531351
    0x10e031b030405130207020a080114390a090e06150f041208071104051501080714131d040321090503070f0201030f11090409020607050d0f031a090a 65
    0x1240c020a4008140c1181c13800c2c4100c068004d080401e2007200c001010648071000207007212245103c011003150070001155480c0c000c1e226440c900c4c400c8640c9140301414100543c50506c1e007030800c8000b0071400140c00d0417141d81c0405200c000d401070300202101400c6c0800010704c68a840c4015038220310300048d0840c149025442100d0041c501300c0304a110794465400c201d002500544801d507280c80722004403881e50b280610030184a504007001360654900d04c0001121160340c010850000d00040a820011512102c030160401c441011450301c00c041c01c3c025441c0980c14030702201112401d0030070600c0002504850984088400243c140705900c1c0310f0050b40002e0001c94401a1290000180607000e0102c00341d8903540e03080c001c0e2004d200c40580641c84504681003e400d0b0241c0b0242806001400d14060b08500082c90000344628202044ca8864600b44043d0118001c0450b4244080b02104e82c1c050040d5926501402e908040444910000c00c591040007800b00f00910759550807401c882e50 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 437533821 1250 437532571 437532577
    0x30a120905091914040201020d030f060911030103050c030a0816020303120411030c0f010c03030911030d0c14060f01030b04020d05010e10060b1306140c060f06040509010e031b03 78
    0x3000e00400e418100f05000400303040e40b00c180350242c1051a0200341d0101188824040c136410703130092500510214007100200036984000341c500340c03100c100084030390706070240c403070a4148141802c3c0e49508d103103419880c0c40c20411009001e42c00043c005000f01c0e00440a603002c0e0202c40c8412111001140300080c2144911407402080f14411700502c0140b00702a64034028442c010381c11204003204200400480d04007000800e030024101d075075603800081c8650003d1300302d148141d00002401e20301d20002424444451f8910000868002c0c00700140040302905000500c0c44a02a04240c2040c0354003003203001d01400003810b01c1e00c090b000705045440703402c609080e040c0c0000080042085004640e5241c50503a6503000c481ca040500100f05840c2017021201207010b641c034101745403407400c2801c0c2c514944548249c028107106001100e0540401c3c4440d610811244101030b06a19121080004550000d4030290442c0c3c90100c8450752660000100e4000b007003406803280321440b000c06440c0c5544 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 437535071 1250 437533821 437533829
    0xe1501061e0c06110406020c090412030c110a080a080c040810020315030a11010e0916231306141321060e030301080f031c020904060b070c03060f0209030a1209 70
    0x6150041181c41300d41001d02400665149078295103588144100304405444140d40143c107a961380c00c03500c140e10b40207504c046143c0c13850381010080400011a0a8200948070206840b41440020f00e4806e0b50340c0501c90550003900d1001140c142405d100746a03507100d0301c00f4200804507038000041801c0141014100d007a41400404071111041246000d0a6841080e8030a601107041500680d030640361407020740f0300c0717051084036140f55542400f200301c581401c040300380b2105020080e5906002c04a020040550060810780c0300481807410200802444200002002283c0144001c418141e01441c1410807607042081030045441cad1005c00c0380b0b580c52102d200502091510304d00030509500800694100d03442c1000740c801404141d11456245c1c0b0034404120040c48042205564420700c56000d094010300141001405a8442c8882c004a0784910425030b00e42d046c0180030030401c000d5005207061900126030075070825000c100460f80e140103455008152484034001c5d03a442714881e0b04110014 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 437536321 1250 437535071 437535083
    0x80c1e12070b040c17070e15012c0a062f0d0806060f12011e030f0b0c0715091b0b0f030903070807120305090705010903020108070e130e1501061e0c 65
    0x241740c40703421881d9189014441e214032000400000340c802805401c120454001c10f8680b03074170a8580c01540400c0c0002c1c80302e441e41c000318180000f50031703454888150002d44425116003079081030407050b00001308a01c000c1c000d6942c501c0241408079040c0416001c40c503100c030f81059040e40c0c54a1380064040e001c2c7d4501007019010100380d1a080545200b1464126040741604039481c103030b45000308481c901e040c00054081c0d11004004000214201e80d00d81e4405d2a41090906041c4280e403012006000603210003502c44c0c40b80660b205100d89c812035034480007022200018158501000e607459401918002084401c0100c001400070354148101c076420790340160b600e40d42e0300581c5441c1000004444c85a80020701d40000100c6100e80016110190350050312500d1a00e07255600440d407280008006400700244404140c540d40c5450990840f55404407001043c0c40390707240710941c6003030304000b000b5043c3c00c4580010840c140d00100d100050703180801c4580700c00503440e803041d109204a04001004 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 437537571 1250 437536321 437536349
    0x1003150f0914070e06151603030905100b01120c0f0c0203070302060d02041a030402130506030c0d2a0509011a210415050403081f03080c1e12070b040c 66
    0x1189101048200c2074034024080041107459150500c42d0040780c0d106c0b01e40c0081010803c07a007100c848041c80300c084621070b00d80420314042e5a0788190810900d070b00c000c28500c1c0c485441c181c65603042100741c2522034100204200400a0b00c1004150b07d47c2002500700b4030050f00740c40c03000c1d51001d0002c1400303141c001d000d0503610101861010000d5005110700c208000c001030315540400074220840b4001c6400601c62170a000c1d0b811030600003010054050b83c0d0521030340421802c9178840c2d2440e45c0040d0300500c800300b20307007001d203040c0780d9404030f4020070740a0b02d035858406118540d00c8801e01030544410110700c120384103815048038001c3c03080954a03401c50b40d18008580152514a0750984510301c00e5035080142d4000800c188203440042c0c0d00240071070000702c00075919580c0442d40351910148640ba0040c42552602e034a00700d0352045200e0705440c2c0200081e000e8650b5500388605c110900e44004240000004030b41154602030b603080103001c10850004601030007150440600641021415815 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 437538821 1250 437537571 437537603
    0x402090711010e06060f2e030e0a03030b040f02070c0b03100b1201031e0843020a0e07050301031202030d02030a090501050f100504050a020f0703090e1003150f09 71
    0x19039240205c555030720862080c0041c00881c00d14807083c072120502d18109940640c0e101c1c4201c0b5540510356160f00030542d41d2405e029204000b0030440c9000f074003a0f200081e800c100c900600c41922500c094801c80d45004125440001c3c490007441e00861b0400e220040e10307510748010400041e403466000102592011552030060401d48034024100c80c40350b003811003e81d68140c3d046504428103040500401d03018044112001c00401d461702d0074002c90714550000d04042c424890640d0030450101c1030110700b00380304104504014038030a01800300c40c1000e188034942004018041d01c41400000c2803012480007840d4094000c0003510a003107100a0295100e20b4070301c2c01d0300003c0038141400e46aa44c03c02010800a842e590440ca01403032846010308205030900d024000502006841e030490fa9030708201c4e24488505807c00b4042e01c0e4800e035075400c840c03860614450241030000e4940404042c461008000040680340c400e456020711920115941d07000420f0315000b02060007000c0c0642d025114401 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 437540071 1250 437538821 437538823
    0xd14010f06061701090522051c200609070b0f09041406010201050a2c1002070c08160e040f1407060201020c161406090d0f05060115170402090711010e 66
    0x11401e00480c08070f0200a80c2c0c0c07500c2060903540305580038001d100b80d1060400c3c034a022080941003150042c000c481654811064200410000320084000210b1003040280300441e0034215802c003040070340040c100b03814100310484c0c6414280c400d03aa900d002c00a840380100d1080d01c15a82c00010041c400c00210010305607210110004507562401540b0300000036102150912840781d11140501101444080798100d07480003081e0303420301d070f4880d210748010007803c103140e40003d0082301e2007116540300c4540303000c07401440c2110340104600006102001840100866009154065044400c008011100f0304000041c400904c13101c6c40e1031300a0341c1c804200c194054004010b031000040444407520402000e070300301c6400c0c80c01041c40d403440c07080725060f01e440c1440140099040c0209012003001590303a4607850441c14040849098008400401c004000c0301400b807104000c50070003504051001c40340203000e00005100174490708582002c00c29291141640100309036440008000102c4540511 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 437541321 1250 437540071 437540087
    0x1203110a0809090f10170f0708010204080d08010e130f0210030c08090c03030405120c0d03030b0108060f1804080405030a0b0f090c130e100606030e1501050d14010f0606 74
    0x10b42d01500e401400309040d202c1d4100c0142c4a01d1500d00280311481c1051719800350200c1415501c1402c2c400d214841308510001e0210400800702d00d0001030b60b41745003091f16400c1c50b00c440c101000b800184030040126400840950342e0101c00c4060306244800c1074030701410650701c1c402029401c91400288a00f0f020b80540c0800006186521a05425030f24050a203a4600d01300010300c0c1c241e0000d110821442c1130403254046944146816541c10300150b0011820034403030f40b003054000076110149510156007006803907800503000d90344000505089000300b81d210305180c804010084c200310014091000c41c0041d0740c041c0c0f500406480d4001000d0030254150081661205a1034110501051400000160340c00d02164007515440081e00b04a07034049c014100741424200c240102400880e20960b20700c075107409445951000120340703940310345c02ca191840c480800c500d4060424014007050f9681401c282200f680300c0d802c12680c595182030280540390b116205030055080c900c020588503003005007 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 437542571 1250 437541321 437541337
    0x6130b030601110309030d050c010603121701090b010519090f090207170a0e130e150405060703050411040b0a1208040315020f1e13090c020f01151203110a08 69
    0x1410f9581d401c034030b007094076071003009207450740755001896488040c1c1c05500509082c4041c100001350349940d030344941402000301307510323280050242da540c0c440c2582c1d04030300c090152064a404005030406100042d00508c5000e0348132201c0310003e00000e41e0b051107034150001600c188061000308554940c03204000e5082003c0031a8944500901e0041e074844250a43d21a8100c542d60406e0350048a800e01152441d40c1c510050103e4481090030101402041109010800c06085013400d16080c01c2c4035060100260450042600388010721010400301c0300e6280c101c072803c90340041d02140e8178000440109450f4414581140950340000c140052400a041124042c0c40950030504551554070220b21503100c85026091060100780100e010401e01d181488224080c141c0c500019244070000c4c80c0c456502c83c2a00946548012031115030500035030400e41c500380c0090000e485001103054048010340100340c4103048410030102030521401c401e6100303490f18001d642002c010307410607200652020710 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 437543821 1250 437542571 437542577
    0x12011109121b01080c0d0c020c040b010305040b0408180307090f11070b040b0a020d09060506270133020a1a1501080702101802090f100b030606130b030601 68
    0xc1d1040c880318001c00d40c0d0b0209080c0004000e0701504680042d240040058184103003072406020042040110744200b004204d410b400801440c0303107d4080100351030340729503003504060030070050200003a0101c0700590042e40c024201d9480c2c4124884096070364035128013295051152a0000030600f50641c44002c9003a00e40f40c4c21f2010500100c032014035031061140c01411200c42100023000b00d521088269000450400301515054001800342c090381c90042040d6481c0b6550f400f070284c40e1800524903984914803407104c2050401410200003403c50501c10421ba04151a2420380031141307480403d80e61141c011203441071a09e4070b801c029a2003103503076030440c0d4803403217402d1035281d00c00a00520741c8034500c0c0740e01e4514010007480c01103031103402c05411401980302d00305120844184a00480300b0f0724502c0310300402d076410f45004200c1c5110000d0403842e84864424203104140e034102d43d20301e0640b90030384905031750703030702c41501250881c4201c850551207851141c2c0d021036034540c038070011401070034266 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 437545071 1250 437543821 437543839
    0xc02040f111c0204060906030e01060b0304060b03060f1501030e1c180902030c0406050d29090c0c030405090403020708060a050105091b1c020d050a140c0309061512011109 75
    0x2c1a210700324483c40c000c0201240300c0e44d00800c800e6219800c81c0d243e01c2d402d0000070940b80e0ba07174011100b00742c006a8003114805d80360b900380c0c05135080c1081215880340507501c0385c1000342000700e122400345044100c00b504164480b4a051106007042124240e0020b000ca2a022003040c0c03081d0082045c80c0200c2040c2d00400c1105002411820f1802903e0249003e60011780c5001d1070080c0a81e00703035001401150321581c0720305030000c1554450082d246040220101808403070202010003a440e0801065600100410301034001000c0300041070384e0503101c09030781c1c0e0121510380d410140d00e8400140d00004040c45802c6c00c0080d45903d82e0001c074103c60007039812441f41d44941c1c01860420f0841803200c9103401e01440308001d00c90820840c40701a40303044000614010340e41001d0815120211981034100c1d8031904512040600091801d51000f441d4a0160440c1040343c945074a03250040c15903030405a100804400e29aa000e0011440b10f0302d15008008041c0007000d001069000000c445114107050 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 437546321 1250 437545071 437545117
    0x5070b07030b090a02031509010612140438190b0d210905031905070f030503030609041103010207050c0a0803040602060a050901140405011406100e010c02040f11 71
    0x70703000d66005400018028981ca50321041030300f000b9000203000c0f07844940c40c100c1c00c43c61511880304540c0a03006039603a0300512080c41d0ba045003500d942d030710b030359010b14084003c0001007080702c0e0b8064050920709048061783d1603800142501c0103155652000c4980c100428080c8078885410740d0b100360a40c90380207120010204040040400c480d020151800603880120303070354200e00d08004482c000c40f60926511607501c81d004039103406a0340307043c1d00b940c203200c60400c81440702c1004240c0017484002ca81e0703124a4199503a0580368000507040b2400b504041010030700f0000c010b004600700c050050f00840d107a10190800710356809461540c1c1d4018210b400010440d008040125010f032490394004183c992234107840c500040c030000b080d00d00c1c00e55032042c0e6013480c0c95440700ca0034001c5c1e006d14004515850020165455004050f204034417501e400990841d64030382140500700c0c40202400c00c0a000141400403d000e00070300e00010503941c0c90030840c8000348010348040c103208541d1030402c44140d02a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 437547571 1250 437546321 437546327
    0x901090b0a03090b10050f01030c11030c0102180307030c0b030405070302120607030b01030c021506030a0b041511132c071706060705150a15090501060e090f06060906120705070b07 79
    0x1142c010310340c10450507d4520350550081d004800c00070810700d440720204a030410316a0968000100e002d00380d940014410082810001c080480700f14101c01411480b4959a1041004451407040701030400c40440018140401400540021a00136141ba14241c0c4041f01e41501c0340c0d02101e076800464981a107080040d4424410411403e10540060000b20300135036540c24008002020554103120300e005100001d4110100180240c1c07003400040f00c0340c0d035403101190544d040c0d000e80c890184010712400e0184504c0e99100000c840741c0c001c002c40e01d00c0740400c036121018440e065403141d803c01081440328995001d91f520f44c0349028001c801d1402d4a0b92070802c5080d2013a20b40140081c5d11003000c08050034482040c69070401c580a01c00078078880c2100501c0702820042d80401c4400381d030f54004000040d081000c2484200c1c08a40382c0e411450500c1c1c01c40500302020b400d0038080d0502280c94401c58941a045a00ca0320890340e0041c55498200f20060070f0341d100031030854940500710042140e0fa40 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 437548821 1250 437547571 437547601
    0x342115090c1806050412060207021c1406101a09030d0f0323340e0f01170f10050607060606110a05060105010c151508210403080901090b0a03090b 64
    0x10f5664885280034500400824481d18039941912507507420402e010041c0d82e4052800a00000b40a00c4540c41d45607007007030100e0b8004400d1030ae080b0b4000600f080f111490307083e401011742e20841040c1307082c500c00207100440c5001da0603c0a1b0103114400f90123545c2c1d9000640c85500342c0350b56030240f00c070070514007604800000c0100c40d903102106040208590310780c0102c603072030b100da008951501c0c2800141e44801c441c80c0110082c1001c150071003403074469800e1001d0302e01240d1500b030130000899030034580034070399040e00109640ea00c0001600820107125100581500804c03009207115156006420300038010100e0788107141c00f09117581105030130002c0c0420460303812500103000d401940c0c42c2c02d0040d180f4203014903040b81c0032110107007848900f002501c10340707441d004400c0a450034a070800c0c0d00c0620340003001114000f02201106855280340da050110780c245c03948014a40d80b038902800040c2d0b00710600e5000000d40784004170300307041150381c142d00c03011002d0300405a10240d03460f240038503290a1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 437550071 1250 437548821 437548829
    0x31b0506091506031f02070206121009050a05090a0f030908070f0f061b030c02040f050c0901120b1c0f0c0806070e010c02101d030105342115090c18 65
    0xc0f141402c00c01743c040607903002c3e1407068000b40180d403500c00c00700280c4261007402c80311100b0750380c10800207014003242c0d403041c15440314940c0c60810450038003445d0036a07a10a8240011301a080184884040500c564400300090510500305c482d8a61546459903d00060f400781c00e4100c02c4201c0700242ea94860004c0340c10401c030074108040701c51503a440491701001c41e500182d81040d1602e0328007032a001644642486400b00e05000c50300c510340c0030700040010131000d80e80c3c0691030410340c040d242e0b40d90724010f41600700e614020f6014010140d250030b8490740442c0c040502002d5040701c000482003000f00c0c0c40e511684803035a51100c882e00d03071401580c1c589480b500c00307500140951140602140161081c540b95280c0100c1c2c803c00808045c00a825643c0848149400b4100c03035804203104052002c105401c01110402900f144140100080134085a680030245104804000600e8450b403a40455050207921100c40090b0740c0701d00107000585070408aa0700006c9000501c440c0090f04200090191 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 437551321 1250 437550071 437550103
    0x180f030307090b0a0e0a0b0333010e011101150321051801110115180501230a080f0c09071b021e090a050906070c030c031b050609150603 60
    0x9641006040000c3d034004003492000e00206010100c0b40345e480c212030303a004001c001c0501e96030340350854000c0c5400f080c04020400a600048100079440c6544103108920342080c606001d070b0002c003400403100444a05580303c1c66520303005c0c01d000003905204020094034011007003c001c035040e03811b0304480a05401e815100241e014800c8400044419219422206052400c104110100160302d4211102002081d00c40c0400910800000240000e0070a0b503500c00f0b28200125850300503070400b90310600c1d0300c0840d0300d84180a5413440313075980031805010300340704c1e411036400d0110009415540d502ca07503460380c407440d06a03000031100c6208001c42620789464624110340c80a044e800e02080307141442e4224031410740f500c012106625144d00c4c0c50b100316400303a800306a600340b4402c40e504002014000c0c0c41084248c1601c3c402007500025413844590781860200340c211221400540c1455001c14024201d00035441808185d80b40000d810101e00b00c803030307000540307a29100b007016540c0310311080c02004 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 437552571 1250 437551321 437551337
    0x2040b0d03020303070c082101300609030504170d030b0a081c0210021303150513030e040906050117060106030606120515060408150a09031d0a0509180f030307 70
    0x6102d0b41d110344138144600c03415130410100410b100322a0408c81c400b43c22a180c80c400422803a03403d80c4414100c4440c82000f040800c68083c842145099181c41c080c0105480782c1a440030544110110f030010211429041c1e1003054034a030b0103448e02c0840031111f0000b41031038036886561425015030b20488003200004d00761040c400c507030f00b0303050106d0444403415030280140e5903010002030f0000340610300d03104841014850952500e00a031604c2080d001039a035240904105541040a19489c0015010300380591200420300002c5e01500541c800204580e0404000140762b00c5008070599210300590700b40c079442da07200c038000c0f0102c402500c40c07000050390031102e90341114150b07407201e43c0040f80e2544854001110b9001303c0c0309036210342e112a5490b4040040c1d03040c80040d001d4041d80010455906000c1d001d5152401000310501c1007110811112403414098960b540b41c4081004110280c1480b000d4074103690100f403500e1b03820b90514054002c80c45520608640401220321540c4e281d1235004e5 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 437553821 1250 437552571 437552581
    0x10c03021204112107030302070f0608010b0c0c0303070b15120d0302070318060809070807050a170a0506010b1306020a0203030d0504020d0b130309080d021e0a0b100302040b0d03020303 81
    0x6a55240ca00442c0c1026030f8400e00c004c0402c110101000d120004002000c2030f510b103180c000d00c2e044495006d81801c42c1264018001d0990080c0400e045682c48030f011910344010042032400c00d044002210741c548000107090b000c002d0007090207441050000c2081000c1c075150400d00154a81801c50113050340c101151013542e0746e0086e40500701d118081d1030100c0140c0413444503002c0c01d0103141c010702c4c080b9a54400300241c188041201c0000341407048050b000462422021840b200c01c14064001c1019200d2a402c140c0c070801c01020090303030340020031100d143d40d40c1c104400269100100061031250300d0f40740410414000505403c50541c0503006518000c1000403001c02400060800c03a44440d04e0368044010032441003a0030700408000b10495010204c0c0e10f00075046245076403001c1c0498000010303e80d0043d40101d8080340d01005464440b80c494400a80b0f18180b008801d0014001c114840c14010084408100c8100f580d100350b9003005013135004401c001ca0b80005003130040c010b902c02c10002e2 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 437555071 1250 437553821 437553833
    0x906050a0e130e1006030209071d010819021204110303091516050304090c020c0a0311010c050304051e03070501170c2506021e031009111303080c010c03021204 70
    0x1e005400e880000103407002c000303c0190401c941648101200350300c5000034002d52414413030980d004070141c01c2c094003015600612038403105429074014180308801000170541035488084164580c9072000841da0f031004d034810b00d84000d0b070903035060300d01c44400c8a001c245410000708654040d00300412000480841c401d4065060f48200c0b4200c1d25054030781c4045e030020742c0c100040c10180c1103491010a403006456002490b1509104100344508556402000890000701c040624a002882d1013515070519040452840c0700b0303984103070781207848040f06004a044072544004c516408406071944250750380c0044510300f0303080c00302001040d02540030600704843c1c08018024070404180034500300003007a0b00c5000440c800c040030794416400146c810102c0c68561040c40506402032841815070900c0a155180018140901c030300a035035842c4901ca80b048013409a072903802c0f4991210040316203914150009402166a0100c00d41c20300904000362406030007510340d01e942d03600f0355840b80c2d82c0742c2d1200 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 437556321 1250 437555071 437555089
    0x1a010201060803091201061d010e1501050a03020a03090215070204060816050d11041508010506010309050d0e04090503070620030c12060d020909071a0906032d0906070906050a0e 78
    0xc0045c1d903607584400901e20b044114140856400072441c502d541d03261400c98841000d0051400762a150709168400340d0743c1e0000c0507558042c500e40380041e20f0381c260b1082580101001c840103136008580e140341050aa0b001001003080313610a035400d004496803942c640360b58080e06188001d4607440701c48180418102403000c50900c9008134512803000c0c507110301050449403402049400300340380d02028440800240103443c6c01500a10301000303030b040f8540f0f8141e1601528480c8204118158500c08003954036034003d400340070303005000e0320365035401071419000802109202020141c0c0142303110030041c0104040d644119000c403811494004079010ba04100c01e0b0007400c02d680110013800c05405a282c0521192064426030b008000d558204901c1d11013404000001e4240110100201100c68480406503504505441d06040c0b800c8100c004100303107101c00f2101e5440c50b8010360108001c0210008843c1d0141030281c030742d090305c81c0c0c94450454461140c41180070102d01c1035900b4161900700400170f = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 437557571 1250 437556321 437556349
    0x30b060f060d05090c0a050d020109090f0608060c1201060206010f030206071a070c020a0b2a070803070602210105090f09010e010903020c0405060d05070b030c120103061a01020106080309 82
    0x8240d24101d1022003003000c99000b44c0301c5000c0f90340300d4107088a050803ca03040c10041e11048640c0061b4042d40d90009001c01140d00841e446980c6440750b8403d0405c0b11b80004001d04109015039409113000c980c80f00440c3c0010010200c031584a0000203085400412100d050b50b03801c01407808202c2c159000d1002c5944800000c99581d1145c41101185152118080c0d014110741d0751800c401140c40c4c0100200c0e0085500f1440c0030131020041e41c2440c00c03084414141601054288600c00b0301c07040c43d018200724180d804040180000104d40382004074960040861208140c801c00305c40c00000205c50741c1c80d00c24040c568011926a0205050030410025185e004110790008200084a64030031801e4844003c421405070b88a4418240c107881c241c000c0390740c8030b102034542040c007840c1a100d103583c803040351244110607100000418141c3c0d4090081385d20f18031a0b14009984c6503924940b1b0001068602800014845e604441201540c81030280800b103942c0c0c0e20046090100032801c0141f48189011 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 437558821 1250 437557571 437557579
    0x240e0c030702031303030c050d08070e1c050d09170601031208180717070e100b0313021507050f010b060d0c1808071a2104021305010b2101030b060f 65
    0x110880e44c40b001c00c0f9951002e0b600c42d991310000e4008520300b00f031800100c240c200b8280130f587e100b000f5116510544007501d04408640405800114403003041c0c1c0c00642480140280c051203c0c843e03403540e082104241200c0c0c00b40c080420381442c58200c00d4856500f800000c1c4140c00051801c01518429003269401004144030040e02c10400704107a86800000d6001604040c00d003c1e0100742d400081c00004018600d0220043c031501e0004403404140109002c2c2c0045602c004c00420300c0c0b540d6561803052082ea01074203179650810f07500452031151701b0007c000c442c03030303c0350a0700144d2005c0d060140380d120f0384c0040c081e94149109010118090540c1c1074030b0700c04006056107034800040c4203044207002401c0c10009440d490b420240e18103490401e50301491400403013044215181700008040f51740e019103a10701d03801d041d00c076440060f81c0040d26041140031a82804008503107000002c00500c1500341e4070101e040c1c44181c066454080f244e00344005003411101500161460030310412000200740010 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 437560071 1250 437558821 437558827
    0x160305060a050c1c050a140405150705040b070309151d06030a0905060411010e010503090d0e060f0c011a0a0b0313050a05100614010305010b1c1e240e0c03070203 71
    0x3000600c2e0304003134900b82c84103907107450521000c04000d01c1403860032161006074031000d06d0305445042c1d680340c40351030324408100d4000000314058442c00980d805899160000c81d0b81e1506410002c0a006044c010b00c003649011080141c0850700520051403c1810800f00e400c10724003c03800c00c202d41d00020207501c0c19607242c0c58440c1c006981800814440d034820103c0c8041490755100060081c9c1c0239038036480c14440c040041c44011540020001d40448084c90408000240c10011442c03d0155128808110714045115046a50b042d080000b806002e1310041c1d500510f240c3c1000a05005072240015101c07080000c182c500c1523501c41000c0c414080e804075001c1030039581c0c80c24a000600030346441e0043d60f81405024011001c5910951124246018001541450074100c0c3d18480c110304102d00301929a03021400c03030080d4109500e4108200c481d4140769414000100c09808504c940d2810300c8404000c11000d081411541003d8944140c0d41c104070b43d0b5003aa003c86290b002501c4c0c0c3c4190300c414 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 437561321 1250 437560071 437560087
    0xf0807180801092612041506050604091a0604060e060d060e04081b060c0d1d0709020909010b040807061407120e090a06080607120603140f160305060a050c 68
    0x2d028200440e40f20b0b140c021a042603801114105901070004130b80c28a100f0491300514090080099401581001c00d4958108000f001140142296885650000c0c0081000a881b000c02c3d130050803800501684800701c0d4801a04100061080d0301444010500c1504081c10341d00340718010301035140c07a10000184080e2034040f0302025120031102140c0324000001e0150307842000c29080d0342000341900083c015400c09810700301d524080c1071610281c091b942c441d03404805000001d41803030990341400b9a00010303290641300c0080d51101b8441c03400750807100000140524107004560488015101030081141050021540814120081044058140501004505018190402c054580c0c84121303041000c14184100c69400a203040c0352549844030402c420b41c00410340d694000450324041100e500192000b2004041640016200f80c01030380c541c3c0d5085600007205039101101004464504843c4140750306403241c10301006001c0d070098004552618840d410081c0c12007104910141021a0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 437562571 1250 437561321 437561323
    0x30203061b040f080313060201060e01231305061008040c06051b0715031d1c030e070801060f1710180503030f1807030b0f0703020405030a1407060f08071808 69
    0x2d150131880380c980000565548518418170700800800b0240003c0c840d0904d408503403a050001481031440d40f184d00c1d140c594910002140c224001c180c010006a80d038156601a44006c00048507e00e008600700711540c50610f0103000c8e400e2040b548080080700c00d90500d401191646c112044000040c000b200c02840030303080502c81c1002803c40c60494140c984101314005094984410049210304840982034031a90408110603e12440066140300407103c4070b50210010b01c024906000c99020300d10000c0743c540c406410000c104c41003103080903805038481545400c0e100700d00003011000d901104c011280010103401020300b25901030030140554a15440700d9007107600c12218070584c4101320041140020b0b00c240003540001c00d41006041850545d9203810b028000500075410b51001034000606c220b2090301181c002c0c10014040d1158440c032490301b440c00914400692035180262030001c1110340c031500e0145400805907540040715181d8501c1902c8196001b014415411240080845c034020 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 437563821 1250 437562571 437562599
    0xa0b04021201270b06040c0c110a051c020f1503070c080f12070216080d03090c09020412060c020c091302040603050115030c05060301050108010608190c0e09060901030203061b04 78
    0x1011860825010b074506281444d0000b0700342841940703403c04258140c0c3d07001107000304031640300c60400305501040740007a080e120b40c0da0144d0751140300d44940c4c1008030040710044a560b8800d0310920310203803101c001c21252440c0308204554401040c000141411b10801d5103a060b2406140d400c1c0c509903807081208072035130143c8075940c040000340040c800300780d034100100303070030203071194002d9201500781010540c5031078801202904043c3c4030949402031000640d8414010580e01008550310b0740e84900c5003c0c2031000c07102c00c0e116603241c0841e00d00c5130703400421010052040240042090341c3ca0034200f0b0030404c00350500303903001962000d000c80010002d00c50745510882c03c80700d1000c92031961600810115151f0002402100f06000401903660410ba01c0f0f13041d40e9443c24204840d90301e802d0a4a6610a00554210041e081031441c5020540201c00b01444040a945c04485582c581040c800603c10a22000f5010b0340860005880e109003200010b01c0304c540c2060442ca4071b0368a40313910302c81031 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 437565071 1250 437563821 437563871
    0x2301020a050301030201020f0d0f211a10080f04020111031204230f0c010305130b1e010e13020405060a09050f10150c06020913020d0605040c020a0b04021201 69
    0x15038004014401c5d036030100a8141003030348090043ca101142c20000500036403d9030300351020300c001a908090720200f0502c1503840308105130810000855400e000d0645a40d102406074052010400d484c01058030544815214030410401c01c885921036500440b80352805820040c0306000a01c40601c040700c070b03501820f02943c00307541c98440c1c088110310f0440328603030113601c41c41795035101008603d6200400700c2d43c00c0c40d640b803d007070015071070b5218009101d0398483d12000914083e100c83c2000317402c0040c400005018443e540a8a200c2e80e02c81d142c40702c00a0301a2108440c0000c007660b03080062400d43c100325030041028003542c1d1460760740c0c030708403050303074400d0780e89216101c50a030402c10f42c45075001c0003000402d4640141e003441040c00b00054001c5d654040003800e242d40000e240145921002000300381003414100455659003000341c0c44004243c1c60094a2045003001000ea500e03030301c0011030070600f41d045030418030b00d2385072a42002448490100c0005c065501d03550a1007007980780e4860300c841a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 437566321 1250 437565071 437565077
    0x190b130f0f0b0702030702090a05060609030a2402281b0b090c0301020313030c0f080f0304060f02030601050406030b1201020f1201050324150907050a03050f04030c2301020a 76
    0x40301c030351402c8030500034000c2101046510900803000076a5500b00d06940041c0d040764000f904da1207010201d030648c4560007183c2c1e014411103204404000c0660100f0f0072141c0e0720300c0808243c458021300441a40719950302c0108a4240c010b1542400c2c100c40100d40c2600304609240c10b100d502c0e0441d4528004250704e082e07454020020800081d1001400b0620042c0e1044000f18558544188803105c10041f503100a03003008a54944036040011140f00d01c464580c01081041c0c50705030b055491907466204590448006040c09004d000f601e03000c1c02543d008031b4058413030714103103030070000118014403c10102d82e82c846800c0c0800b0701010741c02c3c070090a1200100704000d075a5044080d520000c290103911441c000c0c3d004241d00820315010340ea201100d2011f10102c25060780310901c0340c070402d482819406034006e424070309020050380c1000c0282524a0a6107051103555503165100104810032903003d00420a2800d00c0800580d0900444c0070604c800c1030030b5010b4040160b81103003260060b5601c4004 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 437567571 1250 437566321 437566343
    0xc060e04050a060f0b030403170412020d09030309090b010e0a080604210215040302010b09090705010201061a030a0e0708070e0109050a02090f130915020a0801050102190b130f 77
    0x3400c140c025580d100200001c01c3c054140703803c16180e0040080d1080714604480032000c1010144252030000070642c0c14a0202d280e8102400d0201204188100000c0584103e04a290211740580c0c1500102c03501911007004407450524008050588500b4032410005400902d240c1551000f4001c0d01a00c00741004003110300d820700d003458006100241111000428041030b4a03c1075000415a08601c00d03801000d039a61107629007640034010605203e548056840108841c0340c400282c21001c0300c500760300900c14030307903100000d03200d420031400c004041081c01c2000074038645558120302407480c4a8011900c1041c0e90388070ba582051041d810403031000340c15100410034204240501038000c40c488504501d403c0040d000941c0240c8414800b0f8095450712014280b03486190380f0145a0a0b0004402064140a00c2211000f94440c490b00c1c0b01040811001241c43c1d44005800e00041d80a07060050350024991150b0740e9580f0000e008410b6604802590070018000511010489104100b1004 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 437568821 1250 437567571 437567597
    0x3171f0b0a111207020d0201030905010903120518060f0915070903020315060306060f400b01053103300e06090a0512070812030103020d0803070c0c06 66
    0x700b10308006070505541d034440d000f00039100944400701d54003d07604960b100b01613034080c40140d000d8400040058095460203071454240754000d1349041487c19110010045503640c0d40c0380c40c1c509164010300003c01d5001c00005070121b07030441c820b550000015000c4504c04164040e0451200004840100000e0080c500400450904000d01c84000019210101061600c07002196507194020403052040d2003120620206480705c5540c0c107440021066074400c4d00c8070890309109407030191011036002d00c42d0590303500c158a06910a6001d942016900c65107048030f8404102c0b01c2d0007480042100c0260300101011003001d081e41d0410007035100e01042801d02c3c01d107000910310164043e4026103c0c101c941c0060b011a40c2c0404105070174001100c0240e08e600036032000c140320025a07004550010a0580042c0b00d581c400160402124508006c4440803202d40140070514002844000d400040402c45600028425030181d90301c0300880c0f82100c030081d9240c42d42d00800015900c044082104200a00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 437570071 1250 437568821 437568827
    0x80f0c07060f02060a05040803150a0e070c150207020a0e0c0903061006080f0c0d020d0626070b07030f0509221e1509240806010f08060403171f0b0a 65
    0x145c0c1c0186482da04018916140c6c48904c210321005201c0184003c04080c005060303520020660301606004580040c00c1c984410098050b1008a43c01d03650a10311000c4003a00c00154022103d003507a020706144e04691410000708200c0f00050a03100328000144000700d001c0c4c0f01008410f100c0e01c820007029021915104014011510241030340d611440c0c5041006110b6504500b1200030445883c1d0040e942d541c0301090600a000c49d80250064100b0f0f07803002510b1041c00c841002c044440002a2028242c0c0d440300e1945a00c10854010082002c0340080c4525034001c074054521560040d014212810b0001040d54288142c0d0f54054a07041d640e81c0d141e0400c401060008001d04002d10307080241100d1040050010007941c40751400a07038035603a04030480b00c03107c8080142c0780c07611a03c5250040d1200120b6032100d40034082d00e040c04e1a480f00c0050748100002c0d00901458043d102d00751010501060100e501800801802c0d420212081081590f1000d12140c4002c02c03000c0c3c2c9240e02c1d450070740390003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 437571321 1250 437570071 437570083
    0x4030b07031a33040306022d131202040912181401020606040207030311030106020a05011a09180304120c0f0f050102060711121207030b1903080f0c07060f02 69
    0x18003030901580c44400d00c0003c026594000300394200703950007401e190b0150746014421a0070041c403090000c50b5442c01c000122400d4420003882c1c5100014225a441c056025800303000d000c54100c0784020010800c0d074407801c40c1e0b0a20b060000d0000b280c3c00015403140060501482d8041000400c5100307224620720b05070101d100580900001d002034450303040300003599290007516880c8541e03030008070441050b000303510040380882d20410b030980340e60f59040b010303407192140d94003a00c00d9403c20070102c04c4150071155004015400600304d80840c2c40d500042400072020b1001d0084c14802000301007061a000000704003c01e01c10246000d9a904019101601e00c816a11980700324004c4101800140c0e004200d40f42c2c44900d900c1c0018564a003081203c1c80c0980e40510a90b4154000800076528506040031038031400458405228685c40b000501030140b280754030f4004900f2001400340005010b4600a00c29050034080701803c1c94070510200d41090300c41e52040010500f5481d40c4130403a0380500030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 437572571 1250 437571321 437571371
    0x2090603190212030c0f0f010525030213090f020403020a0503010c1e0c0c0303080708060307061b05071a040e1807030308070c050a230c030a06090804030b0703 70
    0x50300300c05018540010078a249840e00a01c0388450044000b1420420825101c2d0800c0e42e000b00d071403101b1900206500c8018210801f9000c0d400c3c803000802c8007a190749800301000840106e95200000184100d00a40000c500301a02849200d000200c0c0c403864000c200d40300b0300c04080140c1e034520398810440e084421364400d0340240d042c0559420b0740c5800910910101105145206d068140300300c0880f00000b8040005046142c0d110340032060680c40a2424859003580d12110fa07240c035810308059440c1078a20540000505040c40510a1a4101d00381154184944100c8407440d8032984950880c0403c07a280c04c441c220007203000c00c028000d2270140c0f900f0506448000c4200c1c0c0c1c001d90b00b503403070303000a010284c2809814000710307440031b20074610008180d4000c001d41d9a050941d103003a40d111142a24198040055040645032003100070880b60fa00d408014010711004895903125400b070848030a00f40c070b49803030a22000002c1107260740d12030320490f15981c0003e118282d4102c2e0503501681e4140d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 437573821 1250 437572571 437572573
    0x80c0a091401031e0803091e011a130e1c0e0117010b070305270103050106090b031503070312081009020328020c0109030e030c100504090506180c0702090603 69
    0x1600d501c40d40c2240300c410341582d070048100700345540c03403100c4a81c2c200000380006001c504008208a25a0400f0580c0c401e0074204904e00243c8010302c00c007031f50a071820340000a2246501002403180c0707141541c400410038024090102d040018002a5070034010380d1000841484082110404116440101401c40500074202903a1800740c3d03d814203c10f41050150a400400018400d0145802030050710b0516112032500d411150b490340c045505001da03422100d01007401e081c00401d0b5207001c0d80c0140c00343c424a03101e060440c1e03a000c4440051850503186160103009007140030000c80c12906840701c510140392500c0141c0c1c101310078000c12030803287d4021076030f052040c4140702481c0c60904003056419405c00301c0102251040d141800244981d002158056203048084003c00d0b400c0441040442c03002c90540d4491311a117014030000c20300b10919400066001c000501250300c4a9000640080d0050481d5600141c01c11b0000700d1600180c911a0902c800484c42c0401c40c504074203010391040c0258 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 437575071 1250 437573821 437573831
    0x81608090a0602160204110d051503100f1803020303011d13020d03020115080d090b1201260703060e010b1203041a07021e01080c09030613080d0501080c0a09 69
    0x100e10a8451035000402010b10703400003803850108078a80c490b05419a00240104090703002808000f401e0351204040d5161203050500050010303c84000c40c10011001402070002c40442901000c014110075810030002980e51802c1c40f03072038180c0010224035a20a0f0029684c030350400c0003000d8200031f0b03070007032550b400c0704107003006a047e030555603850409506441e00c12050a8918084c0d0142800280d004138210182c03c0005036400700003014003507110a1340b04c2d8500c40340c41d81e1281e045440380c41302c4c11001d904032000402083c86000703810001c0081c03041500c5802290701c40c400703060000f0395000b555110380b0781258403e068404e105499070301c20100c9a04032076120401c0a1912030117144600802c8030030030700030001c8008050301220005503000740001d81800f00e185040990400ca1900280021407110014045800040858510910003002454960b4840c200e2030b24840310707010221990700091000841e40c0107180696406000f2742c0c005410a609800d003403140d16002e079480301c86c001c3d00340 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 437576321 1250 437575071 437575081
    0x30403030f1b08071211101512170918100311030303040b160c0602070831051c0b10240504140a0e01030c060305010f0501020c210706081608 62
    0x100700301c60740607901ca0064803140c045030005807001e070080e5100c06d205015483ea82142e03141705034081d010300c0c04145290340d1100e03100d0400d4006491304071030081401d010012440c00c4c3c511054050101208003e02d03641d41ca0030008040d810100d4141c560203402c0285000c02d0040003a043e80380c02c0d181009400075411845c0548400740307813090181041204003c100040c0c4101c2e4410b02c0403000e01500b105040d540c81c0f03800d2070003407238035448110340c1203106042d4100e0a6003803218550001440b400300b03803120038a034148010010308400e0107000440f0304059181140c0010340c200c0b0150320030301c259078262184d036203404628940e00390b481e1482035180c2110a030709290540c010082e9400d0b03801104da0180464006000b003041c619a80e017101503001c0c800341c00042084040b00c0c009082c0d690076a001d121691fa12002804048030f00d0245601680024082c1c10079030400000c481030709914640c0b40d44980111060480c01d0403855007201e000510340108000301c190310010003041c613001030b10f0620028984 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 437577571 1250 437576321 437576333
    0x21160302181312020c0a2913060302130302120d02010501050907050a0c020a030605041b1d010b18040e0c0102060603060115080903221404050601081f0305030403030f1b 74
    0x500301009160805000b00344455500c200044120285d025240c0c40202e52a003500051007a20610a80e1040c0311640c5201810b05a48043d255800c100062000c3e0386c0c2d003804c40581c080c2d081149c550141350610400000947d56200b40003071485026009040350300d568540080c00e444050f041130340200515414885041d500030115200740f1403510306052110700034800a0400300c85644081c28081c1400e09000038000d0000500d4040450700d0007220200396100291594031861104207980d140e09200100548903031075006001d84c00c1095545810b40e0041d500050403a0202d01880c80c02e548861141d00d41c2c0d5030100075098004104078018442c3d50314183e40c0b8201110600c0c4940308010001d00494107031a810416070740d02944160020001c00c0e00c0101002c0b6503e6140f0807218001c5407801d503500c5504051199a01501041e9a4030800360b035a00780f407602c88103004801540c0c51501d81c400002040060000d0000345100781d49d114403c40e03a0070002844605158410101002103150460014417 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 437578821 1250 437577571 437577601
    0xd1803050f0c0102040e07020f1c1d0f0a030b0109060609140609060d050a14010623030603150408030a060503030a080613020c1e1c05092116030218 65
    0x11440c59803607030b12000d804090340a4061903008001c2e0803800d50a20003d00d4010881074200500c1c03404450356816103001c0506aa10001140f2002c00c844281c60395520381442403000300c01d0805454a41d1560044001c5104030005610039500c016040700144040701490003000c00070011481c28020481c01c200e60306c000d40554501481c0b040100180c0c01600e034540300143e030f1000716140d0041046140c00003c1da0b0140c0b1684085003460501203002250311070090541c2c216548403041802a000c00e5448081056800130340f40c00d605d4890400c0031000c03010108990b51141d40715800035034481c0ad298070003d040e644a078214620a81040c4000360721994010340c21039006808441840810020300000030080c030580216000390302550100c0c000c80090f16400042c04400c01045401440402c0d6500040348460181c8100007042008401154589a07004940300b25030714010f505680c0562070b072903280150b0035910b40b0011a0055003013055191070412044510f0210303d90846510f8860180032004c4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 437580071 1250 437578821 437578837
    0xf010b10020c0d061103040c050418050d080705090a0b221802180409050a03020f030421020a1509080f0307030512040c050909011e06050906090405010b150d180305 72
    0x110b02c9a01003070034040c0c1c2d07401c5000740c62072005c0050307600c0c00e080c01d04400d0304140f402482d02547c2441030a1000400440c00105090b07088005406181403944d000c83c0c0019001d0314a40400100b4000302d4019552a004040201030703240e00141c1d030300c4208140c40071017440e44060304440d0903444010003881c0e1a0500c015804d0302c0711840141c1c0d40c3d4820141008407846030541030b4209241c40c2c84182003000c0010342c90322035030181d02124900401120544d039240704501499895103c0c840000c0003900002c010004210b100412202a070785d1640f4203102c40000301002d880003e018040100500802405800d40b01909031000c1e5280240d2601c01074a248075a0100030103c88001c400034042c40304041143c00580b000408509050911407100d41c0600000310303c20040c40710404c4403030b80080041c41a00100c0d0000f41c0423070300f41d984101c100f20200c03100503c107881035501c89039810613998880501d25000d801c1407614035180c8110b900d51404803512140044104100518500042038102d8260f131990 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 437581321 1250 437580071 437580079
    0x40503150c07200f04060302150702031e0106030b01080610140f03011e0b090f060f0d06050c1201080606031c030207020a0b0d0c02120d05060406050306090f010b10020c 74
    0x1540764146020054401c001000d0b0400c0c00044901040004800b10002c0c02001140c12541c2d9100b80c02c2008112070881c800254422404508042c6101802010f48501c1e03000074140c0d074112804031080c0038042d0307411040c0c00c0b0300c1e5905c2000f0b03c20003580d1003101d800340c50580b0050005290140c5881055440340c09041c009541032406d2020f2903880000d03d4641c9900035000388070000016a6490710302580c51507404003241405034000503400d0140d4403a106640010b29a0f807907485403010b110300003d41000c0d0b56004258803e40c00e0118600f405014020b4030815891550f54944118400c042c80040e080103c42d50090000e0080d20369000628804c030360b1055500b01c4800c00304500076402441801402500551140780c0040c03c499004050401520020420700111407003960898840c40c1050b042c0c45510000d0141382c07204043c1e54045a071203030b40078000144964840b40020f150140444103260b0641c030402c0c01190900080c001d07210360352400d0b03c12000300e862807032000e034179000281040750003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 437582571 1250 437581321 437581363
    0x501121703040b130f140d120c020c060307030905070e090d17070e061b070f05040501030201050d0e07050402070506101505040e1b220b0a0509060901030e03030c0405010212040503 79
    0x10700c1a03000c5440c4051b41d101004561a05c0b443d0340707150700c1ea13030070318204c0020410601c0142c0080b0494010401c000c4800c0d405006ca030790144041100c3c58001610202c109075441d0b500c0b0002420400c000000707050000203c0b1b07064034010050b030789008011403840d030410580141c03214003010020300c619040f203c07a0074140d4140c410040450410b00984031281c1f08603078200d1781155802008a06841036840304101525903607140c109002c02e0740c1c001c1c400240000c0007040b00158460695010300c100700d92903001e9690450b030710740010b010390704500d0040c0d4407900028103105040d04080b11420045c500030903441294512000040c16a001d60303c9220301a03120040084c641d07030110020114265030421005407a03a101c1003146100049500304d4040522070000c0220344a180801511000280c1d661500d00e0b00b44100d080c09180d800681900e8103040e05c0d1008580d818038288082c521400c0d408503201d44887c50a000245842480107160703400301804c200c248015140441d180e00103400310303016103032 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 437583821 1250 437582571 437582573
    0x90f0e0901150f0311150f0c070308070c17070602100f02250c0f0f0501050c0a02040504200906100e0a15020a031709100b010207090501121703040b13 66
    0x4050000c00c0e081c49540c50105802040d19901c15110f042520b0240d0201c4030039000c2101032190000340c104055032070060034007401e018040b000c0000d0441d076000c181a82c00040d541c1e41d035644140c00200040b500740010020a10071080400e4200c0c0c000030944000301001c520b8490023949418072265002039081d00c40c00103240d002c010350100d40000004240303918100c0c4404208454802001004036100301c5000710004040d0407100703410099a80f4030301e0041103d403400c00103640d6a44004085480b900920055a016a603148942845240120200c0c65100b00090103528901c41c0c00420900c911303510400d009594880c103615681880b280c0c104551008150000210b0754091030780b10a002114995509008a40c00724281d50290701caa100d00072151045004903542c2c40c012501d4075116440554840b4550540e5040b840042d6010700540d29441d8031841c5203030903510260480056900c1843d003540c2000308a00c90810030b0600c0ba81480e0560405690340d800d580005030044803202c01c04040d0f44 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 437585071 1250 437583821 437583823
    0xe0a0204030212030403120203070308060d1406070c02030d02120d09050c0307140a060806060a0c082511011b1b0b0a030c0908210d09171207090f0e09 66
    0x58040c6030003d0040d0a0320004030480340c0d50760300c06d00003226a10820000a05841c7c000401d940e5486d1f4075480e420f0041d0356007814020314007020710b8203503041c28881d40c025280003030500c0f01501400c4540c0c2c1c2c00e20061041d0040c146400e000080410440d401091100e034407111a10079070306200e603ea9008640e10246003007440c9041c8410820366030600036003400040d2083c8401c0b0340780c00b00f0300541e081300c9000d0b41e40106503000002110b9090b0082010000264070620a4118be110340380300b100340364100114990844414180381c1c1160800403000000070040c4446c070850310f07004010920b4401ca0800030410142e50801d84450003c18502101c0b04c007019410100450310003070621150040d444002401004000d440c95113003030f2022405011000c03c200b18045442c0002007000c01d0703c80309828148012072100ea114142c4c801040303070f4034280c4400042e2414248018291481150350f1940c401c11075403029900c0282500050121445040044614003420482100c1d8503100d1515190b07542ca04d1a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 437586321 1250 437585071 437585077
    0x3060c09230d11091303030506040c05030718090501062304080d0f0207090203270a02101d030607050421050d082205060a180b0f06031c0f0807020a0b010e0a02 70
    0x940d4821803481c200300175a08200b07070000b940c80c0203035024801c54852600b03120450b408a02c1da0400203408100140402c1e0280840c400130324984948451026138070020101128020313005040020310300c002e80101e5132040c800c034258089003811154135042c580000c08d1f40d221881c040100900034039260802c42c5500230712456000304440c000556407403138420002080c8034501032141c1100c000c080c200c04500b00700010032085a980c003824003280107501036400c0c0c80070784414002c000c2410340f100c9104826101445403c5c0a0f40241e120b0940380d50030f0024003484200c104040cdc4040e065000b0000c0081a07001584041011080c140601070b0348600c44000412a04000302e0442d0a806400d03035401c12400203005803140801c490100070229613241400c3d400400c044000d0320090381540401d00640581c01c4060b00544000c04131031910031000424010f01c40c60440040c086004000717100342c2d182c0c0084001d40d1120b100e00c00b51081482540c0c0711096000107001740c1015200e00e80001d1803102d4142d0407 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 437587571 1250 437586321 437586353
    0x111030c07080703060c03051009110906042411030f0a031410090c0f0c080d06080f010608010c0512041401240801060506130e060402090a03060c09230d 67
    0x1e40300c009898020705a80d83e82584000c461481c030740307031104005034400e11806015840325890030600e0341c60020b406002d0001c000a0b8030710b1050406c8289210f5a40d00010030060404413819034002d542c1208400754032054940c1c070780901c00810001c0b0340300c00012040b242d00000c02ea2010340c4580c80713103104a0007420120800700803900380c4018004104424a0b40c1800c49001c140213000301c035418a021034031002404146004241c6802044000480301e1001d0012a1441c0340c00141413a5501040ea00d0a8201c40d074000d03060755600824030036602d0a0260046030314040c100300e0300e08103e810201c5420a0000c0010301054900000101c0716007080d00400d080c0c40c1e000c9602e10369514049100c1c1c0160343c0611900b1590740c40d01000254505165081d07d041030702c8440c1050f512450200e076006201030082525900642c20010001035586c0c00f615040614061140040c110b0992500503207540200d4000140c40e4014040c0c0b100e9600713009461102d003007001c0d00e4010f159281458803811114070400 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 437588821 1250 437587571 437587573
    0x2060c072d02030d030b0f040f02090301060f03061505060307080709030b0702070905060904050c010f032306090618061c02060a02010509070b1315110109050717031303020111030c 79
    0x2407151800000e070007400d6100e4022400d592002c071204000381c0403110035040d0160400c0c0c018103842d41d2454191f11080d8412100c41d030141c5800700c2c0c0b00002e82100d030b441e0045444105009004d00c01d02840e8898900a00100106014140d0506d80010b501d0f0000070440340400c260b4000151506114107404d10085038025500e10302c504204002a40701c200e6402100c4016140000195280c500881100d01903070b0080d01501075040c0900044403402042010901032640302c1c140c2d050f60100f080000d41d401101e90b02250b038242030040c00c115403000040c0c03c240c810303a00910002c9400700c00c43d041681200b400c9070080040c00c0700e0400c5045565410001a621850100e91201c1c0c440d0103400007849001d00d003080d9122152034202d200080c1c001c0c0240d20610903c03821003070041c0401480300d141e00108500300907040c01d02040030f5a0940341490401c07a030540050100b00070200d80c03c40007514900c0c0150140d4100650410039a000e03406600c006810007020030170080711104180115601000a00 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 437589928 1107 437588821 437588873
    0xc0703030e031603030b040e0105100504050a06170606010f050406020a080913090c03051911100302131d0a092001030e07290a02060c07 60
    0x40310080d40761000304503009503240310b1140600d410748241d03030201d415002c03a020302094030340c20041d208051b0f042c0401c0c04603100c0100b40c0c13030041e20015200007070259141c0400b50082d092690011141c401c001c0c1c0c1c0da00c0c800c8000300c2d009100e21000c2c0c85032803000802c480225a181f01c0c61017203000507008104220300245009000b8881450003d1621041c41c072100b10941c03ca0303031008021105d040f4085010030030000b081c08020300300d00840511000c000c545850300e900d00715003155014410591810720180060280d419203c4058014a40c83e01c0141c4500102e0100e14680a00c0221385000c1d0780040e045140c9c601800142c1c5a000024216070081c05115038013219000c0060b0381455161100010200d40801c10a40188282040040075041200c101154418001c0301d40001301d50812408034501d400152490b044500311103229580c81c1e00d414000c01142484a1020070f0b12481 = true := by decide +kernel

theorem cover : BRFrame.Cov 437410071 437589928 := by
  have h0 := BRFrame.cov_init 437410071
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437410071 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 437410071 ≤ n) (h2 : n < 437589928) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
