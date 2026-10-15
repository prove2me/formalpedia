-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5235
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:11:42.942982+00:00
-- url     : https://prove2.me/submissions/9f42ce6e-327c-4c82-bf9a-23bc27e7835d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 941366906 ≤ n < 941546762 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 941368156 1250 941366906 941366911
    0x190903050718020d0516030b060405010c060515131515080f04170d061404050103020a17071208180f01121e060308070b0f060609040207020111070807080f0105010b12 73
    0xc070030303002c4c010a0805649841102d0050001103020a91701c61122000740c01d48003501c43c982d22402c4107200400450b60400001010140d10800005c0c09580340d810208002a20841c41d0350849180c091010710a16507900424085901c0c550b2103000c0d035070754641210b010007500410400542e064001c108500d050341010744c0c005208034900c002200070f120014909030481c13900140180e44a4800300000c00c00c03030a44642d505402d442c20700466046401180c280078580c0300701078007080c00031260f4000d0361091003030b13a01611a2180307004030b0900d20704003640307581c101d004111000c0c03030b52490014003450310410044401c44103031207082c1d00100d0840c2040c018090f20040084501116076500c041000e20b20680c800b0b1441002143c1d1100b00c82d0a0200f90000010807401c80390492030188040d541d00ca1066401c251402c0f82c016a40300014401210609407a00b2000500e01c904100810314150108008041c0d898110441d0700720312100b1001400e0703480c28481d8148002041101d26408014031808a0f03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 941369406 1250 941368156 941368199
    0x4090f0b1008040c090c020c0901090c050702150f03010f08010e0708281202150a09050a0602090f1504090c020a02060301050d050a052d010212160c060207081909030507 74
    0x201d16a0345e80705400039100290720800040e0031071048108103250840c40c050141405000800042100110140461103080301c043e10607004040307540c0c800444903048407243c1005096168481d6500d9807424a06003550095010950a26051660301c0d81c0c001000307002c455004000b8050440d0303d400060b0400d8001e903664150300300843c03400000c100007164501101001d5402000384031046013800c80031100c01b0300014180f605140c21003001c01c2001541002c07844d04003c0040c0d490700008005149004000112600301b0745500f0344500c0d0211507006807003228100502800413402c0000c0498803071940a800070340c040000d00050000d400c2000c4140911486142102c042c01c056880f071900c0c0189010207503440c181c28074805003003041c070040401c0d150907200000750b040c40300950000c080d4030740c020030444144c02e40c0101c82100a2148007122607942d0024411596040b46090040d02c1d544951400d50708010112210074074184034501003402c40303822501921807281803910b074800301e10305080f0700e5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 941370656 1250 941369406 941369423
    0x150f15090e090c0d0f1416060f1e0c030f1809021e07150c0e030607141b06010f051504230603090c03060a0e12031b03090304090f0b100804 61
    0x18449604d60045001d4907138018802c121420505103820703c041211584010b00d290000c00d0946034001000d803090080d282c1c64102101c00030b400310806c480c0d07a003140103101c81500341c100712408401c1d04030400c1d10303c00e8005d035102250f1206d00710050b12400004400e80101036180d100c1041141c405a0150151444030040c0966100048002c47d2054000201c2a50f0410586442002c0f070001842060b40c0100d41742407042a400480c400280c072604014030050038001c0c20f0107019640380820089820b180b030444c09420200b0312000110707a44031000d020354040341001220100e42d6140048a489108480c600c4452503d800c20508a0346111501955580c1842000b0814a10361702d05002c3c2d44507480100c0103100c0908001d04140c41c01c03d01a1030342c001603240c14406002201d000c02c000c0c0d1006201c8a04559039124a513142d81000c01c00e8420402441d400b005100c40d17600080000c00440d0f88902d0180034407502040b1050440740c10040035a40004181c4280741407d014061a41e841801180074 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 941371906 1250 941370656 941370673
    0xc0f0d0503340b0703090c1a0706050f0606041e1d190c0e040c020f0a0803060901090e0318060903010e0c03160311061b01150f15090e09 60
    0x400c0d1940d001450400206600401c10745544041200c00580252066005400120700703030b11600010f450160115080544610b82c0d0011321030b480000000900004441c141e440b40b4000c114a000e80010f0300440d519400c050210b41c4482c140908103000ea40010000e07890716181c008007002001c8604e941d814a54600c3c6c1c0c0004200807150810b8241c0b10400381040050b1130815007102e01d00407902019500c09152030b44c280040c03503000c08a20100d1078152000a01e070b05409805900c0c02c1d0301890044080d00c00c0b4a4180e0811032034501039809180300343e40321086a600c030030544003a10316130301540f00642d03c00d0040b00ea901e0344a05900207a814003409042c50035074414046400e4850b1544400203d03400100038001c44c0c01c00700b1100c2c0b00102c626103e0040d440c2507954000c4a203240e00316091040170040307501300030011010107185806202030700030400608800100b030600c141d103206e2140c4586080600103004040009008024100c03603035000d100700d0500c1c0c40d2214511029180c24413500c0342800 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 941373156 1250 941371906 941371913
    0x6191d0702150a020409050708131e05030d0c080709061403060103110a030504030f05041d0414030408070501090b0a02060f04060b031f1b120c030f1b030c020d020c0f0d 74
    0x81030b40c01042054009a0380300d00704000e20040d0750000c2c00807030800c5481010082a4031030740a403041072030b43c0594944001129070610b119110140d20001e4035500002a42c0381e199460b0303a000384800841a218608240e82d603a80c1543d105c02d880c49110003003000104408105d9102c10001c0d64403d0050400042d00d03803107400c5440041d08100003c00200356280c003404141908031810190500c25071a00b50700d0141403c0608007841c0c0c110300e00900c1040e540012070304000d030507003808018001b10002c903503c0700d03943d02200703550301140d1141d90302240d003200001c0746034001c2d030040b142444103a400408880d1130342c03110340c0a0241c00500503105141e840d181c03003103141d900b4810000000c4005106810780108001030720112181c5006c0d89201c0c1d08852104490980c0080700307000b1500c81150b0001e0880c44110b01a40940307006203466041910b46511022000091054040c80715a21ba904000380661802c060340d0b5a9926498080981e0007021420384c6071405410f00800c008000d015812400800d54 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 941374406 1250 941373156 941373193
    0x30105100807020a23060603071202011d040e100506040c0905091f0602010b011d0f060d0908070b0a0c0201060f0b09120106060e01112406061603050306191d0702 71
    0x28031741040e5502e45901d00078000c800c02c00340c2d0300310300100c0292080358a054402c00584e104a04000c2c14440c40c06201c2061010030f10901c00130b0716001e00140415041c1000d0340d912030615a04141f422032611000c03c40d5400c051240038001a00c0d6115401e00c0d0781048104141100000c021f0010807002a0b2036568480b1000c05040040074a60000314101001c04009402c220015442c48010300d00300c4c43d22072a5070b03254601d12110f01c1c0183e8940c3c0d506c020304801c0c900644099040a442c0c11400a0071a08009d581e405a0740b00d4801040100300d02c2030440f20403805e03034056100d04801030401c0d080a000c44541d0b4402440301c0c8100030207040588062040141c00d480550f8042c0020a01c8a00c00c0c22042d60403418844a15100754040c1a056070103002c4241d91140145402500c20042000500103413680b0085a8051a40039091090440540342c02007855004607000c50003a82030340741c0d89141160ba444d8280c20344449074007800080205544400300b0781c034020303c5c0b0030071885081c00311b0409030b20b0315 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 941375656 1250 941374406 941374433
    0x10903230c0d09060e06190f0903060c090f0e1303030b04020c06100e0105060a02060a0225060506150a020c043c060f0b0a030e03041508060405060303030105100807020a 74
    0x2a103e03003210300d00e0640c0242101c842c9200f240e0088600b0418500e006030750a0702c04801c003d25040c000c030503100d100002c036200c2d807550300b004200603c1d0011030380034560042d0300c6c0b40c1100c03072408071410300d26110707008050245010785105400902d026001e000003030003604000101c0501030401030a2010000c10a8604101590300340340041c00741401b84118018401002c0c00f400040d1001c0d40b402400c3c450096659100a080d4040d040d400301d0400c4c0b601d14404034641c04500480308070559000350b800c1c0440201001d5a486108640c880360100049405405484403900c0540290051000c54402c3c07001801c041000c00c42d40e041c8083c40d458000c680000d04007480518010300210900c8030003100c1007110307592303000398050440c440406c1080400d04001c450341c006151a0100b21800045041850b6005603009400f03001e0260702d80310a04c80e80302c03458512070b00782194241701d01c0d140c43c000c5c55100e1000707010f055004450102400040d50140110b90b0700700f90782d0300c110382c0e8155040e1201d03402200c04 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 941376906 1250 941375656 941375683
    0xf0f062101030204050c1303060507050405150c1c0c030c1506030506240d120c050f2a0603010506070c0b120a14150409080c030c0717010903230c 64
    0x5500c01403041d42024400d00b544500900000340c90640140e2401040241600c8000e00032602d51001841d0b01748210290b400410014110f11442c180b90b0728950314070b40090002210761b00c101307040da415001c4864140c4110ba15a92209100c14442e82c40850764195195800c2e40c3c2c41e0740a2110740716850042c82010300840c09040901040d05060406c0d9400c0a2a0a2000010074a1041401071682c841007034181182c0c0c840da86403440301a000c0c1c04d682c40c04000b44060401d010301d80c0b07401d07000700c2d0200b07121040c0f02c01805000704068000015800072032126880ca0703003081080c0014402030400c00020840c3c036000301c1000700042c4d1740e048000516800703009401c82c400001d0b000d0050300780f60ba002c0c21407044000084070060745003003100300d00a10b0802c44007600c59602c40714607100303002e00003007100c00c20712451302902d9803103854401c1d00756100ca280c8500209500d403603000c803a4080040c4520f20744e541c0d266031810301035148440c02040c41500c2030702201443c9800c010b2000b0312107080240d407940f0201d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 941378156 1250 941376906 941376967
    0x51e0c0d030209150c07120f0c0608150a150c0302070f0b070312020c0d08070e1906200a08181e03061602031909080601060503010e01090b0f0f06 64
    0x2250f109000d100c2c1070401803509224818407980c3c94800001c00c0020075100803507440c08195010341854060310700c0105002d8554480d0340c40119090364001c84551280784200c40604a4941400502207822070034410f4100310840c50040d41059841101d500a4850083c412a00340503181e02407402042c03100c0e031000600d1000028100304158100c413601780c103ca440b820031400e10184400c0241c0340e510040c85101080000000200c04a000f0310a18900f4200904444516441060b030410424114014900490021400342290040c0f840a03420105022409000c1a007900da0b00c0214640045042c80302d111881c40e0404415280c5d00090000d070102400b114034162000410300d8206034000e0324617003c2d1114035004c1001180c0001c215107104084080c0310f0b603862042c64044915041d240c00c255403c2c088c1341d0001074119408406903040e2007690200a040e40d80e510701800c00c0703a482010681d000306c0310b0030b6240ba8a150003000e045107032101500d00e900d0b06100700c1054100c0741290750710780d000c200f = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 941379406 1250 941378156 941378167
    0x1908041a09091006050306010c02040e1005041a04050706180308030c0316090510050c07170a0309090b010801120c0e07030f0605090606120a06030b0403260403051e0c0d0302 76
    0x2500c8086183c0100c8158045100325003400c800405510000708098180034411060f4070441d15650b20174412110741d03009075254a0303200c44046010b020700740c90658042ca00084410148001000000d008950220090039660310b4810240c50f180c1003204904858000c2200000c04036600b0f138020b40c41030361100c580320782d80d284c07003141d104041400c2c042000401400d2403003406143c481d0b90030b004400181d418503580b1703007050080c020f10303040380c0340c00c110340c0d1891088042440031400580b18503182d1094503001c0050781c82da0750980849140510030340c0040d000300010082c2c030b8048040b004485000b6038501c0d890a84171154101400c42c10350700c95000135684c0c410081c0083e02c51280c100500350481d9001840d00304100099111f0141f52074072980340040d0400310f100d102550380010700850b4400c0343c0d01c48528142c100503107006401403a5581c1d540d050302d001b554400d194000c01d4451581a11020308055802c0001c404c0700102180c60307c01e101c410401c0e000314000400844c1c041c820030f59009030b80c44 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 941380656 1250 941379406 941379409
    0x3f0c030403060509251415070507180b0d150905010c091d010b030403050a0c0c1404051e150a18060819120323130201140c1908041a09 59
    0x15000c1c0b49143e81030718000d00780055803c8144604958010080081009480300060f51f81d1401c0c00d0030342c0345030360002040c1e403c00c0000b08003407007181c4880f101901028844413812081c0e50740040d40540c841e03000b14038900000c02d4480095043c2c017002030300141502032603480c4ca08540c0b0800c10500800c840c158100a281d80038a00c9668100c4104140c00007545841010246404041d0009040c4100881c04584a40c4078210200c0080d400554104c0380300e03603516074140340d0f5240d14102c80c010350400b80020b101d0141002c180004c3d4980480290041d6070740103100b9500d000308a48190300ca141c0c2c1d880001c041051984841d503403d8041c40c0003800e01e1620840e01c4c07420716801000031080008a0050002c140204c0d000160710702281004500b408507400400c04e000340030940040800482400e114580111483c2440240d1003a2100d0f1580e4a0750080d0944601a1a5030b94510703512032842818410030b40501498410310a040c1c05060a8590f1301c00b4200450691403210a20030108415445 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 941381906 1250 941380656 941380663
    0x2a14012a020a0c0e0c1c0b01090b0408060402010e03013308060c0f070c0f0b0901031125020a090c360e062b053f0c030403060509 57
    0x200038090008011550b03403076031440c01c2940c00d4481c500d44070794070788002101c00210a048402c1d02048050a030201c42d40c14840714014100308909900003810400d020480c03a00c0802220150340d82c010050002c2e03a15940112403044040d0845501075484604803003040aa00d07041180d4002403107107140c058141a29074054406a41e441500a54000310034050381090310000c0300c20b0441d480b41d41646d241c5181c00d048071516010784c024074104141e09000200602e403e4054201c00809036410f02200e01e001080c089d041c0100284641d81d924110303035003168540080103840b8542d1000c4d000b00701ca1592070002c5811100401c6c0c000c0082841c441d82c01101900c289400c0c0d0340514080300b1690000b542d800095884015405a40003120003800412615035441206034000000c0360f8082d009030103511480025543c480700201c071603129400e440399041749800900b00d80c916072900305101d0a0807030300c64407a41541203400614000340801c00e21520b0b08007400104040e6001310404540380c240b02108615 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 941383156 1250 941381906 941381981
    0x10e01020f1c0b06070b0705130b1b01050906071101150e160207140f011e03020a02010b0607020d03030510090e03071403090102060703050c1c0e0705012a1401 70
    0x54152501202c400c03d580d812090301c42180d000681b4203495510604150352511074082c6010482c401190b0000310b0a40d480010300e0044076408140f07880040d560411826601d0070b036424010340e0441400540c4561103603a007040c008507504000f0500c0402040d034018655204c0e005000b05585901c1000111081c0c20341c036066009052000707205417450903503400100c26404400a10803401c1c1107a25803c1c0c0c2c851803d43d00303015180510800e6075031003200007030020b40c00440608059400d0801c5801c0b82e240140070b40d0f06140d0003400ca01c98110550741c0890041c20000c01c000c0116041c0032000c81c1b00607040c403582841c1203100c401550742e419103003000740211103031100d0f600c441c3c6c4c0100329000e2140d0317002c01c1c0307a41c010066040100d40d41d02c507a40b1360281805582d1414036020115400074400c82b480e50085003455a1100643c0c185a03210801112140c0036a0003c40d031410251060107140c10341c080c0a240700600541010b100d02115280e51400d441e06c20b56049900040c001d5940351282503a640c402 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 941384406 1250 941383156 941383207
    0x703020c030d090302190b0a030e07090e070306050a15031a100324060803121b031b0a0c0f0b07030605040608102019140a1b0302010e01020f 62
    0x240342082200041102c245030000900411186c07480f40c0154030341e407513210080c206c00707008561103a02c290401401403112001d90f000c5413140100014140341c99128110001003502d0143c00d11605640781c0c0b90181c400580340e09820340e940d807409032022b051280300380050f610900e80c11241600d613039440200d0442c06000c10300048034410040000802210014210503818a4030841d050464091500201f0186e403114000d4000011070840703116500e072a0500c2403212440c5046030305513084c2d00600900088902d40c080038103286110030140d8106016005e149d0307840c030b000341c5903e8460f42c0c1c44400d01200007040b10003c80800501620980602500000e85010f40d020403615140000d01c1d9500c4200c211500c007082d940f0611040b07401c2541d0311915120307000c5d003031f480c0d91200646c521240c4198100701352800035108140103407030f0800740c004840400c44070b07949201c044034400c00c0c1052074641912044042d9075860000d904190070070300261022402c041482601c888050696030803028a601941 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 941385656 1250 941384406 941384413
    0xf080706030212180f0d0504030b010f081203150d0c03031707020c0d02150403052802010f200d02010f0c050408030711060d05190b01080405151b030108030703020c03 73
    0x1204009880c0303100750303200003511300c1842c141810341480741c207000c0c0c3e080039480136000d0411003590540d00100148200c80c407440c0c4a903090381e41c030000c51382001040d01800320ba90308400030144135880c061010f103070446080d1486905002c2035900244005c5030303c240494120080380000c0040c181c00c042d0342c185440c00f4101d0041c0b44e2070060700013500c950840311000d01ca58039490080041d51204800507456143c0d108605645a449061007a56103804200c911060741074802507021282d0b652101d4000913506071610040c41c0c0d1410000c0e80c5d4483c05540f00c2c1c81071000d1303081c0e00a03030103000c02000c0100c0100f50000100184400c00740b0003514000c01400b4180141000200b010020010899400d60b1b0400813403402102c95a0016480b03101e00c42c41c03080600e041034240000c0442e085e20600b1094001c003420040100100300558498000304d50142c40ca40000240c01050300300f00b61101e5000701d00103441420014a47c102e4005500280c0101085520125005003055010000d00046403000c0b4000d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 941386906 1250 941385656 941385667
    0xf040e070806270714160f0209090d081605120f0604050c04050916020703080d0e0d0801080316111003091707050d030902060f0c10111c050c130f0807060302 69
    0x50b18800f000381035181002404400c89000f40d0040c415104400314444500e8400010f604100050b038643c0141030384140200000f0918080000486000404103038550f06455550180e0090320398000002200901c00f0821a060b890313444a00d480c0c2c03086159030f01d1001c0e0750500100780001c07504001e01607205020104400d000360303503d2804031170303021091180c040c130414059803089040030b50307651006011030004030740e2182846003a0001c200701c5240000700d03001050b00c0b103030440e4003000a1049550075042000015040300c40c5030b104c82d49003800381d00c08251000300c502c0032a80b601f102c0c0068000190f0b0b5204801e00304806a212880b00c415000e504c03d0801c83c55071509621141e81c1d500200034150380b00350200454035002c00752109061044111521540c8a0180b2a103600c0d240d480c0540c82490f02001d02000180e14050f07603002100c4010343c00d10386501c4809030004260140041c0288a002e1007100d10040c031840135640038001c0101c04103042417401c166207141c803259810440c03d05005200 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 941388156 1250 941386906 941386969
    0xe1911180a0e062229160216030c140d1415090d08010501180e01181d030a0509010504050d08090310060e13031709010b030c0d0c03080f040e070806 65
    0x850001c09500310b03403070322800903060341000082c1c01c054602e024440307190320401c1040502100703084010040d940a0b81d03803029100340e003a50613481c04d000040011505400a0040c1d10bc0044e480d41540b2018001c10701554072034803901d24003550f246600303d00ba403100c00307000d40b400804040c154000e100a401080300c0310b0603503c040c12146050158504000000c406490040d00c54503500b4014280344481503603c2d40c60340040044031900c54a482c282905005070880e10700c034100001e040009026020303605000c448001101c43da03001382d0f0301038100001440041550350f604c3c09000d0495203e900c4180d51071a40350141402c0070304400340c040d40540703040000c02c030803c2c0b0681030a9118440544030325100145240607070b049103c800c5036005190300c02c0100709100d8015446545d201c00201d0440320907402c08402c019051139140e40040051810550800c00a40c151000c1c00207180f42e144da071410aa210207411410140c201c82c94000a0390003001c0c8846801c0516213500c0854550f985158104e0140c070 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 941389406 1250 941388156 941388211
    0xc0703080702010f1e15180e0304240e1c1e081b061f05130e010507030525171b0a0507030e0604030b070c050f120705010e1911180a0e06 60
    0x301044c0e8088d16401e416550031424800c4802801c40548494903c91010280301c13035100c4010300b62000b050640e081030500e132a1400516100342440d12000840042c141e85600c040000d100b8210400743c40048103500240109024251040c0b07101565050805405030f498542000036290000381c032041075410311420b048094000a0b280d05850303010103800b103405288000d01320414010100e510301000e00081c2980750b04130038010904d0700c00107900c8503030080744000c113610041c0500c40854007500d40e052003441d440d0070040d8056600d1304840708450845042c1c0420303504ca010b4400000d000081c800c020150003001c0c00d000c0700026140541001d04513620758680802c05080c0328144130740c1c0b07649441084020041084098007400c29583c0743c68068044490f90341010780300700c5c1d0070750030401501c1106500003660008c44907445a103074400c0405441d070600c60307900000d05640000c540c0000c840030800d5504918003520744180001145a1604946810008050b04030b0000f0f0054000c0016810304c0382 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 941390656 1250 941389406 941389439
    0x310091e05130b010305010b01020c010e010504060318080f0a0833040b040e07140609010c022205010e1806010503060a27060b090f0c0703080702010f1e15 68
    0x20200041c0702d840741505510018040380c4010940c210460011003003000c19000704615030800c0e000c50b030074015084010b45103444605c0c070090000303806000412115100b50040051114000301100b00c0080540b00e26555920402d4526040c48002441491040c1d202c5003059000560824405108400559000d010610190b406412500101440c181d40c0d603241d21088090320300a02c100f00c2a880c0041d242c0d20384546209030706e91160a680b2604003810040111490481c050391030300582005035082100010240003005001c585a01200390b8007007480c41001e010303250010140c9694138100a02c03030703c1c282001d0407080c0700b80c1150b40100100d450004800c1c1c2c201440050101e050b81c4518180380c02d070b030303807543c20140c11300c00100780e1106100880d8030210270040c0940d00303045150365407414410ba042c0242c911400301172040003107001003485030f00c0316074028010784000314001d00c1c00f454a00a4400c0700144a50b20ba0403c4280c41a101c024031a00e40041c0035500048402850b04c00c500e802e010f44e1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 941391906 1250 941390656 941390711
    0x90c091508040c2607090b01020d0302090f0402070f0602130f0b12180a060204090207020f0a15180e090c0a150c12110604030503010e0a0911130612050102031009 71
    0x40303412000c003a1360842c80c0705412014603011103000da5968121032002c1c08210f00310794094014074041c503100c603200303000f11109968042c110b44246280ca0301404025440307031100307890b128001511500089c1e21030000b890616004803500030080c0c20004400c01d400385c1c2e644481035228003000044441c05005002c103505c18100c9001c007004042d105039090410049a0b40206514070024000c180481c182d4003a004143c001c0d6154030504040d002070004000307903805599005922081d248841074840d620750068203248640c103020161303860004081340481690344e08407941240e8900485428141507000090090306036a40c038514076000050300b00e9110031005000c3c06000055003000d940100c40401c0300307107141021a045443c0506008055402c00e00401c0950201c000c046450f880305130080804040d009000c02280380030480401403244000c60441b101562542000038206044001040c0024041c200242c1d036440c20ba07401280c1c42c22650400300f24103141501a9420804c0c5103a24582c5000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 941393156 1250 941391906 941391929
    0x9010e240601080402010207080a0c140a320d140d0509011b0c1509090c020703110607151109031606020c12100c03090203010f0c2106090c091508040c 66
    0x22107000403410507503181c022002030321504041e5010402d190bd1034000b15004c190803513020150040412107010074034405d40601d41c84504a003405001c101001e00010040c20406019418020001c51643c00039100140c4081218165000440b4030501c074131004c0c1c44240c940189020780d1500040c222481000541c17640605074501201001007442c1210054440d130185400c20300c00f4120b00400305225402260351281c107010f40411224000680317082a03903400440c410301b2140700c6082c0800c81c1c100c02c00644111a20707001500342ea070300e1480341130200526204110782e00c140c818189845c06101404e900e000602c1000100040c550114888100007800c40c0c0c0f0032003c034001e40c7e002d45005915550f00c040381d80392280c2182515013540c00001591b02c240c00912039005d10030f441d00200e5804a00c42d001141d6441c1468240703d20210301c50b8400b05182d000043c0254a031000481218034450444cc04a040c103281171122201c2502c003403118035039524120b07485242581c2c0c4c8201001151141801108 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 941394406 1250 941393156 941393161
    0x8150a1203020114010e041e0b0a0f021e0a03060f0305031207020f161a1207030c0203040e0c0d06080712022e081906030305070b04020105040e09010e24060108 70
    0x500c04c0d0010f02d035025850b0401c0b461561a8a0908094034080c2c80450718611007000044507400f034503482502040e08070140e0b5103a950391600800160520940652040c0c1d800c01662a090b4000120b2201d80c40c5440c3d01d2070b40301c002840b0050f0450398150010800c01840d9101000000c0000081f25841e138001c01c1c0005058135140d0040c0d181ca0308504282440f801070010144d00d218443d407044048510b111880116036036800107101482c415074804c8049044d1080c00500c01c14001e803c86090700f47d0501c101e038030342076031440a1005000181c410b01e00034a0001600c00f40316249008207405444913001804142e40303045166408107003020030080c000c1004d4601c4021189004002c3c08510342249130401d1055500140107100c0e0400b11a00395418215601218140c0c001d4850381c0c040c0c07545a1a583d20384a01030700c03846144d0000410072810000c08000c0030584100310142036009681600010403182240e9a9483c200114102c1100510000d00300c4121002e101180c0749070044001e003004e0030b454 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 941395656 1250 941394406 941394413
    0x1030e0106180908090a06030c080a052412070603021b120304061e05130204050108010b0f090c0f07080705071a032202150c070b0a080c0c07090c050a08150a12 70
    0x1780074007100b05a000040160024005415406c0204220450f0b0344060b03680e0f8074100c0d6002101e80503226800b1003111090b0685005201c0c102402560900a084403000060440e1041c500038141c4c00c0400080d4001c50b0354400112445106c81012410501800080070f103080d005420340401400900540d445241c40c1c41705041d980201c00080305410801d103ca854149510343c0700d03c41c030800483c055454040000740d60074041c031940e25080c02c0101842c1d0055211401c00005440c00340c02c0c200805010881501440b280c00f00518049201d400c1494888a043c1401800c1c2841d95100811488040040c9031220300124210b80d88603e0b024418502466409240241c0c01403001009400c0038103190400d5920744064050154000d080c41200c00741a19201e2030325440c0502e0140c00086116840461000c13400e0b0400b410401c00c10364202c40131b00c3c1d6580d0ba40410384601100480c00301e170380000c608070b40a03803210034543d02c404d482440801d40da45a6010035a0022103200b043d00c004104020070041 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 941396906 1250 941395656 941395673
    0x110307082107061a130b0603130201030f050430082409150a17190f1205040311010509010f0f02010f1b0e0d05070306051512060601030e01061809 64
    0xb40d90800010061042c04010040000c8120f25a0f944a0480000007401801c2e0310701802501e40c802410090a6489a045110031302040d02d004a05142d1108a61801d2007200d01c030b070314030a500983e48074461280d0311b14140c24003034940d184959200101600000c003660071500700c0d50000c1d2088141c40312a02e01d41003030002c2c0c006c42101c0781d0b0300440314801e00646c120340d082c003070320bc450040714400416550b49003409022400c6002e941d8158105801109944116408441c1c140f401784001e41d0501d0314568490a10503003c840c1d0348085400454288103010f006100d12039103071000c1c2081440d1014250010780920303070145040040003c41c01d0409141031003034000c2c40d01c207200c0d07440500008001c616070a01e0800c6038005080084c010708040a254600001540e40345600040034205035815905c6141c00762400070301150015a40c4904206a45c94001e401c90010600c0d0000e0320580c02d00c24001016540c03109051301c81231f0706104060002c140c1c0d001c1680e007600c584400004860400e494014907 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 941398156 1250 941396906 941396917
    0x813060608011a1f02061302030a02060406050d0f0e0a2604090e010c03060e0c0703140f03060f0a060234080d03053715080a1103070821 60
    0xc1d550810305032510400c071622a8200000c811601030050311040304c695012415034641e904010390215010842d04010080c1c090701c02400039050301c01422480c0c002c64040d030301540c40f40340012400542030f80412450701c100584604401801e0086130000c042e03842d542d44000c0409094406c1510b528030110440c0c00704000101e80341d46040303403900c2d500c0c3c1840001f8548491203000c0c5508191501003428460b11070304003540d40d403100900c0681c0352400224015040004120709021081a01090545222010b050442388003400c41c1d55a18000c400d001c010814105124024000702105020641d0045400c8087e45801908104181e0400300c050158803801c512184e600040030710049549030001c5841010f41040380c80a1205841b0384028501c44000036500030103213101d00302c1c600e0100c4072803511076000c44101d580c0850655155285003140194585c40070540b030f84040e001d04d00700b00c0c0300b8001c0040840c04401900f070305441d22110b01e80b0b8042500c20a41c24014105242090015010035101d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 941399406 1250 941398156 941398169
    0x71403090c041a01120204050a030f050705220b030d08060d0309050d050105070215070903020909010b040f020d0c02160501080c0408010906021c09020a050f010c0b04050102090f0a0608130606 84
    0x2100c0703408010f51444a070ba1541280001c1d4222071a13841c9840d10300803501101d101500398104185980c8400d101c0d070701c6c0c0340811900782c014400700003801d80c4c40300680100c076407501a81000405004180000712500c9036219402a0402d030719207007843d40c001001503802001603801d0642710200c0d260442d12815290005a440021440884140041507000034402c0c0d585800312125042d041074810002d2208681c020001000200144018100f15680304e4000d03d13054004030340c00c5002d00010f015900c0200b00c03000041d9001c6141000c00416000c0c0407020301050000d0604040e0943c8620000a818016241404151804103020ba041d650464004190f5200200141807103840d01d0760103503000c0e01010310101c2c2450070065515206201e404d0040383e00500103180c0301d29250078850f280d226034240d50305120705424a1030204506100b1780748240d02c01c000060b5100301c8401080080c2501e82c080074020800c00c80144605c98018500d503400004120180340050568a01280503000301e03004007 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 941400656 1250 941399406 941399411
    0x80102030901150501080c1c020c0a0f0510140c1b190201080105010f050a03050c0f0c070f0603090519080d090b09060105100207060e0a0807030f060b030303071403090c04 75
    0x101070440d065106080310a404002080700544d41c1004545490003600c11080403407082000726400c04052403109000e0039a03407030150602c62003081326420004018030580b4800900044d104c1000342c2407000f400b20a696220400840034071070ba03004401c503001442d505801200040b07000762083c1c0504a000d20005031800c5501c4020020303503802c0207040b40b1404030302084100001146a60240f148020344c2c07141741d50354a080810210080303014000213400004000f10030003000c108070240718024100b2031307075100c010300c00070b8945220710a80d6082a80414101031400a010700091000f01d032090300711400080e0112103d2090038445034a2240708880c0c108a4605480602044510b002d0302c0d204016540c03d6800076a40c61003842000700100780409c005070449041446064003410313015410b0400a41140e0050340c9030a051858803003503410603101201140d000030200440c0740100d2604c0b1800381e01071415800c0031000034280900b14840107001210100000b0108181080214002040100123 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 941401906 1250 941400656 941400661
    0x1104020d0203010308220e060105031008100608061f0608340f03050c190c02060f030108071e0b0a110d0509041d0c010809160e061807090b09030708010203 68
    0x180c0042d60010601000100000e42030341845881b4440e1070003141c03940c410b1250340360740e003e0044600d42d00041c600e054240d00702c480498108070401c205040b10115410016400d03050000c0640350410040c000d0f580351030b038003d05034220001c09003031004445040c1489012074a441070030040301a03215840250641d000c1c4104d81850b030709001c450b484038506484100460380380e81422000e48904480040c3e81c1d000400103400a8201005c042c4074060945ca04071703107400040d9000034a42d900180200000aa01200612110001384031000040c4a040d00394041e040301c2043c0010032660a20400c219074401061881c4464020040741d89050700ba003080d210401d09007c0c000c1c156400200300d0fa03000740d240c11180c3c9141440c1d00c482d81c0b142c8003040018038040341075100442c0d2041d0f00a01d0241c1c2d03405a500c01144002d409400e2034040c251304035032032045143c1070083c442086481e51080000e2842c400a00c410150800c1c0d6607c16280311341030782ca9943d8400300101e40b8000282d4040349466100008 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 941403156 1250 941401906 941401913
    0x109020f0415080f0106321c05010e06040b2d13050307050a0506060607050606150c06073f09170c0703170703050a030b0a121a010e10031104020d02030103 68
    0x414006e1f84d4503014030031003d10f4007140d030405007100c40c580c211002c00c0c0340b6210314040c070b48481d405a244c42c1c22800d02c01042c51a5a5940c04e4420b01a02e4881e141d010030107010402001586d40d81d44490301e023060b403040002d441d4521902e0550081100014405100030440340e80e100d0030720b0f400054021701142d81e5420345240c483d660b42144401a20140100004501e280c03801d0404c9400b0650410000c00322034488000b007100b46da0518441070042036040003401441d100c284001ea11900d0b0549410121701782040c98442030388400391032840c250009011303000b250890940c003101245a0f407407001454282510349a010201c2c00f0005006505011030001201d0700c0004003003003901e101c0d001c20100d402c040902500c45024028001380461010310a44618a05c2540500000007005020501c000d03914a00310f240358120b008260380301c040c5403442c0307041400001066401440b4070780803003da500e4015a810b0045840340030042800040200341111661103070143d03402c8440040046660f541c2d01e19 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 941404406 1250 941403156 941403161
    0x40f150902090103120f18050f030109170705010f0209090406180b100501020c0d260d020703050901030506030d0f0c080f0d05041502090105070821071206080109020f0415080f01 78
    0x1d00500000b82895100b1b00318a105d0440913a00c461401030407d50b2034100010008100c814401007a0159604e1031200085801c2520141940e900c1159550f0f4440e4282032043c00c1d50450026080114010844070b0079913100c45109a600641140d00015180080c3d04550700c51103003120044d151407914814443d24516200709202100c5d801d030215013070418a4000e00032551185000a406490502c142c0d41c41d42003161503c0b036115500038000c0d85800020251402243c0002c50158002800400c0700381003960180305241e00020b04500400c00101d9000004101c0070034440075400b0440d0754413841040200031410f469064901e0180f45494504401068004120446095912440b45010080c060001e03200311280014183c1d03c8500d41601a12524101e82c0b01042c503406020000080b1100e041030300d24082e01541e401d50300d072240c20395444100401c7d680742d5001150241d240585600051355505100400e96905513004103980c440d011b2802c0445009501042c0d06008004c5400c1c444141035 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 941405656 1250 941404406 941404433
    0x14101707030608190807060b030f10290306041101170a051b07080f071103060906060906040b0102031e04241205060306130503091009031208040f150902090103 70
    0x710104c60741145500b08401040d2014a0007502c58241008400b0102d00150842c5594541c0601144c0d030211221100070701d01101d04400c1c1035600d03696070400b00c0701007015a1600303541d48004c1f110043c841d0a18002502d800014200070210802c6100040c02039000c0e0801e003241440031150752069140044450300640303012181254460500a150a02403100d0020348441c0c03500801c401e800c013258030700b1198180d072204030242d81c84031020400025651301000b40030b00c80c01c48480074081600b407481c14800b900c0c0b006000e0a100714103180c0340b000e4070b0b42e002050b540808440c615400802c4c0400103004140c0c41a5040019120700c213961500c0c6003401d0000003400080f850359100242c0035040007040407142d0548060f981034000c1d03c00304201044440301690101c0c051403e0b203107409000000152200d040854840c081041c204082040c844441420140c1e46014140710b600c522f030656405035100401c000c028080d034803503400080110b10507840024525400f41c030601c8103586905040c240c0c4110f2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 941406906 1250 941405656 941405669
    0x1a0604030c090c030c051603021e0c0a151403040f02120f0c030303130201050306010917160506030709060c080d0f02070506131e150c030c090f141017070306 69
    0x2d014800c28244e10a124072a02090780b80c0c2c6041c103210020883c48a20b0740206e0064046110f45010442d0b000101e204034440528045d000b00307056071251040c8480d0144561080840c1661104100c001c280c00088030000120b009038102e907250f81e2490041441407041101030341003912201a00940040000c20450301d4030490304039a803030b490360f07400c040c2c1d40d1100f02c0300d0113a280303103005410b00154091400756400c104141440e0f8080c54642402d00710400321191031060541c04658402d141c805600c02442c0076180941e21303149146444200038142003c144509401c000d0030311405c400b4002058150344004050240500030640d07202050000317504552001c1d10180a40e0020505503070080f10403280e01603000b9000c548034800b44800411043e10140281c030040900c0d0f5040301c4100c0d03988120619407029440c00039260408181c0240810100c1c0c01c00c4204003501c170400c0c0300c13203075810300d90340041a02285e141a540303c5488088449091410143d01205481c8050080d00703a090340012054448 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 941408156 1250 941406906 941406911
    0x110a0530040302130e0307141e010e1908070c1805090a0b0601080a02090d0b18070f03060b0d0f140f0106051302090f060a020f0114040302030d1a0604030c09 69
    0x10081103810944128840254450706034081e2090141694022028140200041c0d0742403c00a440f0b000c16000942403584198100c0d04145000c01d5070609403030006d22041b0b00800c413469041030a1a520020b081e0800d029a0f404480001000140c10881d4641d030340c0429108480c03641c400c050368140c0b0f4070500e403d441c18100000105244000180d102e205ca8000a24010545a160041d0740c404c1001e016400c03441e8003000600040d85840c1403404000d44036540e1350303c0620b0300003c0c45110071241c0718001d0080d001444204006a50800d8450035039030448400641d00c22181300040526201010041092904000b14401e006442c242001800c4541054501c1003d6003d0420708840940c00703120f900560050803840c00c042c0740e40c060a0507040c054142094580c2d54400140303550440050310703005030701501000c010550280500054100b4800701400941480d0390065202e000b40145030700c01c01d9075007080c02980c0c00818940176140001810442d565600e0f0308210721011814001c0320252070 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 941409406 1250 941408156 941408233
    0x30501050f0d110402040f0602150f040c030b0c0409050901020d0c05030702030a140c0304080607030c031a1002150a0207060e0312060d0c031b061d060a110a05 70
    0x285100103001c003140c0104807481c81603041e07840d412400324a1140030b402c542d007400702060b22040350090038042e101a80052491400880598081c041c000b0031155040d2942d02c14800051540c44c401425a03a0194041c8001c0da14822081103600540d480000200d05203000d100e03c0090641c01010b44924610301480305651409050310300384401e9a03108010b0740700300410114244140310039401d84483c842002e25000441e43c3e400e1454009400040440c0c03c0101030254164051150040720f10560405011946c500c05541c044110400c646502880c1480f000c000614824484182c2a080c4e00c0035030b060604145050000031341044500316006d6180800800d00744c8000400d541184080103c00c104543c0c460782805280c10744100121015144400007000055164009101007020710781a1010145800c02c0180034080d009030f040182d0701e004103000345580b40c030401c03a17000c0c003064202010111400350b4164904540c41030041c0141c0501c2c1c0d4417442441010f101d440d00a614040c0a203040c1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 941410656 1250 941409406 941409409
    0x70c0e0a09050705040c11070b1308070510140d0e03130b0c0709230103030c110603040f11010221041a04120f03050403021c120507020f040b0d1a0703050105 69
    0x56003071200150066000740c3c001c001910b490703007002d0700d426003d2401d16502030404903168a803014640003030401020118112440c000d0150101d4000d09880f00104181440c107000b20382004000f40f805010480190344280440300250304075100310200c1c00c000c2040c0f21300f900e1a07a80729085a2007a10040b0620040007a000f0310142c00c0d217034881c002a01078409039103012441001440c2611a2412024081d851144c044100c4825980254000d484448840045161004002c1003403c0ca4a1080e0300c1130082c04082104111144401d5a00986188030b0046203001030340b0f040510300c4d400701300c0b0310751501c0030400c400401f028204480d03201205c80e804c0c2d628440e860303000780550b00944e08040b00602c02a00030641440100300042c2c00380c10440d14041e143c4d00441c42d5200b5172000c800d002c154040b044010005441c22078840c1080a2910505003000d542c0040d030241c030303410241c07440b5544031b04000300141d41c0d1503240c51784158840030440c06005000342c0340c500c40104613607004c00309141c07c00000d20b5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 941411906 1250 941410656 941410661
    0x42c0706120606270b040b0406020115031e0203010f0609140f04030f05070c0504020307110f0d0c17160c030c05060f0319150f032006030c03070c08070c0e0a 69
    0x3a1052a00c88000c01c20101c1040d480302d041c6044d20006510440ca00002c5003442100200058446000b406a8403400c040010f42520504481100c00110035201080030801d0740021032401100c480003031441e542c1c3da0000030f01400c00382188141841c80d0840005003043d0b1644081d002c0340b0011000f1015540c0c015111a03100800ca501802040c1882c41c42c40c0d48610a10003403610728803480c5c0d00c0c0b41140e22000440c080b41c20888a02010601860384c09010304804c10446500c400c1502c0104402e4188400050a501c05450b00130880d00711103040d03c10460070341c4d044d6000304400e41202e020010007400c0000c410051032100755050560000302003403d041c5a42201c1c0d024941245640c55a201c4203a1a088040c00131411386112f591f40c492180c0c0c1c8800003003d0030051403441c0021480c5400c2d810444500c4051344078060303017054144024011915400182d9512211000419880b41d81c1d054080d500d0a03100c08000780f01c01c1c400614007003080300040e81282a02c4145e500d11100f561841009000c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 941413156 1250 941411906 941411909
    0x5130b28050607054b031b07080d0e09090601080a120e0a0801021e161707060501091b02030a0801030b090c0409060c0206070c0809042c07061206 64
    0x16014009030381400a41007900050100700c1c8250216586150005c1110b81040003040420302981c031082494151800743c1e0740c42c5500c2079112005681c55800b5840041e54912a402c038070410080f198040c80b6600e541400100c00401c0e07071005580340c07155003510090000400b000c503688502601c0010803582e04000544178141c4031001b00400030640c00780c0350b805000210052880400001c141a0b00b81510b40d80b111b0070050124100158450500e04032180d00185000e8102e04010000e0002034000e060300f0398200009034008056209003510481003401e688240c0101030304060030a400001d0708032107a8050f0b40f10304c0c40e06001c41c0000d400140c0887c1c032442103001e9440000c800200500104540c0c950b502e030002c0d241012541a01410004075041d1005074038203598650341c80314510042e9030148040d40d0720103040c0c80d10340a00d1000c2e646505050042031107180c010790381c4a248405813012095681d141109a4060900344120381d4109981c0c4c00c058086d00340040c40c030780b260035407080c207502840d0f0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 941414406 1250 941413156 941413219
    0x809030c010e0f160e0a022b140622021b06011d010501030b060909060f0d060212070215070813020a090e100b100c020d06020408150702120d0203060a05130b 69
    0x10074507280d40b00e641c00039405c61101044400c1d1149990300740c4990407040ba1081240c01c003004514000d104514140c20427000340041c1c01200c69140c11032103084854030034807422039060b0005880d51000806807840031080200a90f40b40b040500100d01c14010001720300d00424040b580f555a43c0c0c070743c0011403e80302d486a1b030b02d401a0080c005042180b920f8501181d000c00d0150048910140076000107c96005c10700042e038015a00080e00145054603444040d03200703545000a011100e40954410308401008120804020040c404102d140002450320011070b50010701200c60b03180c9907201d903401022206603021541c07103001703000d0000d11440d0140c0e401c0c4640040c04000e441c4c4500d902503807500d510403000c036804034804080d0740020b040c41c070141000d403964000401c011211188601c0300382d0000381200080d98007202071a40700101e01403c86548102a2001503140d807650030100e00100d2180d001603500c20507448207070390000070590051000c200d04a421461940c0c0031502c0d0714501100100c010b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 941415656 1250 941414406 941414429
    0x813082407020106060c1101140d060f0f060f0f1404030b0f0603010b281802040f060804050c01030b010e0907230705071509030b0405030901030c0e100809030c010e0f16 74
    0x294003144143e07d810f03650520605000c0401d21480c50340c426188d0123000d405210607900c40301071002c030412001c2040070f450f11080c1c2d200060300344680036115600c504c4441040052488000000c80e12034072840c100032a480340f000762260b44900e4210002c0f042203e03618001451213002500b10301c1d0501840d6001e1001800407104a0201424460103906024480c02c440c0d810080020b054841ca80c00c2015642011100503115401c040e0750b0444145d65500c01020040b0047c24400402d00100d203040d07610700709082c0021060f80c0c000068070012021404190300c4044802082076180d081480c1c040d200d51212070320400f4803005000a0081d0080b80b0018216921101050104150850012541503483d0420011b40c541c1c039503c074118110202c0d4102c480790808a044095940c0600460090100a0518038a207a55604c041015a65140f10000820403070070042001c1c0c0100b4400c072030301c8640c980002c0c40b20403031080050395500c5507107944245920411340c08007113118180050900f510200550b8 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 941416906 1250 941415656 941415677
    0x40b071109070816030c0e130c030507080403210b1002060901050c040617090109050307052508030739030b1008071512142a07081308240702010606 65
    0x321700a009060344038061269031000109555101407025440354041c1c2c03404600c0d900c1d204001000c1c2c40002e0244001c1c001d044080c480029081340c410f10000c80d2164081440813107504146001d800f0b454001508000c0301c84000410541c003040072481a1041307002805580c59056241c44a4495440782c140020b41c504a41d0403144101120150030092440011640c2ca5064a40340e003583c0c8042000c90b4198044004040b040d04d022140c041c08040a00c01a00319500c1c0010040c1c43e4030a0741402800040002043d041291548039050003c40c010503410301c805d100184025030002240c0022b4171005644d20000c2d0922844005400c00c0d2403100300078180044c5443c2d80c4110304c08088100c101400102400ca0894034294403a0340000740d0050000d810ba8180b10007024a4280d45403519020399610304440d201020000040340d00341380c0c1c81150181d46464240f004040008a500640c18a004000c2c103c400621000354205c0d8100d0700180340a00c946500c2c800364200e40c9644112000300f840e1030103 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 941418156 1250 941416906 941416951
    0x2010305090a021c11041104210c09091e0503070b07091208041518050609010905060c06180601060804080c100c030e10090b01030b0606040b0711090708 67
    0x41500720409900301c0e2a0342d45603500003007a034112001c1c14504c441000c07001c2014403030310400a01e42c4107415a401c100344031309443e06951510a500400210815040c00d1211480c140301a00b41c0854008404004071900d8151000190131078030303000c2e40e9072042c1261202c89820700940360b40206a11070003c52518119036074981000c1d000500360f00c240124000300268421010341180b02e102d00c220f21f10b581d0b490034000c50b00a94840013030b000c0204860b6070f05200200e2001001d0000340e80c4102d5540e07446810302c9004985055094000e681c020a000c1a07003140d00c0e5000403481c0c05030400c40880003e10104103000b030f0385c5480910030000040c0c1c1e59004034010694120083c0040d00e80502a80c14030262030540344143e03500001408002a40c891000c50310800c284500000010400802c1c01103459a4076500c66024060001074180e280d4440440c400e40c0d81ca00840c0c00070006d0b4450680c44c1d03506070400da0340440013900001e000d001d0b6400003441e0346204684c4903101d0b040448026040c0c4801b2038 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 941419406 1250 941418156 941418161
    0x1240503010e040b04031101180611030603120d0e01090b010501090b0712080a0f02031e0c040608061e03070b0403020f0d0312110405031e0708031201060e01030f052d01080a020103 79
    0x24026420322600d1401f07500504800c1c0107503c40750514190220202609181c40e0048440e076400d90440c401c0c0c02c1c020f00c1443d40c0c0105400e80540c00d47e40c0c400e61103401400028000f800b4000700b101d1a5071800c1c600d00704008160301040d040303603030036201c15102c0d80e83c0303a040c170b91603204420000301000c00380e1030000b91080c014050b039a080021618000b8039114200c0c00c43e002c0307034400d90300d10a070080115103141880304844002d80d405111412510b040074940710029001080140c40b542c4610158070004d1400409404a2008008002c00312002c0955a6001c0800b5600600040c0d00499521114150600309084c071182810380c10b0792000442c05100c02e10800038807880101000703681041100003042d43c0c04103e2804101c04103e1002c41c01c1101c0e0049600d086095444510590414031042d074a03c0740414525044502c01c0c1072041e044803840d801200240b0840c007000c00114548000d00030000c64074280110b118105103078807000700e1003800b0040307c0a002489801c035168000341c0311000651098 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 941420656 1250 941419406 941419411
    0xc060b1009060507062310050619030e03130b0a031109060304060209040603022218021012091208070e0d020f15040305030a0327030e060c1501240503010e040b 70
    0x2c120018445807003214452a20105a829045441400e401d01098200101135a030003030204032741041c5003801c070f080054030070403500c0903050925a0700c005a2000c9101801240d070380c40d14020002010b02c0e228206031005412460a10300024500340011003100c254404807030010500400080c00c55a6a07515000a540304030035407138000b03445400010042e10703424602c00c0340c070400508000c07140202c0407000d41140d03c00c40c00c540b8a800d0390744500e00076854220300000c441c6100e1800380c2c500b851448111f00500500388000700f400e1034161042c140e0a0340000c5a0303000b03807000d64444020010080400c0188240000083d50020324204c1170742940c0b503c8000380c06007001c030107102400c00ea44c81e2a000d095030090646140030a0302c03002c1e12011031403151501d40c076481600712202e05054150310000c00a41000c03a0792800f03903800007041100c080c020032000d02d0541408507850000d684900800703411550301065035100c0d0740c03c84096000c01d4007442c20749058490040d050704040d40c03107445400e5501c201 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 941421906 1250 941420656 941420663
    0x80c0c060118090f060204050f041b1b0f0c1508090d030b0d051c030605030f0c0f0f100e040606052b0e0d03090b070806030a03030c0219030c060b1009060507 69
    0x5821415000850844d04604803074052440107884038038120a1100008041d440b4a02c141d25000b46a10100c2c0d240001c41003c00051400c10320148030340340308480a06468001419202032500c0802c1008401e030744001c103032240101003c074a0780050109540c045d2003a5000d02140c4c00c6845100e100600c039a00c0064000d000a09180d00700e1000d8440c03c2c20890390035107844400090000401104e40c15000e810300901081c6c005102140c8101807443d1102e0007108110300c01c0081c1d8220040f50764840c10403240c4a480240003c0c051100340101074081c000000440c0c0c0598241040012598011810f032640718580051041e0840d9200da051603d44401c219030001c540c4d40c58641011b080d208001403180c441007501d0000740e0003424108001c4505005062001b00501036042046a44001c2011202ca50307050030f0119a6041102d401d038141004402c01501480d00600100c0906501a0b00441e1250140c1001c00c55012443e062001040c00154a40c002c00c48045080008074401c03001842002e00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 941423156 1250 941421906 941421911
    0xd0f1505130f17180a170607080a0617010203040303050703020a1d04062409050a030206040b070c170a021e060703051804020711180403091202030a1401020a080c0c060118 75
    0x121000d07020ba00e4101018402d201d00491213209128201140c000000d0003800c01d11550b60380d48205001e1b9030351401000401040400030128080501c00d82040000c5c1042e80c445010f800a001030a90007504212000e8000a0600011412160091080301d224070300d01d50300d10621140c032039000b003c01c150182c4140c0c0c20995541c2e002450710504160030746030340c3c840100300b9894000c11000400aa40e150000d501c105401a000c10060340d4010844003110801e03070707135291141001d04021460075481e83c040f44c452038900d0110768240a0104000a00305d108945101c6014000e40b407040701a00842c05841d002441000034902217402007020741010381c1e82c10b04450301401210080340a13a0003114088460040e08619005285000c0c003140101c4400c91038416214546924010304006541c410b04244c522521400400d644007031200b801300380e40080c0c50074270031243c00c1902030007940183c90f0700c00055079200c080340403002c16200b00d403207100c14440104820b03420402040301030b0030340d04c0078600c0265 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 941424406 1250 941423156 941423183
    0x118060c08270c10020c1206010e011206202d090d0804030c03080d1407020601090f090c030b010e060109030b0a020318061003050c01020d051b0a020d0f1505130f 71
    0x9941c03030811880b504d09079025185205c0103106115060b5183c04d080b0078640c00100050000011000d200d038115440c007174003d8214415420458000c26400c0545048400b00542203041c0503044002880400b2696800c00c61140412049101013141c8010040b1740c1c04040007114000e24204042d11105401030258918256803aa20000e500141d81d1088559103070220b0600c0c9429110304c22100c006005c988443d5644ca4503910003900c4040c140550355800380c0e503185c0c00240c03240c180d01c1480001d50110609044544038200380550b02424466003207803030301100c0065070701d52040280504680d4416070f0400c0b43c0d11000d201801030740000f0070080300f10b0b070070280c10341807800c08015541c014404d01482c203114604508045081660b000700140c1950b00103081c1c0e00740319038410100d41213403c2c80c0701d030300c60f03c182590354031418040040006503100300c2c40d41c008401d00c029883c40600840c482c00c1c1d444d02145000303882e601519422505c1c00c0703c1940301d0300c007440482c0e4904c1c080c0300081e04c12020700c1000c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 941425656 1250 941424406 941424409
    0xe0d0c0e070905091b1b0609120c0c13061503061806080303070804060b100302070c05030d0203070f110d0c0e011203050904052520190311010e0118060c08270c 70
    0x4540c0b400c508807194003c00501441004c01c0c0250300c0d027020b00312031007450402c2e890710080d40c800100021a02030364082001c244030b0b018035801040680390030641c00720301012064005024002a000700310a850442e5207503042110603115500032165041c000d1402d43e65040820b90340c0480013041900d40c1c940720085041303d55240d988032491074403561801a207030340c52403e1155522045030030860207544554200030045400000f03484402e5488042a5604c0e6a640f40c150036629040d40550b0300010349400c0e070f1007001000c4c0340c6181991180d186c0c8066603030369a0310441e800c64a840c40540032620030410703400f030ba0415030840c0760b0064401c8110042005c004c0c551581c545000c0c000000040c01550300442c1d081e1030500c3c501c1d000e0003224028404001e9405e05510803c6098400405104245044449080082d008200c0710740c9110000c1241b16900c11340e151004c030403034004481d540d1901925004081c0145003803400303803845c1c0e401ca114212006440041c0070700c600003100e546224110a90103039 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 941426906 1250 941425656 941425687
    0x904120f0c05060406240503100c0e04060806060108072d0201090203120c01060801020f03220c0605043201080c07060e0a11011416030e0d0c0e070905091b 68
    0x480c402c00b00010310300380c0c400301c4140b100341e078080c6d20380b10042c681d1003041a87d80000d1982c8a06202100c0014000360f0301c030381030715618a02d04405070454188900024024400308045100c3c0c1000c1e00c94108660310702c4012683c20080782d00f8545202c11886003000d144100080b05000e41d580b900002400e510346400091401d074507520804511100081e80b5800490203010300001020b00c08001d506000e00a441c00005002c001c100350b400c0b600b0804134044410072418101c80707654201000509807901d4500003010f41d4002e002d04a078002d51802e4444c0e1140208440426040001c0c01002d403950860004490101c0050065403000c5410312002e401300b200c80c4545080300c454000144415189071402950008021050505224030615103800c400c01000813074490003450034001e4007550b070900d801d0b204d00e803c808150303400c10f005100510400c000c03001d041e400d0f200c6140c040c00c005c1d601c181d0101c1e4000b003a4003456410990b100042003202e070405410180a440000515040051043d0004038 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 941428156 1250 941426906 941426911
    0x307021902041d0c010207050109080a02040506061204050c0102061005010c02040507030f0e0c0a06020607080c0a0c1a0403080f01080d0e030a06090305070b0c090a14030f0f0d020c0904120f0c0506 86
    0x242ca42140b41c04009070346e01000b4000041800303007401e401a610b8100c40544824002c14044e001d50b44510000c0e11725681d0070200e0360004400d0400c0c07502810281023859a030f080e44841540544580404100c14000c400c14200443c6ca050303480342c601804503130900000d0100600070000380b6407146072000003000300b40070740b9460310703402c1d0000c010200101041007017000180d4071074810740d0800030510041540c0294040d0b0721420b0184841d43d540c0300d1400840711440509070240131005816030044070301c803507260300c0f0b8010b5000ba50f85c0002d54941c40205881304100388103000c4181d11042030424458040c6c480088402002000e64402c109661154400c3e42c02540040700060f800140400420103510003558200e00030305c0003036003803034003000c0410384020703c0e40615804400c144000321035503074080007402148084501516207078191460456502d40c08030709400e000d40a1180c482e01141045203031796202d00d070414095242c042c94018281c42c02a614040d050030400c00303071003030004617004210701c0c1e0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 941429406 1250 941428156 941428211
    0x106050405130605180a021e0a0909060f1103190e0d180b07020a0306050919051c1701090902030a0f05160b07020d060203070c05010f0203070f0203030702190204 71
    0x407070415441c0c20b03404c5031001010160450400d01100d4042c40000606034029a4141c3d0084060401c0040410710302800d982e041d5030203144100042111101070b00b001b000340f0311820080c0082c8001d25420025540c494441c030b500d03800d0a000042c84824504c0130701c83c0d400918840094005640d00e8014204407188a100d0089003030b6029890302c0343c440d0300e00c2d4801030030021491414072059034000340c2c0c9000144000782c1500d4035034020412125080c4000a0100884030390b202d6982c2240c601946c45990142d070b410360190000080d080789074007074a14014000000c0d92905031582c00c003000d070300040c40c0304081607800d440341301106030004080d1140070031500e0144000f8040007085083c0c90340b01e46a9600070790705840301071103448016240c0110300c498071584034402507242c3c2e6030f03100215030441803d03002034460340c00c00d84040d00c003414590055000722290341d41e2002c40c100210003a81d503884259610300c0181d0100054420400500704020300741c910080c80803502003586c5aa8020081d46c0c0303503615 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 941430656 1250 941429406 941429431
    0x2190206131a190f050d020304030314040516050d020a03080c0102070b18160605270607150501091103011809060203010618050102060c0405090c16081803010524030106050405 77
    0x88001400c940b0030462003d10918119010103a0703240018014003c0d10131004195070080041820540207400c080c031040480a820035042ca01401c0003940c4125030913102e2000c5800c098003140310b003004039145400540150280b04a0307441e40d551076019030320012580700d4a5509000040005202424407030180030140340c01c00d032040410250504000b0880c2c2c0100d00154010400c00a007500407081e1902541c104249440b5001ca0f0340024440d840a501c0c081d1744210005242c0342085050603440480c00941c00d81049280c0e08e5883d107a0444440c003006411101007880108001884036082d00202c4100e040b000c42c149519941c0d403010380e0820b030460404640001010788040003418244001030500b48010110760074000f210080314450340c01114043c0c00350a002a104a180c10308075084012458260307902d100513402c01c903025800610b0654076285c01941a29054a41402004d001e11400c0c241404201e500b41603160850345000c21058240d500c5000005840c0c0e26845620310445100586 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 941431906 1250 941430656 941430667
    0x60204031205070c0f03030e1e03120d1401030f080a120f05040201030e0d080a09081e0913021c1a030d050406021911060721050904060602190206131a 66
    0x4e425550650004d06080d0b5503d02e040012a034021403401d080a4251800d04a121a48120030480c00801120540511a0352592400b00c4510b80051511150841e02000007560b0b030748906024800030310012b0448050b031004440452030710001071014081c00d0500904541c949100c038030680d415145203c001596880400040d9609409a180211600c801414035a8100307400607120741c0c0040c0c041507480769126070203010407403c40203d0340c0c101189580c18201003041e0440115552213001c0f402d005648400f8041c1400c00f880c003c0e1020302d04145150100c500c107004c1c203c4014200c50210907101621720450148584050103020b00e414201c0d550b0554841c204800a4507150070140744c0807070301d0a640d1b034020208646c11031801010700200c6441f5078880d42424034090b040c0e80940014a150030564181c0c064540050040c40c0c00c2e8000e40701440300303550f110b1084e41c852142c50900703005080e280705c1d59001440d10500521a4502e20780443e229243c03102059603207001ca600e002c0605c207800240 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 941433156 1250 941431906 941431913
    0xc0209010504020304170d060b070b0a0b030a030f180312120c0e060702090a2403030e010c082a070612110408120a0207030b1315110a0c06020403120507 67
    0x44640c05400c080d58254039505050740c80c0c0b902021003400001c4403510101c0d8130448520755804c61030041030700401507501c45140e800c11100ca510140e88414645180c4000139119040204019050070781544919411018440080d0391245144035800c20151801c4404000901008005101c440c0141e4401046c0001885040c0c110f40d1440d6051050040c5114108505d0b80c446040303030101c5031305480448081e1102c05006025010403039980c850030205038002d00044404c4040d41e000c480c0a030703480c1983c141d01b840043d288944000c10180c2503407030030041c2c0c11002c003855070300448503500083c0e40000d081c6488a40380c100300c601d4101c000022424441e0042e8140e40e0301404c0e1982104405591505180c002156910b80c0c100e080c1c0c50180c0004202000b40c28028446100155003240c42400306203040c0340003449403255103000315400ca06194504a0003c002e11400300b00f6500c060600786460900c45007642e140c0081141160301c144c0800002c400580740c2861240d10b9185c2d0b480d003e840300740f60315 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 941434406 1250 941433156 941433169
    0x50702010b04020f091512010b0c0d080c03012606071715100c1509060b0910060f050c0f070b1308011406280e070201200f0f190c02 58
    0x5182c42075005000c0c684011405504844d00d000381210103100500b00150a030710345015502d441103002403080000207a0901400080488036141300c20b89a8007441c4d1142a2801e26086e80c1c0e20400c00418001442190300a4400090240000c2040900c04001c50303030040c178250080760a84009103100c4150032900d0440d481c0f07160404160b90141c00700400c490301103282034200c24204402c004080111006100240d01c40701200703480103000f4003a911150900c100501609040c5a0003510030400081c0d5006000304954180c80540d603c0030402d00c500e00b400c441c030703402c4840a14a18082c11100d5140a541017024000800d420420242c4800000024642c050b01c07aa011030043e0341010710410024145142e810380c403803022100070100c10041880302201c071141182d030b034004411042000c65004600c0c0c2803140700301c2c1e45500a20009041c40350120401401c400c2e6070310f0350f0806010350888900020007801030050404c02003800d0508801d0680c2c40603c140303640402084100750010309505011 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 941435656 1250 941434406 941434421
    0x19050d1d0d120504030c090b011d030a08092106070206090a260d15050f10121d0a081921240e01140d1a060f0d030305070201 55
    0x1214003888280c40000c80c00003402803400401990076403480c140114000c0c026030f1301654000c1e440700c0080d900c4043c03a00c0200440102c1c0c03400700700d001c141c11030868104c0b52000012303c4040c0103008402010742d210307545a0002148181d000500745200806442d040302a0038082810400405032810a110040d0501c3c2c0c014205200b40e4016040d5500443c810440500260f285000c011070140044415583c55000c0e144a0341d0019051410001d0035154000301c100c01d13520111107500c01d00b1052402c05c407041000c207880c040401e5031018031031144000c0d64007415003004000c083e084c040403001001d0342400d0300300700100e4103040301040c5944040e1080342c1d00301a880d41414080c00100c40502d110000f00714070710a00d9030a5403030740030746180094101a8180900004001003641a4803000480ca10b148240206255030020b45145605854143c0300c942030179800611100302886400004001c200b8010429070b0030961049a500b00e07511001003c10300517000e903600103403504101c20000c0c25150780303 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 941436906 1250 941435656 941435687
    0x5041a0d0f05040309210b010e061203090102121c0e250e01050d020109090f1a0306010609120f08071514090d11010e010e03041701020a09150219050d 66
    0x1c182c01c11002a8100180200b958911050b0619081d154421059900e802c80b000402d03492481c07000042803090000254061a400c032126544150001d805640e0b901803142c500f40143e0081c041e400c558a452401000c968861801c0c42e00d00300044654802a07802103440754620741e00203256941c80d4010310981440c0814a6400102003514085040c013161206005071031060f420180e01d00c00b1a8050b000b044003d105140c4140081c01c07441d14281d00500140458518200030304500c00101d01d400b0440c64181c0b0ba240d02d0303003c0d02501b072095903903102000940071119800500100c101048001000e040450b00c10429150311340c8002c0300c4030054524030410780c0e05e0019001d06004003410080ba219051030b0741031600310041ca03000b0f4030340e0780980b840000c005041c1d440d0a580341001c64011004005a0381c0303c0718030b00c0c808410001c0d61400c07407150703100d03500008803081000c2c0200d55003040329050104a0344100c8501c4511580320681940000e81c00f04c03041e80c00b4110507800141c0212079120010321 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 941438156 1250 941436906 941436911
    0x3040b1b180402071506061b1a0702150a0c1b11131d0609060718150e03030a081006020f1c090312031a09130f0305041a0d0f 55
    0x6500810305280d001e40c98502050140d40200070455449941c113a4110703640081111150007982d4078490020407030350140d400000c814018280c0340203c5550b41176001a030100785d82440c0354180d0740446407094040d004d507045000312125000f00d01e12841065000c2c3c40c4041000400303089014000d0000180402d00000c0c400c900b085d00c0000ca07551001040304ca42095035009a40c07800ca24450006246502180301520210602a03803140c02c005401c0d403007140b18400301c411a0719610425503103020303142c0d8031800c0380701900820700c1004019449450041e0a45c00c0190303a40040200081c115007140c403180000450080810131011000a244802000a07002904103c1c03111500d0f281c40d140c1505160380160064041145024441d8103210b00454000c101d4440441c80c5000c010007a11340c8400c0c40102038007000380c0a1007450495901c2c0c1c019442161158200107003944da420503100150810b500b03000007400700064804084007003481000f0342c00303105a5200048101c41c02107824401202c0080391 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 941439406 1250 941438156 941438191
    0x1030c0f1401080f070509030304080c13142a12060414092d01050c030a1a0a0e090f06010906060315060801170c0d1a0702120a0e01020a061103040b 65
    0x76000b003070454111806072044c51641d6034600e016178461040e028020f4140c8000680014074441c00b1030200100c0d4401c88126039680c020701c0303c801c181c404a03510802280719410105a00d200c281e00356101d0309800250040b01c0150912410b0000c3c2c1003001c007004a0601c40040200625080c4502402c4242c10804072041c0c0c100182c2031940d8000320b15411900841d407580c40c58148642903007029030401490001e220615210600034030300d030025a02d010032203007005098080d00015568100700c0c018050981e0307551300d16000000d00408405003030002940103074910480c02c0101404a9806013107485404182e0328036045004007110414445c1003d00c0f1017005050005950107024a811030701c000d40c42800000340001c8590038a955100b10542c4004c1801c40d9500f0400c840c00a072100300d000322210b001940d031305071060340c80d00c83c5140c03520210481000a011050301408440010700018811600e4110030f42d5501c0007103444d189541b0001040100420080068010303210b98400d450252400400 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 941440656 1250 941439406 941439409
    0xf060108072c0703060f290318010603121106090d033204110409150c030608071d010503121207141801030e01290a0e01030c0f14 57
    0x882203409440302c101c0301c5442d80605a0300300d0000101c51100031101030640d00b0641000b400401251080340a0003a030b5130400a981c0110541403040440c54440301c0045101c05040300c89a03900c001d14400c0a401f11614400c0001c10921548000c0e6100d00030780c65031403416190142c04c280301e1801d4420540d0140e02005a0703800f0204012030321004504000c1028200102c0e84c0c41e1001c40c9084200f000411100315124070002c50007403d001e1402100800919540b00051200765200800058603040c00c180022f03098184550285035040c1080c03500061039500e5a4143d820708030103074040008030f0380b51540311140e14901e00e0840d00404044008100780304800072490b2007801040c0711015054100f00000781c0c02809440c10401d144a05450599030f658105644851114000503050000340b4000e900442e6010512802160b8591440c003841820900803012072500c3e101011036801900e0b08c0d40c00a1083c00c0b84004501031841401d05504060606000c000c3c21510755014a111290f08506071816 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 941441906 1250 941440656 941440663
    0x606031202010c03050a0e1504050f0f060601031a06220b0d05061306051f050d0203091e0606150309011103070908010506010c0b0c03130c1824150c050105010e07020f060108 76
    0x12100ca123401b04504c3c2e0b460381082410200440364a11150044032044184410041400c910800007601c01b0000c400355070311a03440c0d06545a0045400400422014400d907100344a440c2e03c00c1c82c02c081c460715907502c030454042e482d00081902490542c81e1003d00a5910b8840f400d200140e803c12020049103242100081d607182c4a4065071500c1c0405e02401c2510b2885501201d0b02e00300031079003e640c1ea0408240d2280d0f648940c1c0304080c000d00641c41000241640410100c4c000c1d500140314401981c0852840c0281b5840a8041300b1650341c0d0304920045a51140c019500c10003864540c44403041c5481c410300e0a46900400b180d041104201c00b4100080084041d01c1c1c122680140103500c0c0d036a90614005150f14890000d812025180d60005000d001f0341e40c0c0c5545083c1401c8107101c0d9032086400880c9903080007101e04500a00001c060004814801410205010300d180256101601d07807105802c64070203811600100c40200c04110f041303a0104a18900905010000e00c06507241580301c644 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 941443156 1250 941441906 941441923
    0x160906031508010c0e09060d052a030d050c0f010e071a07120306030b01060e0d032a080d180507140109090f050f0705090901031707060608011406100c030c0606031202010c03050a0e 79
    0x44ad6201d803403013541250b034646582000c00b107000e022110740c80c10111000c2c0840e08061481c048612599050a144a0040c0103000d10340082c50010500a400c2282c87c66203010758a4452032501800d2104501084104c11000188080b035100040c1c6541541407050a140d4140c21803018085503003660701c0940c4540010142007901031500c034015400100b00181c0c040201e42e490040c8021f0038503920103000c21080103044104400713904002c001c0c00c54106078216403030b0042c00352043e0008101045607000901d94580b22120524103452038503120010031301100e0203002c501114640d80c204004c80054505140e84e00301c02542070041c00c00729103100007421440140002418600303031403034000d11408000e080c0ca0140358411400c0c85441d40740c94189000b005010030290800010b03001180040c1001d078004424a6000e9441f4250301c9050388007501c3d400300001e402c40d0051764802c1c5c0040803a1002000c0746001181c3d038000704e9000c21b46a402401d41e400034051070340c01403074038207078880000c8001007060303 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 941444406 1250 941443156 941443183
    0x11d070b1e0304020a0902071119060903061505100903020a060c260c0a15140f15010203090a080c04060501030b0d020f0424030b160906031508010c0e09060d05 70
    0x103941c3ea03a1440483d003140e4242c0d10400020780041080c50402109016111401c2c00c01e5030b501c40c910408501042c500a8684550004a0200c3c4018030101c3c41c2500300c0e5030303504100380d2840c10700795a56007c43c000c600040c0d0f40c040060b040d42401c1c0304504e0710103250001044503241c0500d2510090710f030303a00e516400d2012100458040d200007080e90100303d095030a40d14203801a12000c1c10141000001d1030070300040b9070400c40c40c1015582620000107070107030249042c060018401d60741c03421060108408410964194801400400c140e0741d2171200c884041d00c9290003402e03141e91408188401c0e9503594105c14103260808282d16080d86800640b50b1080da0100c50150040940c031300850010b044e880901998081c0717400c400110f0f40c14000b281e0084034464445000740f0364601c5440d14203205030885030000613001d620b0822106210390041c00041d504605000801c50351ba800305402c44000540d01d0001c40c01880c410300b924500180c100d40c2c800800e40341c10764800703490f94803a0381340c410700307c07285 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 941445656 1250 941444406 941444467
    0xe06010e0a1a0310020c010e0106031e05070f06050c061503030d020702130203131502070b06010f051b1c03060b09101202070f291501050c011d070b 65
    0x440c403481c02e4000040140c03000750541e03001c214800d401c0c102039484038845903810742c00d00821046487d41441480200c03500a00f045038405122020302038828130107141039a0314842d00b900810344c903000d884148014615900d405036980c844688540c2000c0d0020010070b515180c00b140e860b015280402206d296000104c8016500c00741391002640f810011207845174094404820415081c26003504091721900854404944030001d41d104e0061f8031034804001e02d05181034003c90700c0c42d405656108003100e503c0c100b50b41020070030368104c110070002080e11039460b4018080b40d200c070403d102d0751742006116403506100d0503050080c074803494400c614945000d06a4884a9240d440c0314443c0d000d40212031800c25035681c809810f140104120a80c01920094880102203650707c0b40c103600d51100c0e64000c4849003150b904d10381099266000d4a04550500200f0030818626107002e2040343d106401d03090b61001e440800142d81c5281c20390303a130002c40d04031078200441d4a001140c5d01244c0e0510701d5440d10f0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 941446906 1250 941445656 941445671
    0x2150f0d0b180601080a0e0a0c05030f060c041401090806040c0501090b0c15091903020c030601050609100c03020c0a06080118020a051605010209100c2109140d02090112060e06010e0a 80
    0x1210080041f05020860760041b042134000304040d05400c0411a9411070481d51840604280d590300d80c4020355820007104000c20080080c940180c5e10131910700b0050406044441da140700c0743d0f0800c1022207088501100301c0c80c05018a680016101d0041c066030545141007804954a1540d5515001144140906071100141010301c08021510517003058242d078221a4240f032801030364503d450302d0054443d005440000c01c0d10304106095807190031008107100c03c681c10107103041e1450300c0074910139802c6001d84010540e0944030110754000800d1140d6641c05150324100b91000040c00b407140c408500d500411280402a60080559480030038103242d01e92101f100c0d01d08030b402849072241c00d070341258019007040c0c0100c0d004510060f1441c0600581035680507425981143d681b1145400800b00340315440500201c02d01c40d00d41d01c0f00320780103442c5641e540c0141c2c000036450a026840320801e2001c800303190007044030780d0144c0c4401040c00c2000701000d5040090500042c130000307241601d5540c0d01c910 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 941448156 1250 941446906 941446921
    0x10c080c0c03030a26060d150f051f0b090904021011100f0b010306030c060c0606031709010216050d0b04051e24011a0702150f0d0b18060108 62
    0x1d0003101820040403031366543c4040c200500f100d0858040021011801010159000b43c1c000c0c0b40b0b031003904000e02451612146994641c034100350101109146941e82060755074589080c4100d41c02070070400d030440c0b80340044081400c4040e41c01d40103003840210501c514032081e03c031480c0c0e99420950441d03400140743d005000460b02c1505200080c011031003462415010440039030300c400f01000500e00309010480d0008015400c1c1d680510001740000c07180e00c410820b2034400c1c00540c00152290201050055a0340c50324050100d80130780f030544540f40010040d03010b41e010012050200020914418090310780b00001d150400c40f840c02801e5503034448000703400c10a0502c40041d403140c1c3d0b0844003c41a2010850300d6a8280070031103010555208034028015815004000e8102d520b5035020103d101c1c44400440540e8100a0007281c00c40900510244803450b5034014144c03c0001c0426035440b0310780c07500640709840c1c40c880300300d00540c04000381e110704200d280c0c50160700c03030002c0c01c10f040076448054 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 941449406 1250 941448156 941448163
    0x10e1603110d1a0406050906041a150a0b0d05070c0c050603071205070e101809020f1605010b010e0a0302060a0e03032101150e130b151b1b010c080c 65
    0x40b401400514114194030395600001e000d18011405610100200d60b00c0e204026643c40069601900611a459128220318005d40c202c603401600103251601d50748004010550706007281d0010314100102190105000701c49110383d0b9130242203850302d0035400f1142d80b81e51034074160307902846003d210000001901c0702d002d070200d806400c4d4404402c01181c545100e0051022942e10101849071140c602c62145061082032150600d80849401407841b40c604004440254082442c010b0f24000a00c0300203a884001100050058041c1c000842c2c0c41862200042000c150300121034801c241c00c1c0014000b40e00c4003400d88031907044a0800694884101740001d01d94003400f01d0460714001030798052803440d4031140c110b9048684040f41d41d8121540024255412488540ca403500050304401211000c5443d401c0201d038101e016011029850003184902c40075404410491402d002c0f07109402c0c008142044244090100030400c2007001e041d84000038075141c0a0000600100340c0842c010300295000d2 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 941450656 1250 941449406 941449429
    0x30c050f180a080610140105090d110405040b07020607031e0f090204020a02010c0210142208030109060501120c0f0e13060e10090513080304111e03010e160311 70
    0x901440c0030360f6581051079a6a4070450b0000c51400c0d08440c0003400115000e140e43c01203605848990038482001d0600488203120642034403c0d50304807802c1061340d00c0f0f0f40b088501460107131f8104100c0b0f10b02088045e19000c00540b190007090300e0805000c1038050040c40c8040b0340c280114022400b2045100a000944103040010350b101d0b01c00280402140d405502904440e0465000d41e4002c1c02c441c10080c0840d010103040100c03201c0094001030000d45200000444050a840704000e03c41340c40d103d48015400036080b00c1700b0517a55000c2800550b130003248210f1002c0c101d102c140582d250503000101981d0301d6601007024004002c0112036156039030700c4012505016140c040082c1039403020712000040c0b0945270460808520b550106000484e400707183c0c80742110601080007003e15580740c80c50755100900594103251081c1403034080b45e07200880500c640c450703102c201303000200c503408150856503e20402e040c10760000c0c0d111300003200d03100c3c0400103d80d042860b1060145805002c1580602e50 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 941451906 1250 941450656 941450659
    0xa120c0e0a0e0f150d0c0602060a0605120615030a0807030201380105031012081b031213020a08060405070305010e010b0a05040906020405061b06130201020606091b0c0a060507030c050f18 82
    0x1456020500c0b5500289e140e10600703010605025081d541d40a00010305022020b004280d003200000648200847d400a403e8207405412120081c403903482d40100c581120740d080b40180d4488a07a0b4102c088540c010b01e40c0ba80c25800205401a0342c010b0100c403d0b0030403c0e9a03414084003100058000d19071024081c01015000340c460904071700361030004030f030b03501c4141d0311810030301c03440381501e01002e000082c0c0d120080380d1f1100c03083e983c40741080b801e15022030184c226403003048440c0c00302d202c3d001442a540154030640003048060300b10300d40030f425203402c40c5031442547c0c03400c03400c40240da4460040340211902510b0014440e4034608111003c0d1085402440d08207100040c51304c00c24128458001d0b01c2c1c2ca0880c1561040d4070780040e0980810103000020f401a071004003ca082481c1090301c0c0d84d04428001d2071055036005854070912550001c03115810103403c80312485090040d039009090340204a40f81c03c0000040c950300261041c06403507400904070304049050507044500d40c2d14544071300c00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 941453156 1250 941451906 941451923
    0x1020705040e060f07020d1704060f060902071502180f060f1306020118150b030a0c06050a0806030c280504020d0603051605060d020a120c0e0a0e0f150d 67
    0x8080002e20356924054904c1c8001280480c0091242407020810710b0007180140d0b1000b050010b0008203c219007400380003542c1890b5541001b200c01652132190000800e96040c000d608c9001078100109540b5004100380c0030140100542d554840210301202c158000454102030f15002540c0820f02034001d1461152111a00145484500c008550b1410842e80d0035402800780e1280c4a205011010012000a2001014184180070014250030808200502804494100045464030602003030a82c0c81b100200d2400900386080550184107541c1c454415402088084900c80203d4903541500443c10b03907400c2c51020407040390007481469030003024010025900c40d6a409400340003040c11788401c858038404c5208110007040100040710465000420309800d000103802c1c3d40000e0360140f0b00000c100187c1c8802d01d801010948200d961001180c1e9a070310309100e646003800058009500280540d456050800200160210100c4e500103180421b8115101c02ca0b8042003403a040d40c80010216003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 941454406 1250 941453156 941453171
    0xe060a090b0903070b070c03051c0213090504050c01030e0703120906110c09040303110c01051014120d120b0d050d090b0f070803070504031505060108062205060102070504 75
    0x994004004031030007806103000075140c0c031980c2d0380e49100d0b026009004a50000000c0c0502c0e02a441f48604030340a801d02a1421541d400320200c0d5900040701000c4555000c0307514004140746a0031200034000f10041041281071170b0f100d240c1e860062400c00c070304241c0c440605090008050020344000c40d400201d161180802e9440a48036000340d0080200041d007400d034064041f10002004548068003800044258441c0c0d14118090b01c00b1007001e14071488200f09200280d80240314203441480018000c150150410a8000c40150707100d03100e5200d07005c41c600b00c00030084046850a9000c40d58108810061040004007011385000300d09983c2c061043ca03a40d02c180100411108180d081aa942c00c0c4000e460300521805030148804000d0009000c1c00205e00003a00300009540010f002d0504034105580e07607603440c244d5040507084086c015140c2c0140001540c0040185820640844040301407502404004c1084503401e003c20051a8540c0b01240103a4020700421024040c060002d00440 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 941455656 1250 941454406 941454421
    0xc130e0a050106080c0f0d03080901060b041202150c100b030a02060d0b240702061b01061d0c03070e0904030309060c020a0311070807170115030b060f120606040f0e06 73
    0x8000f20310518426024981c079a030381900e41030049004101e0010704841502e085500c0440304580d0082000805643e2100c002c07805554250140005042e18004814031030210b00c140030a02510049203110441c0c14803103002c8102c0f0104034561200941880001d201000030002894030700c1700980a50003107400241011030b5001070304075034080d4406480114450500d200d4030686081d00038032451004000780040c0c4014a1700c0001005107146001c009441741c0d002005241c2141e0395580041e01d49080b0040120031281d000490551111842141c0b6065151008028041150300400310388264400301c00207007054029408048540e41100e41000222032600020703544084800c02035011036225889500b0a5800003000030039100719001404200d441c1078040131080d20401b5510f000f55403583c44001c280520441184000e6005403911841c1e424800c05001c000751810074a1801159060002c101c103030707800112260001000e640010b0750840614800e002444daa144029650041d1018400714 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 941456906 1250 941455656 941455661
    0x50601050d030c06060b041d090717030c010608070302150a0c140f1002210103230708030703030203310206032a0d1103041a04021305090706080907080c130e0a0501 72
    0x15181425110603031503a2302e484040702121b040b50321703490359070104d0824030505000f180b4070541c1c458008100d905080c4400c100074290364854004ca09964042c0f0010010b500d000b1440d11802c900c4802c009141648000c0001c040d49403010003d484840111a4040c903244100f00001001c040709080e243c0320348103425807901030f60050914000b103000c029404010022481c44641c100ca038040ca031800c0d44035084080b89140451039800b803c0e80c0c00352000001e9200010700091800170b20982e00161b891410002e0400307030f410200c21181c4d00d00b2501c203282c003184402c45640107410303030112070854a0b43d56803801802c02984003503018052003141d1000c6941500c494000e823030b01d50545041444004018070050f1618001240c000e4401c19644406a0054003600d01c01600240003514204d40da04001c2d1900080e074400762030322822940090b50800401d503000311600c0c1c0014840c03001c3e260345880c010030540d80d0400c0401700d9105298031072800e0307014403103640208900c61002042c3d072505121820003500 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 941458156 1250 941456906 941456909
    0x52e020a050c03010b1804050a080c0d0f030c0813050f070801270b18070302100503040605091f0e0c040e03121e040303020706090c150e0d050601050d030c06060b04 72
    0xc0307a01c55a4410000da181c18080c54260b5000544046201140528141400000544155020f001d00181c80000c03855440c01001e4a18500d0000c1c10b00d01442c8200405000240010703404062401d448008526880324220340c00c20000441558004020309045040411898084404c1d10403c07800089104040d0000c51003a0500514100a000c3c18600c400c40300301480b200a000460000006d100020020a0040b6841e4450700311120a42c40794089800613411010050100e1000700410003040319070f000382c0b54850252409003031034080703640407845165050401d5100083c0ca03001c00c030510040402c1408511000200140201e01c560485162aa400340d19940c0101c1d030f040c00001c04a0383c603074140a0000c0d40140602c02c56540f0707618128029080344000301c41058440c0600e0300441c20310711000000d01841e00f02a1449840d02d40064400b54030407092901400c04007030380c0004254040340c064119501520030fa4a0041c0318641110000000d030700c0103006520b800408200e0184044c050300 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 941459406 1250 941458156 941458163
    0xe0105091f060f180501080c0c030c0d032f0d1a03060c13150e09040f020414010503010c03112a0102040b0d06081b15070b0c07120503010609052e020a 66
    0x20868441458003404c00100d0146501143d000c80100b61144c0303240d4000d24261700080c059074109401c580b807580c07c00c207020206000098440d02020141ea1380903141404203c210010380d1602115211001524065004444081740d9603034088041d1044c1c0301000c000c8600d00909442c440e2610030180e1409420165500b010a2014140130031a0701e065800600c6940c002e0f190a65409490404c1241080005008991404403042d03510016141ca02a1442c40c25084690081540c1072905143c00c47d010940c4070401c2508009510055240396030440700300c0300050310143c044071600003a5182d182c0c03000c0380300075080d0300c006400500a0018806441202440070040c0300aa5807041c0290f0303600951010820070280c0301d4000e189518003900d00b0150000341500c228140f10141d25150301c144001c035541c00c104803001900300d04110307491901e6600c114440c1070440c1154141100102420200e000722409681d441d91481d5081c804c108207110204085140940d1540c014100251507480014084 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 941460656 1250 941459406 941459417
    0x3060109093f0509040912140703120c140705030a03060b03070f030f1d0601031106030c0409091506120311061b0f041203080106180e0105091f060f 65
    0x140001401030041c2035010121002ca035520716031014500e03403911124640400d100c800c004581564980707006180d500b07405100010404064198040c29a003450350b4070300500e0104110a8000940196a41144c0f2125080008951148240540c0c00e121944c0c044c416419002c00d60700704101c800801860502180d590030f01c211640c0e084010824007090342c7c4000480d00000d18030750014400d40c00410500020140414145024050320007490410995202c498016030f005005021103981113a003408403d031001071440c0380500e01410a400340d4062400e4089d1501405c5051000c4090405107204400c01300b00306413035803001e804070301420041088000c2440748040310700c50b203004500140f08080307206059590710700c1c0b02404841e40d4050301c03007103c5041042c003012400c8001d009154a070540700340c44184440d41018400340801000300c15a0041c2c034a00003050041c81c88c8422541d044810503990351006403203032504c000220055049400c0d401108450000f4590381c840035060b0705c000141c858 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 941461906 1250 941460656 941460683
    0x1c06031b08010504030e100201270c0e0103051c02070e0f010501030b0102060405060601140d14011701090f0b07030f0c0521040b0610020a05030301180b0103020a27050306010909 78
    0x1d1030a8550446020700400c90030640881d1a00303151700c049500031294400041c401e41501109003010102025a26aa00b00700340f2180401a034138413144040c0880714035150180d851aa81c040e40d5104103600a07603000c25004000345203034000c01920703002d8060190b0400152420400b240600d072024820580060b0420f002500554000b2034200c1c0940e400002419a03961540b0040d01c0700e0402445559101104212000202c070644c40b0b8480f0194080c52001400d51400003160300c0c100d0500ba040c4030f41d92415810100080e8010407010f0502c2e03014400704083d59a000c011b8008000e1680951515424034000c89030050748100204485415140104540070214407600701404084034002c01c00070610b408203400b45420444529030201034411240050015030700c1509580086c1d0108510290070710031410300d4005130144036200103080c0f0b000c42c02d01d80d25071001482c40018000c00c02203204100242c003080c4c103a00341218046c0402600300d80103565251041c1004100c1e0403815200da034910f110 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 941463156 1250 941461906 941461919
    0x80f10050a140105041a060304080c061602030a08100803120405070906120f080906160210050a1b0204021603021e210d1404050a030f0806151c06031b 66
    0x200588000034000c800380c0b580c01c0c407051200a25043c2a1172944002c5881c1041582e07507000c005620a51081000742d403a00034691609203040303c054480c00720b84900035510003034a80d002003600c2c0c030007040d850052190f0715440c440d4030301d0f207031160003480f41800300045e4411110b07110200140110f1161044408855640702c0100440d02c56008842d079218001c04030303001084040f40146035150144580a2503e10b600b00043c0d5682c1c0084101341c1110141a0040d081d4a41240d0005c0143d1003424002d2a1003020301005061040740c030404580c03810022100000d40d1101c0e415201d419082c40075400c81e503801e50501070760328180305901c3d0484521042003900c1c0d021011a103150f08902c8150a004405510090035140d500110240c201c160354035900742e0003d664156040340640e00407005050340b5000ca0a000b010303008604400424890444244002a245c24407000e114010b010002606c510407030140d6803401e401a43c0c5641002d08007400407003031000001d42c5021150829850603441551075a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 941464406 1250 941463156 941463161
    0xd03081003080d0e121c23010e07030e0610092022150903030c140303010e060405130c180f0c05131410050c010b10050d0c020708060406090c080f10050a 67
    0x1131000e801501c0206e56148112029007001c404d002040680e04c006640684151140d1002680040780c08602c80c03081c0282140c0501c01d00c081e5400c13650140005207041001c00e460340041d40700355070038150380701005003040381c085400716812130110219030381c0d40c18100740842443c20030074149560707000344030300010300050b01c91660840404662035013181c3e1031440c0c40a4400030352100041d0342034a40e42040f9141d40c08148021801781c09040b80207801420702905200072250000d180844150000c000e00c00800c40b80c00b000d5049880c0003c0e1030300c0014050344620003404c00503030000c6080e414212039440031501310380901581d40400c0d039000d21569031110b0003007840014a4106410500100103011303110f03c55030041c100102d1900007c21181d5408001c5140302c09000f00200000e003010540c00282059270041c010055031f0f62009040043c14040181d84031080580300400703450761143d501c801c002d6407010881c000c00541b001d4610044494801a4030781c1008000301a002e4a0100000c80d8483e051 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 941465656 1250 941464406 941464417
    0xa0b1510020a0f06110705030d06034103090319030e01090b0a030b1c150b03030a1b020a0e0c0d0507030c050d0e390306060d03081003080d0e12 63
    0x382c0d5071902e40c20941c441500802107940071003a03081702008004045042000104107113100344ca000940e00e0b107141841d80520074074841c03841004102010140c81c2004030401502c00880c403e0b100c6103c0c1081d0380c800782c598490300e418542c040c042c040307a01c00f011058039045080d1501944480c1c140d41132110045440c3c070200d00540004002c144403810341076100380c1c03045165900103049400020705422156034400e505500440c1c00c540c00703d80b01e42c000040c902600904500603402941000f20455001c1d025202c0c0085400c1c4140e16480c4000a641e40c110380c890040245000c441454200101c0314819548070300c1444d50424140808185101d10030f201e0b07180700807540e580711818a040c01c400400600107034801c80c45d59208482a011411031806400c12084a2022000c900f4684a0701c0111010490215891107500440d0070001c0913140c102480c03c0003039040c82c1000b203da030b40f8040400203a10641018004070400b1a900780e044645a0162104c0c40da00401c40c1c2c1d01c41c09010300303181944100d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 941466906 1250 941465656 941465663
    0x504060501020a0f06150302040906020c0f010b0132161e0215030619060f1b030c030804050307060f0b281205010e01050403270303051603020a0b1510020a 68
    0x250344c0d604081112684041000c503242c003d40c1002643e40d07000079050740c1c120101030303960b50340c001400d540810040003100359518940000b401032051210000c0c1803c008260b821002c246e25420b042c980049030242d5050f0f03e00a1240c09481d2074a00200f81d1400b00c40000450f0b08503548001c00c3d1011141140300c501e500d074018003400500c0c0e04c03207400c000c0a42029042942000c10b0311041840f00d1800300749000034220703c3d61a0300500301158001000c40d0f4607d03501d01607285250400c000841c1d030010003a10ba054260526a0741c42d02d491802d18954412508050300d00c52800b92020700050150b00243c150ba401150340c44903580740d10000c1040c1003400900c50010080d8250104650811303d1030781b40d00d40e030080c0e0001071003030051f41901d403d60b00212801c40000300000740c007000055513030103002007007042c10340c1d00302d00750b415940c01030880e00c40e200c0c0c00510603046003203684c1050300c00c02c90030310901d0b070191283c1407608020000741c14082150220074400c00650b285000c0c4640b0008400356860342 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 941468156 1250 941466906 941466923
    0x1050a030201030905011b02010b010e09090319090305070e04020111010b030a021908150610090f0603021e2106030325210503041a0114121905070504060501020a 71
    0xa903600540c004c01d10501e04440c2c039500e41e685461312a0102801c0d00444603185c002044090014000600c0f0702846c184403441280a50180040da10001007528a003c2109403240080d2681040a441a500d10380c0000c100e840b0300000800c2000c506107426000e0382c800e896a07036080d05003809041c08c0c3c488184d074184e015808840548050310740103e01140078090242d9040303440e41c0f1030681e6410720031916145021a060710080c0441030800c40c1e0300c0007295044d03180c0950014206812000604420f00c11002010b80102c2c0512664003002c211044249450340c600b0303510110341c040443e60b46480c1c090f03120101c014030001400c5007000701c00c40e01d005040c184450030021021030b0201c040040300a00751105142110a000707150540381a0031901b25071b0f5210315440f0b1400745443c4101c401058121400b80c1e00c81001000100e401074003403aa501c80440700c00301c200030306030350f002c0c5402d5074051380c2003180c0418100041409808220201603940680c1c0a2001507101c1005980e9654a010020210790 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 941469406 1250 941468156 941468159
    0x151204060e070b091c151d0c040605091501140408060a0b0301060b04050909010207050105040506040c090603030c0210021501140906030d051909090c03020406020d02060c18041d031e0301050a 84
    0x480c21094892200d10a0320410f8052040c48041030813640780e00009140c04647c4942c1140e880c40070400b6212040c0c0494050180d01e0414020507010100130f031041d40c482441c0401c0700c2c1543e000d10003a41c0c007449000700142d19a0380c0c03026585c0d90313001c040e6019900580341500100040c10180580001d9407008441075181a04d0032040c81a0b42e0401001282595824450040042c60030300400f40101d0088004003028101403d2050622110b640b0040c0c00c10b15104081000035000801d40e901c55804440c450400400300c0404e03030410042c41d0946412003030200002c80c540e103241c0c12400c203030030342075401c001e40d41e80302d0341415507400024a810010440500c03405500c038481c003c0700781e03800e4014071b01408165a5007104070b080d03451a16501c008650007140c02c0c05065030400c58400300e501e540c070060085043c1201c80d0070061140120342d41d03204049c0b20440f0400c3e10345412000308013120900a00700e958060020648076006005101034034000c400441000c0010207007520b0503620010229001c09 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 941470656 1250 941469406 941469439
    0xa110d090219211103120a140c0c2b050f0f16030615030b240d113001020a0e1f0f0e22050106030c050405151204060e070b09 55
    0x72400c500c01200c00800d80c1d10030741e000c0d407014807007151051b034104403598458100c03841c0071303120180922004240b4030051010800e03500e80043d6a0740714040580e444d43c1a1a000e040f281c00040703442c5812030b240040410a40308110001409400f2804120305981c1b0400d102e1003207070b807141040f0440750300403071510106002045ca240d03c500445007042c00b51646590350303a550140131520445c1e5000049c0c00c0d155103400740d4a000030007400c2c610b0045a03c1001c19005079565100ea102c0c3c04001e034003800c815018a440701403401e91441854100410b10046102648003040c0070354441c0e808180007410401c001d9019050020726541c901d0003c0303d07031880700c50010380103c440d204042d03641001c020541c2c002041645803e80c502d05001c251242d0302c1e00c3d001705445507505031541a03000c40c00f094031345480a110968054182c40c15a107080311401621780503031440d4501c0780114503940d100d11182009110030014241d004030101125200ac0d1882142e607000503a031720b40182c4403d280c010010700181143c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 941471906 1250 941470656 941470709
    0x90510090e100f060c020d0f141b0f01080f180c10030b0f060f070807050a06051305070503030406050a2106060309052a06030a110d090219 61
    0x4590a19001103050750341c0420700c800800540700d40014003240b034014007141c1440d00282c0050012418100301c000c3d81070f4081881940310240260000900c13040310010088090b079030620554a0004071003910300d03480101240e4061480d0141c0c40b504003480340c0d0641d540034030005031060701e644d1550800355403540e14070141c9142e40b040100d900c5c001c50359aa940340d500c501303c029014800b0b99000a1400c4880140701a040148a12502c9684140129a525000001140c01c0c850b480008591944228a003041c41c00c5408100240305505020802411400b500301024989001d01c04455080396240140340c2c0340d2103140241c5000030300070010004a14000c0b042c05075020385000c0910284044264450100c600941003800001d485042c01c1080c000700308171104203150800c1041d81070820100d10308034407228280000b030042c03030080001000365000b9445040400b406820281d5240c081000403002058050012449a03402c4000e583c6180201c04110042c1e078241d1614a2080011094403080c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 941473156 1250 941471906 941471929
    0x905250509042301090c062007150c14010908031b09060f220905180309031e1005010308031608060102100b2107060f11120706141305010506040204060905 68
    0x16640340c45c171031800620440c42e09401010b00e0383e24090a9480b1561000f18603042800c00d441507403000d20140254051001303002402031a84c18080004015450702c1301d0350b1710219990040035460410904107110002000f03610880c8240911842e07003208101100560140e0010190407140c14030210102c05403c10080900212401e4039607405524030000e01d0401c90580c02c0000459180c0c4c040c45000600000e15031140880341d40070f54100503d02001c25a10381802419004610100b210050400c2060080403410004c201003403100b5a180d045c14406517000b0380da03860420f003e000a968204d0701c00d420007030042405074041c00400202d4440b0030003911411480d9a4002a03d030000c402410b04030220100680c1e03000701501d0000c0c0380000180c036407884425607a0502c04524003190301d500010522200c403c81501c0c925403520980d0034070030020036002003200000811682409151460029680f0800c1d11601c000e00c9503903104000c0c402039009521901020031408101400f191400c40319059 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 941474406 1250 941473156 941473223
    0x50103090609021e0418080715020c0703060b01090e0f061918091b180f09020a090212070912080f0c0607171e0a02030a090525050904 59
    0x1d0030b00410b800003030007000302032603603080098020b484c4c1100c0d050038040c083e4000700c20750180c4414003094035028070620070248000c01404052808019000407681600d001c6400c1004035009642c42e031410000804c520080c07140401d00030000010056146d43c0300f54428120b03824000a1030321031000340800c4202c415a1095010050070700414070918003c20f607148000c00a03000300303880f01c40703082845040c50b1803004000240010745003070108900e0089210402a12380c44001458050003210400030510030100a50040480000080c100c170250040c10518400705124040ea48030382c0020b4543c850381e4411620307100c4010f90040c01041c030b4140900b00c14001b2410191500300510851070414104541110103e685580e0146503024052122540080345182c04406103494061600740400300a0004400680000019141483c19002810a00c0c3d21108940340800f040303549000407051550001400c00300390400058038502810481d014507080003410104400c2e0034104040c06126030501e0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 941475656 1250 941474406 941474411
    0x1020f190c05030a09090f090201021906091b031b05150f090406080a05120313060b1c0b010501030c14090d0c0e04080318010e150601110102041202031212010501030906 74
    0x1c00220b9030510041810503440d9403801c1c0c00605206908003155143c1d10100700161904111a0042c3d800069060420360940c460840c0d01c3c1a614140b80079015414004200d029065243d400000c4030a01540c2660310a901103007141c60580c0741c005003415940f289590120101e0300a410301c000b0f84004107203458604540710720700030001e070109084c0e07421548605403d074055030440041c09014480e018450480d46601c1d481c40c02c1295211407000070100002d0a1665101c01b0803c0e641d6404c2c0d041080000c0c070f050f01d9280c465050500024a010900c1158046414491980305592096058401820800040070b080042403010310021000b000c904072041c06100380003040710820b08000d14400d5205140a40d920f140c0701d211010b007460b0314514241d181e81004a0b10580c0000400c1c908001615122101e00550715900120703285c2c0031200396600154400035022030300400306500d0051080c021340847d140410100c641501c103124110410310358111407001480150700c03079000b0788012405184003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 941476906 1250 941475656 941475677
    0x6190e030403110406051c290a060501021605030714030708150a061211040902010e120106171507031505040218040f020306180910060e1801020f19 65
    0x609145900c01d030000d0b1405440c2003004003061030b10380104c80140806403012843c0c1c401a001c0b205282050f54002040031003455450800c038074000c0c004a130303025501c401c40c20f500d0410701c0100c0010406400391078014010094840c4a0241d91680341d0120f55010300203041075031511144252912810700c0076a4036002d100b10000700000200704003000c1d00120719a0103c203051080d8000110380c456805440c0c1c000f09840090301040c03900c011417512110540d008a03d00035544012927064400c048102d500c1000400024045181540840150349614103c038012170001c00c0b10070f40d26104410794501c50b1880d139000440072071098009111400d400000c004c1001e031a400010305981040c0389a561901c40c0103003107070203490940a132900d201d14100c0e0841ca54181130021030000c10f000540740c5000410680031034400741042042d00e541e458100010410b40c2e03210414051911415076180e142c480b01080340750301141040c4201c9a4046407a054503140c04c6103c14081074440980301d5034414003860901 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 941478156 1250 941476906 941476931
    0xe0a0b030103030f09050f0f0909010b040203100501090b032505070210050a081e0c22030b0f0c0405030604032706050327060408091c060203040b01090e0619 69
    0x345020314803035120402e41c00301064000300400d410b580010f00c0343c100d01d1224111515400080c1030f4143c0c0035101c0200780c0d038580c1d000d180501514114a60400e10010030000c1148500000d081614804d90740c502e04290b48004182081c0400d1740c42d6922036a881d00f600e4100f440d5900a10f4500c6520705109090454580015000d40010142c460200c0c2c0c002441c800320a1340080d00710743c080a1039802140d42d0b00d031040d8240c5040f41c0201440400b00002902a42150715281d80800c541e86c0c150b2114000b603101e1501c0301d410725040e50b01e0344c06030141d18045107001101c0800d5505a500180007485a541e8130b444c2181d40c80400c412402650b051801c44070114004150808003a052540301e055403030401c1070500b00000d9101d072250301c5541003240d480c0d005440c0800d030550402d401020680d190b5440f500020075010310014400740e29150502036001b0008940c020b5807049010f500c034030007180c0c1d849030002d09803144509011802e030090300002d484941e2100440a0124a04500280c03c100444 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 941479406 1250 941478156 941478179
    0x1060f03170307111603020f01180b0f0903100606080c0c060411040f0507180b071e0615183c0b0a0f0801060602010219050a051905071b12030e0a 64
    0x401401107440c18172014815814880b0b1600d10310300081c0781a45002d41c040488001008071401181c0144500155110680381c1000075502e0441c801030584004440c001003140c020501803203040003251f601e0700011150181c080680e0020003102003d0140d990b00d0342c0d585a4119540003500d98442d0b59001c3c2c01003c0c40c40d81c030450748152000d80710400450800082c007001c00260781e001c960b216800300700040000d0100c0007904007815aa603041e001d0020940b51030000341042c50710400e01032820030070002d0541300e1513405d04070207a09200c1c00c01c503403032100d1802c00341e102082020701c101c1c03034520803590140c4269041c0c03031038401b6407007100107440d0307810100103415411540e0007450840102541400011030a104035002406180000c6181a41d0130504242881180202c00240b020100701d08070f03500e00030070448803540140302d21208818007041002d441074000c3c2a080c1c1d407289e50703010145484000504624241d8410440303090344540f0980d402ca501e50b4071150500d070007641c0369400080644509 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 941480656 1250 941479406 941479423
    0x170d0203090f0c0f010c0209040f0501020c03030f071b081b0f0708011a101b12031e11030c0d0906050c03041406010f05130b120f01060f0317030711 65
    0x200030b8031580031281400ea240c040310644491141540c1d00303884040340e811400d4500040d038181c0e0410740540e550b04000d503a1160030380d0040c200794000108511801c0001c40154402d90071170f2326040c0240c45401086030007407504017a04040c581c00d204c01202050604002e00711141d071040032017030003400d40d0b6100c078148403004900192540c0040e0045c04113540a0241d02c64110041610200c68411030700010304a080da103085005002c0404148686500052507800c19642c01243e161508009510002d000700035810909c2c0a040800a100ca400c0a86000360390128a12130a140e0858841d480c4120559101c3d10b84540d08540d10500d14001800a015a5200e0828111019200d10b800e090200a01107a40070707034410b42d008100180042840000d0700c4080c2c07030702500d95816240c0216000e000928080781c00640c4031442d401a445e00c0c1c040029800b8406800b5802401440d44d241204200c181e5140801030030351010490820003921144040c581c010034074504441025400b160460400540 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 941481906 1250 941480656 941480671
    0x106120912030f0f091e0305130e06010813030e0907020f150a180c2105010e0706030608010608102a080a0b10020606090a0b2d0a05030307170d0203 65
    0x3582180c00b6490364600c0384242d100d2900d40c01740200d55050341c074405205d1002c0400e07003440a00d0f8282c201454801c1050701d100130000c00340300302d50310380f01d054075220307100c040b1041c900241c0781100090680c034103280c0c2c0c0070501d07030303d900c441c200c040c0746070b041090b04500242010214400c1c3c12054201d210108001800340c01a4420640c203800e00100c41d03019260010004169003801440340380001e400d4138100012540e0a940d8130f0526000c01802d83e0103110038500250940d803c103041c034508000302046c0d08080300c50645007002125526204035003070356058491144240c212203840c000802040d000400080c524013148ac5103039040c110f00080c5600e5000c40000003070140020000e03030040c0d6200f5480ca11004450001d5145840503000b0f688410041c0594020391109000c500551815003014206a40080000000c5000300e0340030303850121286a2440035640741c0200c101e10307080a000c1c8206849014000d9843c04c0700e5a2103200c1054800161039034080300c00c002a907130642140c40518000d203070 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 941483156 1250 941481906 941481911
    0xf150604060909110406050708070602040b030f0f1f0302010e040e0303091e0102030606090d05070308030c0a030b040608030316021903031e0501050603011802070803070e120a030503010612091203 86
    0x4100f00107007200c10a031402d1140c1c003001c100c28881250040c041c0c074410f82c0c0c000c2182d82d986e00c851030302502901980d0300100c1d2003030340030081c0040b03050a921058828000040c2241c0303e6600c00240c250307030740b80d007107000460111600c50500c00b5500c50700c894200320102601c08200c04a40300a618610f5004480852080d084000c0700d800900c01040ca090751004040d000754150f06000b40000e4070713445080440d078070aa00b49a13025041003000c0c09103200460304250510b407a464031034003091580e0302030701008c4000b0385820114911861b1074400e1000f83c801010045081d03986a69800b00b450064095403815446503409208043c0080c111310442c0b01d11a0f40c0100348840030300c00c2100c90801c0541f414115600f800010f01071500c40302c003130307a0449030001c0031480400401400c000c000e04c900d034005405164000100040941c00541c1305440010640302451110861210340da150300c030303070364005001410400040000038400e118100f0141d0003441c000079481c0583c0d40c2c61071055403103000c0501081c2c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 941484406 1250 941483156 941483159
    0x15170f13061d07060908030a02030421050a03030b0a080105010b190917150109021e131a0316050301030305070f030e060a0f031a130906060e04060203090d03140f1506040609 76
    0x44d4400002402400070708003e504055039210081d484e0301441c000c103001c054102d80e0f0003301e10301b01c4504140d51900f20050700c82c2000350f810010090042c100d48030b402222800300c00500400c0c14420581258148600c0e1418422071034022a000d41107401c590040201a4001044600c080c0b410107990b41710b070400800d603e02842859500c11741050740449407151041c408002980c40004110b00107080c1c031403410756988114002807400c0c00890f0454481110004010f0005402d108000c40c02406100b030482e5002411480032250380c8824000200090002c0c00f1805c0040da0903030281c8103240c440c0c1800b6440c020b270f0901240c0c803600f00b01a0a070020301700c0d400e180780b299007511480ba1a0100015101c240d0b2401c007002c20480b03007420613686105a070782e5200e86c0c1840303000d500460140100490b424164100741c14204041d400a89004d03041d80079110352101d4042c0a8401d4220f07185184c2034800003541c410020040b20301000b4181100c403c10b103100c5040940d40c6000801c05000542c5130180c005 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 941485656 1250 941484406 941484419
    0x9060302100c030e010c080c03041e09061214010209060a0302071101021c0809030909100e0907031703040312020f0c010506240c0309040615170f13061d07 68
    0x4461410003000340502e000110700840d6008404401c400c400b0308041d603000c941c078600203189104100003a1510f00006c00c020515a10300c1080b84c12003610440e112202d1a12142900c4c03c4808038461220141c005140000014031442d200142d0a0404030005040c0802c0c0c1010030915440140040e000035800a440000c00804101ca00100b01080c4010080260010414a50160712448034814050807000003007004004004848213080c004c2e00c400e0f000d082810102c00d00484901841e030001c0c4048000036010640002c2d240112500b00f000140c003101c94074039045003580080c0080c2c04002500803094282503441c0018220f60040101180da90700180c1055400c4a20103400280b00322610f9080e00d0000501e80c2d50703620403401c50780140c0d0b550f030344240d91589140301c0c04a00640042c10402d0000740e2036004100d2440c1010b5503290300603601d034410000e036007001c021114030b2001c141c4440810310303608107000031f03160492003004002100050142100b4145000380086081c0350b0246034144100c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 941486906 1250 941485656 941485669
    0x106091e09020609150702031c08220f030c0209040b06041104350d020307060b010c03091a09060705010203220f030810050907110f03090303030f06040b090109060302 73
    0x1100e040303901000001031541c00103285209807004144940c180f46600e000048100003100d1619070b009007240c00040306064070001003080b001c01d090110302848005030740040944a0100c90b10f200756050341c48811103594240440600f00404c3d810041800c4203600142c444803005c030701aa00911141d00e81d0f240080410003501c952901c4145900d03424001081358081da882d821095a0f50b43e401103048490301104e104040750441d1107025a48a808504c59511750084010b00f5a107004081c240318030000c41005480891980e440240002c182c540104180c99401031038103030740e0182aa0305454079000c50006803054100300c0068802d65400400d00013074402c410340d90303484400c1c110400e4007913550a0701c421004d0000301c40d015040c02200b20000d10303c046618030f01005032a0061101c802400c09141c002c001181086a1003418403420402c3c0d103507000000f090720308622000307004501c2c0d643c500c0c000b40d408030703006800780340c2140d01c449a0b9a0165522031301e4074003a01d600c0304001007684c43d50040214 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 941488156 1250 941486906 941486951
    0x5011418010b010e0f03011e0207020a06030e060435040f060201060f121e03080f0c09030a060b0406080102120f070509060a08060f04020a0e09010b03071b1103010609 73
    0x6a9038500b028508a80c0d8100002c40c2081d001202c11403480301031803003c02c0c0501540d00040c0511240c00500b500014000c0c0d020702075241c004d03549420050340744c0c03106500700c1d58810041e0401e42d201400160014118480c00d004221400070442c403c940403500340c0c0d000d800c1c00500c0c801c0d102004a402c0c40a0010507500e00000d104a1000b480324515024880d001d03400c41d8000c04224002078102e04d0280014119100e45a000701340e11039a0316603c50600030308540301510f058410041e40c10114070352030504010780c0c1d03080d40c00501906505a05640700c900410440c0003a07504551500000203080c8401e101400e8441d585482d0406245490340a840c0c40c050018040780030b015061152401d96103420b030680e4066825070600140c20340350500050f0a40351000300c50b80e80a40000742d80f142044c0e2080c1c5040940f241924071944030303629820b00318406d020444000001428444031401e1403502c02d99200c4116024503010f41c200c490800200c4d0945485802481c43c00e5205d145400c90f401a9400d203d4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 941489406 1250 941488156 941488201
    0x8070314011404030c030e0603070309060513032a0c0902070b1f03030e130e1b061602040c050708190813020a0608071404082118010516050114 63
    0x8142811002c001901d0003d0000b50030480c010341d00c682014080c4003c041442c2008151646a10f05188010060a9103a17000c40b203d6017000d020480d11925103040c0140f156054031040360014400016a400c00d180415410f105108209103c01040c00700348488050401e40e40301580d0f9647e142410300008c00c000d80113040051016941401040d038002d070990035030381e1625201491802440020307015143c41c108031344c000b070715000d55090300d07003030010700400c0c440c0d00c00403c521012900e0040084601031161201803070ae40c4012014010b1a2a030710110381c09030036040040c100601c5442c0c600c22600120408141e1045080070740c1001a00100401e40c004520054401d8040407030f03002c180101ca8912075001813010000c04502d03428000e0078000000003a0b00301d99034880c9c6d074171858265110b00d90400c00b41c0e1000115580d0040702940012900c007901148a24440f406a10004498603444102010b180301e84400d082d1000580a02a841e0000c1c50440003981350b081c0745850380000304029003000c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 941490656 1250 941489406 941489411
    0x15060f03091606021207150e1b06040b0d020c0a1406100b032413020c0a1b08120c1501120b0105310e010207150609020708030609040f05070807031401 66
    0x1042030755030004180344101c08240010b601c900c1ea40c03034000103c0070880d86481f601c1d800c1601c01428403d00040c0c4034810840342281c0e14020f9281814056144903d00505074031b824208041105028190010300080c802c0c00300704c590303075a0303280c807540380c503003152080e1400c280c20600511181d0021041301c140501000d900103480c60074940c0801412181010380210f111101003040c03585982c1d80700c2c5902c3c1076120528299983c40424044a81b134480003c8225200e82820500300c0b82850440b05500940e904603004140c0c11607850740050719038100110146aa00c40d103148060b00c07280d0031000c2402440d0100881c1c034881c4661500101c4400705030492805007045601079028000380c81007a1300000e24540714103000c2c8958030007400c003034680c0362001030303148d80002691410840c3c0c0600c6054030200154003040041e444050203170981c81621406000c200003440440c4d050310340400247d801c90300c606208000311210b81d50701420900c0325804003025400482c002c04c10f111000b011000b080403154000c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 941491906 1250 941490656 941490659
    0xc0c010516121e02150903030108030f0c01090602040e010501020c040b0901061b0503070c0f12020102030f16050f0705040f0203131106120108010501060311030702070b0315060f030916 81
    0x1e014080c1c07210380081e20301100315a05807011402501c03000240050710b08039100090507014060b40e10000302101c10160740140000a0a514000c4203030b034142e50f10380c0f010f9843d0045040100c80c0540085403100911355071030242c2400540a84001c100504000003082040c0d07141100180c144001500380f81d01943c1426282001541c40c080a58196155410b180642d07104022018481045800c002400c4d4071001a00d5410b0200000d104001c07180204114691161109901d05070707903501101c001d016900c00d101401f45100c04a006d482c8440202c0f20914080030325490f00c600d060f030030029401484d084140e06210a041c18080c8407006e00203e4029031031400c2c0710401c1e045a403e20800500041c000e58030546c0c6a81da2a03048404a010700c2c244030386c855840b031120074001c040a01c1030001091030070b1305200142c400d000c280e80c4030710b25503005041c086103480301420542d0300092602400721002034402c4c1d01d42d618100a021410303010052503860345000035480e807400d00514400c85501011060 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 941493156 1250 941491906 941491927
    0x12030c051b330604050a2d0501080706020616030e030a030b030601141f020c060d0e0d0915030b030c130f241a2503031113051e060f0c0c0105 62
    0x202c64006909840014140e5a501d84042c021b100b0503403004206003020f6070780030b01d054552018500400d17003440c040043e80d91f80c000d2140d030b504640c4036040168000d83c3c00582d200c4842e1118400c0003041d805c02003216040c03440c1190441d40003480c0e41020030303950031220b03285042c01c001440c09001d400002109c15035100780000c1030b0010907241061161031542000c0c20b024400e10001c950140080c2c0003540320180c41814401401c150940c24120313208050004480e0b0f413245035400c0468100000d145041c580c0194101c015002c50000340f0f07054826061035041d26183c0d450143c3d4040c4402800041a0b602004048103880140c0e25070200d40c45800107174074081c00c003620107604846c0040202e940c00b030783c0301c4116a02802040c100d0040b00c28008000c0489000c1202002c0d1124402c0d90b081141d40c0d5484603000c1c6501170500c61481540d4440701c14404d900748259219104680c20220100d2440e80400007805680402010200c030313680400c098000140808c14403ca0070401d0070039038180001d011 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 941494406 1250 941493156 941493253
    0x150307050a0308190201290a05090f16030203061804030c050709062c0c07060902040908071b03050d1202120907051903030c0204020f0c07150f08010312030c051b 71
    0x110b0b00568001542e416404c26034910b8000c034012700015000b8092854400320390300070074004a80ba40f40ca51010340030801003521070b1084034410a0004c0c200045051000c001d00c0c0f8106005000302d06012040c80c0f11408140304004101c002c1a021402003070b00d40c20540f04d000d03410306003411190942d101070840b0741e030000454038055002240341c1085440341d6541c202000038080500c0c019410a1404081406004d440001400c09a020764405120b9035444214405203c04511018000b0b400603082c5903000e41c0305100388443c0d4000c84c8005030410464007030700e030003207103007540c2260407503004101c10022810030316201a101074a000034407031a0b0b450741e00c001d09005440c400007803090f6400511000f41d50380840c15200c2c509440070880c4e01240c0c4640c2c02603010a2200240700c00304400d0030081840d10311810441d0705a96020002c3d00c000c141d5288150080c0854803d00c500f0700c0000c0c800480d004201d400c00b85c0e541c1155200900940d04c00001840c041d5140301c0d080e81c180c0d9040740840d0300c03007030b00304 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 941495656 1250 941494406 941494451
    0x1e010b1c060b030304031202150c03090d030e0a052a0a0806010909081204030207030224091002011b050a230a120f060f08010f060e150307050a0308190201 68
    0x102020031402e14000020b4254405d640005000d41c8065403900b9003154000740d18580b490362804605aa600d80314004074683c0811202e0780b80580c031040203002c065109402035140e0100404c1201c2000c407496807281c0c1008005004003250001d840b0000e400c0131040da40e403400b461000c0d140f48110303d0400103200e07124501402800046911a01800c0401c1010303403c9445a0040d40e0101c1c240341006d140c000d441302001c0c402a03100d1041c500d8000840c0780d07040c0308180b080704e4480745549040030100a0100d030841521250301555600c00c100d0488011404502c0c111200c156500e607941d1480036005009884217004801a241c0d440842501304c100d00c9049a504500c681480a5945000201600900b07400c40d4131181a905010700001d400c0044010791007520403400c0288217200c0c2d11103e60b03003141c96510940d4580205100405c596110b82e00d01030440380c00140aa03881c25486101081c40700c5441c0c3d000300c49a510000d04c49415102c160790030b0040c40014802400b1210380c16070440b000b03200d203 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 941496906 1250 941495656 941495663
    0xc120307030c0201020a020d0303150501090b07060b120f07061101050f07110124030303061d010b0f070209040b06181015090e2a1c020a0c051e010b1c 66
    0x59280e0807043d6030003000035888450b40142000f00c1e001c1286001400341642d00b0070038091180c0c82d01c4c04116036000c0c0c030388142541c40242e102c0d030a02117142c4a2201401501c0c80294100c0e62058164440340424010030b40c03040030300c000030080c1a2a0800081400d03c4601d000c00d5642d1515040c0101c0042d40803c194100c4d00e5071134001d6103105140d1070180107111110201022160101c800c2d00801c8142c540f0100300e07802910208880c42d075461000e408084032080304107060025400500250414034042c2070b40144a5070100d003444456400701c0c91110080e6010740704140304c8800c0220a01d421880b805425454600e00041402c18011701002c07103000f801030202060001106000091207654480c4c01011281d00e1707001541824070b4104964110310340322041041d03c000e0040b40709840d0008886809030307000f111030205140c14a00760001e400015002c0104102d0a04980220b03208028440c62000400410a51404114034007401c503041602e040740110071550381080341200f0764082c004610340 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 941498156 1250 941496906 941496917
    0x60302070b0a05061306030c2d050910030b0112140f070e070c05010513020a0e090c100302090306040c050a0f14040203100f0b07030e040b10030c120f020c0c12030703 73
    0x1684c50020317416804a51008000901c1c00c50000141700e801046101150740d040c1800300046d41d41d0210041505000301d0110030007000200c01c2000b030178084c00342070340600c078014480d41319501d0f543c2d2030880c8074080e400341a00e05049510781050007504d0801e004a000d0301d03001410800b060b00000c03503c500d0240314507603140e1061000640200e0007901c3c08403006500c80000c01c1945020b510944058040c404240e01400750020040340d680580c500c19070107140490010400c4200c11030401000000c141c400004058080c8018201520b080146e24004c603c41c074123071107140c0d0130078052150703240392540b0415405401d02c2080010306160402c844540c0010303500075a603a0b49140d5412621101c80c0d01a491205403041f0024070001c40d000070f8680d40e4401d694894281a14000708010303201ca9280050303009082000000c1610b020340c0c000c6241070040d081100c10300c404001802c0460315800e1101d40d1a83e000030b01d80d9080c003402e01c101c0d0200c03c030031545c03460450310030a900f07a664051110300a06004 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 941499406 1250 941498156 941498161
    0x5010e010531021c020315030105061c0206072102010b0a1202010c050f1509060f04022d1f11031204020907030f05160219031409010c0203070e10060302070b0a05 71
    0xb240d40e01290b681003030184900d00a404841e03c10300095008a0701c546985443c0444607a017440c043c000d0f540540c030700501100d4603c03015440d428401105140c00ca03440b1004200310000220f0046d251551294882400300e1381d409a2500603094441c0e4011452244070546424000b103040c0c12030070071007183c085c41c0c0002103420078a40140303000d108000312440b030711800c1c403c5500341c008820001d110312415000e46002d51110542111160b80c00d5400941c0310301341e0780c041010440d040c0100000819094500c0c04114000e60210b8001107131000c00300f04060707150080c01c8801c2d401112081442c0c1e401f6005501d00b058540b0364000314800548024428401000420101071280d0070038114640c903603404100c541060914502c0200d042c040c41c0c00035010b019038505049410714080480d098054a0b0900180c1d521103480072594000c08900741488a8841c0b40742c05030310100441006000800014880b504003818980800845a84140c0801d4010000440040c40305041c03250400c00007540412141c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 941500656 1250 941499406 941499499
    0x20d050a0c0b16110d0c020d02040b1012110405030706030b13020d020d0b1c080a1403040b04050c090907030305090406230109060302070c030f08160605010e0105 71
    0x1c80ca812400780071400c100c0d0902142030b080c070052500707944154544a50550304090040d4a07803101d01d404102140c8001c6410700035060045041301d0840c4002c1c000151031140000040c03074009994588000900075048000401c6258858440e05000e0b2041d00c9003414a4400003035075807007150041c082096152aa02c180a0f21341d049128001004640700350b4603080e004010344000d400c035141283c20f0909148511006042c8080d6602ca48000070008800c016020388030100c0680c45003245008000180d00c900b40300f2100140590301031440384000f0302031801d090070407034a86664481000d100300b104209010545000140c01c40c201ca9250400704c0c1c8440880000800811056110348140d04e40a09100080320b00000d03079481c4203030240c0343c285011380c40d00e030300f242203004d0148010f203204d541000500c0411410070652801a110b5851180b82c1691012403541d02402e03a8011210380c8d0b10341005000e181350012001d030241400341e4615914140508002c0b00800313440510b080b0516214070081c0c40b8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 941501906 1250 941500656 941500667
    0x1b090c0705010207080409020705120c0c0915040c020c1e030303010626161404120221030a0c03170714032a0c061333090b2203020d050a 60
    0x5820111142c6c40d17555942405003c1e500650f0308958a006403441140400d62450941d46400009801401440c2c0c0c0002445a8044003038484140c2e111141c4004200d56a14006d40c0e48265242d400303405d0003010f21040c050644030180c618a2102000b80854031a40c0b8000281d03070440b440d13854039540d42c030040003d6001e07203480000007c82d411150002c000b240619a9000c0300c9a52060b6a683c2e0007142a030107803d001e020305d000c0c4588206c403400700040540307044000e80c15845210084020451000b58985d40b1b541d00000c8102e0204080d000c1003010306422030141c1d14403846825090784d552038942d900600355a050110040520008004500030b4507100c1000d6200741c1861040010391886075465031a03581001c02d09508074031881000402c264110302d081044076a006401001030342050b80300c070740100b07402d140300024004000c4005c504059540100e20100713002d40b501e0807a50910542119606a1580c514900f003010780c8078030300c0080e50000340d13200d2060003854081e803144418413040300c6 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 941503156 1250 941501906 941501917
    0xc25080d090804081b0a0909020f061b060c190327081c0e070b16060f2021061804080a030501061803060c0306120b0103051b090c07050102 61
    0xc00910388000c803820401500300034001e03a0400e008840a4100710499408580c514618054001c1441d92040001d0026500104500c5100400e2400040114004642c947e0419860904400c1c201d28900380020300a008140d00001c41106242c5003640c258080032000d1040001102015500e101101640503e9901000c140d50201003200b030070001c6060480c00c0b40c10900140105400c001141d60051545100e041050420140075109075482c104101405400036194254005440407460300020b9191161140000c1c484500041c18034001c441001244500d1045403007483c0b003005002c0b9101040c01039946071520300401000702c0d6840801203803803005030500c0c125903800d0031000e10003044000c50140c040c8a5580c0c0d000c105507a038807032044960505048132454203100711401880828074603004004141505c0c03c003c03e203683d8442105458055000c010b036000340185d030040c0704210f014080240754196010004c1503804242c3c00140c61200f000d400440011400200b100c00c2110a4043d00c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 941504406 1250 941503156 941503177
    0x100c0b04141029030a12030b090112030e01080106080a05060a05040c0534120915020c01030605040605150c121308150f01050402070201031b030c03050c2508 69
    0x3141d089880764000040d080030b116810302001c0e14901114500f1012000d8a41a0340090003401318550507150000c148802c0c0050100305a1140000a00d54681062039402000c007810141c05492300e50800600c2c80d83d001d20303114104034002d401045030f158088642c5030000c040ca50006000d80b982130004681f0700c19688150b41042c00d03c0724041e8115045009060044260400765041145d00c400c469402d0210f401c000700b0903448119008082214161110807030041400e0290310716842c0c00407100d0042040d1404030041c1e100c940300710519645800b58500034102521b0030700c555410200052902210080d80e41861140401c288600d41c0c0e00f004400d402c0c09020f1502d079564540410205040100c60240004901c54031008000f91080c003180284100001038115505908002c20007001e90701c20700f02a0704150b15004071540c0e41c100c0001c0d04400b040300d1303240003071178904d5880081c0030307298010003041c1880010b000c401321602441c03002802100788191401d010305c82ca40b82000c07241c0548003290 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 941505656 1250 941504406 941504413
    0xb09090d03153615030c08010615050c07030c090905011a031209040b040f020324010804020f03150a020c07050402070f0803130b0c071a04021014041d15100c0b0414 72
    0x88007104c00b41154541580c0c0070305400b00215843c0c030180d80c00e841aa124102d08818410008400c1521500140032498152001d40d0f0b0b041e580c90715070b05014183da802440f0880d60b2100301104001d001d108034915429101c880d18012501023001a0f244d044441030000b41d15000245032a00d0346d615402283e00f0303e00200104200020105064000e4108a0303511002100c1d004502020303d940c18200e85031460144e4508030503588070380c20f0004112001c442036426106010035200e03c906124a12442806c0780b0b8001a2030b50052940d0625040660340064000d9204100c0100420014200c0c810300304d0300001c00542c3c94851000700301205240030809031142d020b24050041e0100c0680082200030f0194040300c002440c40d20031070307080708c0d03056500a50101e00d1101c5001594020340a803503e041c4001010ba0074260b9540000690400d0250007149030903002c020018003400b0241a11034039841a203403014100d2801c0c174003074120285841c3c003a2900c00a03900050400c52500031100103111500145d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 941506906 1250 941505656 941505671
    0xa06021819030605090a0804090f11030a14010b0909041e0206120a05060a0506030a05060613060206040506011223070512030a0e060a0e0d05010b09090d031536 70
    0x446003040842c00704441035801c01000c1141d01d840007407030044081e04540c0701e500e02480c0000b040024066411a038841030380300e98610840c101c050000d540b1800e40c02c1d0000c00d2a88001801d80203502c1e0580019070f4081c418032407203207282c03a84400140d05c2a880707510100300c41006062016805d000c0440250b004400151007100500070801e05401b4406001c8107008544440b400c01c400c0c08102c0c010541c1001062000070300000850b008241c03c50700160001d480c3c09140c03007024407203003000c0d000a0050303031240c010b001c208002003098074014030300c42001e007100c42c20580d902106c41201140b40344810196080c604403481e014040000100802000003243c403034020041500c0c2e4004485200c041811426003580508045044626858141d5101c80142c29950b04001d402e001c040c909503030542d600d802e440d04603194444c502d400340380400000c12480511100c010190303810340303400c20380c2c0c0c4080310401c00284440704180e0140324811800400c0f00135000e81300c2140d040c055050a0b50765400c0444 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 941508156 1250 941506906 941506939
    0x2a0d03050414060a0f030b04061a120a0c0c38070e0a0b040510091a0912010207020f0d02060706062306030907120503040e010602010f180201020a060218 67
    0x60044555560540d80c80314807000801c00d2600803008844007060580f00c858070103900c80d034485921603100903c005074039501c074032b034415070040c040e4151400340d1400a04140c0f0940c50440303040d880103050000744000cd41c240401850321801c8440140000c40c1000d540c1400d172441001402e906401f802041580444009031408404090750700c03502065140c081c103101410078558810a54094124040c80d0500d0507051080395411a01c081040002c00d400101302002145280d0f07203040c82d032030b0741261039802c0b0b4007c00024000011079140b85a10400105006868100303003401160001c481c240345246403400401d041c0d10074580d0041c8810300c0c000001c1030000800001c000f6102c05410301030310001d600c8040c4096403000348c1c0c44004a9202c8001040a0701c5082020107000d441a03007501d08241d590005040d080c6001c0c2c0050700980d448884802e8404828401e807a407042c401d104c40266410160000303500d40300000005044243c00291125a20480060041d1020340180107021850019403 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 941509406 1250 941508156 941508167
    0x324090721020f06210c0705030f070201090f1a16060e071e230d2411180111160806040605070203031b070303140408030a06080f2a0d03 60
    0x20120712440b50000e00e01a1401c1107026280f840d03040c01e41c807544520840845c5c40d0494801040d658128001300201c4000079824009400a0903161248640350085840003601c2c01046400602d41040c01c81d10400906c1d204145110344007902c440303503540d1286030b4500366242e6081200081e00312410f2801c441d07828640000c02c00115141c1810117a440441040c0b4401d481469100b8007005d03100e8a054960300b1070300a045d000a02c03800400700d8046044a50701d2074082400003440c128070024035015104001024000c000882182c41502e038505441c1c20800300741d80e40341940040c1041030b102001d4890420400c403606c04407440c001d5003040c00796500c460f6555078904807400c4a400707081c0340200ba0380c1c0c1c0c00041503900610505034502240e0184046c00300301a04020b10130f90805858032040100201d042d00664002c0740240740309580d92030700041040540e48581d100480c80d6105401c542007041021680b45000c090008129070094480041c615151a500300b085901c520f440e07029004040c0c104 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 941510656 1250 941509406 941509469
    0x806091f09083c03070f08130501060b0a080a0b130902040b0301060b0c0c0306010e010b0307020109080a050414150f0c1e0102070201021903050313140d030606030b03240907 76
    0x881c94095150310283c1e1110076000548440c40440d0310204100042c82c016071060ba8044040d4031040701ca100643c4803d801e440e850352110b1800500010003001151b80034242d81c2e030104541409100c01d0310b401012640c8003a420100005540d510f00c0302504654a9400c03003440d00000070001e01070386444042030501c80d0311180310450148603140300c0a2981c10701144a50481d00800001010f80e8a403128100c19a030004103060215540d5050000000703241c04050024000e1656504d40c44a04180d00080031640b90801e851040002450002880030b61b1700403034102c035000c044816112040109851718188061040210b4000c1e00e84035282c0111055004e490918002d030b00311b4040a607469240307102e00001c2007018000440c1040021100405e501003880c1d9203118020134401d20001c030080c20306000c015030b144800a610380380104070440e0305009042c0300070011400b4050300d5031400c050b000c1c0c0b04006400c0440300111000020b40c1c100c1d042c0400402003400281c0100c80c509014461840c1c0b4090 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 941511906 1250 941510656 941510737
    0x112140601180e010b030c0c01060e01030b0105030a111e030111130f03211116260601210b18060a021903151e0806091f0908 55
    0xb0a1800c06400c030806407040101c0c0c2083c020300c405a400d101885260707920040203884c21141c00c01c26041d200f1800d00c1004010f017075804410040d9415454150410364060b40054030a0303000c0c290740c1010840500d04503550000072902c1903558021000c034184600c3c103000e00daa03419481c01d0132401102008500601050360344490140a454480e10450a2039030f46001c0501041c012802c000b00c035403c030149440490f0381b9401c00e10300901c05c08604a184c041e0410044c83c0315081000c1c2049035038410015440202000d20759015100504d10b0103994074881440741641761000381150100307d071108103250320040d410010745421717460410f81e40e071500e41c00c4560a00c9a44034800004010140034800d541001e481041c90a00c4e1180f8010304401515415089440f01400c0d400005161080288100d03100718804078045449c51910f011642044401070442d0b40035000042c010f88079880c0325915091040002d400001c0c004102c0c1030801d101e024140d00042214880403c80ba0020400e01045001014 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 941513156 1250 941511906 941511917
    0x7080709050901051303050d0f0b1f030f0e0c09180f0a120f0f0503061206090109020301150302031c0212130e090c0105041205120a2609060a0b0112140601 68
    0x440c81042017081d21007143c090001201800f100c00540007a80003010060102030010602d0700e91113001075000c10090903070200c034904005c5038583c010303010300550700c4d41d05041c50200182c0c80c02c07984a035140d16030119054404d14035000058400443d8020b0740d1411090802102d5481c0c0e480140b003075441120000c00c0d2406101206c00e00111481441c004008128680d59410b08031000310082e10707070342c201400e00c5070300c8445a140407480034020898148600310b4000040f400d010140185403c50f80b04210308081c8001c41c210510268800040c00340e141c2051011071400310b04140c9080b420700b1118106016420760000d11742002e10503045e002d000780c0e030000e42a1001c50f290203c0b07540e178038100510900d012400074401000612844650380115500440c1503403e0074001d41090318040e4803001410000c00c2c0ca015510015040808480c00344030304003a00790640341003400700750b036581c00d004240444441d12003d2855080e481401d11850403200c2a01c18401000c0c4041e40c402c1490027100e09030300066 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 941514406 1250 941513156 941513161
    0x31905100905340905070e120607170f0105060306120615010915020a02120304050d06090c170a0b060d1b06140703050403080a0201061802040602060a0203090d0c03020708070905090105 81
    0x8244601d403102c140956010810900c0c50b004824001d4040188200180600f07ea03d0020701e03103a80200301a03c05024020b0070113031401c01005001d1102e50240d002d03440e800c000402034840d100c41a45810f41e0401c6803400d840743d0310800001c000801d444905a414066803040c402000b00490042c103127640c0903220550244d44030150700e80010f4004210b4401039101c4400c200141c02d1142000c02c5590820041d41e1500d610b60300440d005241d107510488010307588207584004c0c8100c605206024000324034110360f0201d0104000c5954003500c0c3d102800030a101800f02c2c04582c1c4242c0d41c88280d5900505503414245c5030008481da2004070710070240480c0c0451580c4c1500c542000480da0902e47c1512110306050940c3c41d901c141d03400041c003071425903603112808a0a60442501d02e0380c540a07902001d40e60b80d0801030000d0400101610740b07000140148103010364a03501044218000380c080c940b9401c18040c9040491404280398070001c1d07240250400440d042034140c00c114402e00d4590024045074 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 941515656 1250 941514406 941514463
    0x30901020d05161520030610021f020d141509090c030a0b0c0909010807140a0b1605100203180118050303190b190602150402031905100905 61
    0x1d108000d810502208401580030000d040d1040c0703209541c1e0501d00002c1d01700d880c01035862030800c0c002804100000c001c000c10409140100071443c1d041c2d610300c09007034550f822180503d01c10020700055a44240c020030111451000c550005244d0a41c2d04501940c40c10805d40070200101d03094060b40c007441111000031803c0c880003807a071f104040003038003c02c965595920b6480c00c035200500900001e100421000d0690741ea013401c0540a8070303840000d0005985000d1048541c480d68003030080c040d400d1304038104024900c60094400c0349070b00020150316120a464020300340400b00100c0d6604600c00301c14000b045100d0710300042c940c260b240007008443c404500c900004030140ca0700500c50f600070400110b940000801d00740c00c0c01445100811100d00c1c0100240b50324031010141c180141c40011f00300002641008440e49440b0110b948400508080d00030a841d1100011011411803001e4230f03d2007084400c2101c125110240101041141000d280c410b440d280c0d034482c005240e0501c10141d0b0b400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 941516906 1250 941515656 941515667
    0x21c0c080a0e03031b040801062606010609090e012c0c01030612080c120a1e0e030d030e07120b010302041b020a0303050612100b19060207030221030408030901020d 72
    0x18100b0320045040d6959141100080a03411510100110040c000090030030003d0150a0281000824100e4206036907540c109c078a140c80701b5000c100b588084c00402c0b049820003040c0381540c4072042c02052a011780010303540544001d0002c105032103581250004004296254001032030300e004280ca070001100401101500d5082c0195540c488040310058001584000200080340c40c0d0410f480a0340145a0f0a080c03640000c0301040119001803540c001e0055400c0a00c0650005409c00c02240d80c2d180000c61b03a14442c1003c0002070641d222404440320100300f2454008290b001c100005070369040c035200910701020701c4100e0145007400d0f5854081b403601c61001403811380650080000e0442034034110040c0c44050030303017500b00d40343d58911401c1d42820310240c0c240c0701002c8404a108020b61041c0240d11005140440750046204414070502d0b82c0420850101ea07011140b0302c0980c8207441c404090b940400d000e10b6204c1c480028002000b035000700140ca1200026000d603008c010700310300d0586a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 941518156 1250 941516906 941516921
    0x70f090b070b0a0b0a0f080a0b0708090a1502040f080a06050105030a0f1e06050708150102030f0f0c070f0312080106080105100813021003061410050906030703021c0c080a 75
    0x11040c0745500150f002c662031307401045040c800070080c0d0416507403000441c81c0c08426030807550075038104108001c11301804102c040c1d0004000e150a58807442d200100c01c1d225909028020101c4a1031043c13040311141e02d4050342e001c4d00d54001b115581c03035600e00403540d849074030782c030120b5009050100015903454081007061989812461005032582a580c0700310b0600e42407007461501c1c140d10440345001c6000c5216081c80355020752264451030406c540020f144807501c1b0707000c50440d0720400c8072001446020040e03c52440e0342c0644c95807501ca5601d50241403140c29041843c008810742400002c0c0301c0b03a03507055928912251510b24461b42c0310001218188400d014030343e008030f01c47c905013142900c5000d000e90700000c0c590111411645c50350001d005124612060070010743c03624002d100505520b222450010801c881d1b0114403080300320090030901950041e28810b03400800040c00242c040e804507644440c645c034400c034544550010b0f4400400043e6449400220901c00040700407c1e40c1c401c900 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 941519406 1250 941518156 941518163
    0x2100507020d05071707110301050906071d0d0206030a09140a030e01270e0613050f06010c0f05060c030109050123101116141905010e18070f090b07 65
    0x850002e001000e43d074076880207900300e61101c85560510180084400909040b51041055100504c07a950405d8252000503201c50320701e4100d0740c284110181c20070141004412184940e25099486900049c420181101d003c1d4210350b0003c104010012154003e0346003500c00c103050609038160104a035950308009000501054511084512660007402d80c6492104131200c900070703110322080c1000c0c51800990007c40041d44d0b0300d09001180c50608801540c18581c81010481031400d07455804c44090041d10b441d050004840300c1c1c8003071001c0e903804c103150107800400f00c0ba414100030304074048943c42446107100b00c514200c004a0204005460100d521800f24403030100e0b425550100003c80c1d5010400c5010700507220003841e01c6030420720801842c08014051030003c64074180c445d40103c3d400d8910148107175103e010111210b0401c55080040c0c1e4402c1c600001d000441401144e05505804140e0110141140400110f668040d01070498040e680d41e0310030b4060b80c0e8120340d00d1280a4800b00a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 941520656 1250 941519406 941519413
    0xb1e0106050708130b0c070306051b030a02070f020d0c030611072307052d0105040807060302030702100216050c0901080c0405060d0605072a020a1707081204060210050702 75
    0x1c80220b2008405004c2100c10a0202d809485d550313045040954400d10b20080c032504084010001d1020307c0c03103280d511440c10346601100d461100680a0948401400c2c014040e83c0410000140b0140c10034401005501810454005119040c07010070358006200403100e2a08100d0350742200031001c1c040d20780b030541c03000441103035200809600c044031940c55484a054807480000052075503070000110315801c0e450050f400340210000360700454100300182c1505000f01000100300c40c0c0d40c0000c42c02c0031102c0d17034a00140c80b5101c01c5400c0b410459501d40003244103001280030380c500900c0c00c0100e40400e1042e0110780205000c0003d0041c124000d07c00d007600d540204528024070304082e0000c40c4d120034010412540610940e81d283c0480c0c5040d120640020b21181e40c48206600303100100d1210440301d80b402407070110716400605454268040d41d074013480e10001c07202c2d030a081013107180e01418440055803200d614240443c006900039201b0900144500005420060007510031240149a950b019 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 941521906 1250 941520656 941520667
    0x160b09012304050c0306070f111219120f0b040506011707180f08070f080a08030406110c06010b0a170402100e01020709140106090e280f090b1e010605 66
    0x2042210a00078003c0d20240105204ca840c2e0340d40c03d0003643e200700d81e5a00c60b1801090755610084c22040c8400310b01540c0d5002c00180f00303e441810041e0740c0c4500c245150564241344101040f40d031003807901d51500c45c06d81441c42c110b8906030150814800c80f80c00343c0c2c040010780e80b5000111100403148000c4064041d941000c620010b01c60000d1980e9a18007540c00507140750b6424035802c8403041d81d4480907058000302400d001a400a0104000901030340000300030700103080d1260021440050320060540b644c45c0c0358a95103085503801e403203e1883c030000780c82d52507030369008105080e40151580350009034000020012510140b00850103950058400a29511550819641b80c2c040246440c158032418500050005490250003d04000b980d160000365140110103000640c10b5004a840b41340320301c0c10008516021480350346064149403440100d8008141120010200381c241840601c3c1400450400e000b054880140103a000139020604040700c0d04801500c22000c1c000d00e40003c104004 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 941523156 1250 941521906 941521961
    0xc0e0610141608030a0b0a1d0c0d0f02120603060604090b2406070f02010216061b11030f030310120305030a0b03030d090b0a050f01150c050a08160b0901 67
    0x74044a1980c0c02d000d20940290f0307110502e03e6001101d02c0d405541d12030709034000760f04001c41d84400401c0c41c9490014102400101c012030080f0050480c126101c02003000160100e06400451510071000021540d40c008201c03900c3c01c56604481140c021301c151008128142018854000503d07003101c80da484544401210f0300c0c462401140c1c0031044044080c0840d000e80c0d5980041c07511500c9007040c00350259042c4006030601d0924a94200a8803840e482084110740040381c8401243d41c1b01d800700d8010308d8071f1502a02041040851503007611401c81400d5100d04000000c6010341038030070f24210a207036075a0300c084418030107081c001e002a01c2400030995048070340d004040400340003016a82401e80c04502d510441e20444810340b55481140c06000e10802c01e4411503801c440b40c900848460b43c140010340841c0c03840d030300f00d44c000c00000113042010300c5030502ca1100c5c625481070102d0781e940320f08828000007010034602916235610400100348a450141300702480040e00e030450903860b010020 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 941524406 1250 941523156 941523197
    0x1d0703020409081e1b060708010608040c0906060f0201060911070308040f0b0a020301031101090303021e1212071d091801020c0703050610051816050f03040c0e0610 72
    0xc0d42290450000e01a4181c00309019070a5090304060640c05610342c41c503807051105e07451017050000510b4000c241031044442d400544103040d078002d41070030003e940310351030314451051b426888a20040d00c0c002021804942c420a1650b0444d0582d000340131039a1100c4511045642c6409020001c4804001420000e0702804865601a01522080c00354104d00e44903182e50080803a504c01000c1d500000501c1001008044241c500f002071809828450450780e02a548a0715001d101c901070b1154203089103104010032190725a00040c044081d201c0320f012208078110340c010703a1140c010410010094076007411858900d1a2407800411807886500c800d0300d07610312520301c481120201d540030041ca0390100c40c100850001140300304c2c010001c2e45004000d10010340080c0d00503511452070b18050510108091a8960f00102c001c0907403480b80c0e44442060b905031054941005004c1804000c002c28001c01c40d50090032030324407a683c0d185030342d41c003010045610070501254012926280e00126818241c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 941525656 1250 941524406 941524421
    0x1c18050a0312050c01110409050a0209090106031d030c1b0d050304060c080903010e0d09080f030f0904090f15420504060e01050301061203050a0302030604060506030106080405011d07030204 83
    0x7418618941400d01500a080d110b800740c1c6800c0e1b000c80041c2c200028074540c414a03030b0002c1f03010000c505241002d130014400c2d0a040c400d2508068440c004890280c01d030342100d102c400140c000300d9645018242d0100e0b211809035464185062882003070b00e1b2141400c0c08154445984034001d58038060400e03405031001007010030151410107090201d01d455450034854a030313480d04280b000303003040d80726800c000709450016002841a80c10110403082451400010381d10603900c010051340e100c110040103e0010322441d036020f005080b605502c3c50a0010348140ca06c1c84042126044c01000c0e400c1201c00785034109010038040440c80c1c0c036001008180200902c1c10401c48000e9504801079558000034282c40b143c1d082120b1403200d070b0b0b00401c09407509100f02d0000300f035082c0900ca103c200c641c83c040c00310f0195444000903d900000090b0180c1c2d515400072015240050030540c89503158100103154000894080300d840d842c1042841d800d215004507044440c8601005190321340c1954248005803894 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 941526906 1250 941525656 941525693
    0xe0703060506190909180c1a31030b1504020c03070b0c220603240302062b020a02100b1813060f0b010e010e091803160f0506071d0402030402121c18050a03 68
    0x503205100c0c50003e100c030700c1e41c00860092f1051619820200301c0b2038050700e1051000d42c0b00780c0c030400003000c5101011007562400358001c020603480703643d0800340800d80d11071900e03403031260720517070076801602500b03040c0b00300503a03405e66030030810f10b8111803000c00c1c0ca0b10610051080380206000800c0103180c10001002d0151501000c05940382030140e0100380c52414480f9130314003039008a01c2d40e4007250304220f6041640c0028205010241130b50000c07840d80c120b42c00c90148080c03c1403000800301d0a0440d541445264000400c020051000500d080203041c503000f400d0000d18120300608042d03225251184482500805c044803036100d2180d80481191241e0644645010910a015081110700441c6d440c40d4015400c448034200309241150400c00001c1010040c0200a400c4003900718000d458507030f00c60401c0e00d0043c0d50f600c841c0001001048180810406403098800400440d01c0042803824802d41da52204041e80d241a40800c812001c81d0007502d030051541c401c1000814140140160f10004 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 941528156 1250 941526906 941526967
    0x11a1606020c0d02070611070f09090f0503030403020a0b010b070201173408090613061a03161703040503121608130e0703060506190909180c1a 63
    0x61100400341002416503d0740d01680296404211054001010401c10a060806420f5650801400e95243c69450003001080c6a40f40b20b60004c2041002d0100521500402101d8413031400340b80081d40d522804004039044042c1c01d000141a500250580d00200c4d416159075614843d2120075411080d4010030368003448000b038682c6000c88011800551240440c409501103a41d98280c0140903c0340181200c00107a004404000446404030358005405501c0400400d80c0d04130307a0401008900d205541e15458080c0441c82c140c075620000c551000c85070a07544985006091440c403a450f40107a100da41e81540182002c903070308880d5000200017020124444410340341c0b803601e4182454009500203094a0a00d50f028043e44a12004599003c00340e840c062091030b0401002c26550301402040741424682082155482d5002c2c110941c050a50b9440400922440a446a14242122a00340c40c0110154170118103c410003040c0078803880740c6440589468665500d03e4041c0c51080e081703110706035 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 941529406 1250 941528156 941528167
    0x3050714010c0308040f060b0d20010c0b041b09020c0a140705030c0d06060b070f030201060806270c040f020904050f1b0313020316140f010212090a080304060314011a160602 76
    0x1601d00c0150071541e406501030310480f02e03203103071041c80e074ac64100003050500c400322820400180038044503070303030103640200950f141038107041d51056503149a411211000f400441c50f101d2228000851812503806070f135103c1500e105400d0301a0312928203000c0d450305500f200014a0b01410600280e0f40c041d481040e0000311959564140f100c1500000022a80f00e00098959014154240030700c80141c10a0009400c150405032050040c0501d008885204c02060180288200e44140072403181d01c48064000d0029254441055000758410b1745002e01c40d81c540004182e1780d07441c9502641c4610780904e048035640e50b00d104a4078254000034403c080040720030398481c006843c00d02420b50344107501d00c031b6545e5260510000240d07642030b5240041c06220340c100c814030140c1c1d0014002c20b110901da10610b03036418901020464141c040d400c81c05040c40000340016001d43c2c164030105023075a071410380c0b48060b600d0303044107030703241e0901c00c2d0084015005000d140541808480f04249080c4140b90051608 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 941530656 1250 941529406 941529409
    0x110f1b030705030403020a080c10030c0c0209010305030c2e090f05013204030f05030601030902030703051507080c070206030a090219030c1a0d0e031303050714010c0308040f060b 78
    0x5520401c401c444582010908204500f060140000078049010144ca250100344021030301c22801c904032102090785589281a1990003003030310401c1c85030081c001908039a141d08010741e40e50f2145984080741d100c5d0710503005440108003600c0c1c1c25000034000c030711031241001503005c019119507901610409140844440001c40174400c0308442c0807580b404250540c040a00c1c001103141c12502d200501c0e2201c010440040d50001809148100c1418415129258800120000c4c07450b0003000b50588200342000c401d012002034850040311100b2000c0c010b981d0303225012030307020b4021741304808021000d20840c030051500f00003460340079070401d03000101100c040e000038072160b05075035070002090146a010f20a12442d03160035000342003c0180e03402c840c0421901401c440c4900c070414062290b840b000720441020620855800d1421500d00350940b0b600d0f030424685501903840b41d40800f00c110f0f010748030f00354062030520f4803194140c1c4a001e05c41d500c0d5120741e204500204821100c0790340d5003c20784031a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 941531906 1250 941530656 941530663
    0x10030b0d0f0302070b030a060f050f2103130308030916080a0b0403020c101205060a0501140c03070203011401080d0c0b01090e073804050306060111010b21060a110f1b 73
    0x2d0742003c2e40c0410390b89d04d480030001b9003028907080180121501541c001c03440c0c1381c07542901c581014151105207200c00d80751107a411030003064000d0b8500c8002110000070300c0001005540140381410685001003014035a52503101d49500c0f0301501500040e4408003c241403400d07040d4004e01a0060b90342c80101c1200195038020305038644004a03c0405103008140310900c90240c0c407071001e80b0b05210075801c01c0c0010341848039150a1200c045000136254034001404c2c070a48151070b90203002404811544050411b031040240034940e00b0303100341c1c5281b6a0151040e1440d4103d83e4000c45201c0c1c0c40d0742804050009042c40f020486101d100f41100040c950300342c06508500c50000384248000610348400e0360705442c03122103880c401c602d401c2c08140f19a0380c02084c000e4015800b420550500005035040d18090310908140c2640448103241000384c01d0704022810714100e41040c1980e200e6034800403c10308540c9840702c81076504105010108443c004840100b80801001c3d035105030f00305144040d1841d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 941533156 1250 941531906 941531911
    0xc0302030d0f1e0e0d050102040b130510031107020607020f10050309010c030902031c14070606031403130504050606040b0c010e01450f030e10030b0d0f0302070b03 72
    0x7544810b0061449501074a4070341500451120a00d055000c81c0008105894944000c1c0c425141c00300d01c8400c1040c254110360060000c031a400d03440d801c803e141d00003082154070a81b805154100d8040041c1e6200340b1400d0b4501d101290070f20700302082ca409000040c0c0000f14126040b4280c0700c0103920300d07581d00341341c2c40d8480ca45644007980c2c1e10703000c8482c909441c101242003081c1403c2100c0500180c0d0081810159003110003103070076050840c2c1c0400c4030345045550740650382440000d0580c052200b260401c0054a0180c00401d07000c03400001501c0d80e80c491565036034040f114002060241c0d28081e0007071500004001c00c664106a2039041c100700551000e20340700a581c0d514101d01d05032203001e010b50394505441c3d00c103102c0048c030400640c0030700f0301825038490001c4a94888107222150000b5448030200e402000c800c820b003249203006852440700700822032141040034150403aa52080c0038881000c1d4014003408140507a562b980103105504090450a43c012240d0108486846202951 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 941534406 1250 941533156 941533183
    0x40902120406060f03050c10200d02150f0a0b040e030a0201150e0103020303040603050603031911100b0a0311040e010507170f22031707030f0e0114130c030203 70
    0x6581050300c2c0500c00c4601980c402c2850710f00c101c0040000c910f02007500380841e0f4003980d02c81d50351107108000722000707602004c40d44078022800902180c400710010b08800840626002c44002000c11410b80006010448444146d20790040019000950300d40110826190251000c11800751080816086401c1141c0d401e0042c0c2d5519141740d00420002151030013400c201107104620b50458003c29104c1c0308030f0040310107040d10781000c110640c50400407291104120074021035000440c2034014080c5151501005161040300503c01c40c803441072041464208000700072240c0c42d03180d582d40d511000100c0b443d0b980e0042d80d4011aa40a0400380500c034440c4030107550709075141985038040859586c0203010b105004004000f00f0070391111903004560b44d04040503038000b0584040c40e00321001c040c4114407903282840b00c0103105510390180c0148845004054040c40000c400c031070b549003218030400807000c040701c1541c04a0318451030386080580030360181e00003156203526038010a103401c0c405103001 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 941535656 1250 941534406 941534437
    0x10201091e17030408190e060a03051503011517010b090a020307090b0702030d0c150e0f0712020904030e0112022113050601031113050f010317030f010306020f040902 73
    0x2070701000500d452800700c2000d9070b4541415070130140c817088690b0103603c43c0f25022101200700c500119000340c00682245600404d03481d40c0c0d104040005001e050251505103030700c41e0f481c418007810b00d0107014002886800341041440c1501e40741030240302066025a500417556960600e544e1606c600001508c140000c0401507942c0c24042001420382c0d100360b0061740b121400384110070040c0d402060f142c80b0a049450594134940542c28400c0703892005c2100c0c100414a04482c041c0c2144000c24000b0003009480309980506680304064200c2180c0454029405854170000900281c054400890040c3c410b24003042c07600178061202c02241d20913140000c0030f0821010740300201890f060115405040c400d940181e0540c15641c482d0343d00810301008220413421841312070a912112305524481d16100018482400d00c1703e81002e0095013804241c450082035040759650580d0402280e016a0f50003003c0d00c016865911408029044510f80450380034041100041910031070001d4950440b0f0000301 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 941536906 1250 941535656 941535713
    0x150a0f060905090c0906030a1d0604140f030f0f16060501140a14010e01050903071217040b0a0c0c030209070f0908060c0a030203090114130501050f1306090201020109 73
    0xc0c0003111280e00c014410542c040422002074040c4c42030300d0400390261080340e183e4903a880c0d40707809407990700111944095800d101242401000070b80d5800380c2e01808103640740f40d01c1000b01030303155031081406004d141d01c01c1040c0c0c122070905038014079407407030380700ca250f410301c41e807803402e0050100303502d0302501c5007612000103200444d481c0b203540010780800c590f5280c00c640b410006026480b10014400d05000640280030341c030b81d00a03400c4410861008081e00c0d0425241c5000f41c22420480381c0c11341d94100c0142c0c0d950015407401085500307541001c0c83d0b1b41c0c1040d14600d012145070302e68a200300d40342417401000100507290404107034001c5545840d150824030310814003c0040440344d0040c001c69010710140700d03504401001301c8800d00003c1c5000340e542c0d0303a14016140508a040d034410710704d80a86040040c0100c0754001790340072074070401c000d200d203440310341d90300321424810f65184845555202025000408542c00798400d68411f00011800c4440c40c0c4542c0d80120b54640303000320981c2c01d00e68 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 941538156 1250 941536906 941536919
    0x907020607030c030207020a0302090613020417060c07050a1b08070906080c040c05030114040e0a1a16090b0c0f06090102030105011209050d050730090603180803150a0f 74
    0x34900991510303d000c50611b14a0b40006006210310b10003c0d004202082c00f06160b501c4001881c1408a04440155942e56494508031308501c1c0030090700034a4001c8101048049621400f00c40f803440d0003400400110840d5111407220740490a0b0f00803800090442c0041c1e6004140700b480000c00b1030030303130008499142c00c0704613040203003118502d0702c142d01d000a02d610320354016090360b0540301078550140c0e0800800340410300500310801040103a105505c000001c115001e21004121b22120803100c41c030351203240140a40b0b48200d01c80d00c01003103002d4802d000142d04030026101048001c800c656a039021120941d040c040b0940313800c03400c2c2c7d4000006102c80e50300600e4201c0502408181001080c4175a110307943c0f2907042009407402c20000182c604140176407691440040c2c0c0c030080c6000d40b4030b4103e1203848070052185000c1c00120b44007040c00201d2034064810609a5a40741c1400112a28a55150001d0b84e200803c0400c0e0201c0f040c86006094417800d07406000360204110040d5094180003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 941539406 1250 941538156 941538161
    0x11100f050601020d090608130812060a06050f0d0c210b0306130305040531050106090509190518010603030e03012004060311160602070209010f06051206030705090702060703 76
    0x8003854199480084d50300451035008442030201c80c001d142000060f2110080507c040c00505006460010041020641590180096030080004454100d2640c1e40d5201c00c0c1d031540240151000600d6081c0200040f2503195006070703002c941c1031b05e48060002e8a4000d408800828a000c00c040c03540d40305003807025400d0030000d841c2c1010251a68502c5c071801554010940e118a0207401d0140300550040c0205941480300c2040e1568298140200980848a1800140000d00c43c1d000040c41328280000c09040c9214200d01443c40003104210340c00c2400080000f4103000303443e0320f619080280c0b150b0f50408080c8a11409184660380300c80b40341003044105400c0d214030b130b40c404540c40b24201400d80c840c0b01040448003142d9240c1400325902026805178400c2e40200c0200300003c0000920031802c0107116401404140d10880e1002d1250340c039204220780c00b40445c004c640208100b04800310038081d01d250410b50108009040307444080d1240d01052005409841e4540035910000a200301c550701030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 941540656 1250 941539406 941539411
    0x60a030803090a06240323030a12112511040e03221d0c0f0f091305090309040b0d050f0a0b01060c150507120c0e15041a0a11100f05 58
    0x40c060041303518210300c002d514040751000529548540800da132092400e03144104030541024181c131b2712046010300141410752828806070029203001904080040c2c0001a1540c1152070003210a001c2281081c0c0381e20f440409402b502d000c490040707503050315270f070700d00459207007000100c055503c5494031100c0c5801010841520382404072041e0081c0140d070400b0f0b2031a0389540c102c18410885486070b10604407184212005650040c0c4006a101e081c108540014100c000041d0b41e01100c4e4505004180220383c0217941c1207043c0d4104210882003442e15030010b02ca8024010b1104a22801640d0342501c2c4c2101600c115099400003500c0609000c584142980108541e060403801a90f00e075a6401c1c20341c6050051400c0c0695800c00316401c0f034401c4030903400705184070344200b1a1f80c0c001c1f44040c02c8a51040c0364188a60700c020322541a0081500a586c00c5600608000001c00c2e0350f02140070040d003091000c00100010541c034502c100c00c0030000500c8440d5040e400095034500a0503081c141d4800 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 941541906 1250 941540656 941540681
    0x30c1406030f1b1201030f030f05032413020301030b0f010b16060c0318111e09061201020c0706080103060507030b010c1203111209010e070602030a0503060a030803090a06 75
    0x40c03040110019201102c15800072407040100b102031507102404440f80039103101c0200c016a101d0001c41002440090699014000c0c2c40306030b00c0d006101402c0351709100440382d82c3c0e80803011100303824a40c2010030074074040c0d5100400c0b20040d0010002c0c40c00803078100740c0c01501c0d400c0c0000709204001d40140207490151221003040f92420f0120103c4900c00c804103800106200d5599482442407407280e032017207283d203c0802c00c0d010380c4c44443c02e011060198a000d4184a0310f41007040c5c00c2040c017203d101070403529015101c00115643d49040040415440c044c55119540801140b18041c07024041c40303002c1e0410340c5941c00b441d410b50811604a803001003520051516007a1114001da03044a1001d101c3d50b884541c0d42100e90107500c0c210054030a031513102000a80104500c45a41110001244601c040310000c00080c01d21469055440110380f1514000d0b802c10400c20404902c40c1d1b009540c00700b006031403e046140d0780e94450145904c00c585641454018103040c03001c110640c000d046030380780b6 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 941543156 1250 941541906 941541919
    0x80d090515070203060708150909031c2c010e1603150504020f040b0406031e02190302150c0f1608010506101d1f02010c080115050403031d0a030c14 65
    0xb40c5601007640d460000d8000300511800d2030000c0c46945840342180d103500c2000d0041e249d1410103840141d982d0300038021851040000e0a41e44070902914410b802c1003042d40072807454900035080c550f10540c2030340300540303c0c25500c483c841c1072031040810000200340d41e201d03000d000c0e551650402041241c411240c140050b400c280078480542d0755a100006550400c5800203540904c0d200002c00800705680001c011040c145000c030000170fa00c40606000c07900960383c040070444100f2a003032142030607020095000380a50030a409031440300c0c02030082c55604c402150060521a03441a1400d0194038601c46c481300100c809002c9180e0038015990800c40654219003507011a503400f80200000c9016803c1c102d00c0ca104681050f41c3c0c1c480401040201390307002c5130030388814410082c06411450f44900102e1104030000644503400300c0c0da40704002e9655245414282103560440d03111084803070b10200f01c1d194000c80ca0207a030303540e07404000451080c41c44c1c1ca0703254a0700702c9094040e210000e40d1481400e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 941544406 1250 941543156 941543167
    0x30b09270a03021c110609100e0a0507030803063f011509020a170c0c06011512021b060f070e1e040b010c080c010509010b040915090507080d090515 65
    0x980002d01001c5004d15088a88220754140b0002c50302581d038030117800c54a02ca81414811500c102190b0580103500368901400711182c01f0100c02d60368041c03032100034801c0e0300001c81000412b041e6009503800c2900200081c1240c0c54181110114145040541326400c6a852000c0c91024800b01d1308010343d003000d0001c0c84580a481341e810a002d58034403c0054141d0001802c0303484902c10131031420080342d10300741040b0700c1c10110781030000380d0021480d1007901e20404002083c90b1448059900803407400d65601c40011000218840c0650058200200c108000c40303209445c04505102051103044500c3c1c032110f191410743c6000784080a6110028007840e0b015101104c07107050031b2a450100d04095a0100c0d08031440001241c41ca9510b810240480201103040003541c0010f401160040301e110000b0310000b40044208012100b44443c01491182000071000c0307040d4564001443c214007800503a50340c5a03540d40710780c0c140003519440307400058190314140518540210310341400300780ca071303a098140f0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 941545656 1250 941544406 941544413
    0x8071205040e1509040f17270102011404081612081f0f0314070f060c050105010f12110112050c07260a1b0f0303020301090b010806060d0c030b09270a 66
    0x4e410140000c1c000024080c1034600b800740c40105061001403070350006a03180340072008603021000e107000b140c0004000d502211103070740c070500030010342d9428251518402d458542d5540312561017242d02c26009c8a4410400b004a03560051900c1d0300c0c0c441d40c45000c110320b4142c2410901d200c0c5010317064818084c181c41405a40312000d042016250b103c1c06c8100d8003000780381c50a02d012115480444001014003000c201a85c0c04401009064410f000038082640c981c40b000c03504804a0184c2140c202ca400c201e400071596500030780c1d500c03034810305005071a00d842120110955038200d817508080500050890308002d140072480c0000c0064294900b0361a5032120107406a11800700c41744108443c00503003100800d107180c4580c1d101a030002c10100181c515140c003a001c1c0d00b00b481100c03059458aa41e40c02994051820300380700d080001e103a54502400340c29000000d000c54660f00e0105a9103108104035501c0b441754180c028018202c0080b00513030461071100c0c00c3c030440340c855a10b40c2c10640180000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 941546762 1106 941545656 941545669
    0x90d0312090c0e0f06060304062a091d19020c070807180b010302070201020d0f121802030c0d030f0f2601140d0b060d08071205040e15 59
    0x1580d507030b420348112500084502c0350300100d042000a000421030b9101e1110181d200412081e18ac460f5001d02c8007251071341400030f020a41050080c0181c000c24651540a54583d0a0381c02d02498021500701c4940c804c1ca082e025000e030086420641c0e800c1c148200406401c0c0d0808503074000390340f03e000c88203250312016000c101c10f141c022003801c554440c2c0203e036680f0b034060f001800781001c1000125141d4460340500b008101d010f40c00b1564040341070080c10361134a250a0015001b4065004050030100e172030307a186205146540041c2e0000c0c0e0400b08492a8000d035080c42d030002d2503001800c0d0760402000460348070b152010026641101040c00c4064181e0303070041105080400c0e84014400c50310384041c1c0103040c0400850008805d45030403240303000d51911800029083c4103c41e6629240f4015001581011490100e0700780403004043c2d03c5d0703590182520594a41113854070f000f103040c = true := by decide +kernel

theorem cover : BRFrame.Cov 941366906 941546762 := by
  have h0 := BRFrame.cov_init 941366906
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941366906 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 941366906 ≤ n) (h2 : n < 941546762) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
